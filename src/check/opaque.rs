// Return-position `impl Trait` (docs/ARCH.md 2.11).
//
// Collect gives each `fn f(..) -> impl Bounds` an opaque type
// `Opaque(def, args)` over every param in scope (edition 2024 captures
// them all; lifetimes are erased here and the borrow checker treats the
// call conservatively). Its bounds are stored over the fn's params with
// the opaque itself as one more param (`OpaqueInfo`), so a use
// substitutes `args ++ [self]`.
//
// The defining body checks against a fresh variable in place of its own
// opaque: the returns decide the hidden type, which must be fully known,
// must not name the opaque itself, and must satisfy every bound. The
// hidden type is stored over the defining fn's params
// (`GenTables::opaque_hidden`, from `reveal_plain` and the template
// check), and a plain fn's `FnInfo::ret` is revealed to it for codegen
// while callers keep the opaque (`Program::ret_view`).
//
// Callers (W-CHECK-G3) see only the opaque type and its bounds, as in
// rustc. A body that uses an opaque value is checked twice:
//
// - The opaque view (`OpaqueMode::View`): an opaque type is rigid; its
//   elaborated bounds join the env selection and normalization use
//   (`note_opaques`), so it has exactly the traits and associated types
//   its bounds name, plus the auto traits its hidden type has (rustc's
//   auto-trait leakage). Trait calls on it record picks, as a template's
//   calls do. Errors come from this check.
// - The revealed check (`OpaqueMode::Revealed`): every callee's opaque
//   return is its hidden type (`reveal`), and the calls replay the view's
//   picks, so the hidden type's inherent methods and other traits stay
//   out of reach. Lowering, borrowck, and codegen get this check.
//
// Instances check revealed and replay their template's picks. A template
// that uses an opaque value checks in the view; its borrow check still
// rejects opaque locals (L0602), so generic callers wait for region slots
// for opaque values (W-BORROW).
use super::*;
use crate::intern::FxMap;

impl Ctx<'_> {
    /// The return type a body checks against: the fn's return type, with
    /// its own `impl Trait` as a fresh variable the returns decide.
    pub(super) fn defining_ret(&mut self) -> Ty {
        let p = self.p;
        let ret = p.ret_view(self.fid);
        let TyKind::Opaque(od, args) = self.tys.kind(ret) else { return ret };
        let owner = p.gx.instances.get(&self.fid).map_or_else(|| p.def_id(self.fid), |i| i.template_def);
        if p.gx.opaques.get(&od).is_none_or(|o| o.owner != owner) {
            return ret;
        }
        let v = self.new_var(false);
        self.own_opaques.push((od, args, v));
        v
    }

    /// `t` itself, or the variable standing for its hidden type when `t`
    /// is an opaque type this body defines.
    pub(super) fn map_own_opaque(&self, t: Ty) -> Ty {
        match self.tys.kind(t) {
            TyKind::Opaque(od, args) => self.own_opaques.iter().find(|(d, a, _)| *d == od && *a == args).map_or(t, |&(_, _, v)| v),
            _ => t,
        }
    }

    /// Queues the bounds of the body's own opaque types as obligations
    /// on their hidden types. Binders are region-erased here, as the
    /// body's other types are.
    pub(super) fn push_opaque_bounds(&mut self, span: Span) {
        let p = self.p;
        for (od, args, v) in self.own_opaques.clone() {
            let Some(info) = p.gx.opaques.get(&od) else { continue };
            let mut full: Vec<GenericArg> = self.tys.args(args).to_vec();
            full.push(GenericArg::Ty(v));
            for &pred in &info.bounds {
                match crate::traits::index::subst_predicate(&mut self.tys, pred, &full) {
                    Predicate::Trait(b) => self.obl.push(obligations::Obligation::Trait { trait_ref: b.value, span, depth: 0 }),
                    Predicate::AssocEq(b) => self.obl.push(obligations::Obligation::AssocEq { eq: b.value, span }),
                    Predicate::TypeOutlives(ty, Region::Static) => self.obl.push(obligations::Obligation::TypeStatic { ty, span }),
                    _ => {}
                }
            }
        }
    }

    /// Records the hidden type of each own opaque after body end, and
    /// rejects one the body did not decide or that names itself.
    pub(super) fn finish_opaques(&mut self, span: Span) {
        let p = self.p;
        for (od, _, v) in std::mem::take(&mut self.own_opaques) {
            let h = self.deep(v);
            if self.tys.flags(h).contains_infer() {
                self.err(
                    "L0610",
                    span,
                    "type annotations needed: the returned value's type behind `impl Trait` is not known",
                    "Annotate the returned value's type.",
                );
                continue;
            }
            if mentions_opaque(&self.tys, h, Some(od)) {
                self.err(
                    "L0110",
                    span,
                    "cannot resolve the `impl Trait` type: the returned value's type names it again (a recursive fn)",
                    "Return a concrete type, or box the recursion behind a trait object.",
                );
                continue;
            }
            let _ = p;
            self.out.opaque_hidden.push((od, h));
        }
    }

    /// Rejects a value of an opaque type in a body that gets code
    /// (L0602, see the file header): a revealed check that still has one
    /// (a hidden type lust does not know). Views may name them.
    pub(super) fn reject_opaque_uses(&mut self) {
        let p = self.p;
        if p.gx.opaques.is_empty() || self.is_template_check() || self.opaque_mode == OpaqueMode::View {
            return;
        }
        let n = self.out.expr_ty.len();
        for i in 0..n {
            let t = self.out.expr_ty[i];
            if mentions_opaque(&self.tys, t, None) {
                let e = ExprId(self.out.expr_base + i as u32);
                let span = self.span(e);
                self.errs.push(not_yet("L0602", span, "using the value of a fn that returns `impl Trait`"));
                return;
            }
        }
    }

    /// Adds the elaborated bounds of every opaque type in `t` this body
    /// has not met yet to its solve env (`Ctx::solve_env`), so selection
    /// and normalization answer for it as for a type parameter.
    pub(super) fn note_opaques(&mut self, t: Ty) {
        let p = self.p;
        if p.gx.opaques.is_empty() || !mentions_opaque(&self.tys, t, None) {
            return;
        }
        let mut found: Vec<Ty> = Vec::new();
        collect_opaques(&self.tys, t, &mut found);
        for o in found {
            if self.opaque_seen.contains(&o) {
                continue;
            }
            self.opaque_seen.push(o);
            let TyKind::Opaque(od, args) = self.tys.kind(o) else { continue };
            let Some(info) = p.gx.opaques.get(&od) else { continue };
            let mut full: Vec<GenericArg> = self.tys.args(args).to_vec();
            full.push(GenericArg::Ty(o));
            let written: Vec<Predicate> =
                info.bounds.iter().map(|&pred| crate::traits::index::subst_predicate(&mut self.tys, pred, &full)).collect();
            let more = crate::traits::solve::elaborate_in(&mut self.tys, &p.gx.index, &written);
            if self.opaque_env.is_empty() {
                self.opaque_env = self.env().to_vec();
            }
            for pred in more {
                if !self.opaque_env.contains(&pred) {
                    self.opaque_env.push(pred);
                }
            }
        }
    }

    /// A callee's return type as this check sees it: unchanged in the
    /// opaque view, with every opaque type replaced by its hidden type in
    /// a revealed check (`reveal`). Records the `Sig` read of each
    /// revealed opaque's defining fn (its fingerprint covers the hidden
    /// type), so a daemon rechecks this body when the hidden type moves.
    pub(super) fn callee_ret(&mut self, t: Ty) -> Ty {
        if self.opaque_mode != OpaqueMode::Revealed || !mentions_opaque(&self.tys, t, None) {
            return t;
        }
        let p = self.p;
        let mut found: Vec<Ty> = Vec::new();
        collect_opaques(&self.tys, t, &mut found);
        for o in found {
            if let TyKind::Opaque(od, _) = self.tys.kind(o)
                && let Some(info) = p.gx.opaques.get(&od)
            {
                let _ = p.sig_of(&mut self.out.reads, info.owner);
            }
        }
        // A generic definer's hidden closures are its template's; the
        // instance this call runs has its own, which body end maps in
        // once the args are known (`build_closure_map`).
        if !self.opaque_calls.contains(&t) {
            self.opaque_calls.push(t);
        }
        reveal(&p.gx.opaque_hidden, &mut self.tys, t, 0)
    }

    /// Body end: the closure map (`instance_closure_map`) of each generic
    /// opaque the revealed calls name, at its resolved args, for an
    /// instance mono made (none exists before mono). `zonk` applies it.
    /// Two instances whose hidden closures have the same type (`T` only
    /// in the body, not the captures) cannot be told apart: L0602.
    pub(super) fn build_closure_map(&mut self) {
        let p = self.p;
        let mut found: Vec<Ty> = Vec::new();
        for t in std::mem::take(&mut self.opaque_calls) {
            let t = self.deep(t);
            collect_opaques(&self.tys, t, &mut found);
        }
        let mut map: Vec<(Ty, DefId)> = Vec::new();
        // Per generic opaque met: its args and its hidden closure types.
        let mut met: Vec<(DefId, ArgsId, Vec<Ty>)> = Vec::new();
        for o in found {
            let TyKind::Opaque(od, args) = self.tys.kind(o) else { continue };
            // A method probe that lost records a call at vars nothing
            // decides; the call that stands has its args resolved.
            if self.tys.flags(o).contains_infer() {
                continue;
            }
            let Some(info) = p.gx.opaques.get(&od) else { continue };
            let Some(template) = p.local_def(info.owner.hash) else { continue };
            if p.gx.fn_templates.get(template.0 as usize).is_none_or(|t| t.is_none()) {
                continue;
            }
            let h = reveal(&p.gx.opaque_hidden, &mut self.tys, o, 0);
            let mut cts = Vec::new();
            collect_closures(&self.tys, h, &mut cts);
            if cts.is_empty() || met.iter().any(|(d, a, _)| *d == od && *a == args) {
                continue;
            }
            if met.iter().any(|(d, _, c)| *d == od && c.iter().any(|t| cts.contains(t))) {
                let span = p.fn_def(self.fid).name_span;
                self.errs.push(not_yet(
                    "L0602",
                    span,
                    "two calls of one generic `impl Trait` fn at different type args whose hidden closures have the same type",
                ));
                return;
            }
            met.push((od, args, cts));
            let args: Vec<GenericArg> = self.tys.args(args).to_vec();
            let Some(inst) = generics::instance_for(p, &self.tys, template, &args).filter(|&i| i != template) else {
                self.out.closure_map_pending = true;
                continue;
            };
            map.extend(instance_closure_map(p, &self.tys, h, template, p.def_id(inst)));
        }
        self.closure_map = map;
    }

    /// True when this check records its trait picks for a later check of
    /// the same body: a template check, or an opaque view.
    pub(super) fn records_picks(&self) -> bool {
        self.is_template_check() || (self.opaque_mode == OpaqueMode::View && !self.p.gx.opaques.is_empty())
    }
}

/// True when an opaque type's bounds name `trait_def` for it, directly
/// or through supertraits (`impl Error` is `Display` and `Debug`). The
/// structural queries (`has_display`, `has_debug`, `is_copy`) ask this
/// where they ask the env for a type parameter.
pub(crate) fn opaque_bound_holds(p: &Program, tys: &impl TyIntern, t: Ty, trait_def: DefId) -> bool {
    let TyKind::Opaque(od, _) = tys.kind(t) else { return false };
    let Some(info) = p.gx.opaques.get(&od) else { return false };
    fn reaches(p: &Program, from: DefId, want: DefId, seen: &mut Vec<DefId>) -> bool {
        if from == want {
            return true;
        }
        if seen.contains(&from) {
            return false;
        }
        seen.push(from);
        let Some(rec) = p.gx.index.trait_record(from) else { return false };
        rec.generics.predicates.iter().any(|pred| match pred {
            Predicate::Trait(b) => {
                matches!(p.tys.args(b.value.args).first().and_then(|g| g.as_ty()).map(|s| p.tys.kind(s)), Some(TyKind::Param(ParamId(0))))
                    && reaches(p, b.value.def, want, seen)
            }
            _ => false,
        })
    }
    // Every trait predicate of an opaque's bounds has the opaque as Self.
    info.bounds.iter().any(|pred| matches!(pred, Predicate::Trait(b) if reaches(p, b.value.def, trait_def, &mut Vec::new())))
}

/// What an opaque view hands its revealed check: its trait picks and the
/// Fn trait of each call of an opaque callable.
#[derive(Default)]
pub(super) struct ViewOut {
    pub picks: FxMap<ExprId, picks::TraitPick>,
    pub calls: FxMap<ExprId, closure::ClosureKind>,
}

/// How a value holds `impl Trait` values, from its type in the opaque
/// view (`view_hold`). Lowering marks the locals that hold one
/// (`Body::opaque_locals`): such a local captures every region of its
/// opaque values, and a `Drop` one also keeps them live to its drop.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Default)]
pub enum Hold {
    #[default]
    None,
    /// Only opaques whose bounds say `Copy`: rustc knows they have no
    /// drop glue, so they add nothing to the value's drop.
    Copy,
    /// An opaque rustc assumes has a destructor that uses every region
    /// it captures (its drop check cannot see the hidden type).
    Drop,
}

/// How a value of the view type `t` holds opaque values: an opaque type
/// itself, or one it owns by value (a reference or a `dyn` owns none; a
/// `dyn` made from one carries its captures in its own region).
pub(crate) fn view_hold(p: &Program, tys: &impl TyIntern, t: Ty) -> Hold {
    let in_args = |a: ArgsId| tys.args(a).iter().filter_map(|g| g.as_ty()).map(|e| view_hold(p, tys, e)).max().unwrap_or_default();
    match tys.kind(t) {
        TyKind::Opaque(..) if opaque_bound_holds(p, tys, t, p.gx.lang.copy) => Hold::Copy,
        TyKind::Opaque(..) => Hold::Drop,
        // A rigid projection of an opaque (`<impl IntoIterator as
        // IntoIterator>::IntoIter`) may hold what the opaque captures.
        TyKind::Projection(..) if mentions_opaque(tys, t, None) => Hold::Drop,
        TyKind::Slice(e) | TyKind::Array(e, _) => view_hold(p, tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().map(|&e| view_hold(p, tys, e)).max().unwrap_or_default(),
        TyKind::Adt(_, a) | TyKind::Closure(_, a) => in_args(a),
        _ => Hold::None,
    }
}

/// Fills a revealed check's `Checked::opaque_holds` and `local_holds`
/// from its opaque view's types: each expression, pattern, and binding
/// that holds an opaque value in the view gives its revealed type (the
/// type lowering gives the locals that hold its value). Also the values
/// the view moves where the revealed check would copy (`expr_moves`,
/// `local_moves`), and L0602 for a closure that the hidden type's
/// `Copy` makes borrow what rustc moves into it.
fn holds_from_view(p: &Program, fid: LocalDefId, view: &Checked, ck: &mut Checked, errs: &mut Vec<Diag>) {
    use crate::check::collect::is_copy;
    let moved = |v: Ty, r: Ty| view_hold(p, &view.tys, v) != Hold::None && !is_copy(p, &view.tys, v) && is_copy(p, &ck.tys, r);
    let expr_moves: Vec<bool> = view.expr_ty.iter().zip(&ck.expr_ty).map(|(&v, &r)| moved(v, r)).collect();
    ck.expr_moves = if expr_moves.contains(&true) { expr_moves } else { Vec::new() };
    let mut holds: Vec<(Ty, Hold)> = Vec::new();
    let mut add = |t: Ty, h: Hold| {
        if h == Hold::None {
            return;
        }
        match holds.iter_mut().find(|(x, _)| *x == t) {
            Some(e) => e.1 = e.1.max(h),
            None => holds.push((t, h)),
        }
    };
    for (&v, &r) in view.expr_ty.iter().zip(&ck.expr_ty).chain(view.pat_ty.iter().zip(&ck.pat_ty)) {
        add(r, view_hold(p, &view.tys, v));
    }
    let local_holds: Vec<Hold> = view.locals.iter().map(|l| view_hold(p, &view.tys, l.ty)).collect();
    for (h, l) in local_holds.iter().zip(&ck.locals) {
        add(l.ty, *h);
    }
    // Both checks bind the same patterns in the same order; a check
    // that did not leaves the bindings to the type match.
    let same = view.locals.len() == ck.locals.len() && view.locals.iter().zip(&ck.locals).all(|(a, b)| a.name == b.name && a.span == b.span);
    ck.local_holds = if same { local_holds } else { Vec::new() };
    ck.opaque_holds = holds;
    // Without lined-up bindings no binding is known to move: a binding
    // that might is not supported yet.
    let local_moves: Vec<bool> = view.locals.iter().zip(&ck.locals).map(|(v, r)| moved(v.ty, r.ty)).collect();
    if !same && local_moves.contains(&true) {
        let span = p.fn_def(fid).name_span;
        errs.push(not_yet("L0602", span, "an `impl Trait` binding whose hidden type is `Copy` when its bounds are not, here"));
    }
    ck.local_moves = if same && local_moves.contains(&true) { local_moves } else { Vec::new() };
    // A closure the view makes take a value it moves (by value) but the
    // revealed check lets borrow it (its hidden type is `Copy`): rustc's
    // closure owns the value, lust's would not.
    for c in &ck.closures {
        let Some(vc) = view.closures.iter().find(|v| v.def == c.def) else { continue };
        for cap in &c.captures {
            let by_value = vc.captures.iter().any(|v| v.root == cap.root && v.mode == closure::CaptureMode::Value);
            if cap.mode != closure::CaptureMode::Value && by_value {
                let span = p.ast.expr_span(c.expr);
                errs.push(not_yet("L0602", span, "a closure that takes an `impl Trait` value whose hidden type is `Copy` when its bounds are not"));
                return;
            }
        }
    }
}

/// How one check sees opaque types (see the file header).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OpaqueMode {
    View,
    Revealed,
}

/// `check_fn` for a body that is not a closure body: the opaque view,
/// then, for a body that gets code and uses an opaque value, the revealed
/// check that replays the view's picks. An instance checks revealed.
pub(super) fn check_fn_opaque<'p>(p: &'p Program, fid: LocalDefId) -> (Checked<'p>, Vec<Diag>) {
    use generics::FnClass;
    if p.gx.opaques.is_empty() {
        return check_fn_mode(p, fid, OpaqueMode::View, ViewOut::default());
    }
    match p.gx.fn_class.get(fid.0 as usize) {
        Some(FnClass::Instance) => check_fn_mode(p, fid, OpaqueMode::Revealed, ViewOut::default()),
        Some(FnClass::Template | FnClass::TemplateClosure | FnClass::Stub) => check_fn_mode(p, fid, OpaqueMode::View, ViewOut::default()),
        _ => {
            let (view, errs) = check_fn_mode(p, fid, OpaqueMode::View, ViewOut::default());
            let uses = view.expr_ty.iter().chain(view.pat_ty.iter()).any(|&t| mentions_opaque(&view.tys, t, None));
            if !errs.is_empty() || !uses {
                return (view, errs);
            }
            let out = ViewOut { picks: view.trait_picks.iter().copied().collect(), calls: view.closure_calls.iter().copied().collect() };
            let (mut ck, mut errs) = check_fn_mode(p, fid, OpaqueMode::Revealed, out);
            holds_from_view(p, fid, &view, &mut ck, &mut errs);
            (ck, errs)
        }
    }
}

/// `check_fn` in the opaque view only: the hidden types of the body's
/// own opaques, before any caller is revealed (`reveal_plain`).
pub(crate) fn check_fn_view<'p>(p: &'p Program, fid: LocalDefId) -> (Checked<'p>, Vec<Diag>) {
    check_fn_mode(p, fid, OpaqueMode::View, ViewOut::default())
}

/// `t` with every opaque type replaced by its hidden type at its args,
/// again inside the result (a hidden type may name another opaque). An
/// opaque with no stored hidden type stays (the revealed check then
/// rejects the value, L0602).
pub(crate) fn reveal(hidden: &FxMap<DefId, Ty>, tys: &mut impl TyIntern, t: Ty, depth: u32) -> Ty {
    if depth > 32 || !mentions_opaque(tys, t, None) {
        return t;
    }
    match tys.kind(t) {
        TyKind::Opaque(od, a) => match hidden.get(&od) {
            Some(&h) => {
                let a = reveal_args(hidden, tys, a, depth);
                let args: Vec<GenericArg> = tys.args(a).to_vec();
                let h = subst(tys, h, &args);
                reveal(hidden, tys, h, depth + 1)
            }
            None => t,
        },
        TyKind::Ref(r, m, e) => {
            let e = reveal(hidden, tys, e, depth + 1);
            tys.intern(TyKind::Ref(r, m, e))
        }
        TyKind::RawPtr(m, e) => {
            let e = reveal(hidden, tys, e, depth + 1);
            tys.intern(TyKind::RawPtr(m, e))
        }
        TyKind::Slice(e) => {
            let e = reveal(hidden, tys, e, depth + 1);
            tys.intern(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = reveal(hidden, tys, e, depth + 1);
            tys.intern(TyKind::Array(e, n))
        }
        TyKind::Tuple(ts) => {
            let old: Vec<Ty> = tys.tys_of(ts).to_vec();
            let new: Vec<Ty> = old.into_iter().map(|e| reveal(hidden, tys, e, depth + 1)).collect();
            let ts = tys.intern_tys(&new);
            tys.intern(TyKind::Tuple(ts))
        }
        TyKind::Adt(d, a) => {
            let a = reveal_args(hidden, tys, a, depth);
            tys.intern(TyKind::Adt(d, a))
        }
        TyKind::FnDef(d, a) => {
            let a = reveal_args(hidden, tys, a, depth);
            tys.intern(TyKind::FnDef(d, a))
        }
        TyKind::Closure(d, a) => {
            let a = reveal_args(hidden, tys, a, depth);
            tys.intern(TyKind::Closure(d, a))
        }
        TyKind::Projection(d, a) => {
            let a = reveal_args(hidden, tys, a, depth);
            tys.intern(TyKind::Projection(d, a))
        }
        _ => t,
    }
}

/// The closure types of a generic definer's hidden type `t`, each
/// mapped to the def of the same closure expression in the instance
/// `inst`: a check gives a closure the def of its parent plus its
/// ordinal (`Ctx::closure_def`), and an instance's closures sit under
/// the instance's def.
pub(crate) fn instance_closure_map(p: &Program, tys: &impl TyIntern, t: Ty, template: LocalDefId, inst: DefId) -> Vec<(Ty, DefId)> {
    let mut cts: Vec<Ty> = Vec::new();
    collect_closures(tys, t, &mut cts);
    cts.into_iter()
        .filter_map(|ct| {
            let TyKind::Closure(d, _) = tys.kind(ct) else { return None };
            Some((ct, instance_closure_def(p, d, template, inst)?))
        })
        .collect()
}

/// The instance's def for the template closure `d` (see
/// `instance_closure_map`), through enclosing closures.
fn instance_closure_def(p: &Program, d: DefId, template: LocalDefId, inst: DefId) -> Option<DefId> {
    use crate::def::{DefKind, child_hash};
    let e = p.gx.closures.get(&d)?;
    let (old, new) = if e.parent == template {
        (p.def_id(template), inst)
    } else {
        let pd = *p.gx.closure_fns.get(&e.parent)?;
        (pd, instance_closure_def(p, pd, template, inst)?)
    };
    let ord = (0..4096u32).find(|&o| child_hash(old.hash, DefKind::Closure, "{closure}", o) == d.hash)?;
    Some(DefId { krate: new.krate, hash: child_hash(new.hash, DefKind::Closure, "{closure}", ord) })
}

/// True when `t` names a closure of a template body (a hidden type's
/// closure before its instance is known, `Checked::closure_map_pending`).
pub(crate) fn mentions_template_closure(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    let mut cts = Vec::new();
    collect_closures(tys, t, &mut cts);
    cts.iter().any(|&ct| {
        matches!(tys.kind(ct), TyKind::Closure(d, _) if p.gx.closures.get(&d).is_some_and(|e| p.gx.fn_class.get(e.body_fn.0 as usize) == Some(&generics::FnClass::TemplateClosure)))
    })
}

/// The closure types in `t`, each once.
fn collect_closures(tys: &impl TyIntern, t: Ty, out: &mut Vec<Ty>) {
    let in_args = |a: ArgsId, out: &mut Vec<Ty>| {
        for g in tys.args(a) {
            if let GenericArg::Ty(e) = *g {
                collect_closures(tys, e, out);
            }
        }
    };
    match tys.kind(t) {
        TyKind::Closure(_, a) => {
            if !out.contains(&t) {
                out.push(t);
            }
            in_args(a, out);
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => collect_closures(tys, e, out),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().for_each(|&e| collect_closures(tys, e, out)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => in_args(a, out),
        _ => {}
    }
}

/// `t` with the def of each closure type `map` names replaced.
pub(crate) fn map_closure_defs(tys: &mut impl TyIntern, t: Ty, map: &[(Ty, DefId)]) -> Ty {
    let args = |tys: &mut _, a: ArgsId| {
        let old: Vec<GenericArg> = TyIntern::args(tys, a).to_vec();
        let new: Vec<GenericArg> = old
            .into_iter()
            .map(|g| match g {
                GenericArg::Ty(e) => GenericArg::Ty(map_closure_defs(tys, e, map)),
                g => g,
            })
            .collect();
        TyIntern::intern_args(tys, &new)
    };
    match tys.kind(t) {
        TyKind::Closure(d, a) => {
            let d = map.iter().find(|(x, _)| *x == t).map_or(d, |&(_, y)| y);
            let a = args(tys, a);
            tys.intern(TyKind::Closure(d, a))
        }
        TyKind::Ref(r, m, e) => {
            let e = map_closure_defs(tys, e, map);
            tys.intern(TyKind::Ref(r, m, e))
        }
        TyKind::Slice(e) => {
            let e = map_closure_defs(tys, e, map);
            tys.intern(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = map_closure_defs(tys, e, map);
            tys.intern(TyKind::Array(e, n))
        }
        TyKind::Tuple(ts) => {
            let old: Vec<Ty> = tys.tys_of(ts).to_vec();
            let new: Vec<Ty> = old.into_iter().map(|e| map_closure_defs(tys, e, map)).collect();
            let ts = tys.intern_tys(&new);
            tys.intern(TyKind::Tuple(ts))
        }
        TyKind::Adt(d, a) => {
            let a = args(tys, a);
            tys.intern(TyKind::Adt(d, a))
        }
        _ => t,
    }
}

/// `reveal` over each type arg of `a`.
fn reveal_args(hidden: &FxMap<DefId, Ty>, tys: &mut impl TyIntern, a: ArgsId, depth: u32) -> ArgsId {
    let old: Vec<GenericArg> = tys.args(a).to_vec();
    let new: Vec<GenericArg> = old
        .into_iter()
        .map(|g| match g {
            GenericArg::Ty(e) => GenericArg::Ty(reveal(hidden, tys, e, depth + 1)),
            other => other,
        })
        .collect();
    tys.intern_args(&new)
}

/// True when a value of type `t` may own a value of type `inner` (is it,
/// or holds it by value; a reference owns nothing it points at).
pub(crate) fn ty_contains(tys: &impl TyIntern, t: Ty, inner: Ty) -> bool {
    if t == inner {
        return true;
    }
    let in_args = |a: ArgsId| tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| ty_contains(tys, e, inner)));
    match tys.kind(t) {
        TyKind::Slice(e) | TyKind::Array(e, _) => ty_contains(tys, e, inner),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| ty_contains(tys, e, inner)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Projection(_, a) => in_args(a),
        _ => false,
    }
}

/// The opaque types in `t`, outermost first, each once.
fn collect_opaques(tys: &impl TyIntern, t: Ty, out: &mut Vec<Ty>) {
    let mut in_args = |a: ArgsId, out: &mut Vec<Ty>| {
        for g in tys.args(a) {
            if let GenericArg::Ty(e) = g {
                collect_opaques(tys, *e, out);
            }
        }
    };
    match tys.kind(t) {
        TyKind::Opaque(_, a) => {
            if !out.contains(&t) {
                out.push(t);
            }
            in_args(a, out);
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => collect_opaques(tys, e, out),
        TyKind::Tuple(ts) => {
            for &e in tys.tys_of(ts) {
                collect_opaques(tys, e, out);
            }
        }
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Projection(_, a) => in_args(a, out),
        _ => {}
    }
}

/// True when a type names an opaque type (the given one, or any).
pub(crate) fn mentions_opaque(tys: &impl TyIntern, t: Ty, which: Option<DefId>) -> bool {
    let in_args = |a: ArgsId| tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| mentions_opaque(tys, e, which)));
    match tys.kind(t) {
        TyKind::Opaque(d, a) => which.is_none_or(|w| w == d) || in_args(a),
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => mentions_opaque(tys, e, which),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| mentions_opaque(tys, e, which)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Projection(_, a) => in_args(a),
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            tys.tys_of(s.inputs).iter().any(|&e| mentions_opaque(tys, e, which)) || mentions_opaque(tys, s.output, which)
        }
        _ => false,
    }
}

/// Reveals each plain fn's own `impl Trait` return for codegen: checks
/// the defining body, and on success sets `FnInfo::ret` to the hidden
/// type while callers keep the opaque (`GenTables::opaque_ret_of`). A
/// body with errors keeps its opaque; the driver's check reports them.
pub fn reveal_plain(p: &mut Program) {
    if p.gx.opaques.is_empty() {
        return;
    }
    let defining: Vec<LocalDefId> = (0..p.fns.len() as u32)
        .map(LocalDefId)
        .filter(|&f| {
            p.gx.fn_class.get(f.0 as usize).is_none_or(|c| *c == generics::FnClass::Plain)
                && matches!(p.tys.kind(p.fn_info(f).ret), TyKind::Opaque(od, _) if p.gx.opaques.get(&od).is_some_and(|o| o.owner == p.def_id(f)))
        })
        .collect();
    for f in defining {
        let (hidden, ok) = {
            let (checked, errs) = check_fn_view(p, f);
            let h = checked.opaque_hidden.first().map(|&(_, h)| h);
            (h.and_then(|h| crate::check::generics::snapshot_ty(&checked.tys, h)), errs.is_empty())
        };
        if let (Some(owned), true) = (hidden, ok) {
            let h = crate::check::generics::build_owned_ty(p, &owned);
            let opaque = p.fn_info(f).ret;
            if let TyKind::Opaque(od, _) = p.tys.kind(opaque) {
                p.gx.opaque_hidden.insert(od, h);
            }
            p.gx.opaque_ret_of.insert(f, opaque);
            p.fns[f.0 as usize].ret = h;
        }
    }
    reveal_plain_rets(p);
}

/// Reveals the opaque types left in revealed plain fns' `FnInfo::ret` (a
/// hidden type that names another fn's opaque), so codegen sees concrete
/// types. Runs again once the template check has the hidden types of
/// generic fns.
pub fn reveal_plain_rets(p: &mut Program) {
    let mut revealed: Vec<LocalDefId> = p.gx.opaque_ret_of.keys().copied().collect();
    revealed.sort_by_key(|f| f.0);
    let hidden = p.gx.opaque_hidden.clone();
    for f in revealed {
        let r = p.fns[f.0 as usize].ret;
        p.fns[f.0 as usize].ret = reveal(&hidden, &mut p.tys, r, 0);
    }
}
