// Closures in body checking (docs/ARCH.md 2.9 and 2.12).
//
// A closure body checks inline in its parent fn, so inference is
// shared with the parent, as in rustc. Right after the body, capture
// analysis follows the Rust 2021 precise-capture rules (rustc's
// `upvar.rs` over an `ExprUseVisitor` walk) and fixes the closure's
// kind (Fn, FnMut, or FnOnce) and its type `Closure(def, args)`,
// where args are the capture types in capture order: the closure
// value is exactly a tuple of its captures (ARCH 4.5).
//
// Rule zero first: every expression or pattern form the walk does not
// model rejects the closure (L0820) when it touches a captured
// variable. A wrong capture mode would change drop order or moves
// without any error, so the walk never guesses.
use super::*;
use crate::ir::Proj;

/// Which Fn trait a closure implements at most (its kind), or which
/// trait a call goes through. Ordered: a later kind is weaker.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

/// How a closure captures one place. Ordered by rustc's merge
/// priority: when two uses meet, the later variant wins.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CaptureMode {
    /// A shared borrow: the env field is `&T`.
    Ref,
    /// A unique borrow of a place reached through `&mut` (rustc's
    /// unique immutable borrow): the env field is `&mut T`.
    UniqueRef,
    /// A mutable borrow: the env field is `&mut T`.
    MutRef,
    /// By value (moved or copied in): the env field is `T`.
    Value,
}

/// One captured place: a checker local plus IR projections (`Field`,
/// `Deref`, `Downcast`) below it, the capture mode, and the type of
/// the place itself (the env field type follows from the mode).
#[derive(Clone, Debug)]
pub struct Capture {
    pub root: u32,
    pub projs: Vec<Proj>,
    pub mode: CaptureMode,
    pub place_ty: Ty,
}

/// The checker's record of one closure expression. Lowering builds the
/// closure value and its body fn from it; mono registers it.
#[derive(Clone, Debug)]
pub struct ClosureInfo {
    pub def: DefId,
    pub expr: ExprId,
    pub kind: ClosureKind,
    pub inputs: Vec<Ty>,
    pub output: Ty,
    pub captures: Vec<Capture>,
    /// The closure's own type, `Closure(def, env field types)`.
    pub ty: Ty,
}

/// The env field type of one capture.
pub fn capture_field_ty(tys: &mut impl TyIntern, c: &Capture) -> Ty {
    match c.mode {
        CaptureMode::Value => c.place_ty,
        CaptureMode::Ref => tys.mk_ref(false, c.place_ty),
        CaptureMode::UniqueRef | CaptureMode::MutRef => tys.mk_ref(true, c.place_ty),
    }
}

/// One projection of a capture place while the analysis runs. `Index`
/// stands for any index or subslice step; analysis always truncates
/// before it (arrays are captured whole).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CProj {
    Deref,
    Field(u32),
    Downcast(u32),
    Index,
}

/// A place rooted at a checker local, with the type before each
/// projection (rustc's `ty_before_projection`) and the final type.
#[derive(Clone, Debug)]
struct CPlace {
    root: u32,
    projs: Vec<(CProj, Ty)>,
    ty: Ty,
}

impl CPlace {
    fn push(&mut self, pr: CProj, after: Ty) {
        let before = self.ty;
        self.projs.push((pr, before));
        self.ty = after;
    }
}

/// What an expression is, for capture purposes.
enum Cat {
    Place(CPlace),
    /// A value that is not a place: its uses capture nothing by themselves.
    Rvalue,
    /// A place form the analysis does not model (raw pointers,
    /// overloaded derefs): reject when it reaches a captured variable.
    Bad,
}

/// The state of one capture walk.
struct CapWalk {
    first_local: u32,
    uses: Vec<(CPlace, CaptureMode)>,
    /// Roots read only through `let _ =` style fake reads.
    fake_reads: Vec<u32>,
    bad: Option<Span>,
}

impl CapWalk {
    fn upvar(&self, root: u32) -> bool {
        root < self.first_local
    }
}

impl<'p, 'a> Ctx<'p, 'a> {
    /// The stable def of one closure expression in this body: the
    /// parent's def hash plus the closure's ordinal in token order
    /// (ARCH 1.7). Instances and abstract instances have their own
    /// parent defs, so their closures get their own types.
    fn closure_def(&mut self, e: ExprId) -> DefId {
        if self.closure_order.is_none() {
            let (lo, hi) = self.f.def.exprs;
            let mut order: Vec<ExprId> = (lo..hi).map(ExprId).filter(|&x| matches!(self.p.ast.expr(x), Expr::Closure { .. })).collect();
            order.sort_by_key(|&x| (self.p.ast.expr_span(x).lo, x.0));
            self.closure_order = Some(order);
        }
        let ordinal = self.closure_order.as_ref().unwrap().iter().position(|&x| x == e).unwrap_or(usize::MAX) as u32;
        let parent = self.p.def_id(self.fid);
        DefId { krate: parent.krate, hash: crate::def::child_hash(parent.hash, crate::def::DefKind::Closure, "{closure}", ordinal) }
    }

    /// The expected closure signature from the expected type (ARCH
    /// 2.9): a variable with a pending `Fn`-family obligation gives
    /// the input tuple, and a pending `Output` equality the return.
    fn expected_closure_sig(&mut self, expected: Option<Ty>) -> Option<(Ty, Option<Ty>)> {
        let want = self.resolve(expected?);
        let TyKind::Infer(v) = self.kind(want) else { return None };
        let lang = self.p.gx.lang;
        let out_def = lang.output_of(lang.fn_once)?;
        let mut inputs: Option<Ty> = None;
        let mut output: Option<Ty> = None;
        for ob in self.obl.pending().to_vec() {
            match ob {
                obligations::Obligation::Trait { trait_ref, .. } if lang.is_fn_family(trait_ref.def) => {
                    let args: Vec<GenericArg> = self.tys.args(trait_ref.args).to_vec();
                    let self_ty = args.first().and_then(|g| g.as_ty()).map(|t| self.resolve(t));
                    if self_ty.is_some_and(|s| matches!(self.kind(s), TyKind::Infer(w) if w == v)) && inputs.is_none() {
                        inputs = args.get(1).and_then(|g| g.as_ty());
                    }
                }
                obligations::Obligation::AssocEq { eq, .. } if eq.assoc == out_def => {
                    let self_ty = self.tys.args(eq.trait_args).first().and_then(|g| g.as_ty()).map(|t| self.resolve(t));
                    if self_ty.is_some_and(|s| matches!(self.kind(s), TyKind::Infer(w) if w == v)) && output.is_none() {
                        output = Some(eq.ty);
                    }
                }
                _ => {}
            }
        }
        inputs.map(|i| (i, output))
    }

    /// Checks one closure expression: parameters, body, capture
    /// analysis, kind, and the closure type.
    pub(super) fn closure_expr(
        &mut self,
        e: ExprId,
        is_move: bool,
        params: &[ast::ClosureParam],
        ret: Option<ast::TyId>,
        body: ExprId,
        expected: Option<Ty>,
    ) -> Ty {
        let span = self.span(e);
        if let Some(t) = expected {
            let t = self.resolve(t);
            match self.kind(t) {
                TyKind::FnPtr(_) => {
                    self.err("L0820", span, "coercing a closure to a fn pointer is not supported yet", "Pass the closure to a generic parameter instead.");
                    return ERROR;
                }
                TyKind::Dyn(..) => {
                    self.err("L0820", span, "closures as `dyn Fn` values are not supported yet", "Pass the closure to a generic parameter instead.");
                    return ERROR;
                }
                _ => {}
            }
        }
        let def = self.closure_def(e);
        let sig = self.expected_closure_sig(expected);
        let expected_inputs: Option<Vec<Ty>> = sig.and_then(|(tup, _)| {
            let tup = self.deep(tup);
            match self.kind(tup) {
                TyKind::Tuple(ts) => Some(self.tys.tys_of(ts).to_vec()),
                TyKind::Unit => Some(Vec::new()),
                _ => None,
            }
        });
        if let Some(ins) = &expected_inputs
            && ins.len() != params.len()
        {
            self.err(
                "L0105",
                span,
                format!("this closure takes {} argument(s) but {} are expected", params.len(), ins.len()),
                "Match the closure parameters to the expected Fn signature.",
            );
        }
        let first_local = self.out.locals.len() as u32;
        let scope_len = self.scopes.len();
        let mut inputs: Vec<Ty> = Vec::with_capacity(params.len());
        for (i, prm) in params.iter().enumerate() {
            let exp = expected_inputs.as_ref().and_then(|v| v.get(i).copied());
            let t = match (prm.ty, exp) {
                (Some(w), exp) => {
                    let t = self.resolve_written(w);
                    if let Some(x) = exp
                        && !self.unify(t, x)
                    {
                        self.mismatch(prm.span, x, t);
                    }
                    t
                }
                (None, Some(x)) => x,
                (None, None) => self.new_var(false),
            };
            self.pattern(prm.pat, t, false);
            if !self.pat_always_matches(prm.pat) {
                self.err("L0110", prm.span, "refutable pattern in closure argument", "Use a pattern that matches every value.");
            }
            inputs.push(t);
        }
        let output = match (ret, sig.and_then(|s| s.1)) {
            (Some(w), exp) => {
                let t = self.resolve_written(w);
                if let Some(x) = exp
                    && !self.unify(t, x)
                {
                    self.mismatch(span, x, t);
                }
                t
            }
            (None, Some(x)) => x,
            (None, None) => self.new_var(false),
        };
        // The body: a new frame for `return`, and no outer loop labels.
        let saved_loops = std::mem::take(&mut self.loops);
        self.closure_rets.push(output);
        let bt = self.expr(body, Some(output));
        self.coerce_expr(body, bt, output);
        self.closure_rets.pop();
        self.loops = saved_loops;
        self.scopes.truncate(scope_len);
        // A parameter type the body left open may still be fixed by
        // a later call, as in rustc (`let add = |a, b| a + b;
        // add(2i64, 3)`). Structural uses in the body already needed
        // a known type (ARCH 2.12); what stays open is an error at
        // body end (`finish_closures`).
        let summary = self.template_closure_summary(e);
        let (kind, captures) = match summary {
            Some(s) => s,
            None => self.capture_analysis(e, is_move, body, params, first_local),
        };
        let mut fields: Vec<GenericArg> = Vec::with_capacity(captures.len());
        for c in &captures {
            fields.push(GenericArg::Ty(capture_field_ty(&mut self.tys, c)));
        }
        let ty = self.tys.intern_args(&fields);
        let ty = self.tys.intern(TyKind::Closure(def, ty));
        self.closures.push(ClosureInfo { def, expr: e, kind, inputs, output, captures, ty });
        ty
    }

    /// For a concrete instance of a template, the capture analysis
    /// the template's abstract check made (places, modes, and kind),
    /// with this instance's types. rustc analyzes captures once, on
    /// the generic body; re-running it per instance could change a
    /// capture where Copy or Drop differ between a parameter and its
    /// concrete type.
    fn template_closure_summary(&mut self, e: ExprId) -> Option<(ClosureKind, Vec<Capture>)> {
        let p = self.p;
        if p.gx.fn_class.get(self.fid.0 as usize) != Some(&generics::FnClass::Instance) {
            return None;
        }
        let template = p.gx.instances.get(&self.fid)?.template_local?;
        let (kind, shapes) = p.gx.template_closures.get(&(template, e))?;
        let mut out = Vec::with_capacity(shapes.len());
        for (root, projs, mode) in shapes {
            let mut t = self.resolve(self.out.locals.get(*root as usize)?.ty);
            let mut variant = 0u32;
            for pr in projs {
                t = self.resolve(t);
                t = match *pr {
                    Proj::Deref => match self.kind(t) {
                        TyKind::Ref(_, _, inner) => inner,
                        _ => return None,
                    },
                    Proj::Downcast(v) => {
                        variant = v;
                        continue;
                    }
                    Proj::Field(i) => {
                        let ft = self.field_ty_at(t, variant, i)?;
                        variant = 0;
                        ft
                    }
                    Proj::Index(_) => return None,
                };
            }
            out.push(Capture { root: *root, projs: projs.clone(), mode: *mode, place_ty: t });
        }
        Some((*kind, out))
    }

    /// The type of field `i` of variant `variant` of a resolved type.
    fn field_ty_at(&mut self, t: Ty, variant: u32, i: u32) -> Option<Ty> {
        match self.kind(t) {
            TyKind::Tuple(ts) => self.tys.tys_of(ts).get(i as usize).copied(),
            _ => {
                if let Some(e) = self.tys.option_elem(t) {
                    return (variant == 1 && i == 0).then_some(e);
                }
                if let Some((ok, err)) = self.tys.result_args(t) {
                    return match (variant, i) {
                        (0, 0) => Some(ok),
                        (1, 0) => Some(err),
                        _ => None,
                    };
                }
                let a = self.tys.local_adt(t)?;
                self.p.adt(a).variants.get(variant as usize)?.fields.get(i as usize).map(|f| f.ty)
            }
        }
    }

    // ---------- Capture analysis ----------

    /// Runs the Rust 2021 capture analysis over one closure body and
    /// returns the closure kind and its minimal capture list.
    fn capture_analysis(
        &mut self,
        e: ExprId,
        is_move: bool,
        body: ExprId,
        params: &[ast::ClosureParam],
        first_local: u32,
    ) -> (ClosureKind, Vec<Capture>) {
        let mut w = CapWalk { first_local, uses: Vec::new(), fake_reads: Vec::new(), bad: None };
        // Parameters bind from rvalues: nothing in them is captured,
        // but their patterns may name consts or variants only.
        let _ = params;
        self.cap_consume(body, &mut w);
        let span = self.span(e);
        if let Some(bad) = w.bad {
            self.err(
                "L0820",
                bad,
                "this use of a captured variable is not supported in closures yet",
                "Rewrite the use, or move the value into a local before the closure.",
            );
            return (ClosureKind::FnOnce, Vec::new());
        }
        // process_collected_capture_information: restrict precision,
        // infer the kind, then adjust for `move` and Drop types.
        let mut kind = ClosureKind::Fn;
        let mut processed: Vec<(CPlace, CaptureMode)> = Vec::with_capacity(w.uses.len());
        for (place, mode) in std::mem::take(&mut w.uses) {
            let (place, mode) = restrict_capture_precision(place, mode, &self.tys);
            let (place, mode) = truncate_for_optimization(place, mode, &self.tys);
            kind = kind.max(match mode {
                CaptureMode::Value => ClosureKind::FnOnce,
                CaptureMode::MutRef | CaptureMode::UniqueRef => ClosureKind::FnMut,
                CaptureMode::Ref => ClosureKind::Fn,
            });
            let (mut place, mut mode) = (place, mode);
            let first_deref = place.projs.iter().position(|(pr, _)| *pr == CProj::Deref);
            if is_move {
                if let Some(i) = first_deref {
                    truncate_place(&mut place, &mut mode, i, &self.tys);
                }
                mode = CaptureMode::Value;
            } else if mode == CaptureMode::Value
                && let Some(i) = first_deref
            {
                truncate_place(&mut place, &mut mode, i, &self.tys);
            }
            if mode == CaptureMode::Value && !self.cap_is_copy(place.ty) {
                for i in 0..place.projs.len() {
                    if self.has_drop_impl(place.projs[i].1) {
                        truncate_place(&mut place, &mut mode, i, &self.tys);
                        break;
                    }
                }
            }
            processed.push((place, mode));
        }
        // compute_min_captures: merge ancestors and descendants per
        // root, keeping roots in first-use order.
        let mut roots: Vec<(u32, Vec<(CPlace, CaptureMode)>)> = Vec::new();
        for (mut place, mut mode) in processed {
            let Some(ri) = roots.iter().position(|(r, _)| *r == place.root) else {
                roots.push((place.root, vec![(place, mode)]));
                continue;
            };
            let list = &mut roots[ri].1;
            let mut descendant_found = false;
            let mut j = 0;
            while j < list.len() {
                if is_ancestor(&place, &list[j].0) && place.projs.len() < list[j].0.projs.len() {
                    let (mut d, mut dm) = list.remove(j);
                    truncate_place(&mut d, &mut dm, place.projs.len(), &self.tys);
                    mode = mode.max(dm);
                    descendant_found = true;
                } else {
                    j += 1;
                }
            }
            let mut ancestor_found = false;
            if !descendant_found {
                for (a, am) in list.iter_mut() {
                    if is_ancestor(a, &place) {
                        truncate_place(&mut place, &mut mode, a.projs.len(), &self.tys);
                        *am = (*am).max(mode);
                        ancestor_found = true;
                        break;
                    }
                }
            }
            if !ancestor_found {
                list.push((place, mode));
            }
        }
        // Sort each root's captures by their field projections, as
        // rustc does, so captured fields drop in declaration order.
        for (_, list) in &mut roots {
            list.sort_by(|a, b| {
                let fa = a.0.projs.iter().filter_map(|(p, _)| if let CProj::Field(i) = p { Some(*i) } else { None });
                let fb = b.0.projs.iter().filter_map(|(p, _)| if let CProj::Field(i) = p { Some(*i) } else { None });
                fa.cmp(fb)
            });
        }
        for root in std::mem::take(&mut w.fake_reads) {
            if !roots.iter().any(|(r, _)| *r == root) {
                self.err(
                    "L0820",
                    span,
                    "a closure that reads a captured variable only through `_` is not supported yet",
                    "Use the variable in the closure, or drop the `_` pattern.",
                );
            }
        }
        let mut out: Vec<Capture> = Vec::new();
        for (_, list) in roots {
            for (place, mode) in list {
                let mut projs = Vec::with_capacity(place.projs.len());
                for (pr, _) in &place.projs {
                    projs.push(match *pr {
                        CProj::Deref => Proj::Deref,
                        CProj::Field(i) => Proj::Field(i),
                        CProj::Downcast(v) => Proj::Downcast(v),
                        CProj::Index => unreachable!("index projections are truncated"),
                    });
                }
                out.push(Capture { root: place.root, projs, mode, place_ty: place.ty });
            }
        }
        (kind, out)
    }

    /// Copy, for capture purposes. An unresolved type variable cannot
    /// be decided yet; the walk records it as unsupported first.
    fn cap_is_copy(&mut self, t: Ty) -> bool {
        let t = self.deep(t);
        is_copy(self.p, &self.tys, t)
    }

    /// True for a user Adt with a `Drop` impl (rustc
    /// `restrict_precision_for_drop_types`: no field is moved out of it).
    fn has_drop_impl(&mut self, t: Ty) -> bool {
        let t = self.deep(t);
        if self.tys.local_adt(t).is_none() {
            return false;
        }
        let args = self.tys.intern_args(&[GenericArg::Ty(t)]);
        let tr = TraitRef { def: self.p.gx.lang.drop, args, bindings: EMPTY_BINDINGS };
        let snap = self.snapshot_vars();
        let obl_len = self.obl_len();
        let sel = self.select_obligation(tr);
        self.rollback_vars(snap);
        self.obl_truncate(obl_len);
        matches!(sel, Selection::Impl { .. })
    }

    /// The place an expression denotes, rooted at a local, if it is one.
    fn cap_cat(&mut self, e: ExprId) -> Cat {
        let p = self.p;
        let ety = self.out.expr_ty[self.ei(e)];
        match (p.ast.expr(e), self.out.expr_res[self.ei(e)]) {
            (Expr::Path(_) | Expr::SelfValue, Res::Local(l)) => Cat::Place(CPlace { root: l, projs: Vec::new(), ty: self.out.locals[l as usize].ty }),
            (Expr::Field { base, .. } | Expr::TupleField { base, .. }, Res::Field { derefs, index }) => match self.cap_cat(*base) {
                Cat::Place(mut pl) => {
                    for _ in 0..derefs {
                        if !self.cap_deref(&mut pl) {
                            return Cat::Bad;
                        }
                    }
                    pl.push(CProj::Field(index), ety);
                    Cat::Place(pl)
                }
                other => other,
            },
            (Expr::Deref(inner), _) => match self.cap_cat(*inner) {
                Cat::Place(mut pl) => {
                    if self.cap_deref(&mut pl) {
                        Cat::Place(pl)
                    } else {
                        Cat::Bad
                    }
                }
                other => other,
            },
            (Expr::Index { base, .. }, Res::Index { derefs }) => {
                let bt = self.out.expr_ty[self.ei(*base)];
                let bt = self.cap_peel(bt, derefs);
                // `Vec` indexing is the overloaded `Index` trait: a
                // value of the call, with the base borrowed (the walk
                // records that borrow). Arrays and slices are places.
                if self.tys.vec_elem(bt).is_some() {
                    return Cat::Rvalue;
                }
                match self.cap_cat(*base) {
                    Cat::Place(mut pl) => {
                        for _ in 0..derefs {
                            if !self.cap_deref(&mut pl) {
                                return Cat::Bad;
                            }
                        }
                        pl.push(CProj::Index, ety);
                        Cat::Place(pl)
                    }
                    other => other,
                }
            }
            _ => Cat::Rvalue,
        }
    }

    /// Peels `n` reference layers off a type.
    fn cap_peel(&mut self, mut t: Ty, n: u8) -> Ty {
        for _ in 0..n {
            t = self.resolve(t);
            if let TyKind::Ref(_, _, inner) = self.kind(t) {
                t = inner;
            }
        }
        self.resolve(t)
    }

    /// Appends a builtin deref. False for anything but a reference.
    fn cap_deref(&mut self, pl: &mut CPlace) -> bool {
        let t = self.resolve(pl.ty);
        match self.kind(t) {
            TyKind::Ref(_, _, inner) => {
                pl.ty = t;
                pl.push(CProj::Deref, inner);
                true
            }
            _ => false,
        }
    }

    /// Records one use of a place reached from a captured variable.
    fn cap_use(&mut self, pl: CPlace, mode: CaptureMode, span: Span, w: &mut CapWalk) {
        if !w.upvar(pl.root) {
            return;
        }
        let mut pl = pl;
        let mut mode = mode;
        if mode != CaptureMode::Value {
            // Borrows stop at the first field of a packed struct (rustc
            // `restrict_repr_packed_field_ref_capture`).
            let packed = pl.projs.iter().position(|(pr, before)| {
                matches!(pr, CProj::Field(_))
                    && self.tys.local_adt(self.resolve(*before)).is_some_and(|a| self.p.adt(a).repr.kind == crate::ty::layout::ReprKind::Packed)
            });
            if let Some(i) = packed {
                truncate_place(&mut pl, &mut mode, i, &self.tys);
            }
        }
        // A mutable use must be legal on the original place: the
        // binding is `mut`, or the place is reached through `&mut`
        // (rustc E0594/E0596 on the upvar).
        if matches!(mode, CaptureMode::MutRef) && !self.place_mutable(&pl) {
            let name = self.name(self.out.locals[pl.root as usize].name).to_string();
            self.err("L0308", span, format!("cannot borrow `{name}` as mutable in this closure"), "Declare the variable with `let mut`.");
        }
        w.uses.push((pl, mode));
    }

    /// rustc `determine_capture_mutability` for one use place.
    fn place_mutable(&mut self, pl: &CPlace) -> bool {
        let mut m = self.out.locals[pl.root as usize].mutable;
        for (pr, before) in &pl.projs {
            if *pr == CProj::Deref {
                match self.kind(self.resolve(*before)) {
                    TyKind::Ref(_, mm, _) if mm.is_mut() => m = true,
                    _ => return false,
                }
            }
        }
        m
    }

    /// `consume_or_copy` of a place: a copy for Copy types is a shared
    /// borrow, anything else moves.
    fn cap_consume_place(&mut self, pl: CPlace, span: Span, w: &mut CapWalk) {
        if !w.upvar(pl.root) {
            return;
        }
        let Some(copy) = self.copy_known(pl.ty) else {
            w.bad.get_or_insert(span);
            return;
        };
        let mode = if copy { CaptureMode::Ref } else { CaptureMode::Value };
        self.cap_use(pl, mode, span, w);
    }

    /// Copy when inference already decides it: None while the answer
    /// hangs on an unbound type variable (rustc decides later, after
    /// the whole body; this subset rejects instead of guessing).
    fn copy_known(&mut self, t: Ty) -> Option<bool> {
        let t = self.resolve(t);
        match self.kind(t) {
            TyKind::Infer(v) => (v.is_int() || v.is_float()).then_some(true),
            TyKind::Ref(_, m, _) => Some(!m.is_mut()),
            TyKind::Tuple(ts) => {
                let elems: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                let mut all = true;
                for e in elems {
                    all &= self.copy_known(e)?;
                }
                Some(all)
            }
            TyKind::Array(e, _) => self.copy_known(e),
            TyKind::Closure(_, a) => {
                let elems: Vec<Ty> = self.tys.args(a).iter().filter_map(|g| g.as_ty()).collect();
                let mut all = true;
                for e in elems {
                    all &= self.copy_known(e)?;
                }
                Some(all)
            }
            _ => {
                if self.tys.is_string_ty(t) || self.tys.vec_elem(t).is_some() {
                    return Some(false);
                }
                if let Some(e) = self.tys.option_elem(t) {
                    return self.copy_known(e);
                }
                if self.has_unbound_var(t) {
                    return None;
                }
                let d = self.deep(t);
                Some(is_copy(self.p, &self.tys, d))
            }
        }
    }

    /// `consume_expr`: the value of `e` is used (moved or copied).
    fn cap_consume(&mut self, e: ExprId, w: &mut CapWalk) {
        let span = self.span(e);
        if self.cap_coerced(e, w) {
            self.cap_walk(e, false, w);
            return;
        }
        match self.cap_cat(e) {
            Cat::Place(pl) => self.cap_consume_place(pl, span, w),
            Cat::Bad => self.cap_bad_if_upvar(e, w),
            Cat::Rvalue => {}
        }
        self.cap_walk(e, false, w);
    }

    /// An assignment target: every place inside a destructuring
    /// form is mutated, so it captures as a mutable borrow of that
    /// place. Discards and `..` rest elements capture nothing.
    fn cap_assign_target(&mut self, e: ExprId, w: &mut CapWalk) {
        match self.p.ast.expr(e) {
            Expr::Tuple(elems) | Expr::Array(elems) => {
                for &el in elems {
                    if !matches!(self.p.ast.expr(el), Expr::Range { lo: None, hi: None, inclusive: false }) {
                        self.cap_assign_target(el, w);
                    }
                }
            }
            Expr::StructLit { fields, .. } => {
                for &(_, _, fe) in fields {
                    self.cap_assign_target(fe, w);
                }
            }
            Expr::Call { args, .. } if matches!(self.out.expr_res[self.ei(e)], Res::Variant(..)) => {
                for &arg in args {
                    if !matches!(self.p.ast.expr(arg), Expr::Range { lo: None, hi: None, inclusive: false }) {
                        self.cap_assign_target(arg, w);
                    }
                }
            }
            Expr::Underscore | Expr::Unit => {}
            _ => self.cap_borrow(e, CaptureMode::MutRef, w),
        }
    }

    /// `borrow_expr`: `e` is borrowed (or mutated, for `MutRef`).
    fn cap_borrow(&mut self, e: ExprId, mode: CaptureMode, w: &mut CapWalk) {
        let span = self.span(e);
        match self.cap_cat(e) {
            Cat::Place(pl) => self.cap_use(pl, mode, span, w),
            Cat::Bad => self.cap_bad_if_upvar(e, w),
            Cat::Rvalue => {}
        }
        self.cap_walk(e, mode != CaptureMode::Ref, w);
    }

    /// A coercion on `e` (rustc adjustments at a coercion site): the
    /// reborrowing forms borrow a place below `e`. True when handled.
    fn cap_coerced(&mut self, e: ExprId, w: &mut CapWalk) -> bool {
        let c = self.out.coerce[self.ei(e)];
        let (derefs, mode) = match c {
            Coerce::None => return false,
            Coerce::MutToShared => (1, CaptureMode::Ref),
            Coerce::Reborrow => (1, CaptureMode::MutRef),
            Coerce::Deref(n) => (n as usize + 1, CaptureMode::Ref),
            Coerce::SliceFromArray(m) | Coerce::SliceFromVec(m) => (1, if m { CaptureMode::MutRef } else { CaptureMode::Ref }),
            Coerce::BoxToRef(n, m) => (n as usize, if m { CaptureMode::MutRef } else { CaptureMode::Ref }),
            // A dyn coercion reborrows the source at the target's
            // mutability before it builds the fat pointer.
            Coerce::Unsize(t) => (1, if matches!(self.kind(t), TyKind::Ref(_, m, _) if m.is_mut()) { CaptureMode::MutRef } else { CaptureMode::Ref }),
            Coerce::StrFromString => {
                // Builtin derefs down to the `String`, then its
                // overloaded deref borrows it.
                let mut t = self.resolve(self.out.expr_ty[self.ei(e)]);
                let mut n = 0;
                while let TyKind::Ref(_, _, inner) = self.kind(t) {
                    n += 1;
                    t = self.resolve(inner);
                    if self.tys.is_string_ty(t) {
                        break;
                    }
                }
                (n, CaptureMode::Ref)
            }
        };
        let span = self.span(e);
        match self.cap_cat(e) {
            Cat::Place(mut pl) => {
                for _ in 0..derefs {
                    if !self.cap_deref(&mut pl) {
                        self.cap_bad_if_upvar(e, w);
                        return true;
                    }
                }
                self.cap_use(pl, mode, span, w);
            }
            Cat::Bad => self.cap_bad_if_upvar(e, w),
            Cat::Rvalue => {}
        }
        true
    }

    /// Marks the walk unsupported when `e` mentions a captured variable.
    fn cap_bad_if_upvar(&mut self, e: ExprId, w: &mut CapWalk) {
        if self.mentions_upvar(e, w.first_local) {
            w.bad.get_or_insert(self.span(e));
        }
    }

    /// True when any expression inside `e` resolves to a local below `first`.
    fn mentions_upvar(&self, e: ExprId, first: u32) -> bool {
        let (lo, hi) = (self.out.expr_base, self.out.expr_base + self.out.expr_res.len() as u32);
        let span = self.p.ast.expr_span(e);
        (lo..hi).any(|x| {
            matches!(self.out.expr_res[(x - lo) as usize], Res::Local(l) if l < first) && {
                let s = self.p.ast.expr_span(ExprId(x));
                s.file == span.file && s.lo >= span.lo && s.hi <= span.hi
            }
        })
    }

    /// `walk_block`: statements, then the tail is consumed.
    fn cap_block(&mut self, b: ast::BlockId, w: &mut CapWalk) {
        let p = self.p;
        let block = p.ast.block(b);
        for st in &block.stmts {
            match st {
                Stmt::Let { pat, init, els, .. } => {
                    if let Some(init) = init {
                        self.cap_local(*init, *pat, w);
                    }
                    if let Some(els) = els {
                        self.cap_block(*els, w);
                    }
                }
                Stmt::Expr { expr, .. } => self.cap_consume(*expr, w),
                Stmt::Item(..) => {}
                Stmt::Macro { .. } => w.bad = w.bad.or(Some(block.span)),
            }
        }
        if let Some(t) = block.tail {
            self.cap_consume(t, w);
        }
    }

    /// `walk_local`: the initializer is walked (not consumed), then the
    /// pattern binds from its place.
    fn cap_local(&mut self, init: ExprId, pat: PatId, w: &mut CapWalk) {
        if self.cap_coerced(init, w) {
            self.cap_walk(init, false, w);
            return;
        }
        self.cap_walk(init, false, w);
        match self.cap_cat(init) {
            Cat::Place(pl) => {
                if w.upvar(pl.root) {
                    w.fake_reads.push(pl.root);
                }
                self.cap_pat(pl, pat, false, w);
            }
            Cat::Bad => self.cap_bad_if_upvar(init, w),
            Cat::Rvalue => {}
        }
    }

    /// `walk_expr`: the uses inside `e` (its own place use is the caller's).
    fn cap_walk(&mut self, e: ExprId, mut_ctx: bool, w: &mut CapWalk) {
        let p = self.p;
        let res = self.out.expr_res[self.ei(e)];
        match p.ast.expr(e) {
            Expr::Int(..)
            | Expr::Float(_)
            | Expr::Bool(_)
            | Expr::Str(_)
            | Expr::Char(_)
            | Expr::Unit
            | Expr::Path(_)
            | Expr::SelfValue
            | Expr::Continue(_)
            | Expr::ConstBlock(_)
            | Expr::QPath { .. }
            | Expr::OffsetOf { .. }
            | Expr::Underscore => {}
            Expr::Block(b) | Expr::UnsafeBlock(b) => self.cap_block(*b, w),
            Expr::LabeledBlock { body, .. } | Expr::Loop { body, .. } => self.cap_block(*body, w),
            Expr::If { cond, then, els } => {
                self.cap_consume(*cond, w);
                self.cap_block(*then, w);
                if let Some(x) = els {
                    self.cap_consume(*x, w);
                }
            }
            Expr::While { cond, body, .. } => {
                self.cap_consume(*cond, w);
                self.cap_block(*body, w);
            }
            Expr::For { iter, body, .. } => {
                self.cap_consume(*iter, w);
                self.cap_block(*body, w);
            }
            Expr::Let { pat, scrut } => self.cap_local(*scrut, *pat, w),
            Expr::Match { scrut, arms } => {
                self.cap_walk(*scrut, false, w);
                let place = self.cap_cat(*scrut);
                for arm in arms {
                    match &place {
                        Cat::Place(pl) => {
                            if w.upvar(pl.root) {
                                w.fake_reads.push(pl.root);
                            }
                            self.cap_pat(pl.clone(), arm.pat, arm.guard.is_some(), w);
                        }
                        Cat::Bad => self.cap_bad_if_upvar(*scrut, w),
                        Cat::Rvalue => {}
                    }
                    if let Some(g) = arm.guard {
                        self.cap_consume(g, w);
                    }
                    self.cap_consume(arm.body, w);
                }
            }
            Expr::Call { callee, args } => {
                match res {
                    Res::ClosureCall { kind, derefs, .. } => {
                        let span = self.span(*callee);
                        match self.cap_cat(*callee) {
                            Cat::Place(mut pl) => {
                                let mut ok = true;
                                for _ in 0..derefs {
                                    ok &= self.cap_deref(&mut pl);
                                }
                                if !ok {
                                    self.cap_bad_if_upvar(*callee, w);
                                } else {
                                    match kind {
                                        ClosureKind::Fn => self.cap_use(pl, CaptureMode::Ref, span, w),
                                        ClosureKind::FnMut => self.cap_use(pl, CaptureMode::MutRef, span, w),
                                        ClosureKind::FnOnce => self.cap_consume_place(pl, span, w),
                                    }
                                }
                            }
                            Cat::Bad => self.cap_bad_if_upvar(*callee, w),
                            Cat::Rvalue => {}
                        }
                        self.cap_walk(*callee, kind == ClosureKind::FnMut, w);
                    }
                    // A call through a type parameter's Fn bound (a
                    // template check): the callee is the receiver.
                    Res::Method { derefs, autoref, .. } => self.cap_receiver(*callee, derefs, autoref, w),
                    _ => self.cap_consume(*callee, w),
                }
                for &a in args {
                    self.cap_consume(a, w);
                }
            }
            Expr::MethodCall { recv, args, .. } => {
                match res {
                    // A dyn method call through the vtable borrows its
                    // receiver like any other method call.
                    Res::Method { derefs, autoref, .. }
                    | Res::BuiltinMethod { derefs, autoref, .. }
                    | Res::DynMethod { derefs, autoref, .. } => {
                        self.cap_receiver(*recv, derefs, autoref, w);
                    }
                    // A call that failed to resolve already reported its error.
                    Res::None if !self.errs.is_empty() => {}
                    _ => self.cap_bad_if_upvar(*recv, w),
                }
                for &a in args {
                    self.cap_consume(a, w);
                }
            }
            Expr::Field { base, .. } | Expr::TupleField { base, .. } => self.cap_walk(*base, mut_ctx, w),
            Expr::Deref(inner) => self.cap_walk(*inner, mut_ctx, w),
            Expr::Index { base, index } => {
                if let Res::Index { derefs } | Res::SliceIndex { derefs } = res {
                    let bt = self.out.expr_ty[self.ei(*base)];
                    let bt = self.cap_peel(bt, derefs);
                    let overloaded = self.tys.vec_elem(bt).is_some() || matches!(res, Res::SliceIndex { .. });
                    if overloaded {
                        // `Index::index(&base)` / `IndexMut::index_mut(&mut base)`.
                        let span = self.span(*base);
                        match self.cap_cat(*base) {
                            Cat::Place(mut pl) => {
                                let mut ok = true;
                                for _ in 0..derefs {
                                    ok &= self.cap_deref(&mut pl);
                                }
                                if ok {
                                    let m = if mut_ctx { CaptureMode::MutRef } else { CaptureMode::Ref };
                                    self.cap_use(pl, m, span, w);
                                } else {
                                    self.cap_bad_if_upvar(*base, w);
                                }
                            }
                            Cat::Bad => self.cap_bad_if_upvar(*base, w),
                            Cat::Rvalue => {}
                        }
                    }
                    self.cap_walk(*base, mut_ctx, w);
                } else {
                    self.cap_bad_if_upvar(*base, w);
                }
                self.cap_consume(*index, w);
            }
            Expr::Binary { op, lhs, rhs } => {
                use BinOp::*;
                if matches!(op, Eq | Ne | Lt | Le | Gt | Ge) {
                    self.cap_borrow(*lhs, CaptureMode::Ref, w);
                    self.cap_borrow(*rhs, CaptureMode::Ref, w);
                } else {
                    self.cap_consume(*lhs, w);
                    self.cap_consume(*rhs, w);
                }
            }
            Expr::Unary { expr, .. } | Expr::Cast { expr, .. } => self.cap_consume(*expr, w),
            Expr::Ref { mutable, raw, expr } => {
                if *raw {
                    self.cap_bad_if_upvar(*expr, w);
                } else {
                    self.cap_borrow(*expr, if *mutable { CaptureMode::MutRef } else { CaptureMode::Ref }, w);
                }
            }
            Expr::Assign { lhs, rhs } => {
                self.cap_assign_target(*lhs, w);
                self.cap_consume(*rhs, w);
            }
            Expr::AssignOp { lhs, rhs, .. } => {
                self.cap_borrow(*lhs, CaptureMode::MutRef, w);
                self.cap_consume(*rhs, w);
            }
            Expr::StructLit { fields, update, .. } => {
                for (_, _, x) in fields {
                    self.cap_consume(*x, w);
                }
                if let Some(base) = update {
                    let span = self.span(*base);
                    if let Cat::Place(pl) = self.cap_cat(*base) {
                        let bt = self.resolve(pl.ty);
                        let named: Vec<Sym> = fields.iter().map(|(n, _, _)| *n).collect();
                        if let Some(a) = self.tys.local_adt(bt) {
                            let fs: Vec<(Sym, Ty)> = self.p.adt(a).variants[0].fields.iter().map(|f| (f.name, f.ty)).collect();
                            for (i, (n, ft)) in fs.into_iter().enumerate() {
                                if !named.contains(&n) {
                                    let mut fp = pl.clone();
                                    fp.push(CProj::Field(i as u32), ft);
                                    self.cap_consume_place(fp, span, w);
                                }
                            }
                        } else {
                            self.cap_bad_if_upvar(*base, w);
                        }
                    }
                    self.cap_walk(*base, false, w);
                }
            }
            Expr::Range { lo, hi, .. } => {
                for x in [lo, hi].into_iter().flatten() {
                    self.cap_consume(*x, w);
                }
            }
            Expr::Break { value, .. } => {
                if let Some(x) = value {
                    self.cap_consume(*x, w);
                }
            }
            Expr::Return(v) => {
                if let Some(x) = v {
                    self.cap_consume(*x, w);
                }
            }
            Expr::Tuple(xs) | Expr::Array(xs) => {
                for &x in xs {
                    self.cap_consume(x, w);
                }
            }
            Expr::ArrayRepeat { value, .. } => self.cap_consume(*value, w),
            Expr::Macro { kind, args, fmt, .. } => self.cap_macro(*kind, args, fmt, w),
            Expr::Closure { .. } => {
                // A nested closure: its captures that reach outside
                // this closure are uses here, with the same mode.
                let Some(inner) = self.closures.iter().find(|c| c.expr == e).cloned() else {
                    self.cap_bad_if_upvar(e, w);
                    return;
                };
                let span = self.span(e);
                for c in &inner.captures {
                    if !w.upvar(c.root) {
                        continue;
                    }
                    let mut pl = CPlace { root: c.root, projs: Vec::new(), ty: self.out.locals[c.root as usize].ty };
                    let mut variant = 0;
                    let mut ok = true;
                    for pr in &c.projs {
                        match *pr {
                            Proj::Deref => ok &= self.cap_deref(&mut pl),
                            Proj::Downcast(v) => {
                                variant = v;
                                let t = pl.ty;
                                pl.push(CProj::Downcast(v), t);
                            }
                            Proj::Field(i) => {
                                let t = self.resolve(pl.ty);
                                match self.field_ty_at(t, variant, i) {
                                    Some(ft) => pl.push(CProj::Field(i), ft),
                                    None => ok = false,
                                }
                                variant = 0;
                            }
                            Proj::Index(_) => ok = false,
                        }
                    }
                    if !ok {
                        w.bad.get_or_insert(span);
                        continue;
                    }
                    match c.mode {
                        CaptureMode::Value => self.cap_consume_place(pl, span, w),
                        m => self.cap_use(pl, m, span, w),
                    }
                }
            }
            // `x?` is `match Try::branch(x) { .. }`: the operand is consumed.
            Expr::Try(inner) => self.cap_consume(*inner, w),
            Expr::Await(_) | Expr::AsyncBlock { .. } | Expr::MacroCall(_) => self.cap_bad_if_upvar(e, w),
        }
    }

    /// A method receiver: builtin derefs, then a borrow per the
    /// autoref, or a by-value use. A deref that is not a reference
    /// (`String` to `str`) is an overloaded deref: it borrows the
    /// place reached so far and the rest is a temporary.
    fn cap_receiver(&mut self, recv: ExprId, derefs: u8, autoref: Autoref, w: &mut CapWalk) {
        let span = self.span(recv);
        let mode = match autoref {
            Autoref::None => None,
            Autoref::Ref => Some(CaptureMode::Ref),
            Autoref::RefMut => Some(CaptureMode::MutRef),
        };
        match self.cap_cat(recv) {
            Cat::Place(mut pl) => {
                let mut overloaded = false;
                for _ in 0..derefs {
                    let t = self.resolve(pl.ty);
                    if matches!(self.kind(t), TyKind::Ref(..)) {
                        self.cap_deref(&mut pl);
                    } else {
                        overloaded = true;
                        break;
                    }
                }
                match (overloaded, mode) {
                    (false, None) => self.cap_consume_place(pl, span, w),
                    (_, Some(m)) => self.cap_use(pl, m, span, w),
                    (true, None) => self.cap_bad_if_upvar(recv, w),
                }
            }
            Cat::Bad => self.cap_bad_if_upvar(recv, w),
            Cat::Rvalue => {}
        }
        self.cap_walk(recv, autoref == Autoref::RefMut, w);
    }

    /// Builtin macros: format arguments are borrowed, `vec!` and
    /// `assert!` consume, `assert_eq!` borrows both sides.
    fn cap_macro(&mut self, kind: MacroKind, args: &[ExprId], fmt: &[FmtPiece], w: &mut CapWalk) {
        let fixed = match kind {
            MacroKind::Vec => {
                for &a in args {
                    self.cap_consume(a, w);
                }
                return;
            }
            MacroKind::Assert => {
                if let Some(&c) = args.first() {
                    self.cap_consume(c, w);
                }
                1
            }
            MacroKind::AssertEq | MacroKind::AssertNe => {
                for &a in args.iter().take(2) {
                    self.cap_borrow(a, CaptureMode::Ref, w);
                }
                2
            }
            _ => 0,
        };
        // Format arguments are borrowed in argument order, as the
        // `format_args!` expansion takes `(&a, &b, ..)`.
        let _ = fmt;
        for &a in args.iter().skip(fixed) {
            self.cap_borrow(a, CaptureMode::Ref, w);
        }
    }

    /// `walk_pat`: bindings use the matched place, refutable tests read it.
    fn cap_pat(&mut self, place: CPlace, pat: PatId, has_guard: bool, w: &mut CapWalk) {
        let p = self.p;
        let span = p.ast.pat_span(pat);
        let mut place = place;
        let pi = (pat.0 - self.out.pat_base) as usize;
        for _ in 0..self.out.pat_derefs[pi] {
            if !self.cap_deref(&mut place) {
                if w.upvar(place.root) {
                    w.bad.get_or_insert(span);
                }
                return;
            }
        }
        let pty = self.out.pat_ty[pi];
        let read = |cx: &mut Self, pl: &CPlace, w: &mut CapWalk| cx.cap_use(pl.clone(), CaptureMode::Ref, span, w);
        match (p.ast.pat(pat), self.out.pat_res[pi]) {
            (Pat::Wild | Pat::Rest, _) => {}
            (Pat::Binding { .. }, PatRes::Binding { mode, .. }) => {
                if has_guard {
                    read(self, &place, w);
                }
                match mode {
                    BindMode::Move => {
                        place.ty = pty;
                        self.cap_consume_place(place, span, w)
                    }
                    BindMode::Ref(m) => self.cap_use(place, if m { CaptureMode::MutRef } else { CaptureMode::Ref }, span, w),
                }
            }
            (Pat::Binding { .. }, res) => {
                // A const or unit variant pattern spelled as a name.
                if !matches!(res, PatRes::Variant(a, _) if !self.multivariant(a)) {
                    read(self, &place, w);
                }
            }
            (Pat::At { inner, .. }, PatRes::Binding { mode, .. }) => {
                if has_guard {
                    read(self, &place, w);
                }
                match mode {
                    BindMode::Move => {
                        let mut whole = place.clone();
                        whole.ty = pty;
                        self.cap_consume_place(whole, span, w)
                    }
                    BindMode::Ref(m) => self.cap_use(place.clone(), if m { CaptureMode::MutRef } else { CaptureMode::Ref }, span, w),
                }
                self.cap_pat(place, *inner, has_guard, w);
            }
            (Pat::Lit(_) | Pat::Range { .. }, _) => read(self, &place, w),
            (Pat::Path(_), res) => {
                if !matches!(res, PatRes::Variant(a, _) if !self.multivariant(a)) {
                    read(self, &place, w);
                }
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Opt(true)) => {
                read(self, &place, w);
                let elem = self.tys.option_elem(self.resolve(place.ty)).unwrap_or(ERROR);
                let mut sub = place.clone();
                let t = sub.ty;
                sub.push(CProj::Downcast(1), t);
                sub.push(CProj::Field(0), elem);
                if let Some(&s) = elems.first() {
                    self.cap_pat(sub, s, has_guard, w);
                }
            }
            (Pat::TupleStruct { elems, .. }, PatRes::Res(is_ok)) => {
                // `Ok(x)` / `Err(e)`: variant 0 / 1, field 0 (as lowering).
                read(self, &place, w);
                if let Some(&s) = elems.first() {
                    let ft = self.out.pat_ty[(s.0 - self.out.pat_base) as usize];
                    let mut sub = place.clone();
                    let t = sub.ty;
                    sub.push(CProj::Downcast((!is_ok) as u32), t);
                    sub.push(CProj::Field(0), ft);
                    self.cap_pat(sub, s, has_guard, w);
                }
            }
            (Pat::TupleStruct { .. } | Pat::Struct { .. }, PatRes::Variant(a, v)) => {
                if self.multivariant(a) {
                    read(self, &place, w);
                }
                let mut base = place.clone();
                if p.adt(a).is_enum {
                    let t = base.ty;
                    base.push(CProj::Downcast(v), t);
                }
                let subs: Vec<(u32, PatId)> = match p.ast.pat(pat) {
                    Pat::TupleStruct { elems, .. } => {
                        let n = p.adt(a).variants[v as usize].fields.len();
                        map_tuple_elems(p.ast, elems, n).unwrap_or_default().into_iter().map(|(i, s)| (i as u32, s)).collect()
                    }
                    Pat::Struct { fields, .. } => {
                        let vf = &p.adt(a).variants[v as usize].fields;
                        fields.iter().filter_map(|&(n, s)| vf.iter().position(|f| f.name == n).map(|i| (i as u32, s))).collect()
                    }
                    _ => Vec::new(),
                };
                for (i, s) in subs {
                    let ft = self.out.pat_ty[(s.0 - self.out.pat_base) as usize];
                    let mut sub = base.clone();
                    sub.push(CProj::Field(i), ft);
                    self.cap_pat(sub, s, has_guard, w);
                }
            }
            (Pat::Tuple(elems), _) => {
                let n = match self.kind(self.resolve(place.ty)) {
                    TyKind::Tuple(ts) => self.tys.tys_of(ts).len(),
                    _ => elems.len(),
                };
                for (i, s) in map_tuple_elems(p.ast, elems, n).unwrap_or_default() {
                    let ft = self.out.pat_ty[(s.0 - self.out.pat_base) as usize];
                    let mut sub = place.clone();
                    sub.push(CProj::Field(i as u32), ft);
                    self.cap_pat(sub, s, has_guard, w);
                }
            }
            (Pat::Ref { inner, .. }, _) => {
                if self.cap_deref(&mut place) {
                    self.cap_pat(place, *inner, has_guard, w);
                } else if w.upvar(place.root) {
                    w.bad.get_or_insert(span);
                }
            }
            (Pat::Slice { prefix, middle, suffix }, _) => {
                let t = self.resolve(place.ty);
                let is_array = matches!(self.kind(t), TyKind::Array(..));
                let rest_only = prefix.is_empty() && suffix.is_empty() && middle.is_some();
                if !is_array && !rest_only {
                    read(self, &place, w);
                }
                for &s in prefix.iter().chain(suffix.iter()).chain(middle.iter()) {
                    let ft = self.out.pat_ty[(s.0 - self.out.pat_base) as usize];
                    let mut sub = place.clone();
                    sub.push(CProj::Index, ft);
                    self.cap_pat(sub, s, has_guard, w);
                }
            }
            (Pat::Or(alts), _) => {
                for &s in alts {
                    self.cap_pat(place.clone(), s, has_guard, w);
                }
            }
            (Pat::Paren(inner), _) => self.cap_pat(place, *inner, has_guard, w),
            _ => {
                if w.upvar(place.root) {
                    w.bad.get_or_insert(span);
                }
            }
        }
    }

    /// rustc `is_multivariant_adt`.
    fn multivariant(&self, a: AdtId) -> bool {
        let adt = self.p.adt(a);
        adt.is_enum && adt.variants.len() > 1
    }

    // ---------- Calls ----------

    /// Facts about a closure type for calls and selection: its kind,
    /// inputs, and output. Closures of this body answer from the
    /// checker's own record; others from the registered program table.
    pub(super) fn closure_facts(&self, def: DefId) -> Option<(ClosureKind, Vec<Ty>, Ty)> {
        if let Some(c) = self.closures.iter().find(|c| c.def == def) {
            return Some((c.kind, c.inputs.clone(), c.output));
        }
        let g = self.p.gx.closures.get(&def)?;
        Some((g.kind, g.inputs.clone(), g.output))
    }

    /// A call whose callee is a value, not a fn path: a closure (through
    /// any number of references), or a value of a type with an Fn
    /// bound (an abstract parameter in a template check).
    pub(super) fn value_call(&mut self, e: ExprId, callee: ExprId, args: &[ExprId], span: Span) -> Ty {
        let ct = self.expr(callee, None);
        // Function pointers and fn or constructor items call through
        // the value directly (fx-method-res / next), through at most
        // one reference layer, as lowering expects for `Indirect`.
        let mut peeled = self.resolve(ct);
        if let TyKind::Ref(_, _, inner) = self.kind(peeled) {
            peeled = self.resolve(inner);
        }
        if let Some(r) = self.callable_res(peeled) {
            if let Res::Variant(a, _) = r
                && !self.p.adt(a).is_enum
            {
                self.check_ctor_vis(a, span);
            }
            let Some((params, ret)) = self.callable_sig(peeled) else { return ERROR };
            self.set_res(e, r);
            self.check_args(&params, args, span);
            return ret;
        }
        let mut t = self.resolve(ct);
        let mut derefs: u8 = 0;
        loop {
            match self.kind(t) {
                TyKind::Closure(def, _) => {
                    let Some((kind, inputs, output)) = self.closure_facts(def) else {
                        self.err("L0820", span, "this closure call is not supported yet", "Call the closure where it is defined.");
                        return ERROR;
                    };
                    // In an instance, a call keeps the Fn trait the
                    // template resolved it through (FnOnce consumes the
                    // closure even when it is Fn), as rustc's generic body.
                    let mode = self.template_call_mode(e).unwrap_or(kind);
                    self.out.closure_calls.push((e, mode));
                    self.set_res(e, Res::ClosureCall { kind: mode, derefs });
                    self.check_args(&inputs, args, span);
                    return output;
                }
                TyKind::Ref(_, _, inner) if derefs < 8 => {
                    derefs += 1;
                    t = self.resolve(inner);
                }
                TyKind::Infer(v) if !v.is_int() && !v.is_float() => {
                    self.err("L0610", span, "type annotations needed: the type of this callee must be known here", "Annotate the callee's type.");
                    return ERROR;
                }
                TyKind::Error => return ERROR,
                // A type parameter or projection in a template check
                // calls through its Fn-family bound: Fn, else FnMut,
                // else FnOnce (rustc's order), lowered as a call of the
                // bound's method with the callee as receiver.
                TyKind::Param(_) | TyKind::Projection(..) => {
                    let Some((stub, autoref, params, ret)) = self.fn_bound_call(t) else {
                        for &a in args {
                            self.expr(a, None);
                        }
                        let tn = self.tn(t);
                        self.err(
                            "L0114",
                            span,
                            format!("`{tn}` is not a function: its bounds have no `Fn`, `FnMut`, or `FnOnce`"),
                            "Add an `Fn` bound to the type parameter.",
                        );
                        return ERROR;
                    };
                    let kind = match autoref {
                        Autoref::Ref => ClosureKind::Fn,
                        Autoref::RefMut => ClosureKind::FnMut,
                        Autoref::None => ClosureKind::FnOnce,
                    };
                    self.out.closure_calls.push((e, kind));
                    self.check_args(&params, args, span);
                    self.set_res(e, Res::Method { f: stub, derefs, autoref });
                    return self.normalize_here(ret);
                }
                _ => {
                    for &a in args {
                        self.expr(a, None);
                    }
                    let tn = self.tn(t);
                    self.err("L0114", span, format!("`{tn}` is not callable"), "Call a function, a closure, or a value with an Fn bound.");
                    return ERROR;
                }
            }
        }
    }

    /// The call mode a template's abstract check recorded for this call.
    fn template_call_mode(&self, e: ExprId) -> Option<ClosureKind> {
        let p = self.p;
        if p.gx.fn_class.get(self.fid.0 as usize) != Some(&generics::FnClass::Instance) {
            return None;
        }
        let template = p.gx.instances.get(&self.fid)?.template_local?;
        p.gx.template_calls.get(&(template, e)).copied()
    }

    /// Builtin Fn-family selection for a closure Self type (the
    /// `SolveCx::closure_select` hook).
    pub(super) fn closure_select_impl(&mut self, obl: TraitRef) -> Option<bool> {
        let lang = self.p.gx.lang;
        if !lang.is_fn_family(obl.def) {
            return None;
        }
        let args: Vec<GenericArg> = self.tys.args(obl.args).to_vec();
        let self_ty = self.deep(args.first()?.as_ty()?);
        let TyKind::Closure(def, _) = self.kind(self_ty) else { return None };
        let (kind, inputs, _) = self.closure_facts(def)?;
        let need = if obl.def == lang.fn_ {
            ClosureKind::Fn
        } else if obl.def == lang.fn_mut {
            ClosureKind::FnMut
        } else {
            ClosureKind::FnOnce
        };
        if kind > need {
            return Some(false);
        }
        let want = args.get(1).and_then(|g| g.as_ty()).unwrap_or(UNIT);
        let want = self.resolve(want);
        // `Fn()` sugar builds an empty tuple; `()` is the same type.
        if inputs.is_empty() {
            return Some(match self.kind(want) {
                TyKind::Unit => true,
                TyKind::Tuple(ts) => self.tys.tys_of(ts).is_empty(),
                _ => {
                    let ts = self.tys.intern_tys(&[]);
                    let empty = self.tys.intern(TyKind::Tuple(ts));
                    self.unify(want, empty)
                }
            });
        }
        let ts = self.tys.intern_tys(&inputs);
        let tuple = self.tys.intern(TyKind::Tuple(ts));
        Some(self.unify(want, tuple))
    }

    /// The output of a closure for `<C as FnOnce<A>>::Output`.
    pub(super) fn closure_output_impl(&mut self, assoc: DefId, self_ty: Ty) -> Option<Ty> {
        let lang = self.p.gx.lang;
        if Some(assoc) != lang.output_of(lang.fn_once) {
            return None;
        }
        let deep = self.deep(self_ty);
        let TyKind::Closure(def, _) = self.kind(deep) else { return None };
        self.closure_facts(def).map(|f| f.2)
    }
}

/// True when `a` is `b` or an ancestor of `b` (same root, `a`'s
/// projections a prefix of `b`'s).
fn is_ancestor(a: &CPlace, b: &CPlace) -> bool {
    a.root == b.root && a.projs.len() <= b.projs.len() && a.projs.iter().zip(&b.projs).all(|(x, y)| x.0 == y.0)
}

/// rustc `truncate_place_to_len_and_update_capture_kind`: a mutable
/// borrow whose dropped part dereferenced a `&mut` becomes unique.
fn truncate_place(pl: &mut CPlace, mode: &mut CaptureMode, len: usize, tys: &impl TyIntern) {
    if len >= pl.projs.len() {
        return;
    }
    if *mode == CaptureMode::MutRef
        && pl.projs[len..].iter().any(|(pr, before)| *pr == CProj::Deref && matches!(tys.kind(*before), TyKind::Ref(_, m, _) if m.is_mut()))
    {
        *mode = CaptureMode::UniqueRef;
    }
    pl.ty = pl.projs.get(len).map(|(_, before)| *before).unwrap_or(pl.ty);
    pl.projs.truncate(len);
}

/// rustc `restrict_capture_precision`: arrays and slices are captured
/// whole (truncate before any index).
fn restrict_capture_precision(mut pl: CPlace, mut mode: CaptureMode, tys: &impl TyIntern) -> (CPlace, CaptureMode) {
    if let Some(i) = pl.projs.iter().position(|(pr, _)| *pr == CProj::Index) {
        truncate_place(&mut pl, &mut mode, i, tys);
    }
    (pl, mode)
}

/// rustc `truncate_capture_for_optimization`: a place read through a
/// shared reference is captured as that reference's target.
fn truncate_for_optimization(mut pl: CPlace, mut mode: CaptureMode, tys: &impl TyIntern) -> (CPlace, CaptureMode) {
    if let Some(i) = pl.projs.iter().rposition(|(pr, _)| *pr == CProj::Deref)
        && matches!(tys.kind(pl.projs[i].1), TyKind::Ref(_, m, _) if !m.is_mut())
    {
        truncate_place(&mut pl, &mut mode, i + 1, tys);
    }
    (pl, mode)
}
