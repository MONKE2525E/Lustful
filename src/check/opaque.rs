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
// must not name the opaque itself, and must satisfy every bound. A
// plain fn's `FnInfo::ret` is then revealed to its hidden type for
// codegen (`reveal_plain`), and callers keep checking against the opaque
// (`Program::ret_view`).
//
// Callers see only the opaque type. Using such a value in a body that
// gets code (any check but a template's) is not supported yet (L0602):
// that needs the hidden types of generic instances and a replay of the
// caller's trait picks over them. Template checks may name opaque values.
use super::*;

impl Ctx<'_, '_> {
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
    /// (L0602, see the file header). Template checks may name them.
    pub(super) fn reject_opaque_uses(&mut self) {
        let p = self.p;
        if p.gx.opaques.is_empty() || self.is_template_check() {
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
            let (checked, errs) = check_fn(p, f);
            let h = checked.opaque_hidden.first().map(|&(_, h)| h);
            (h.and_then(|h| crate::check::generics::snapshot_ty(&checked.tys, h)), errs.is_empty())
        };
        if let (Some(owned), true) = (hidden, ok) {
            let h = crate::check::generics::build_owned_ty(p, &owned);
            let opaque = p.fn_info(f).ret;
            p.gx.opaque_ret_of.insert(f, opaque);
            p.fns[f.0 as usize].ret = h;
        }
    }
}
