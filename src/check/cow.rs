// `alloc::borrow::Cow` in body checking (W-STD-B): its inherent
// methods `into_owned` and `to_mut`, and `as_ref`, `borrow`, and
// `deref` to `&B`. The enum is a synthetic local Adt (collect.rs); its
// trait impls are lang facts (generics.rs) with glue in cgen/cow.rs.
use super::*;

impl<'p, 'a> Ctx<'p, 'a> {
    /// A method on a `Cow<B>` receiver, or None for other receivers and
    /// names (the other dispatch then runs).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn cow_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
    ) -> Option<Ty> {
        let b = crate::check::collect::cow_arg(&self.tys, base)?;
        let n = self.name(name).to_string();
        let owned = |cx: &mut Self| {
            let a = cx.tys.intern_args(&[GenericArg::Ty(b)]);
            let pr = cx.tys.intern(TyKind::Projection(AssocId(cx.p.gx.lang.assoc_owned), a));
            cx.normalize_here(pr)
        };
        let (bt, autoref, ret) = match n.as_str() {
            "into_owned" => {
                if derefs > 0 {
                    self.err(
                        "L0640",
                        name_span,
                        "`into_owned` through a reference is not implemented yet",
                        "Call it on the Cow value itself.",
                    );
                    for &a in args {
                        self.expr(a, None);
                    }
                    return Some(ERROR);
                }
                (Builtin::CowIntoOwned, Autoref::None, owned(self))
            }
            "to_mut" => {
                let o = owned(self);
                (Builtin::CowToMut, Autoref::RefMut, self.tys.mk_ref(true, o))
            }
            "as_ref" => (Builtin::CowDeref, Autoref::Ref, self.tys.mk_ref(false, b)),
            "borrow" if self.std_trait_imported("borrow", "Borrow") => (Builtin::CowDeref, Autoref::Ref, self.tys.mk_ref(false, b)),
            "deref" if self.std_trait_imported("ops", "Deref") => (Builtin::CowDeref, Autoref::Ref, self.tys.mk_ref(false, b)),
            _ => return None,
        };
        if autoref != Autoref::None {
            self.check_packed_borrow(recv, name_span);
        }
        self.set_res(e, Res::BuiltinMethod { b: bt, derefs, autoref });
        self.check_args(&[], args, name_span);
        Some(ret)
    }
}
