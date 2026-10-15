// `alloc::borrow::Cow` in body checking (W-STD-B): its inherent
// methods `into_owned` and `to_mut`, `as_ref`, `borrow`, and `deref`
// to `&B`, and B's methods through that deref. The enum is a synthetic
// local Adt (collect.rs); its trait impls are lang facts (generics.rs)
// with glue in cgen/cow.rs.
use super::*;

/// The method names a `Cow` has itself in Rust: inherent, and from every
/// trait Cow implements (Clone, ToOwned, Deref, Borrow, AsRef, the
/// comparisons, Hash, the formatting traits, ToString, Add, AddAssign,
/// Into, TryInto, Any). A call by one of these names never takes the
/// deref step to B, even when lust does not resolve the Cow method:
/// rustc picks the Cow's method there.
const COW_OWN: &[&str] = &[
    "into_owned",
    "to_mut",
    "is_borrowed",
    "is_owned",
    "clone",
    "clone_from",
    "clone_into",
    "to_owned",
    "deref",
    "borrow",
    "borrow_mut",
    "as_ref",
    "eq",
    "ne",
    "partial_cmp",
    "lt",
    "le",
    "gt",
    "ge",
    "cmp",
    "max",
    "min",
    "clamp",
    "hash",
    "hash_slice",
    "fmt",
    "to_string",
    "add",
    "add_assign",
    "into",
    "try_into",
    "type_id",
];

impl<'p> Ctx<'p> {
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

    /// A method of `B` on a `Cow<B>` receiver, through the Cow's `Deref`
    /// (rustc's next autoderef step, taken once every Cow method
    /// missed): the receiver becomes the `&B` view, from which the
    /// method's own derefs and autoref start (`Coerce::CowRecv`). Only
    /// B's builtin methods resolve this way so far; a user method of B
    /// is L0640. None for other receivers and for the names in
    /// `COW_OWN`.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn cow_deref_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        expected: Option<Ty>,
    ) -> Option<Ty> {
        let b = crate::check::collect::cow_arg(&self.tys, base)?;
        let n = self.name(name).to_string();
        if COW_OWN.contains(&n.as_str()) {
            return None;
        }
        let view = self.tys.mk_ref(false, b);
        let i = self.ei(recv);
        self.out.coerce[i] = Coerce::CowRecv(derefs, view);
        let ret = self.method_call_at(e, recv, view, name, name_span, args, turbofish, expected);
        let i = self.ei(e);
        if ret != ERROR && !matches!(self.out.expr_res[i], Res::BuiltinMethod { b, .. } if b != Builtin::FmtWriteFmt) {
            let tn = self.tn(b);
            self.err(
                "L0640",
                name_span,
                format!("calling the `{tn}` method `{n}` through a `Cow` is not implemented yet"),
                format!("Bind the view first: `let v: &{tn} = &cow;`, then call `v.{n}(..)`."),
            );
            return Some(ERROR);
        }
        Some(ret)
    }
}
