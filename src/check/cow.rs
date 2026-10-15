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
    /// method's own derefs and autoref start (`Coerce::CowRecv`). B's
    /// builtin, inherent, and trait methods resolve this way: lowering
    /// substitutes the view for the receiver operand and place, and
    /// the borrow checker sees the call on the view local, so a
    /// `&mut` method or a by-value move out of the view rejects as it
    /// does behind any shared reference. None for other receivers and
    /// for the names in `COW_OWN`.
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
        Some(ret)
    }

    /// One Cow `Deref` step of a field or index place base: records
    /// `Coerce::CowRecv` on the base expression (lowering's `place`
    /// then gives the `&B` view local for it) and returns `B`. None
    /// when `inner` is no Cow. Only the first autoderef step of a
    /// place takes it: a Cow reached through a user `Deref`, or a
    /// user `Deref` past the view, is L0640 (the callers decide).
    pub(super) fn cow_place_step(&mut self, base: ExprId, inner: Ty, derefs: u8) -> Option<Ty> {
        let b = crate::check::collect::cow_arg(&self.tys, inner)?;
        let view = self.tys.mk_ref(false, b);
        let i = self.ei(base);
        self.out.coerce[i] = Coerce::CowRecv(derefs, view);
        Some(b)
    }

    /// Does `inner` have a written `Deref` impl? A probe only: every
    /// binding and obligation it makes is rolled back.
    pub(super) fn probe_user_deref(&mut self, inner: Ty, span: Span) -> bool {
        if self.tys.local_adt(inner).is_none() {
            return false;
        }
        let snap = self.snapshot_vars();
        let obl = self.obl_len();
        let has = self.user_deref_fn(self.p.gx.lang.deref, inner, "deref", span).is_some();
        self.rollback_vars(snap);
        self.obl_truncate(obl);
        has
    }

    /// The struct field `name` exists on `b` behind the builtin
    /// autoderef of `&b` (the look-ahead that keeps a Cow place step
    /// lust cannot lower at L0640 instead of a wrong no-field error).
    pub(super) fn cow_view_has_field(&mut self, b: Ty, name: Sym) -> bool {
        let view = self.tys.mk_ref(false, b);
        let (_, inner) = self.autoderef_smart(view);
        let p = self.p;
        match self.tys.local_adt(inner) {
            Some(a) => {
                let adt = p.adt(a);
                !adt.is_enum && adt.variants[0].fields.iter().any(|f| f.name == name)
            }
            None => self.range_field(inner, name).is_some(),
        }
    }

    /// `b` behind `&b` is directly indexable (the index look-ahead
    /// twin of `cow_view_has_field`).
    pub(super) fn cow_view_indexable(&mut self, b: Ty) -> bool {
        let view = self.tys.mk_ref(false, b);
        let (_, inner) = self.autoderef_smart(view);
        matches!(self.kind(inner), TyKind::Array(..) | TyKind::Slice(_) | TyKind::Str)
            || self.tys.vec_elem(inner).is_some()
            || self.tys.is_string_ty(inner)
            || self.has_user_index_impl(inner)
    }
}
