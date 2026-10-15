// Slice inherent methods in body checking (tf-slice, TRIAGE T3):
// `starts_with`, `ends_with`, `fill`, `copy_from_slice`, and
// `copy_within` on `[T]`, `[T; N]`, and `Vec<T>` (through its
// `Deref<Target = [T]>`, like `swap`). The element bounds are the
// core ones (`PartialEq` for the needle tests, `Clone` for `fill`,
// `Copy` for the copies), deferred like the Vec table's. Codegen
// emits each builtin in cgen.rs; `copy_within`'s range argument is
// a `RangeBounds<usize>` read by drain's form machinery
// (check/iter.rs `drain_range_form`, lower.rs `drain_bounds`), so
// its panics are core's slice-index ones (runtime/core.c
// `lust_range_bounds_check`).
//
// Rule zero: a receiver form or argument shape outside this list
// falls through to the normal dispatch and rejects there.
use super::*;

impl<'p> Ctx<'p> {
    /// The slice methods above. Returns None when the call is none
    /// of these, so the caller's other dispatch runs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn slice_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
    ) -> Option<Ty> {
        use Builtin as B;
        let elem = match self.kind(base) {
            TyKind::Slice(el) | TyKind::Array(el, _) => el,
            _ => self.tys.vec_elem(base)?,
        };
        // Compare the borrowed name before anything allocates, as
        // in `iter_method`.
        let n = match self.name(name) {
            "starts_with" => "starts_with",
            "ends_with" => "ends_with",
            "fill" => "fill",
            "copy_from_slice" => "copy_from_slice",
            "copy_within" => "copy_within",
            "get" => "get",
            "get_mut" => "get_mut",
            _ => return None,
        };
        if n == "copy_within" {
            return Some(self.copy_within_method(e, recv, elem, derefs, name_span, args, turbofish));
        }
        if n == "get" || n == "get_mut" {
            return Some(self.slice_get_method(e, recv, elem, derefs, name_span, args, n == "get_mut"));
        }
        let needle = |this: &mut Self| {
            let sl = this.tys.intern(TyKind::Slice(elem));
            this.tys.mk_ref(false, sl)
        };
        let (b, autoref, params, ret): (B, Autoref, Vec<Ty>, Ty) = match n {
            "starts_with" | "ends_with" => {
                self.deferred_eq.push((elem, name_span));
                let r = needle(self);
                (if n == "starts_with" { B::SliceStartsWith } else { B::SliceEndsWith }, Autoref::Ref, vec![r], BOOL)
            }
            "fill" => {
                self.deferred_clone.push((elem, name_span));
                (B::SliceFill, Autoref::RefMut, vec![elem], UNIT)
            }
            _ => {
                self.deferred_copy.push((elem, name_span));
                let r = needle(self);
                (B::SliceCopyFromSlice, Autoref::RefMut, vec![r], UNIT)
            }
        };
        if !turbofish.is_empty() {
            self.errs.push(not_yet("L0721", name_span, "turbofish on this slice method"));
            return Some(self.slice_bail(args));
        }
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        self.check_args(&params, args, name_span);
        Some(ret)
    }

    /// `[T]::copy_within(src, dest)`: `src` is any
    /// `RangeBounds<usize>`, read by drain's form machinery, and
    /// `dest` a plain index. The form is recorded for lowering
    /// (`Checked::drain_range`), like a drain call.
    fn copy_within_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        elem: Ty,
        derefs: u8,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
    ) -> Ty {
        if !turbofish.is_empty() {
            self.errs.push(not_yet("L0721", name_span, "turbofish on `copy_within`"));
            return self.slice_bail(args);
        }
        if args.len() != 2 {
            self.err("L0105", name_span, "`copy_within` takes 2 arguments", "Pass the source range and the destination index.");
            return self.slice_bail(args);
        }
        self.deferred_copy.push((elem, name_span));
        let Some(form) = self.drain_range_form(e, args[0], name_span) else {
            self.expr(args[1], None);
            return ERROR;
        };
        self.expect_expr(args[1], USIZE);
        self.check_packed_borrow(recv, name_span);
        self.out.drain_ranges.push((e, form));
        self.set_res(e, Res::BuiltinMethod { b: Builtin::SliceCopyWithin, derefs, autoref: Autoref::RefMut });
        UNIT
    }

    /// `[T]::get` and `get_mut`: a `usize` index (the Vec table's
    /// form, kept here so the argument is checked once) or any
    /// `SliceIndex` range form: a syntactic range, a range value,
    /// or a `(Bound, Bound)` pair. Range forms record like drain
    /// and answer `Option<&[T]>`.
    fn slice_get_method(&mut self, e: ExprId, recv: ExprId, elem: Ty, derefs: u8, name_span: Span, args: &[ExprId], mutable: bool) -> Ty {
        use Builtin as B;
        let autoref = if mutable { Autoref::RefMut } else { Autoref::Ref };
        if args.len() != 1 {
            // The table's arity error shape.
            self.check_args(&[USIZE], args, name_span);
            return ERROR;
        }
        let arg = args[0];
        let form = if matches!(self.p.ast.expr(arg), Expr::Range { .. }) {
            self.drain_range_form(e, arg, name_span)
        } else {
            let t = self.expr(arg, None);
            let t = self.deep(t);
            match self.drain_form_of(t, name_span) {
                Some(f) => Some(DrainRange::Value(f)),
                None => {
                    // A plain index: the Vec table's builtin and
                    // coercion, on the argument as already checked.
                    self.coerce_expr(arg, t, USIZE);
                    let r = self.tys.mk_ref(mutable, elem);
                    let ret = self.tys.mk_option(r);
                    self.check_packed_borrow(recv, name_span);
                    let b = if mutable { B::VecGetMut } else { B::VecGet };
                    self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
                    return ret;
                }
            }
        };
        let Some(form) = form else { return ERROR };
        self.check_packed_borrow(recv, name_span);
        self.out.drain_ranges.push((e, form));
        let b = if mutable { B::SliceGetRangeMut } else { B::SliceGetRange };
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        let sl = self.tys.intern(TyKind::Slice(elem));
        let r = self.tys.mk_ref(mutable, sl);
        self.tys.mk_option(r)
    }

    /// An index expression `base[index]` whose index is a range
    /// value (not a syntactic range): the same slice place, with
    /// the form recorded for lowering (`Checked::index_range`).
    /// Returns the sliced type for a range form; None when the
    /// index is no range form. The index is checked (and coerced
    /// to `usize` for the plain form) in every case, so the caller
    /// must not expect it again.
    pub(super) fn range_value_index(&mut self, e: ExprId, index: ExprId, inner: Ty, derefs: u8, span: Span) -> Option<Ty> {
        let t = self.expr(index, None);
        let t = self.deep(t);
        let form = self.drain_form_of(t, span);
        match form {
            // A `(Bound, Bound)` index panics at core's own sites,
            // not the call's: not yet, as a plain mismatch.
            Some(DrainForm::Bounds | DrainForm::BoundsRef) => {
                self.coerce_expr(index, t, USIZE);
                None
            }
            Some(f) => {
                self.out.index_ranges.push((e, f));
                self.set_res(e, Res::SliceIndex { derefs });
                if self.kind(inner) == TyKind::Str || self.tys.is_string_ty(inner) {
                    return Some(STR);
                }
                let elem = match self.kind(inner) {
                    TyKind::Array(elem, _) | TyKind::Slice(elem) => Some(elem),
                    _ => self.tys.vec_elem(inner),
                };
                Some(match elem {
                    Some(elem) => self.tys.intern(TyKind::Slice(elem)),
                    None => ERROR,
                })
            }
            None => {
                self.coerce_expr(index, t, USIZE);
                None
            }
        }
    }

    /// Checks the arguments with no expectations and answers the
    /// error type: the bail-out of a slice method already reported.
    fn slice_bail(&mut self, args: &[ExprId]) -> Ty {
        for &a in args {
            self.expr(a, None);
        }
        ERROR
    }
}
