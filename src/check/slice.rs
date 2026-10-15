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
            _ => return None,
        };
        if n == "copy_within" {
            return Some(self.copy_within_method(e, recv, elem, derefs, name_span, args, turbofish));
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

    /// Checks the arguments with no expectations and answers the
    /// error type: the bail-out of a slice method already reported.
    fn slice_bail(&mut self, args: &[ExprId]) -> Ty {
        for &a in args {
            self.expr(a, None);
        }
        ERROR
    }
}
