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
        // `str::get` with a range (on `str` and, through its deref,
        // `String`): its own builtin, with char boundary checks.
        if (base == STR || base == STRING) && self.name(name) == "get" {
            return Some(self.str_get_method(e, recv, derefs, name_span, args));
        }
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
            "join" => "join",
            "concat" => "concat",
            "eq_ignore_ascii_case" => "eq_ignore_ascii_case",
            "is_ascii" => "is_ascii",
            "rotate_left" => "rotate_left",
            "rotate_right" => "rotate_right",
            "partition_point" => "partition_point",
            "extend_from_within" => "extend_from_within",
            "resize_with" => "resize_with",
            "dedup_by" => "dedup_by",
            "dedup_by_key" => "dedup_by_key",
            "splice" => "splice",
            _ => return None,
        };
        if matches!(
            n,
            "eq_ignore_ascii_case"
                | "is_ascii"
                | "rotate_left"
                | "rotate_right"
                | "partition_point"
                | "extend_from_within"
                | "resize_with"
                | "dedup_by"
                | "dedup_by_key"
        ) {
            return self.slice_method_r4(e, recv, base, elem, derefs, n, name_span, args, turbofish);
        }
        if n == "splice" {
            if self.tys.vec_elem(base).is_none() {
                return None;
            }
            return Some(self.splice_method(e, recv, elem, derefs, name_span, args, turbofish));
        }
        if n == "join" || n == "concat" {
            return self.slice_join_concat(e, recv, elem, derefs, name_span, args, n == "join");
        }
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
                // `fill` runs `clone_from` per element; a hash
                // table's own clone_from reuse is the same precise
                // reject as a direct `clone_from` call.
                if crate::check::collect::mentions_hash_table(self.p, &self.tys, elem) {
                    self.errs.push(not_yet("L0640", name_span, "`fill` on a slice of a type holding a hash table"));
                    return Some(self.slice_bail(args));
                }
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

    /// `str::get` (TRIAGE R26): any `SliceIndex<str>` range form, as
    /// for `[T]::get`, answering `Option<&str>`: `None` when a bound is
    /// out of range or not on a char boundary. A `usize` is no
    /// `SliceIndex<str>`, as in rustc.
    fn str_get_method(&mut self, e: ExprId, recv: ExprId, derefs: u8, name_span: Span, args: &[ExprId]) -> Ty {
        if args.len() != 1 {
            self.err("L0105", name_span, "`get` takes 1 argument", "Pass a range, such as `s.get(1..3)`.");
            return self.slice_bail(args);
        }
        let arg = args[0];
        let form = if matches!(self.p.ast.expr(arg), Expr::Range { .. }) {
            self.drain_range_form(e, arg, name_span)
        } else {
            let t = self.expr(arg, None);
            let t = self.deep(t);
            match self.drain_form_of(t, name_span) {
                Some(f) => Some(DrainRange::Value(f)),
                None if t == ERROR => return ERROR,
                None => {
                    let tn = self.tn(t);
                    self.err("L0612", name_span, format!("the type `str` cannot be indexed by `{tn}`"), "Pass a range, such as `s.get(1..3)`.");
                    return ERROR;
                }
            }
        };
        let Some(form) = form else { return ERROR };
        self.check_packed_borrow(recv, name_span);
        self.out.drain_ranges.push((e, form));
        self.set_res(e, Res::BuiltinMethod { b: Builtin::StrGetRange, derefs, autoref: Autoref::Ref });
        self.tys.mk_option(REF_STR)
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

    /// `[S]::join` and `concat`: core's two families, over the
    /// element shapes lust takes. The `Borrow<str>` family (String
    /// and `&str` elements) answers a String and takes a `&str`
    /// separator; the `Borrow<[T]>` family (Vec, array, slice, and
    /// boxed-slice elements, `T: Clone`) answers a `Vec<T>` and
    /// takes a `&T` or `&[T]` separator. Any other element shape
    /// falls through to the normal dispatch (a user `Borrow` type
    /// or a plain no-method error, as rustc decides).
    #[allow(clippy::too_many_arguments)]
    fn slice_join_concat(
        &mut self,
        e: ExprId,
        recv: ExprId,
        elem: Ty,
        derefs: u8,
        name_span: Span,
        args: &[ExprId],
        is_join: bool,
    ) -> Option<Ty> {
        use Builtin as B;
        let str_family = elem == STRING || matches!(self.kind(elem), TyKind::Ref(_, Mut::Shared, i) if self.kind(i) == TyKind::Str);
        if str_family {
            let b = if is_join { B::SliceJoinStr } else { B::SliceConcatStr };
            self.check_packed_borrow(recv, name_span);
            self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::Ref });
            if is_join {
                self.check_args(&[REF_STR], args, name_span);
            } else {
                self.check_args(&[], args, name_span);
            }
            return Some(STRING);
        }
        let inner = match self.kind(elem) {
            TyKind::Array(el, _) => Some(el),
            TyKind::Ref(_, _, i) => match self.kind(i) {
                TyKind::Slice(el) => Some(el),
                _ => None,
            },
            _ => self.tys.vec_elem(elem).or_else(|| self.tys.boxed_slice_elem(elem)),
        }?;
        self.deferred_clone.push((inner, name_span));
        let ret = self.tys.mk_vec(inner);
        self.check_packed_borrow(recv, name_span);
        if !is_join {
            self.set_res(e, Res::BuiltinMethod { b: B::SliceConcatVec, derefs, autoref: Autoref::Ref });
            self.check_args(&[], args, name_span);
            return Some(ret);
        }
        if args.len() != 1 {
            let p0 = self.tys.mk_ref(false, inner);
            self.check_args(&[p0], args, name_span);
            return Some(ERROR);
        }
        let arg = args[0];
        let t = self.expr(arg, None);
        let t = self.deep(t);
        let slice_of_inner = |this: &mut Self, u: Ty| this.unify(u, inner);
        let (b, param): (B, Ty) = match self.kind(t) {
            TyKind::Ref(_, _, u) if matches!(self.kind(u), TyKind::Slice(_) | TyKind::Array(..)) => {
                let uel = match self.kind(u) {
                    TyKind::Slice(el) | TyKind::Array(el, _) => el,
                    _ => unreachable!(),
                };
                if slice_of_inner(self, uel) {
                    let sl = self.tys.intern(TyKind::Slice(inner));
                    (B::SliceJoinVecSlice, self.tys.mk_ref(false, sl))
                } else {
                    (B::SliceJoinVecElem, self.tys.mk_ref(false, inner))
                }
            }
            TyKind::Ref(_, _, u) if self.tys.vec_elem(u).is_some_and(|el| el == inner) => {
                let sl = self.tys.intern(TyKind::Slice(inner));
                (B::SliceJoinVecSlice, self.tys.mk_ref(false, sl))
            }
            _ => (B::SliceJoinVecElem, self.tys.mk_ref(false, inner)),
        };
        self.coerce_expr(arg, t, param);
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::Ref });
        Some(ret)
    }

    /// A comparison across sequence forms (slice, array, Vec) as
    /// core's asymmetric `PartialEq` impls allow them (and the
    /// slice `PartialOrd` coercions at equal reference depth):
    /// recorded as a slice comparison for lowering. None when the
    /// pair is not one of core's, so the caller's normal path
    /// answers (the same-type path, a written impl, or its error).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn seq_cmp(
        &mut self,
        e: ExprId,
        op: BinOp,
        lt: Ty,
        rt: Ty,
        ld: u8,
        lb: Ty,
        rd: u8,
        rb: Ty,
        span: Span,
    ) -> Option<Ty> {
        use BinOp::*;
        /// One side's sequence form.
        #[derive(Clone, Copy, PartialEq)]
        enum Form {
            Slice,
            Array,
            Vec,
        }
        let form = |this: &Self, b: Ty| -> Option<(Form, Ty, Option<crate::ty::ConstId>)> {
            match this.kind(b) {
                TyKind::Slice(el) => Some((Form::Slice, el, None)),
                TyKind::Array(el, c) => Some((Form::Array, el, Some(c))),
                _ => this.tys.vec_elem(b).map(|el| (Form::Vec, el, None)),
            }
        };
        let (lf, le, lc) = form(self, lb)?;
        let (rf, re, rc) = form(self, rb)?;
        // The same-type path already answers these.
        if ld == rd && self.deep(lb) == self.deep(rb) {
            return None;
        }
        if lf == Form::Array && rf == Form::Array {
            let same_n = match (lc, rc) {
                (Some(a), Some(b)) if a == b => true,
                (Some(a), Some(b)) => match (self.tys.const_kind(a), self.tys.const_kind(b)) {
                    (crate::ty::ConstKind::Int(x), crate::ty::ConstKind::Int(y)) => x == y,
                    _ => false,
                },
                _ => false,
            };
            if !same_n {
                return None;
            }
        }
        let eq_op = matches!(op, Eq | Ne);
        let last_mut = |this: &Self, t: Ty| this.ref_layers(t).last().copied().unwrap_or(false);
        let allowed = if eq_op {
            if ld == rd {
                matches!(
                    (lf, rf),
                    (Form::Slice, Form::Slice)
                        | (Form::Array, Form::Array)
                        | (Form::Vec, Form::Vec)
                        | (Form::Array, Form::Slice)
                        | (Form::Slice, Form::Array)
                        | (Form::Vec, Form::Slice)
                        | (Form::Slice, Form::Vec)
                        | (Form::Vec, Form::Array)
                )
            } else if rd == ld + 1 {
                match (lf, rf) {
                    (Form::Array, Form::Slice) | (Form::Vec, Form::Slice) => true,
                    // `Vec<T>: PartialEq<&[U; N]>` exists; the
                    // `&mut [U; N]` form is the omitted one.
                    (Form::Vec, Form::Array) => !last_mut(self, rt),
                    _ => false,
                }
            } else if ld == rd + 1 {
                matches!((lf, rf), (Form::Slice, Form::Array) | (Form::Slice, Form::Vec))
            } else {
                false
            }
        } else {
            // Ordering needs the same mutability layers, as the
            // caller's own check has it.
            ld == rd
                && self.ref_layers(lt) == self.ref_layers(rt)
                && (matches!((lf, rf), (Form::Slice, Form::Slice) | (Form::Array, Form::Array) | (Form::Vec, Form::Vec))
                    || (ld >= 1 && lf == Form::Slice && rf != Form::Slice))
        };
        if !allowed {
            return None;
        }
        let snap = self.snapshot_vars();
        if !self.unify(le, re) {
            self.rollback_vars(snap);
            return None;
        }
        let lbd = self.deep(lb);
        let ok = if eq_op {
            crate::check::collect::has_eq(self.p, &self.tys, lbd)
        } else {
            crate::check::collect::has_ord(self.p, &self.tys, lbd)
        };
        if !ok {
            let tn = self.tn(lbd);
            let fix = if eq_op {
                "Add #[derive(PartialEq)] to the type."
            } else {
                "Add #[derive(PartialOrd)] to the type, or implement `PartialOrd` for it."
            };
            self.err("L0112", span, format!("type `{tn}` cannot be compared with `{}`", op.symbol()), fix);
            self.set_res(e, Res::Bin { ld, rd });
            return Some(BOOL);
        }
        let le = self.deep(le);
        let sl = self.tys.intern(TyKind::Slice(le));
        self.record_glue_reads(self.p.gx.lang.partial_eq, sl);
        self.out.seq_cmps.push(e);
        self.set_res(e, Res::Bin { ld, rd });
        Some(BOOL)
    }

    /// Checks the arguments with no expectations and answers the
    /// error type: the bail-out of a slice method already reported.
    /// The R4 slice and Vec methods (tf-small-a): `[u8]::eq_ignore_ascii_case`
    /// and `is_ascii`, `[T]::rotate_left`/`rotate_right` and
    /// `partition_point`, and on `Vec<T>` only `extend_from_within`,
    /// `resize_with`, `dedup_by`, and `dedup_by_key`. None for a name
    /// outside the list or a receiver the method does not take (a byte
    /// method on a non-`u8` element, a Vec method on a slice), so the
    /// normal dispatch rejects it.
    #[allow(clippy::too_many_arguments)]
    fn slice_method_r4(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        elem: Ty,
        derefs: u8,
        n: &str,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
    ) -> Option<Ty> {
        use Builtin as B;
        let bytes = self.resolve(elem) == int(IntTy::U8);
        let is_vec = self.tys.vec_elem(base).is_some();
        let (b, autoref, params, ret): (B, Autoref, Vec<Ty>, Ty) = match n {
            "eq_ignore_ascii_case" if bytes => {
                let sl = self.tys.intern(TyKind::Slice(elem));
                let r = self.tys.mk_ref(false, sl);
                (B::SliceEqIgnoreAsciiCase, Autoref::Ref, vec![r], BOOL)
            }
            "is_ascii" if bytes => (B::SliceIsAscii, Autoref::Ref, vec![], BOOL),
            "rotate_left" => (B::SliceRotateLeft, Autoref::RefMut, vec![USIZE], UNIT),
            "rotate_right" => (B::SliceRotateRight, Autoref::RefMut, vec![USIZE], UNIT),
            "partition_point" => {
                // `P: FnMut(&T) -> bool`, the reference higher-ranked.
                let r = self.tys.mk_ref(false, elem);
                let f = self.fn_mut_param_ref(&[r], BOOL, name_span);
                (B::SlicePartitionPoint, Autoref::Ref, vec![f], USIZE)
            }
            "extend_from_within" if is_vec => {
                if !turbofish.is_empty() {
                    self.errs.push(not_yet("L0721", name_span, "turbofish on `extend_from_within`"));
                    return Some(self.slice_bail(args));
                }
                if args.len() != 1 {
                    self.err("L0105", name_span, "`extend_from_within` takes 1 argument", "Pass the source range.");
                    return Some(self.slice_bail(args));
                }
                self.deferred_clone.push((elem, name_span));
                let Some(form) = self.drain_range_form(e, args[0], name_span) else { return Some(ERROR) };
                self.check_packed_borrow(recv, name_span);
                self.out.drain_ranges.push((e, form));
                self.set_res(e, Res::BuiltinMethod { b: B::VecExtendFromWithin, derefs, autoref: Autoref::RefMut });
                return Some(UNIT);
            }
            "resize_with" if is_vec => {
                let f = self.fn_mut_param(&[], elem, name_span);
                (B::VecResizeWith, Autoref::RefMut, vec![USIZE, f], UNIT)
            }
            "dedup_by" if is_vec => {
                // `F: FnMut(&mut T, &mut T) -> bool`, both higher-ranked.
                let r = self.tys.mk_ref(true, elem);
                let f = self.fn_mut_param_ref(&[r, r], BOOL, name_span);
                (B::VecDedupBy, Autoref::RefMut, vec![f], UNIT)
            }
            "dedup_by_key" if is_vec => {
                // `F: FnMut(&mut T) -> K`, `K: PartialEq`.
                let key = self.new_var(false);
                let r = self.tys.mk_ref(true, elem);
                let f = self.fn_mut_param_ref(&[r], key, name_span);
                self.deferred_eq.push((key, name_span));
                (B::VecDedupByKey, Autoref::RefMut, vec![f], UNIT)
            }
            _ => return None,
        };
        if !turbofish.is_empty() {
            self.errs.push(not_yet("L0721", name_span, "turbofish on this slice method"));
            return Some(self.slice_bail(args));
        }
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        self.check_args(&params, args, name_span);
        // A `dyn FnMut` callable has no adapter call (cgen/slices.rs,
        // lower/iter.rs `call_fn`).
        if matches!(b, B::SlicePartitionPoint | B::VecDedupBy | B::VecDedupByKey | B::VecResizeWith) && self.adapter_callable_gap(args, &params, false) {
            return Some(ERROR);
        }
        Some(ret)
    }

    /// `Vec::splice(range, replace_with)` (R4). Taken as an expression
    /// statement only: its `Splice` then drops at once, and the call is
    /// core's drain plus `Splice::drop`. The replacement is a builtin
    /// `TrustedLen` iterator (or a collection that turns into one), so
    /// its size hint is exact and nothing is left to collect. The range
    /// records like drain's.
    #[allow(clippy::too_many_arguments)]
    fn splice_method(
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
            self.errs.push(not_yet("L0721", name_span, "turbofish on `splice`"));
            return self.slice_bail(args);
        }
        if args.len() != 2 {
            self.err("L0105", name_span, "`splice` takes 2 arguments", "Pass the range and the replacement items.");
            return self.slice_bail(args);
        }
        if self.stmt_expr != Some(e) {
            self.errs.push(not_yet("L0641", name_span, "`splice` whose `Splice` value is used (lust takes `v.splice(range, items);` as a statement)"));
            return self.slice_bail(args);
        }
        let Some(form) = self.drain_range_form(e, args[0], name_span) else {
            self.expr(args[1], None);
            return ERROR;
        };
        let at = self.expr(args[1], None);
        let at = self.deep(at);
        let it = match self.into_iter_ty(at) {
            Some(it) if self.splice_trusted(it) => it,
            Some(_) => {
                self.errs.push(not_yet("L0641", self.span(args[1]), "`splice` with this replacement (lust takes slices, Vecs, arrays, and their std iterators)"));
                return ERROR;
            }
            None => {
                let tn = self.tn(at);
                self.err("L0612", self.span(args[1]), format!("`{tn}` is not an iterator lust can splice in"), "Pass an iterator, a slice, an array, or a Vec.");
                return ERROR;
            }
        };
        let item = self.iter_item(it);
        if !self.unify(item, elem) {
            self.mismatch(self.span(args[1]), elem, item);
            return ERROR;
        }
        self.check_packed_borrow(recv, name_span);
        self.out.drain_ranges.push((e, form));
        self.set_res(e, Res::BuiltinMethod { b: Builtin::VecSplice, derefs, autoref: Autoref::RefMut });
        UNIT
    }

    /// True for the replacement iterators `splice` takes: std
    /// `TrustedLen` kinds with an exact size hint.
    fn splice_trusted(&mut self, t: Ty) -> bool {
        use crate::ty::iter::IterKind as K;
        let t = self.deep(t);
        match crate::ty::iter::iter_parts(&self.tys, t) {
            Some((K::SliceIter | K::SliceIterMut | K::VecIntoIter | K::ArrayIntoIter, _)) => true,
            Some((K::Copied | K::Cloned | K::Map | K::Rev | K::Enumerate, a)) => self.splice_trusted(a[0]),
            _ => false,
        }
    }

    fn slice_bail(&mut self, args: &[ExprId]) -> Ty {
        for &a in args {
            self.expr(a, None);
        }
        ERROR
    }
}
