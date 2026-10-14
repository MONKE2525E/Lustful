// Iterator methods in body checking (W-STD-A phase 3, ty/iter.rs).
//
// Sources (`iter`, `iter_mut`, `into_iter` on Vec, slices, and
// arrays; integer ranges), adapters, and consumers type here as
// builtin methods. A closure argument checks against a fresh type
// variable that carries the pending `FnMut` obligation of the Rust
// signature, so its parameter types come from the obligation as for a
// generic call (closure.rs `expected_closure_sig`). Lowering emits one
// builtin call per method; `lower/iter.rs` expands them after borrowck.
//
// Rule zero: a method, receiver form, or argument shape outside this
// list rejects (L0640 for the declared Iterator surface lust lacks).
use super::*;
use crate::ty::iter::{self as it, IterKind};

/// Iterator methods Rust declares that lust does not implement yet:
/// a call rejects with L0640 naming the method, never L0104.
const DECLARED_ONLY: &[&str] = &[
    "next_chunk",
    "advance_by",
    "flat_map",
    "flatten",
    "map_while",
    "scan",
    "fuse",
    "by_ref",
    "partition",
    "partition_in_place",
    "is_partitioned",
    "try_fold",
    "try_for_each",
    "reduce",
    "try_reduce",
    "try_find",
    "rposition",
    "rev_position",
    "unzip",
    "copied_",
    "cycle",
    "array_chunks",
    "sum_",
    "cmp",
    "cmp_by",
    "partial_cmp",
    "partial_cmp_by",
    "eq_by",
    "lt",
    "le",
    "gt",
    "ge",
    "is_sorted",
    "is_sorted_by",
    "is_sorted_by_key",
    "intersperse",
    "intersperse_with",
    "map_windows",
    "collect_into",
    "rfold",
    "rfind",
    "nth_back",
    "next_back",
    "size_hint",
    "len",
    "max_by",
    "min_by",
];

impl<'p, 'a> Ctx<'p, 'a> {
    /// `iter`, `iter_mut`, and `into_iter` on Vec, slices, and arrays,
    /// and every iterator method on a builtin iterator or `Chars`
    /// receiver. Returns None when the call is none of these, so the
    /// caller's other dispatch runs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn iter_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        rt: Ty,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        expected: Option<Ty>,
    ) -> Option<Ty> {
        let seq_elem = match self.kind(base) {
            TyKind::Slice(el) | TyKind::Array(el, _) => Some(el),
            _ => self.tys.vec_elem(base),
        };
        if let Some(el) = seq_elem {
            // Every method call on a Vec passes here: compare the
            // borrowed name before anything allocates.
            let n = match self.name(name) {
                "iter" => "iter",
                "iter_mut" => "iter_mut",
                "into_iter" => "into_iter",
                "sort" => "sort",
                "sort_unstable" => "sort_unstable",
                "sort_by" => "sort_by",
                "sort_unstable_by" => "sort_unstable_by",
                "sort_by_key" => "sort_by_key",
                "sort_unstable_by_key" => "sort_unstable_by_key",
                "binary_search" => "binary_search",
                "binary_search_by" => "binary_search_by",
                "binary_search_by_key" => "binary_search_by_key",
                _ => return None,
            };
            if n.starts_with("sort") || n.starts_with("binary_search") {
                return Some(self.seq_sort(e, recv, el, derefs, n, name_span, args));
            }
            return self.iter_source(e, rt, base, el, derefs, n, name_span, args);
        }
        if !it::is_iter(&self.tys, base) && !self.param_iter(base) {
            // A user iterator type by value: wrapped once as `ByNext`,
            // which every adapter and consumer takes (W-STD-B).
            let n = self.name(name).to_string();
            if derefs > 0 || n == "next" || !ITER_METHODS.contains(&n.as_str()) {
                return None;
            }
            let item = self.by_next_item(base, name_span)?;
            if item == ERROR {
                for &a in args {
                    self.expr(a, None);
                }
                return Some(ERROR);
            }
            let wrapped = it::mk_iter(&mut self.tys, IterKind::ByNext, &[base, item]);
            let i = self.ei(recv);
            self.out.coerce[i] = Coerce::ByNext(wrapped);
            return Some(self.iter_call(e, recv, wrapped, 0, &n, name_span, args, turbofish, expected));
        }
        let n = self.name(name).to_string();
        // `Chars` keeps its own `next` and `count` builtins.
        if self.tys.is_chars_ty(base) && (n == "next" || n == "count") {
            return None;
        }
        Some(self.iter_call(e, recv, base, derefs, &n, name_span, args, turbofish, expected))
    }

    /// The sort and binary-search family on a Vec, slice, or array
    /// (runtime/sort.h ports Rust 1.99's algorithms). Comparators are
    /// closures; `sort`, `binary_search`, and the `_by_key` keys need
    /// an `Ord` type lust compares (collect.rs `has_total_ord`).
    #[allow(clippy::too_many_arguments)]
    fn seq_sort(&mut self, e: ExprId, recv: ExprId, el: Ty, derefs: u8, n: &str, span: Span, args: &[ExprId]) -> Ty {
        use Builtin as B;
        let ord = generics::ordering_ty(&mut self.tys);
        let r_el = self.tys.mk_ref(false, el);
        let res = self.tys.mk_result(USIZE, USIZE);
        let (b, autoref, params, ret) = match n {
            "sort" | "sort_unstable" => {
                self.deferred_ord.push((el, span));
                (if n == "sort" { B::SliceSort } else { B::SliceSortUnstable }, Autoref::RefMut, vec![], UNIT)
            }
            "sort_by" | "sort_unstable_by" => {
                let f = self.fn_mut_param(&[r_el, r_el], ord, span);
                (if n == "sort_by" { B::SliceSortBy } else { B::SliceSortUnstableBy }, Autoref::RefMut, vec![f], UNIT)
            }
            "sort_by_key" | "sort_unstable_by_key" => {
                let key = self.new_var(false);
                let f = self.fn_mut_param(&[r_el], key, span);
                self.deferred_ord.push((key, span));
                (if n == "sort_by_key" { B::SliceSortByKey } else { B::SliceSortUnstableByKey }, Autoref::RefMut, vec![f], UNIT)
            }
            "binary_search" => {
                self.deferred_ord.push((el, span));
                (B::SliceBinarySearch, Autoref::Ref, vec![r_el], res)
            }
            "binary_search_by" => {
                let f = self.fn_mut_param(&[r_el], ord, span);
                (B::SliceBinarySearchBy, Autoref::Ref, vec![f], res)
            }
            _ => {
                let key = self.new_var(false);
                let rk = self.tys.mk_ref(false, key);
                let f = self.fn_mut_param(&[r_el], key, span);
                self.deferred_ord.push((key, span));
                (B::SliceBinarySearchByKey, Autoref::Ref, vec![rk, f], res)
            }
        };
        if autoref != Autoref::None {
            self.check_packed_borrow(recv, span);
        }
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        self.check_args(&params, args, span);
        ret
    }

    /// A source method on a Vec, slice, or array receiver.
    #[allow(clippy::too_many_arguments)]
    fn iter_source(&mut self, e: ExprId, rt: Ty, base: Ty, el: Ty, derefs: u8, n: &str, span: Span, args: &[ExprId]) -> Option<Ty> {
        use Builtin as B;
        let (b, autoref, derefs, ret) = match n {
            "iter" => (B::IterIter, Autoref::Ref, derefs, it::mk_iter(&mut self.tys, IterKind::SliceIter, &[el])),
            "iter_mut" => (B::IterIterMut, Autoref::RefMut, derefs, it::mk_iter(&mut self.tys, IterKind::SliceIterMut, &[el])),
            "into_iter" => {
                // Rust's probe: the first autoderef step whose type has
                // an `IntoIterator` impl, by value: `&X` or `&mut X`
                // (a slice iterator), or `Vec<T>` itself.
                let mut t = self.resolve(rt);
                let mut found = None;
                for j in 0..=derefs {
                    match self.kind(t) {
                        TyKind::Ref(_, m, inner) => {
                            let inner = self.resolve(inner);
                            let seq = matches!(self.kind(inner), TyKind::Slice(_) | TyKind::Array(..)) || self.tys.vec_elem(inner).is_some();
                            if seq {
                                let (b, k) = if m.is_mut() { (B::IterIterMut, IterKind::SliceIterMut) } else { (B::IterIter, IterKind::SliceIter) };
                                found = Some((b, j, it::mk_iter(&mut self.tys, k, &[el])));
                                break;
                            }
                            t = inner;
                        }
                        _ if self.tys.vec_elem(t).is_some() => {
                            found = Some((B::IterVecIntoIter, j, it::mk_iter(&mut self.tys, IterKind::VecIntoIter, &[el])));
                            break;
                        }
                        // An array by value (`array::IntoIter`, W-STD-B):
                        // Copy elements only (the store has no per-element
                        // drop state yet).
                        TyKind::Array(..) if j == 0 => {
                            if !self.array_iter_elem_ok(el, span) {
                                for &a in args {
                                    self.expr(a, None);
                                }
                                return Some(ERROR);
                            }
                            found = Some((B::IterArrayIntoIter, 0, it::mk_iter(&mut self.tys, IterKind::ArrayIntoIter, &[el, t])));
                            break;
                        }
                        _ => break,
                    }
                }
                let Some((b, j, ret)) = found else {
                    // An array by value (`array::IntoIter`) or a smart
                    // pointer step: valid Rust lust does not have yet.
                    self.err("L0640", span, "`into_iter` on this receiver is not implemented yet", "Iterate with `.iter()`, or over a `Vec`.");
                    for &a in args {
                        self.expr(a, None);
                    }
                    return Some(ERROR);
                };
                (b, Autoref::None, j, ret)
            }
            _ => return None,
        };
        let _ = base;
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        self.check_args(&[], args, span);
        Some(ret)
    }

    /// One method on a builtin iterator receiver.
    #[allow(clippy::too_many_arguments)]
    fn iter_call(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        n: &str,
        span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        expected: Option<Ty>,
    ) -> Ty {
        use Builtin as B;
        use IterKind as K;
        let item = self.iter_item(base);
        let by_value = !matches!(n, "next" | "nth" | "any" | "all" | "find" | "find_map" | "position" | "rposition" | "peek");
        // A by-value method through a reference would use `&mut I:
        // Iterator` (`by_ref`), which lust does not model yet.
        if by_value && derefs > 0 && self.iter_method_known(n) {
            self.err(
                "L0640",
                span,
                format!("`{n}` on an iterator behind a reference is not implemented yet"),
                "Call it on the iterator value itself.",
            );
            return self.iter_bail(args);
        }
        if !turbofish.is_empty() && !matches!(n, "collect" | "sum" | "product") {
            self.errs.push(not_yet("L0721", span, "turbofish on this iterator method"));
            return self.iter_bail(args);
        }
        let mk = |this: &mut Self, k: IterKind, a: &[Ty]| it::mk_iter(&mut this.tys, k, a);
        let r = |this: &mut Self, t: Ty| this.tys.mk_ref(false, t);
        let (b, params, ret): (Builtin, Vec<Ty>, Ty) = match n {
            "next" => {
                let o = self.tys.mk_option(item);
                (B::IterNext, vec![], o)
            }
            "map" => {
                let out = self.new_var(false);
                let f = self.fn_mut_param(&[item], out, span);
                let t = mk(self, K::Map, &[base, f, out]);
                (B::IterMap, vec![f], t)
            }
            "filter" => {
                let ri = r(self, item);
                let p = self.fn_mut_param_ref(&[ri], BOOL, span);
                let t = mk(self, K::Filter, &[base, p]);
                (B::IterFilter, vec![p], t)
            }
            "filter_map" => {
                let out = self.new_var(false);
                let o = self.tys.mk_option(out);
                let f = self.fn_mut_param(&[item], o, span);
                let t = mk(self, K::FilterMap, &[base, f, out]);
                (B::IterFilterMap, vec![f], t)
            }
            "enumerate" => (B::IterEnumerate, vec![], mk(self, K::Enumerate, &[base])),
            "rev" => {
                if !self.double_ended(base) {
                    let tn = self.tn(base);
                    self.err("L0612", span, format!("`{tn}` is not a double-ended iterator"), "Reverse a slice, Vec, or range iterator instead.");
                    return self.iter_bail(args);
                }
                (B::IterRev, vec![], mk(self, K::Rev, &[base]))
            }
            "take" => (B::IterTake, vec![USIZE], mk(self, K::Take, &[base])),
            "skip" => (B::IterSkip, vec![USIZE], mk(self, K::Skip, &[base])),
            "step_by" => (B::IterStepBy, vec![USIZE], mk(self, K::StepBy, &[base])),
            "chain" | "zip" => {
                let Some(&a) = args.first() else {
                    self.err("L0105", span, format!("`{n}` takes 1 argument"), "Pass the other iterator.");
                    return self.iter_bail(args);
                };
                let at = self.expr(a, None);
                let at = self.deep(at);
                let Some(other) = self.into_iter_ty(at) else {
                    let tn = self.tn(at);
                    self.err(
                        "L0612",
                        self.span(a),
                        format!("`{tn}` is not an iterator lust can {n} with yet"),
                        "Pass an iterator, a `&Vec`, a slice, or a `Vec`.",
                    );
                    return self.iter_bail(&args[1..]);
                };
                if args.len() != 1 {
                    self.err("L0105", span, format!("`{n}` takes 1 argument"), "Pass the other iterator.");
                }
                if let Some((IterKind::ArrayIntoIter, ta)) = it::iter_parts(&self.tys, other)
                    && !it::is_iter(&self.tys, at)
                    && !self.array_iter_elem_ok(ta[0], self.span(a))
                {
                    return self.iter_bail(&args[1..]);
                }
                let oi = self.iter_item(other);
                if n == "chain" && !self.unify(oi, item) {
                    self.mismatch(self.span(a), item, oi);
                }
                self.set_res(e, Res::BuiltinMethod { b: if n == "chain" { B::IterChain } else { B::IterZip }, derefs, autoref: Autoref::None });
                return mk(self, if n == "chain" { K::Chain } else { K::Zip }, &[base, other]);
            }
            "copied" | "cloned" => {
                let inner = match self.kind(self.resolve(item)) {
                    TyKind::Ref(_, _, t) => t,
                    _ => {
                        let tn = self.tn(item);
                        self.err("L0612", span, format!("`{n}` needs an iterator over references, not over `{tn}`"), "Drop the call.");
                        return self.iter_bail(args);
                    }
                };
                if n == "copied" {
                    self.deferred_copy.push((inner, span));
                    (B::IterCopied, vec![], mk(self, K::Copied, &[base, inner]))
                } else {
                    self.deferred_clone.push((inner, span));
                    (B::IterCloned, vec![], mk(self, K::Cloned, &[base, inner]))
                }
            }
            "take_while" | "skip_while" => {
                let ri = r(self, item);
                let p = self.fn_mut_param_ref(&[ri], BOOL, span);
                if n == "take_while" {
                    (B::IterTakeWhile, vec![p], mk(self, K::TakeWhile, &[base, p]))
                } else {
                    (B::IterSkipWhile, vec![p], mk(self, K::SkipWhile, &[base, p]))
                }
            }
            "peekable" => (B::IterPeekable, vec![], mk(self, K::Peekable, &[base])),
            "peek" => {
                let Some((K::Peekable, _)) = it::iter_parts(&self.tys, base) else { return self.iter_unknown(n, span, base, args) };
                let ri = r(self, item);
                let o = self.tys.mk_option(ri);
                (B::IterPeek, vec![], o)
            }
            "inspect" => {
                let ri = r(self, item);
                let f = self.fn_mut_param_ref(&[ri], UNIT, span);
                (B::IterInspect, vec![f], mk(self, K::Inspect, &[base, f]))
            }
            "count" => (B::IterCount, vec![], USIZE),
            "last" => {
                let o = self.tys.mk_option(item);
                (B::IterLast, vec![], o)
            }
            "nth" => {
                let o = self.tys.mk_option(item);
                (B::IterNth, vec![USIZE], o)
            }
            "any" | "all" => {
                let f = self.fn_mut_param(&[item], BOOL, span);
                (if n == "any" { B::IterAny } else { B::IterAll }, vec![f], BOOL)
            }
            "find" => {
                let ri = r(self, item);
                let p = self.fn_mut_param_ref(&[ri], BOOL, span);
                let o = self.tys.mk_option(item);
                (B::IterFind, vec![p], o)
            }
            "find_map" => {
                let out = self.new_var(false);
                let o = self.tys.mk_option(out);
                let f = self.fn_mut_param(&[item], o, span);
                (B::IterFindMap, vec![f], o)
            }
            "position" => {
                let p = self.fn_mut_param(&[item], BOOL, span);
                let o = self.tys.mk_option(USIZE);
                (B::IterPosition, vec![p], o)
            }
            // ExactSizeIterator + DoubleEndedIterator: the slice and
            // array iterators lust has, and Map, Copied, Cloned of them.
            "rposition" => {
                if !self.rposition_ok(base) {
                    let tn = self.tn(base);
                    self.err("L0640", span, format!("`rposition` on `{tn}` is not implemented yet"), "Use `rposition` on a slice iterator (`v.iter()`).");
                    return self.iter_bail(args);
                }
                let p = self.fn_mut_param(&[item], BOOL, span);
                let o = self.tys.mk_option(USIZE);
                (B::IterRposition, vec![p], o)
            }
            "fold" => {
                let Some(&init) = args.first() else {
                    self.err("L0105", span, "`fold` takes 2 arguments", "Pass the initial value and the closure.");
                    return self.iter_bail(args);
                };
                let acc = self.expr(init, None);
                let f = self.fn_mut_param(&[acc, item], acc, span);
                if args.len() != 2 {
                    self.err("L0105", span, "`fold` takes 2 arguments", "Pass the initial value and the closure.");
                }
                self.set_res(e, Res::BuiltinMethod { b: B::IterFold, derefs, autoref: Autoref::None });
                for &a in &args[1..] {
                    self.expect_expr(a, f);
                }
                return acc;
            }
            "for_each" => {
                let f = self.fn_mut_param(&[item], UNIT, span);
                (B::IterForEach, vec![f], UNIT)
            }
            "min" | "max" => {
                self.deferred_ord.push((item, span));
                let o = self.tys.mk_option(item);
                (if n == "min" { B::IterMin } else { B::IterMax }, vec![], o)
            }
            "min_by_key" | "max_by_key" => {
                let key = self.new_var(false);
                let ri = r(self, item);
                let f = self.fn_mut_param_ref(&[ri], key, span);
                self.deferred_ord.push((key, span));
                let o = self.tys.mk_option(item);
                (if n == "min_by_key" { B::IterMinByKey } else { B::IterMaxByKey }, vec![f], o)
            }
            "collect" => {
                let target = self.iter_target(turbofish, expected, span);
                // A std source collection (`BTreeMap`, `BTreeSet`): the
                // call is its `FromIterator::from_iter(self)`, as rustc's
                // `collect` is (W-STD-C). The `Target: FromIterator<Item>`
                // obligation proves the impl's bounds (`T: Ord`).
                let tr = self.resolve(target);
                if let Some(a) = self.tys.local_adt(tr).or_else(|| self.tys.adt_parts(tr).and_then(|(d, _)| self.tys.local_adt_of(d)))
                    && self.p.is_std_adt(a)
                    && args.is_empty()
                {
                    // Each has one `FromIterator` impl, whose item is the
                    // entry type: unify it now, so `collect::<BTreeMap<_,
                    // _>>()` infers `K` and `V` from the items.
                    let path = self.p.display_path(self.p.adt(a).name);
                    let targs: Vec<Ty> = self.tys.adt_parts(tr).map(|(_, x)| self.tys.args(x).iter().filter_map(|g| g.as_ty()).collect()).unwrap_or_default();
                    let entry = match (path.rsplit("::").next(), targs.as_slice()) {
                        (Some("BTreeMap"), [k, v]) => {
                            let ts = self.tys.intern_tys(&[*k, *v]);
                            Some(self.tys.intern(TyKind::Tuple(ts)))
                        }
                        (Some("BTreeSet"), [t]) => Some(*t),
                        _ => None,
                    };
                    if let Some(entry) = entry
                        && !self.unify(entry, item)
                    {
                        self.mismatch(span, entry, item);
                        return self.iter_bail(args);
                    }
                    let targs = self.tys.intern_args(&[GenericArg::Ty(tr), GenericArg::Ty(item)]);
                    let trait_ref = TraitRef { def: self.p.gx.lang.from_iterator, args: targs, bindings: EMPTY_BINDINGS };
                    self.obl.push_trait_at(trait_ref, span, 0);
                    let name = self.p.interner.intern("from_iter");
                    super::method::defer_trait_method(self, e, trait_ref, name, vec![GenericArg::Ty(base)], derefs, Autoref::None);
                    return tr;
                }
                if !self.collect_target_ok(target, item, span) {
                    return self.iter_bail(args);
                }
                (B::IterCollect, vec![], target)
            }
            "sum" | "product" => {
                let target = self.iter_target(turbofish, expected, span);
                if !self.sum_target_ok(target, item, n, span) {
                    return self.iter_bail(args);
                }
                (if n == "sum" { B::IterSum } else { B::IterProduct }, vec![], target)
            }
            _ => return self.iter_unknown(n, span, base, args),
        };
        let autoref = if by_value { Autoref::None } else { Autoref::RefMut };
        if autoref != Autoref::None {
            self.check_packed_borrow(recv, span);
        }
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        // An expected adapter type fixes the adapter's own args first, so
        // a closure argument sees a fn pointer the result names
        // (`-> Map<Iter<'_, T>, fn(&T) -> U>`), as rustc's expected
        // inputs do (W-CHECK-G).
        if !params.is_empty()
            && let Some(want) = expected.map(|t| self.resolve(t))
            && it::is_iter(&self.tys, ret)
            && self.tys.adt_parts(want).zip(self.tys.adt_parts(ret)).is_some_and(|((a, _), (b, _))| a == b)
        {
            let snap = self.snapshot_vars();
            if !self.unify(ret, want) {
                self.rollback_vars(snap);
            }
        }
        // A builtin item as the callable (`.map(Some)`) is fine here:
        // borrowck checks the adapter call's summary, so it is not a
        // generic Fn-bound argument (`deferred_item_args`).
        let item_args = self.deferred_item_args.len();
        self.check_args(&params, args, span);
        self.deferred_item_args.truncate(item_args);
        // The expansion calls closures, fn items, and fn pointers; a
        // `dyn Fn` value, or a reference or box around a callable
        // (`.map(r)` for `r: &dyn Fn(..)`), meets the bound but has no
        // expansion yet. Callable params are the `fn_mut_param` vars.
        for (&a, &pt) in args.iter().zip(&params) {
            let is_callable_param = matches!(self.tys.kind(pt), TyKind::Infer(v) if self.iter_closure_args.contains_key(&v.0));
            let t = self.deep(pt);
            if is_callable_param && (matches!(self.kind(t), TyKind::Dyn(..) | TyKind::Ref(..)) || self.tys.boxed_elem(t).is_some()) {
                let s = self.span(a);
                self.errs.push(generics::dyn_not_yet(s, "a `dyn Fn` value or a reference to a callable as an iterator adapter's callable"));
                return ERROR;
            }
        }
        ret
    }

    /// True when `t` is an iterator only through a bound: a type
    /// parameter (`impl Iterator<..>` in argument position is one), an
    /// opaque type, or a projection, with `Iterator` evidence from the
    /// env. Its adapters wrap it as the builtin adapter types do; an
    /// instance checks again with the concrete type, so codegen only
    /// sees builtin chains. A user iterator type by impl is not one:
    /// its chains would need the unfused path (docs/ARCH.md 3.4).
    pub(super) fn param_iter(&mut self, t: Ty) -> bool {
        let t = self.deep(t);
        if !self.p.gx.has_generics || !matches!(self.kind(t), TyKind::Param(_) | TyKind::Opaque(..) | TyKind::Projection(..)) {
            return false;
        }
        let args_id = self.tys.intern_args(&[GenericArg::Ty(t)]);
        let tr = TraitRef { def: self.p.gx.lang.iterator, args: args_id, bindings: EMPTY_BINDINGS };
        let snap = self.snapshot_vars();
        let ok = matches!(self.select_obligation(tr), Selection::ParamEvidence(_));
        self.rollback_vars(snap);
        ok
    }

    /// The item type of an iterator `iter_call` accepts: the builtin
    /// table, else `<t as Iterator>::Item` normalized in this env (a
    /// chain over a bound-only iterator, see `param_iter`).
    pub(super) fn iter_item(&mut self, t: Ty) -> Ty {
        if let Some(item) = it::item_ty(&mut self.tys, t) {
            return item;
        }
        let args_id = self.tys.intern_args(&[GenericArg::Ty(t)]);
        let proj = self.tys.intern(TyKind::Projection(AssocId(self.p.gx.lang.assoc_item), args_id));
        self.normalize_here(proj)
    }

    /// True for the Iterator methods `iter_call` types.
    fn iter_method_known(&self, n: &str) -> bool {
        matches!(
            n,
            "rposition"
                | "map"
                | "filter"
                | "filter_map"
                | "enumerate"
                | "rev"
                | "take"
                | "skip"
                | "step_by"
                | "chain"
                | "zip"
                | "copied"
                | "cloned"
                | "take_while"
                | "skip_while"
                | "peekable"
                | "inspect"
                | "count"
                | "last"
                | "fold"
                | "for_each"
                | "min"
                | "max"
                | "min_by_key"
                | "max_by_key"
                | "collect"
                | "sum"
                | "product"
        )
    }

    /// Checks the arguments of a rejected call (so their own errors
    /// still report) and answers the error type.
    pub(super) fn iter_bail(&mut self, args: &[ExprId]) -> Ty {
        for &a in args {
            self.expr(a, None);
        }
        ERROR
    }

    /// A method name that is not one `iter_call` types.
    fn iter_unknown(&mut self, n: &str, span: Span, base: Ty, args: &[ExprId]) -> Ty {
        let tn = self.tn(base);
        if DECLARED_ONLY.contains(&n) || n == "peek" {
            self.err("L0640", span, format!("the iterator method `{n}` is not implemented yet"), "Rewrite the chain with the supported adapters, or with a loop.");
        } else {
            self.err(
                "L0104",
                span,
                format!("no method `{n}` on type `{tn}`"),
                "Check the method name. The prototype supports a small std subset (see README).",
            );
        }
        self.iter_bail(args)
    }

    /// The item type of `base` as an iterator through its own `next`
    /// (`IterKind::ByNext`, W-STD-B), or None when it is not one. A type
    /// parameter, projection, or opaque type needs an `Iterator` bound
    /// (template checks; instances see the concrete type). A user type
    /// needs an `Iterator` impl lust can call (`by_next_fns`); one it
    /// cannot call is L0640 and gives ERROR.
    fn by_next_item(&mut self, base: Ty, span: Span) -> Option<Ty> {
        let p = self.p;
        let lang = p.gx.lang;
        let user = match self.kind(base) {
            TyKind::Param(_) | TyKind::Projection(..) | TyKind::Opaque(..) => false,
            TyKind::Adt(..) if self.tys.local_adt(base).is_some() && self.tys.builtin_of(base).is_none() => true,
            _ => return None,
        };
        let args = self.tys.intern_args(&[GenericArg::Ty(base)]);
        // `<I as IntoIterator>::IntoIter` is an Iterator with the
        // IntoIterator's own Item, by the trait's declaration.
        if let TyKind::Projection(AssocId(a), pargs) = self.kind(base)
            && a == lang.assoc_into_iter
        {
            let item = self.tys.intern(TyKind::Projection(AssocId(lang.assoc_into_item), pargs));
            return Some(self.normalize_here(item));
        }
        let tr = TraitRef { def: lang.iterator, args, bindings: EMPTY_BINDINGS };
        match self.select_obligation(tr) {
            Selection::Impl { .. } | Selection::ParamEvidence(_) => {}
            _ => return None,
        }
        if user && let Err(why) = by_next_fns(p, base) {
            let tn = self.tn(base);
            self.err("L0640", span, format!("adapters over `{tn}` are not implemented yet: {why}"), "Loop with `while let Some(x) = it.next()` instead.");
            return Some(ERROR);
        }
        let item = self.tys.intern(TyKind::Projection(AssocId(lang.assoc_item), args));
        Some(self.normalize_here(item))
    }

    /// True when an array by value can be iterated (`array::IntoIter`,
    /// W-STD-B): its elements are Copy (no per-element drop state
    /// yet); an element type still unknown is checked at body end.
    /// Otherwise reports L0640.
    pub(super) fn array_iter_elem_ok(&mut self, el: Ty, span: Span) -> bool {
        let el = self.deep(el);
        if matches!(self.kind(el), TyKind::Infer(_)) {
            self.deferred_copy.push((el, span));
            return true;
        }
        if is_copy(self.p, &self.tys, el) || matches!(self.kind(el), TyKind::Error) {
            return true;
        }
        let tn = self.tn(el);
        self.err(
            "L0640",
            span,
            format!("iterating an array of `{tn}` by value is not implemented yet (only Copy elements)"),
            "Iterate with `.iter()`, or collect the array into a Vec first.",
        );
        false
    }

    /// A fresh closure-argument type with the pending obligations of
    /// `F: FnMut(inputs..) -> output`. The closure's arguments are items
    /// (or `&item`, see `fn_mut_param_ref`): free regions, which the
    /// borrow checker takes from the iterator (W-BORROW).
    fn fn_mut_param(&mut self, inputs: &[Ty], output: Ty, span: Span) -> Ty {
        self.fn_mut_param_flags(inputs, &vec![false; inputs.len()], output, span)
    }

    /// `fn_mut_param` for `F: FnMut(&Self::Item) -> output`: the outer
    /// reference is higher-ranked (Rust's bound writes it).
    fn fn_mut_param_ref(&mut self, inputs: &[Ty], output: Ty, span: Span) -> Ty {
        self.fn_mut_param_flags(inputs, &vec![true; inputs.len()], output, span)
    }

    fn fn_mut_param_flags(&mut self, inputs: &[Ty], by_ref: &[bool], output: Ty, span: Span) -> Ty {
        let f = self.new_var(false);
        if let TyKind::Infer(v) = self.kind(f) {
            self.iter_closure_args.insert(v.0, by_ref.to_vec());
        }
        let lang = self.p.gx.lang;
        let ts = self.tys.intern_tys(inputs);
        let tuple = self.tys.intern(TyKind::Tuple(ts));
        let args = self.tys.intern_args(&[GenericArg::Ty(f), GenericArg::Ty(tuple)]);
        self.obl.push(obligations::Obligation::Trait { trait_ref: TraitRef { def: lang.fn_mut, args, bindings: EMPTY_BINDINGS }, span, depth: 0 });
        if let Some(out) = lang.output_of(lang.fn_once) {
            self.obl.push(obligations::Obligation::AssocEq { eq: AssocEqData { assoc: out, trait_args: args, ty: output }, span });
        }
        f
    }

    /// The iterator a `chain` or `zip` argument turns into through
    /// `IntoIterator`: an iterator as itself, `&X`/`&mut X` over a
    /// Vec, slice, or array as a slice iterator, a Vec by value as
    /// `vec::IntoIter`. None for other types.
    fn into_iter_ty(&mut self, t: Ty) -> Option<Ty> {
        // A user iterator type by value: its `next` wrapper (W-STD-B).
        if !it::is_iter(&self.tys, t)
            && !self.param_iter(t)
            && let Some(item) = self.by_next_item(t, Span::default())
        {
            return (item != ERROR).then(|| it::mk_iter(&mut self.tys, IterKind::ByNext, &[t, item]));
        }
        if it::is_iter(&self.tys, t) || self.param_iter(t) {
            return Some(t);
        }
        if let Some(el) = self.tys.vec_elem(t) {
            return Some(it::mk_iter(&mut self.tys, IterKind::VecIntoIter, &[el]));
        }
        // An array by value (`array::IntoIter`, W-STD-B); the caller
        // owes the Copy check on its element.
        if let TyKind::Array(el, _) = self.kind(t) {
            return Some(it::mk_iter(&mut self.tys, IterKind::ArrayIntoIter, &[el, t]));
        }
        let TyKind::Ref(_, m, inner) = self.kind(t) else { return None };
        let inner = self.resolve(inner);
        let el = match self.kind(inner) {
            TyKind::Slice(el) | TyKind::Array(el, _) => el,
            _ => self.tys.vec_elem(inner)?,
        };
        let k = if m.is_mut() { IterKind::SliceIterMut } else { IterKind::SliceIter };
        Some(it::mk_iter(&mut self.tys, k, &[el]))
    }

    /// True when `rposition` runs on `t` here: an ExactSizeIterator and
    /// DoubleEndedIterator whose length the expansion knows (`size`).
    fn rposition_ok(&self, t: Ty) -> bool {
        use IterKind as K;
        match it::iter_parts(&self.tys, t) {
            Some((K::SliceIter | K::SliceIterMut | K::ArrayIntoIter, _)) => true,
            Some((K::Map | K::Copied | K::Cloned, a)) => self.rposition_ok(a[0]),
            _ => false,
        }
    }

    /// True when an iterator type is double-ended in Rust 1.99, for
    /// the kinds lust has.
    fn double_ended(&mut self, t: Ty) -> bool {
        use IterKind as K;
        if self.tys.is_chars_ty(t) {
            return true;
        }
        let Some((k, a)) = it::iter_parts(&self.tys, t) else { return false };
        match k {
            K::SliceIter | K::SliceIterMut | K::VecIntoIter | K::Range | K::RangeInclusive => true,
            K::Map | K::Filter | K::FilterMap | K::Rev | K::Copied | K::Cloned | K::Inspect | K::Peekable => self.double_ended(a[0]),
            K::Chain => self.double_ended(a[0]) && self.double_ended(a[1]),
            // These need ExactSizeIterator too: lust keeps them forward-only for now.
            K::Enumerate | K::Take | K::Skip | K::Zip | K::StepBy => false,
            K::TakeWhile | K::SkipWhile => false,
            K::RecvIter | K::RecvTryIter | K::RecvIntoIter => false,
            // hashbrown's iterators are forward-only.
            K::MapIter
            | K::MapIterMut
            | K::MapKeys
            | K::MapValues
            | K::MapValuesMut
            | K::MapIntoIter
            | K::MapIntoKeys
            | K::MapIntoValues
            | K::SetIter
            | K::SetIntoIter => false,
            K::ArrayIntoIter | K::RepeatN => true,
            // Only `next`: no `next_back` reaches the user's impl yet.
            K::ByNext => false,
        }
    }

    /// The target type of `collect`, `sum`, or `product`: the
    /// turbofish when written, else the expected type, else a fresh
    /// variable (which the target check then rejects).
    fn iter_target(&mut self, turbofish: &[ast::GenericArg], expected: Option<Ty>, span: Span) -> Ty {
        if let Some(ast::GenericArg::Type(t)) = turbofish.first() {
            let t = match self.turbofish_ty.take() {
                Some(t) => t,
                None => self.resolve_written(*t),
            };
            if turbofish.len() > 1 {
                self.err("L0105", span, "this method takes 1 type argument", "Write one target type.");
            }
            return t;
        }
        match expected {
            Some(t) => t,
            None => self.new_var(false),
        }
    }

    /// `collect` into `Vec<Item>` or `String` (from `char`, `&char`,
    /// `&str`, or `String` items): the targets lust builds.
    fn collect_target_ok(&mut self, target: Ty, item: Ty, span: Span) -> bool {
        let t = self.resolve(target);
        if let Some(el) = self.tys.vec_elem(t) {
            if !self.unify(el, item) {
                let want = self.tys.mk_vec(item);
                self.mismatch(span, want, t);
                return false;
            }
            return true;
        }
        if self.tys.is_string_ty(t) {
            let it_t = self.deep(item);
            let ok = it_t == CHAR
                || it_t == STRING
                || matches!(self.kind(it_t), TyKind::Ref(_, Mut::Shared, x) if self.resolve(x) == CHAR || self.resolve(x) == STR);
            if !ok {
                let tn = self.tn(it_t);
                self.err("L0612", span, format!("a `String` cannot be built from an iterator over `{tn}`"), "Collect into a `Vec` instead.");
            }
            return ok;
        }
        if let Some(ok) = self.hash_collect_target(t, item, span) {
            return ok;
        }
        if matches!(self.kind(t), TyKind::Infer(_)) {
            self.err("L0610", span, "type annotations needed: the `collect` target type must be known here", "Write `collect::<Vec<_>>()`, or annotate the binding.");
        } else {
            let tn = self.tn(t);
            self.err("L0640", span, format!("`collect` into `{tn}` is not implemented yet"), "Collect into a `Vec` or a `String`.");
        }
        false
    }

    /// `sum` and `product` into an integer or float type `S`, from
    /// items `S` or `&S` (Rust's `Sum<S>` and `Sum<&S>` impls).
    fn sum_target_ok(&mut self, target: Ty, item: Ty, n: &str, span: Span) -> bool {
        let t = self.resolve(target);
        let numeric = |k: TyKind| matches!(k, TyKind::Int(_) | TyKind::Float(_));
        if !numeric(self.kind(t)) {
            if matches!(self.kind(t), TyKind::Infer(_)) {
                self.err("L0610", span, format!("type annotations needed: the `{n}` result type must be known here"), format!("Write `{n}::<i64>()`, or annotate the binding."));
            } else {
                let tn = self.tn(t);
                self.err("L0612", span, format!("`{tn}` cannot be the result of `{n}`"), "Sum into an integer or float type.");
            }
            return false;
        }
        let i = self.resolve(item);
        let plain = match self.kind(i) {
            TyKind::Ref(_, Mut::Shared, x) => self.resolve(x),
            _ => i,
        };
        if !self.unify(plain, t) {
            let tn = self.tn(t);
            let iname = self.tn(item);
            self.err("L0612", span, format!("`{tn}` cannot be the {n} of `{iname}` items"), format!("Map the items to `{tn}` first."));
            return false;
        }
        true
    }

    /// A range expression used as a value: `std::ops::Range<T>` or
    /// `RangeInclusive<T>` over an integer type (the iterator form;
    /// `for` loops and slicing keep their own syntactic paths).
    pub(super) fn range_value(&mut self, e: ExprId, lo: ExprId, hi: ExprId, inclusive: bool, span: Span) -> Ty {
        let lt = self.expr(lo, None);
        let ht = self.expr(hi, Some(lt));
        if !self.unify(lt, ht) {
            self.mismatch(self.span(hi), lt, ht);
            return ERROR;
        }
        let t = self.resolve(lt);
        if !(matches!(self.kind(t), TyKind::Int(_)) || self.kind(t).is_int_infer()) {
            let tn = self.tn(t);
            self.err("L0641", span, format!("ranges of `{tn}` are not supported yet"), "Use an integer range.");
            return ERROR;
        }
        let _ = e;
        let k = if inclusive { IterKind::RangeInclusive } else { IterKind::Range };
        it::mk_iter(&mut self.tys, k, &[t])
    }
}

/// The adapter and consumer methods `iter_call` answers, by name: the
/// calls that wrap a `ByNext` iterator.
const ITER_METHODS: &[&str] = &[
    "map",
    "filter",
    "filter_map",
    "enumerate",
    "rev",
    "take",
    "skip",
    "step_by",
    "chain",
    "zip",
    "copied",
    "cloned",
    "take_while",
    "skip_while",
    "peekable",
    "inspect",
    "count",
    "last",
    "nth",
    "any",
    "all",
    "find",
    "find_map",
    "position",
    "fold",
    "for_each",
    "min",
    "max",
    "min_by_key",
    "max_by_key",
    "collect",
    "sum",
    "product",
    "size_hint",
];

/// The user fns a `ByNext` iterator calls: `next`, and `size_hint`
/// when the impl defines it. The impl must be non-generic and define
/// no other method: std's adapters call the inner iterator's own
/// `fold`, `nth`, `count`, and kin, which lust's expansions do not
/// (they loop on `next`), so an impl that overrides one of those is
/// refused rather than run differently.
pub struct ByNextFns {
    pub next: LocalDefId,
    pub size_hint: Option<LocalDefId>,
}

/// `by_next_fns` for a user type `t` (concrete), or why lust cannot
/// iterate it through `next` yet.
pub fn by_next_fns(p: &Program, t: Ty) -> Result<ByNextFns, &'static str> {
    let lang = p.gx.lang;
    let rec = p
        .gx
        .index
        .impls_of_trait(lang.iterator)
        .iter()
        .map(|&id| p.gx.index.get(id))
        .find(|r| r.local && r.self_ty(&p.tys) == t)
        .ok_or("its `Iterator` impl is generic")?;
    if !rec.generics.params.is_empty() {
        return Err("its `Iterator` impl is generic");
    }
    let (mut next, mut size_hint) = (None, None);
    for &d in &rec.items {
        let Some(l) = p.local_def(d.hash) else { continue };
        match p.name(p.fn_info(l).name) {
            "next" => next = Some(l),
            "size_hint" => size_hint = Some(l),
            _ => return Err("its `Iterator` impl defines a provided method"),
        }
    }
    Ok(ByNextFns { next: next.ok_or("its `Iterator` impl has no `next`")?, size_hint })
}
