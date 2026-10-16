// `Extend` on Vec and String in body checking (W-STD-B). The argument
// goes through `IntoIterator` (`ty::iter::as_iter_ty`, or `ByNext` for an
// iterator lust calls through its `next`); the item kinds
// are the impls std declares: `Vec<T>: Extend<T>` and `Extend<&T>` for
// `T: Copy`; `String: Extend<char | &char | &str | String | Box<str> |
// Cow<str>>`. The iterator expansion (lower/iter.rs) writes Rust's
// exact reserve and push sequence. Maps and sets: check/hashmap.rs.
use super::*;

impl<'p> Ctx<'p> {
    /// L0610 for an `extend` whose item type is still open (rustc E0283):
    /// std has `Extend<T>` and `Extend<&T>` (and `(K, V)`, `(&K, &V)` for
    /// maps), and an open item picks neither. A map item counts as open
    /// when both tuple parts are.
    pub(super) fn extend_item_open(&mut self, item: Ty, arg: ExprId) -> bool {
        // A fn item or closure output (`.map(Enum::Variant)`) is known
        // once the queue runs.
        let d = self.deep(item);
        if self.open_extend_item(d) {
            self.run_obligations(false);
        }
        let item = self.deep(item);
        let open = self.open_extend_item(item);
        if open {
            self.err(
                "L0610",
                self.span(arg),
                "type annotations needed: the item type of this `extend` must be known here",
                "Annotate the element type, such as `Vec::<i32>::new()`.",
            );
        }
        open
    }

    /// True when an `Extend` item type picks none of std's impls: a type
    /// variable, or a tuple of them (`extend_item_open`, `std_extend_item_open`).
    pub(super) fn open_extend_item(&self, item: Ty) -> bool {
        match self.kind(item) {
            TyKind::Tuple(ts) => {
                let ts = self.tys.tys_of(ts);
                !ts.is_empty() && ts.iter().all(|&t| self.unbound_general(t))
            }
            _ => self.unbound_general(item),
        }
    }

    /// rustc E0283 for `extend` on a spliced std collection (`VecDeque`,
    /// `BTreeSet`, `BTreeMap`) whose argument's item type is open: std has
    /// `Extend<T>` and `Extend<&T>`, std source writes only the first,
    /// and selection would pick it. The argument is trial-checked and
    /// rolled back; a call that passes checks it for real.
    pub(super) fn std_extend_item_open(&mut self, base: Ty, args: &[ExprId]) -> bool {
        let TyKind::Adt(a, _) = self.kind(base) else { return false };
        let [arg] = args else { return false };
        if !self.tys.local_adt_of(a).is_some_and(|l| self.p.is_std_adt(l)) {
            return false;
        }
        let trial = method::ArgTrial::mark(self);
        let at = self.expr(*arg, None);
        let at = self.deep(at);
        let item = crate::ty::iter::as_iter_ty(&mut self.tys, at).and_then(|it| crate::ty::iter::item_ty(&mut self.tys, it));
        if let Some(i) = item {
            let d = self.deep(i);
            if self.open_extend_item(d) {
                self.run_obligations(false);
            }
        }
        let open = item.is_some_and(|i| {
            let i = self.deep(i);
            self.open_extend_item(i)
        });
        trial.rollback(self);
        if open {
            self.expr(*arg, None);
            self.err(
                "L0610",
                self.span(*arg),
                "type annotations needed: the item type of this `extend` must be known here",
                "Annotate the element type, such as `Vec::<i32>::new()`.",
            );
        }
        open
    }

    /// `extend` on a Vec or String receiver, or None for other receivers.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn seq_extend(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        name_span: Span,
        args: &[ExprId],
    ) -> Option<Ty> {
        let vec_el = self.tys.vec_elem(base);
        if vec_el.is_none() && !self.tys.is_string_ty(base) {
            return None;
        }
        let [a] = args else {
            self.err("L0105", name_span, "`extend` takes 1 argument", "Pass the iterator.");
            for &a in args {
                self.expr(a, None);
            }
            return Some(ERROR);
        };
        let at = self.expr(*a, None);
        let at = self.deep(at);
        let Some(it) = crate::ty::iter::as_iter_ty(&mut self.tys, at).or_else(|| self.into_iterator_arg(*a, at)) else {
            let tn = self.tn(at);
            self.err("L0640", self.span(*a), format!("`extend` from `{tn}` is not implemented yet"), "Pass an iterator, a Vec, or a slice.");
            return Some(ERROR);
        };
        if it == ERROR {
            return Some(ERROR);
        }
        let item = crate::ty::iter::item_ty(&mut self.tys, it).unwrap_or(ERROR);
        let item = self.deep(item);
        if self.extend_item_open(item, *a) {
            return Some(ERROR);
        }
        let b = match vec_el {
            Some(el) => {
                // `Extend<T>`, else `Extend<&T>` for `T: Copy`.
                let snap = self.snapshot_vars();
                let obl = self.obl_len();
                if self.unify(el, item) {
                    Builtin::VecExtend
                } else {
                    self.rollback_vars(snap);
                    self.obl_truncate(obl);
                    // Only shared items: std has no `Extend<&mut T>`.
                    match self.kind(item) {
                        TyKind::Ref(_, Mut::Shared, x) if self.unify(el, x) => {
                            self.deferred_copy.push((x, self.span(*a)));
                            Builtin::VecExtend
                        }
                        _ => {
                            self.mismatch(self.span(*a), el, item);
                            return Some(ERROR);
                        }
                    }
                }
            }
            None => {
                let k = self.kind(item);
                let ok = item == CHAR
                    || item == STRING
                    || matches!(k, TyKind::Ref(_, Mut::Shared, x) if self.resolve(x) == CHAR || self.resolve(x) == STR)
                    || self.tys.smart_elem(item) == Some(STR)
                    || crate::check::collect::cow_arg(&self.tys, item) == Some(STR);
                if !ok {
                    let tn = self.tn(item);
                    self.err("L0612", self.span(*a), format!("a `String` cannot be extended with items of type `{tn}`"), "Extend with chars or strs.");
                    return Some(ERROR);
                }
                Builtin::StringExtend
            }
        };
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::RefMut });
        Some(UNIT)
    }
}
