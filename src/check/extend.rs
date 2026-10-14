// `Extend` on Vec and String in body checking (W-STD-B). The argument
// goes through `IntoIterator` (`ty::iter::as_iter_ty`, or `ByNext` for an
// iterator lust calls through its `next`); the item kinds
// are the impls std declares: `Vec<T>: Extend<T>` and `Extend<&T>` for
// `T: Copy`; `String: Extend<char | &char | &str | String | Box<str> |
// Cow<str>>`. The iterator expansion (lower/iter.rs) writes Rust's
// exact reserve and push sequence. Maps and sets: check/hashmap.rs.
use super::*;

impl<'p, 'a> Ctx<'p, 'a> {
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
        let Some(it) = crate::ty::iter::as_iter_ty(&mut self.tys, at).or_else(|| self.by_next_arg(*a, at)) else {
            let tn = self.tn(at);
            self.err("L0640", self.span(*a), format!("`extend` from `{tn}` is not implemented yet"), "Pass an iterator, a Vec, or a slice.");
            return Some(ERROR);
        };
        if it == ERROR {
            return Some(ERROR);
        }
        if let TyKind::Array(el, _) = self.kind(at)
            && !self.array_iter_elem_ok(el, self.span(*a))
        {
            return Some(ERROR);
        }
        let item = crate::ty::iter::item_ty(&mut self.tys, it).unwrap_or(ERROR);
        let item = self.deep(item);
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
