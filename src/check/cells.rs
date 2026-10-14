// `Rc` weak references, `Cell`, and `RefCell` in body checking (W-STD-A
// phase 3). The types are builtin Adts (ty/mod.rs `BuiltinDefs`): their
// associated fns and methods type here as builtin calls, and codegen
// emits them (cgen.rs). `RefCell` borrows are runtime-checked like
// Rust's: the guards `Ref<T>` and `RefMut<T>` deref like smart pointers
// (`TyIntern::smart_elem`), and their drop gives the borrow back.
use super::*;

impl<'p, 'a> Ctx<'p, 'a> {
    /// The associated fns `Rc::downgrade`, `Rc::ptr_eq`, `Weak::new`,
    /// `Weak::ptr_eq`, `RefCell::new`, and `Cell::new`. None when
    /// `ty_name::item` is none of these (the caller goes on); a known
    /// type with an item lust lacks rejects here. A user type of the
    /// same name wins, except on a std path (`std_ty`).
    pub(super) fn cell_assoc(&mut self, ty_name: Sym, item: Sym, std_ty: bool, span: Span) -> Option<Option<Res>> {
        let p = self.p;
        let (t, i) = (self.name(ty_name).to_string(), self.name(item).to_string());
        if !std_ty && p.type_names.contains_key(&ty_name) {
            return None;
        }
        let b = match (t.as_str(), i.as_str()) {
            ("Rc", "downgrade") => Builtin::RcDowngrade,
            ("Rc", "ptr_eq") => Builtin::RcPtrEq,
            ("Weak", "new") => Builtin::WeakNew,
            ("Weak", "ptr_eq") => Builtin::WeakPtrEq,
            ("RefCell", "new") => Builtin::RefCellNew,
            ("Cell", "new") => Builtin::CellNew,
            ("Weak" | "RefCell" | "Cell", _) => {
                self.err(
                    "L0104",
                    span,
                    format!("no function `{t}::{i}` in lust yet"),
                    "Lust supports Weak::new, Weak::ptr_eq, RefCell::new, and Cell::new.",
                );
                return Some(None);
            }
            _ => return None,
        };
        Some(Some(Res::Builtin(b)))
    }

    /// Parameter and return types of a `cell_assoc` builtin call. The
    /// element type comes from turbofish on the type segment
    /// (`Weak::<u8>::new`, `std::rc::Weak::<u8>::new`) when written.
    pub(super) fn cell_call_sig(&mut self, b: Builtin, callee: ExprId) -> (Vec<Ty>, Ty) {
        let written = match self.p.ast.expr(callee) {
            Expr::Path(segs) if segs.len() >= 2 => segs[segs.len() - 2].type_args(),
            _ => Vec::new(),
        };
        let elem = match written.first() {
            Some(&g) => self.resolve_written(g),
            None => self.new_var(false),
        };
        let mk = |this: &mut Self, which: fn(&BuiltinDefs) -> DefId| this.tys.mk_builtin1(which, elem);
        match b {
            Builtin::RcDowngrade => {
                // A `Weak` is a thin pointer: no `Weak<dyn Tr>` yet.
                self.deferred_sized.push((elem, self.p.ast.expr_span(callee)));
                let rc = self.tys.mk_rc(elem);
                let r = self.tys.mk_ref(false, rc);
                (vec![r], mk(self, |d| d.weak))
            }
            Builtin::RcPtrEq => {
                let rc = self.tys.mk_rc(elem);
                let r = self.tys.mk_ref(false, rc);
                (vec![r, r], BOOL)
            }
            Builtin::WeakNew => (vec![], mk(self, |d| d.weak)),
            Builtin::WeakPtrEq => {
                let w = mk(self, |d| d.weak);
                let r = self.tys.mk_ref(false, w);
                (vec![r, r], BOOL)
            }
            Builtin::RefCellNew => (vec![elem], mk(self, |d| d.refcell)),
            _ => (vec![elem], mk(self, |d| d.cell)),
        }
    }

    /// Methods on `Weak<T>`, `RefCell<T>`, and `Cell<T>` receivers
    /// (after autoderef). None when the receiver is none of these.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn cell_method(&mut self, e: ExprId, recv: ExprId, base: Ty, derefs: u8, name: Sym, span: Span, args: &[ExprId]) -> Option<Ty> {
        use Builtin as B;
        let n = self.name(name).to_string();
        let (b, autoref, params, ret) = if let Some(el) = self.tys.weak_elem(base) {
            let w_ref = self.tys.mk_ref(false, base);
            match n.as_str() {
                "upgrade" => {
                    let rc = self.tys.mk_rc(el);
                    let o = self.tys.mk_option(rc);
                    (B::WeakUpgrade, Autoref::Ref, vec![], o)
                }
                "strong_count" => (B::WeakStrongCount, Autoref::Ref, vec![], USIZE),
                "weak_count" => (B::WeakWeakCount, Autoref::Ref, vec![], USIZE),
                "ptr_eq" => (B::WeakPtrEq, Autoref::Ref, vec![w_ref], BOOL),
                _ => return None,
            }
        } else if let Some(el) = self.tys.refcell_elem(base) {
            match n.as_str() {
                "borrow" => {
                    let g = self.tys.mk_builtin1(|d| d.ref_guard, el);
                    (B::RefCellBorrow, Autoref::Ref, vec![], g)
                }
                "borrow_mut" => {
                    let g = self.tys.mk_builtin1(|d| d.ref_mut_guard, el);
                    (B::RefCellBorrowMut, Autoref::Ref, vec![], g)
                }
                "into_inner" => (B::RefCellIntoInner, Autoref::None, vec![], el),
                "replace" => (B::RefCellReplace, Autoref::Ref, vec![el], el),
                "swap" => {
                    let r = self.tys.mk_ref(false, base);
                    (B::RefCellSwap, Autoref::Ref, vec![r], UNIT)
                }
                "get_mut" => {
                    let r = self.tys.mk_ref(true, el);
                    (B::RefCellGetMut, Autoref::RefMut, vec![], r)
                }
                "take" => {
                    self.deferred_default.push((el, span));
                    (B::RefCellTake, Autoref::Ref, vec![], el)
                }
                "try_borrow" | "try_borrow_mut" | "replace_with" | "try_borrow_unguarded" | "undo_leak" => {
                    self.err("L0640", span, format!("`RefCell::{n}` is not implemented yet"), "Use `borrow`, `borrow_mut`, or `replace`.");
                    return Some(self.iter_bail(args));
                }
                _ => return None,
            }
        } else if let Some(el) = self.tys.cell_elem(base) {
            match n.as_str() {
                "get" => {
                    self.deferred_copy.push((el, span));
                    (B::CellGet, Autoref::Ref, vec![], el)
                }
                "set" => (B::CellSet, Autoref::Ref, vec![el], UNIT),
                "replace" => (B::CellReplace, Autoref::Ref, vec![el], el),
                "into_inner" => (B::CellIntoInner, Autoref::None, vec![], el),
                "get_mut" => {
                    let r = self.tys.mk_ref(true, el);
                    (B::CellGetMut, Autoref::RefMut, vec![], r)
                }
                "swap" => {
                    let r = self.tys.mk_ref(false, base);
                    (B::CellSwap, Autoref::Ref, vec![r], UNIT)
                }
                "take" => {
                    self.deferred_default.push((el, span));
                    (B::CellTake, Autoref::Ref, vec![], el)
                }
                "update" | "as_ptr" | "from_mut" | "as_slice_of_cells" => {
                    self.err("L0640", span, format!("`Cell::{n}` is not implemented yet"), "Use `get`, `set`, or `replace`.");
                    return Some(self.iter_bail(args));
                }
                _ => return None,
            }
        } else {
            return None;
        };
        if autoref != Autoref::None {
            self.check_packed_borrow(recv, span);
        }
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        self.check_args(&params, args, span);
        Some(ret)
    }
}
