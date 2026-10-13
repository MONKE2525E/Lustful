// `thread_local!` statics and the `std::thread::LocalKey` API (ARCH 7.3).
//
// The macro (expand/builtin.rs) turns `static NAME: T = init;` into a
// static marked `#[thread_local!]` whose value is the path to an init fn
// `fn NAME#init() -> T { init }` (`#[thread_local!const]` for the
// `const { e }` form, whose block is the init fn body). Collect types the
// static as `LocalKey<T>` (its C value is the key's slot word, zero until
// the first access) and records the init fn here. Method calls on the key
// type as builtin methods; lowering adds the init fn as an operand
// (lower/tls.rs), and the expansion after borrowck turns each call into
// the runtime access plus plain IR (closure calls, Cell and RefCell
// builtins).
use super::*;
use crate::ast::{Attr, Item, ItemKind};

/// What collect knows about a `thread_local!` static (`StaticItem::tls`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TlsKey {
    /// The init fn the expansion made: the lazy initializer, or the
    /// `const { .. }` block's value.
    pub init: LocalDefId,
    /// The `const { .. }` form: the value counts as initialized from
    /// the start, so `set` never skips it (Rust's `EagerStorage`).
    pub eager: bool,
}

/// The `thread_local!` form of a static's attributes: None for a plain
/// static, else whether it is the `const { .. }` form.
pub fn key_form(attrs: &[Attr], interner: &Interner) -> Option<bool> {
    attrs.iter().find_map(|a| match a.path.as_slice() {
        [seg] => match interner.get(seg.name) {
            crate::parser::TLS_ATTR => Some(false),
            crate::parser::TLS_CONST_ATTR => Some(true),
            _ => None,
        },
        _ => None,
    })
}

/// The init fn of a `thread_local!` static: its value is a path to a fn
/// of the same block (`stmt_idx`, a body item) or of the crate's flat
/// fn table. None only for a static the macro did not make.
pub fn init_fn(p: &Program, value: ast::ExprId, stmt_idx: Option<u32>) -> Option<LocalDefId> {
    let ast::Expr::Path(segs) = p.ast.expr(value) else { return None };
    let [seg] = segs.as_slice() else { return None };
    let Some(sidx) = stmt_idx else { return p.fn_names.get(&seg.name).copied() };
    // The expansion puts the init fn right after its static, in the same
    // block; the first fn of that name after the static is it.
    let fn_named = |it: &Item| matches!(&it.kind, ItemKind::Fn(d) if d.name == seg.name);
    let at = p.ast.stmt_items.iter().enumerate().skip(sidx as usize + 1).find(|(_, it)| fn_named(it))?.0;
    match p.body_items.get(&(at as u32)) {
        Some(BodyItem::Fn(f)) => Some(*f),
        _ => None,
    }
}

/// The `LocalKey` methods of Rust 1.99. `with` and `try_with` take any
/// value type; the rest are on `LocalKey<Cell<T>>` and
/// `LocalKey<RefCell<T>>` only.
const KEY_METHODS: &[&str] = &["with", "try_with", "with_borrow", "with_borrow_mut", "set", "get", "take", "replace"];

impl<'p, 'a> Ctx<'p, 'a> {
    /// The `thread_local!` static a method receiver names directly
    /// (`KEY.with(..)`), by static index. A key reached any other way
    /// (a `&'static LocalKey<T>` value) is not supported yet: lowering
    /// needs the static to find its init fn.
    pub(super) fn tls_static_of(&self, recv: ExprId) -> Option<u32> {
        match self.out.expr_res[self.ei(recv)] {
            Res::Static(idx) if self.p.statics.get(idx as usize).is_some_and(|s| s.tls.is_some()) => Some(idx),
            _ => None,
        }
    }

    /// Methods on a `LocalKey<T>` receiver (after autoderef). None when
    /// the receiver is no key or the name is no `LocalKey` method (a
    /// user trait method then gets its chance).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn tls_method(&mut self, e: ExprId, recv: ExprId, base: Ty, derefs: u8, name: Sym, span: Span, args: &[ExprId]) -> Option<Ty> {
        let t = self.tys.local_key_elem(base)?;
        let n = self.name(name).to_string();
        if !KEY_METHODS.contains(&n.as_str()) {
            return None;
        }
        if derefs != 0 || self.tls_static_of(recv).is_none() {
            self.err(
                "L0640",
                span,
                format!("`LocalKey::{n}` on a key that is not a `thread_local!` static by name is not supported yet"),
                "Call the method on the static itself, as in `KEY.with(|v| ..)`.",
            );
            return Some(self.tls_bail(args));
        }
        let t = self.resolve(t);
        use Builtin as B;
        let (b, params, ret) = match n.as_str() {
            "with" | "try_with" => {
                let r = self.new_var(false);
                let rt = self.tys.mk_ref(false, t);
                let f = self.fn_once_param(&[rt], r, span);
                if n == "with" {
                    (B::TlsWith, vec![f], r)
                } else {
                    let ae = self.tys.access_error_ty();
                    (B::TlsTryWith, vec![f], self.tys.mk_result(r, ae))
                }
            }
            _ => {
                let tn = self.tn(base);
                self.err(
                    "L0104",
                    span,
                    format!("no method `{n}` on type `{tn}`"),
                    "`set`, `get`, `take`, `replace`, and the `with_borrow` methods need a `Cell` or `RefCell` value.",
                );
                return Some(self.tls_bail(args));
            }
        };
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::Ref });
        self.check_args(&params, args, span);
        Some(ret)
    }

    /// Checks the arguments of a rejected call (so their own errors
    /// still report) and answers the error type.
    fn tls_bail(&mut self, args: &[ExprId]) -> Ty {
        for &a in args {
            self.expr(a, None);
        }
        ERROR
    }
}
