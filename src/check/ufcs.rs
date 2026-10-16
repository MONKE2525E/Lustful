// UFCS calls of builtin methods: `Vec::len(&v)`, `Cell::get(&c)`,
// `std::thread::Builder::spawn(b, f)`.
//
// lust's builtin methods live in the method-call tables (`method_call_at`),
// not as items a path can name. A type-relative path call whose type is a
// builtin with no item of that name is checked as the method call with the
// first argument as the receiver, then held to UFCS rules: a type-relative
// path never autoderefs past the written type, and its first argument is a
// coercion site for `Self`, `&Self`, or `&mut Self`, not an autoref site.
// So the receiver's adjustment must be one rustc's argument coercion makes:
// a by-value `self` takes the argument as is, and `&self` / `&mut self`
// take a reference (of that mutability) that derefs to the written type
// through references and smart pointers. Anything else rejects. A `Vec`
// or `String` path names only its own items and its traits' (`VEC_ITEMS`,
// `STRING_ITEMS`), never a slice or `str` method the table also keys on it
// (`Vec::iter` is rustc E0599).
//
// Lowering calls `method_into` with the first argument as the receiver
// (lower.rs, `Expr::Call` with a `Res::BuiltinMethod`; a `Res::Method`
// call already lowers that way).
use super::*;

impl<'p> Ctx<'p> {
    /// `Type::method(recv, args..)` for a builtin type path `segs` whose
    /// method is a builtin one: `written` is the path's type when it
    /// resolves with its args (else the receiver's type must be the
    /// builtin the path names). None, with nothing checked, when the call
    /// has no receiver argument or the path names a slice or `str` item.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn builtin_method_by_path(
        &mut self,
        e: ExprId,
        segs: &[ast::PathSeg],
        written: Option<Ty>,
        name_span: Span,
        args: &[ExprId],
        span: Span,
        expected: Option<Ty>,
    ) -> Option<Ty> {
        let (&recv, rest) = args.split_first()?;
        let n = segs.len();
        let name = segs[n - 1].name;
        let ty_name = crate::intern::source_name(self.name(segs[n - 2].name)).to_string();
        let item = self.name(name).to_string();
        // A type path of a std builtin with methods (a module path such as
        // `mem::size_of_val`, a user type, or an associated fn with no
        // receiver keeps its own diagnostics).
        let std_prefix = segs[..n - 2].iter().all(|s| matches!(self.name(s.name), "std" | "core" | "alloc" | "cell" | "collections" | "sync" | "thread" | "vec" | "string" | "rc" | "boxed" | "hash_map" | "vec_deque"));
        if !BUILTIN_TYPES.contains(&ty_name.as_str()) || !std_prefix {
            return None;
        }
        match ty_name.as_str() {
            "Vec" if !VEC_ITEMS.contains(&item.as_str()) => return None,
            "String" if !STRING_ITEMS.contains(&item.as_str()) => return None,
            _ => {}
        }
        let at = self.expr(recv, None);
        let err_mark = self.errs.len();
        let deref_mark = (self.out.deref_recv.len(), self.deref_sites.len());
        let ret = self.method_call_with_rt(e, recv, at, name, name_span, rest, &[], expected);
        let at = self.deep(at);
        let ok = match self.out.expr_res[self.ei(e)] {
            // A builtin's std source method (`HashMap::insert`) is no
            // item a path finds either: the same rules apply.
            Res::BuiltinMethod { derefs, autoref, .. } | Res::Method { derefs, autoref, .. } => {
                // No step through a user `Deref`, and no receiver view (a
                // Cow's or an iterator wrapper's): plain builtin steps only.
                let plain = self.out.deref_recv.len() == deref_mark.0
                    && self.deref_sites.len() == deref_mark.1
                    && self.out.coerce[self.ei(recv)] == Coerce::None;
                // An eta closure's argument stands for the fn item's
                // parameter: exactly `Self`, `&Self`, or `&mut Self`
                // (`map(Vec::len)` over `&Box<Vec<_>>` items is rustc
                // E0631), never a deref coercion.
                let exact = !self.is_eta_arg(recv) || derefs <= 1;
                plain && exact && self.ufcs_recv_ok(at, segs, written, derefs, autoref)
            }
            // No method of that name for the argument (`Duration::from_days(2)`
            // is an associated fn): the path's own diagnostics stand.
            _ if self.errs.len() > err_mark => {
                self.errs.truncate(err_mark);
                return None;
            }
            // Any other form (an operator such as `String::eq` as `==`,
            // a comparison builtin) has other argument rules: reject.
            _ => false,
        };
        if !ok {
            let at_n = self.tn(at);
            self.err(
                "L0110",
                span,
                format!("mismatched types: `{ty_name}::{item}` does not take `{at_n}` as its first argument here"),
                "Pass the receiver at the method's own `self` type (`&value` for `&self`).",
            );
            return Some(ERROR);
        }
        Some(ret)
    }

    /// True when a receiver of type `at` adjusted by `derefs` and
    /// `autoref` is an argument coercion to the method's `self` type at
    /// the written type (see the file head).
    fn ufcs_recv_ok(&mut self, at: Ty, segs: &[ast::PathSeg], written: Option<Ty>, derefs: u8, autoref: Autoref) -> bool {
        let mut t = at;
        for i in 0..derefs {
            let next = match self.kind(t) {
                // The first step must be through the argument's own
                // reference for `&self` and `&mut self`.
                TyKind::Ref(_, m, inner) => {
                    if i == 0 && autoref == Autoref::RefMut && !m.is_mut() {
                        return false;
                    }
                    inner
                }
                _ if i == 0 => return false,
                _ => match self.tys.smart_elem(t) {
                    Some(inner) => inner,
                    None => return false,
                },
            };
            t = self.resolve(next);
        }
        let shape_ok = match autoref {
            Autoref::None => derefs == 0,
            Autoref::Ref | Autoref::RefMut => derefs >= 1,
            _ => false,
        };
        shape_ok
            && match written {
                Some(w) => self.unify(t, w),
                None => self.names_builtin(t, segs),
            }
    }

    /// True when the type path `segs` (then the item) names builtin type
    /// `t`: its full std path, or its bare name when no user type of that
    /// name is in scope (std's own source types, such as `HashMap`'s, may
    /// bind the name).
    fn names_builtin(&mut self, t: Ty, segs: &[ast::PathSeg]) -> bool {
        let Some(named) = super::alias_path::builtin_std_path(&self.tys, t) else { return false };
        let n = segs.len();
        let path: Vec<&str> = segs[..n - 1].iter().map(|s| crate::intern::source_name(self.name(s.name))).collect();
        if n > 2 {
            return named == path;
        }
        if named.last() != path.last() {
            return false;
        }
        let p = self.p;
        match self.binding(Namespace::Type, segs[0].name) {
            BindingRes::Def(d) => p.adt_by_def(d).is_none_or(|a| generics::is_std_adt(&p.tys, a)),
            _ => true,
        }
    }
}

/// The std types whose methods are builtin (or std source methods no path
/// resolves as items), by their bare name.
const BUILTIN_TYPES: &[&str] = &[
    "Vec", "String", "VecDeque", "HashMap", "HashSet", "Cell", "RefCell", "Mutex", "RwLock", "Condvar", "Builder",
    "OnceCell", "OnceLock",
];

/// The items a `Vec<T>` path names that lust's builtin method table has:
/// `Vec`'s inherent methods and its traits' (`Clone`, `Extend`,
/// `IntoIterator`, `Deref`, ...), not the slice methods it derefs to.
const VEC_ITEMS: &[&str] = &[
    "capacity", "reserve", "reserve_exact", "try_reserve", "try_reserve_exact", "shrink_to_fit", "shrink_to",
    "into_boxed_slice", "truncate", "as_slice", "as_mut_slice", "as_ptr", "as_mut_ptr", "swap_remove", "insert", "remove",
    "retain", "retain_mut", "dedup_by_key", "dedup_by", "dedup", "push", "pop", "pop_if", "append", "drain", "clear", "len",
    "is_empty", "split_off", "resize_with", "resize", "leak", "spare_capacity_mut", "extend_from_slice", "extend_from_within",
    "splice", "extract_if", "into_flattened", "clone", "clone_from", "extend", "into_iter", "deref", "deref_mut", "as_ref",
    "as_mut", "borrow", "borrow_mut", "eq", "ne", "cmp", "partial_cmp", "lt", "le", "gt", "ge", "max", "min", "hash", "fmt",
    "index", "index_mut", "to_owned",
];

/// The items a `String` path names that lust's builtin method table has:
/// `String`'s inherent methods and its traits', not the `str` methods.
const STRING_ITEMS: &[&str] = &[
    "into_bytes", "as_str", "as_mut_str", "push_str", "capacity", "reserve", "reserve_exact", "try_reserve",
    "try_reserve_exact", "shrink_to_fit", "shrink_to", "push", "as_bytes", "truncate", "pop", "remove", "retain", "insert",
    "insert_str", "as_mut_vec", "len", "is_empty", "split_off", "clear", "drain", "replace_range", "into_boxed_str", "leak",
    "extend_from_within", "into_chars", "clone", "clone_from", "extend", "deref", "deref_mut", "as_ref", "as_mut", "borrow",
    "borrow_mut", "eq", "ne", "cmp", "partial_cmp", "lt", "le", "gt", "ge", "max", "min", "hash", "fmt", "index", "index_mut",
    "to_owned", "to_string", "add", "add_assign",
];
