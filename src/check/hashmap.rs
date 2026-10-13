// The hashed collections in body checking (W-STD-B; ty/hash.rs,
// runtime/hash.h, cgen/hash.rs): `HashMap` and `HashSet` constructors
// and methods, and the std hashers. Bounds are proven through the
// obligation queue as the std impl blocks state them (`K: Eq + Hash`,
// `S: BuildHasher`, `K: Borrow<Q>`), so selection decides.
//
// Rule zero: a method Rust declares on these types that lust has no
// port of rejects with L0640 naming it.
use super::*;
use crate::ty::hash::{HashTy, hash_parts, mk_hash};

/// The methods of `core::hash::Hasher` lust declares, in record order:
/// `finish`, `write`, then `write_<int>` for every integer type.
pub const HASHER_METHODS: [&str; 14] = [
    "finish",
    "write",
    "write_u8",
    "write_u16",
    "write_u32",
    "write_u64",
    "write_u128",
    "write_usize",
    "write_i8",
    "write_i16",
    "write_i32",
    "write_i64",
    "write_i128",
    "write_isize",
];

/// The argument of a Hasher write method: `Some(Some(int))` for
/// `write_<int>`, `Some(None)` for `write(&[u8])`, None otherwise.
pub fn hasher_write_arg(name: &str) -> Option<Option<IntTy>> {
    if name == "write" {
        return Some(None);
    }
    let t = name.strip_prefix("write_")?;
    IntTy::ALL.iter().copied().find(|i| i.name() == t).map(Some)
}

/// HashMap and HashSet methods Rust declares that lust does not port
/// yet: a call rejects with L0640 naming the method.
const DECLARED_ONLY: &[&str] = &[
    "iter",
    "iter_mut",
    "keys",
    "values",
    "values_mut",
    "into_keys",
    "into_values",
    "drain",
    "extract_if",
    "retain",
    "reserve",
    "try_reserve",
    "shrink_to_fit",
    "shrink_to",
    "get_key_value",
    "get_many_mut",
    "remove_entry",
    "hasher",
    "union",
    "intersection",
    "difference",
    "symmetric_difference",
    "is_subset",
    "is_superset",
    "is_disjoint",
    "replace",
    "take",
    "get_or_insert",
    "get_or_insert_with",
];

impl<'p, 'a> Ctx<'p, 'a> {
    /// Pushes `t: trait_def` (one-parameter traits) to the queue.
    fn require(&mut self, trait_def: DefId, t: Ty, span: Span) {
        let args = self.tys.intern_args(&[GenericArg::Ty(t)]);
        self.obl.push_trait_at(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }, span, 0);
    }

    /// `K: Borrow<Q>`.
    fn require_borrow(&mut self, k: Ty, q: Ty, span: Span) {
        let args = self.tys.intern_args(&[GenericArg::Ty(k), GenericArg::Ty(q)]);
        self.obl.push_trait_at(TraitRef { def: self.p.gx.lang.borrow, args, bindings: EMPTY_BINDINGS }, span, 0);
    }

    /// The impl-block bounds of the hashing methods: `K: Eq + Hash`,
    /// `S: BuildHasher`.
    fn require_hash_key(&mut self, k: Ty, s: Ty, span: Span) {
        let lang = self.p.gx.lang;
        self.require(lang.eq, k, span);
        self.require(lang.hash, k, span);
        self.require(lang.build_hasher, s, span);
        self.deferred_hash_key.push((k, k, span));
    }

    /// A lookup by `&Q`: `K: Borrow<Q>`, `Q: Hash + Eq`, `S: BuildHasher`.
    fn require_lookup(&mut self, k: Ty, q: Ty, s: Ty, span: Span) {
        let lang = self.p.gx.lang;
        self.require_borrow(k, q, span);
        self.require(lang.hash, q, span);
        self.require(lang.eq, q, span);
        self.require(lang.build_hasher, s, span);
        self.deferred_hash_key.push((k, q, span));
    }

    /// The finish-time test of one key (or lookup) type, with types as
    /// bound by then: the hash glue hashes, compares, and borrows by
    /// structure (derives, core impls), so a key that reaches a written
    /// `Hash` or a generic written `PartialEq` impl, or a lookup through
    /// a written `Borrow` impl, rejects with L0640. A key that does not
    /// implement the traits at all is the obligation queue's report.
    pub(super) fn check_hash_key(&mut self, k: Ty, q: Ty, span: Span) {
        let (k, q) = (self.deep(k), self.deep(q));
        let (k, q) = (self.normalize_here(k), self.normalize_here(q));
        let unknown = |cx: &Self, t: Ty| matches!(cx.kind(t), TyKind::Error | TyKind::Infer(_)) || cx.tys.flags(t).contains_param();
        if unknown(self, k) || unknown(self, q) {
            return;
        }
        let p = self.p;
        let glue = |cx: &Self, t: Ty| has_hash(p, &cx.tys, t) && has_eq(p, &cx.tys, t);
        if !(glue(self, q) || !crate::check::fmt::mentions_local_adt(&self.tys, q)) {
            let tn = self.tn(q);
            self.errs.push(Diag::new(
                "L0640",
                span,
                format!("a map or set key of type `{tn}` reaches a written `Hash` or `PartialEq` impl, which lust does not support yet"),
                "Derive Hash, PartialEq, and Eq on the key types instead.",
            ));
        } else if !self.builtin_borrow(k, q) {
            let (kn, qn) = (self.tn(k), self.tn(q));
            self.errs.push(Diag::new(
                "L0640",
                span,
                format!("a lookup of `{kn}` keys by `{qn}` goes through a written `Borrow` impl, which lust does not support yet"),
                "Look up by the key type itself.",
            ));
        }
    }

    /// True when `K: Borrow<Q>` holds by one of core's impls the hash
    /// glue implements (`borrow_expr` in cgen/hash.rs).
    fn builtin_borrow(&self, k: Ty, q: Ty) -> bool {
        if k == q {
            return true;
        }
        let tys = &self.tys;
        match tys.kind(k) {
            TyKind::Ref(_, _, e) => return e == q,
            TyKind::Array(e, _) => return matches!(tys.kind(q), TyKind::Slice(x) if x == e),
            _ => {}
        }
        if tys.is_string_ty(k) {
            return q == STR;
        }
        if let Some(e) = tys.vec_elem(k) {
            return matches!(tys.kind(q), TyKind::Slice(x) if x == e);
        }
        tys.smart_elem(k) == Some(q)
    }

    /// Methods on a HashMap, HashSet, or Entry receiver. None when the
    /// base is none of these, so other dispatch runs.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn hash_coll_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
    ) -> Option<Ty> {
        use Builtin as B;
        let (kind, targs) = hash_parts(&self.tys, base)?;
        if !matches!(kind, HashTy::HashMap | HashTy::HashSet | HashTy::Entry) {
            return None;
        }
        let n = self.p.interner.get(name);
        let (k, v) = (targs[0], if kind == HashTy::HashSet { UNIT } else { targs[1] });
        let s = *targs.last().unwrap_or(&UNIT);
        let lookup = |cx: &mut Self| {
            let q = cx.new_var(false);
            let r = cx.tys.mk_ref(false, q);
            (q, r)
        };
        let table = matches!(kind, HashTy::HashMap | HashTy::HashSet);
        let found: Option<(B, Autoref, Vec<Ty>, Ty, Option<Ty>)> = match (kind, n) {
            (_, "len") if table => Some((B::HashLen, Autoref::Ref, vec![], USIZE, None)),
            (_, "is_empty") if table => Some((B::HashIsEmpty, Autoref::Ref, vec![], BOOL, None)),
            (_, "clear") if table => Some((B::HashClear, Autoref::RefMut, vec![], UNIT, None)),
            (_, "capacity") if table => Some((B::HashCapacity, Autoref::Ref, vec![], USIZE, None)),
            (HashTy::HashMap, "insert") => {
                self.require_hash_key(k, s, name_span);
                let ov = self.tys.mk_option(v);
                Some((B::MapInsert, Autoref::RefMut, vec![k, v], ov, None))
            }
            (HashTy::HashMap, "get" | "get_mut" | "contains_key" | "remove") => {
                let (q, rq) = lookup(self);
                let (b, autoref, ret) = match n {
                    "get" => {
                        let r = self.tys.mk_ref(false, v);
                        (B::MapGet, Autoref::Ref, self.tys.mk_option(r))
                    }
                    "get_mut" => {
                        let r = self.tys.mk_ref(true, v);
                        (B::MapGetMut, Autoref::RefMut, self.tys.mk_option(r))
                    }
                    "contains_key" => (B::MapContainsKey, Autoref::Ref, BOOL),
                    _ => (B::MapRemove, Autoref::RefMut, self.tys.mk_option(v)),
                };
                Some((b, autoref, vec![rq], ret, Some(q)))
            }
            (HashTy::HashMap, "entry") => {
                self.require_hash_key(k, s, name_span);
                let en = mk_hash(&mut self.tys, HashTy::Entry, &[k, v]);
                Some((B::MapEntry, Autoref::RefMut, vec![k], en, None))
            }
            (HashTy::HashSet, "insert") => {
                self.require_hash_key(k, s, name_span);
                Some((B::SetInsert, Autoref::RefMut, vec![k], BOOL, None))
            }
            (HashTy::HashSet, "contains" | "remove" | "get") => {
                let (q, rq) = lookup(self);
                let (b, autoref, ret) = match n {
                    "contains" => (B::SetContains, Autoref::Ref, BOOL),
                    "remove" => (B::SetRemove, Autoref::RefMut, BOOL),
                    _ => {
                        let r = self.tys.mk_ref(false, k);
                        (B::SetGet, Autoref::Ref, self.tys.mk_option(r))
                    }
                };
                Some((b, autoref, vec![rq], ret, Some(q)))
            }
            (HashTy::Entry, "or_insert") => {
                let r = self.tys.mk_ref(true, v);
                Some((B::EntryOrInsert, Autoref::None, vec![v], r, None))
            }
            (HashTy::Entry, "or_default") => {
                self.require(self.p.gx.lang.default, v, name_span);
                let r = self.tys.mk_ref(true, v);
                Some((B::EntryOrDefault, Autoref::None, vec![], r, None))
            }
            (HashTy::Entry, "key") => {
                let r = self.tys.mk_ref(false, k);
                Some((B::EntryKey, Autoref::Ref, vec![], r, None))
            }
            _ => None,
        };
        let Some((b, autoref, params, ret, q)) = found else {
            for &a in args {
                self.expr(a, None);
            }
            let tn = self.tn(base);
            if DECLARED_ONLY.contains(&n) || matches!(n, "or_insert_with" | "or_insert_with_key" | "and_modify" | "insert_entry") {
                self.errs.push(Diag::new(
                    "L0640",
                    name_span,
                    format!("`{tn}::{n}` is not implemented in lust yet"),
                    "Rewrite this part with the supported subset.",
                ));
            } else {
                self.err("L0104", name_span, format!("no method `{n}` on type `{tn}`"), "Check the method name.");
            }
            return Some(ERROR);
        };
        if autoref != Autoref::None {
            self.check_packed_borrow(recv, name_span);
        }
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
        self.check_args(&params, args, name_span);
        if let Some(q) = q {
            let q = self.deep(q);
            self.require_lookup(k, q, s, name_span);
        }
        Some(ret)
    }

    /// The signature of a hash type constructor (`HashMap::new` and
    /// kin), from the path's written args or fresh ones, with the std
    /// impl blocks' constraints (`new` and `with_capacity` are on
    /// `S = RandomState`).
    pub(super) fn hash_ctor_sig(&mut self, b: Builtin, callee: ExprId, span: Span) -> Option<(Vec<Ty>, Ty)> {
        use Builtin as B;
        let segs = match self.p.ast.expr(callee) {
            Expr::Path(segs) if segs.len() >= 2 => segs.clone(),
            _ => return None,
        };
        let ty_seg = &segs[segs.len() - 2];
        let k = HashTy::by_name(self.p.interner.get(ty_seg.name))?;
        let written: Vec<Ty> = ty_seg.type_args().iter().map(|&t| self.resolve_written(t)).collect();
        let mut args: Vec<Ty> = (0..k.n_args()).map(|i| written.get(i).copied().unwrap_or_else(|| self.new_var(false))).collect();
        let rs = mk_hash(&mut self.tys, HashTy::RandomState, &[]);
        let fixed_rs = matches!(b, B::HashNew | B::HashWithCapacity) && matches!(k, HashTy::HashMap | HashTy::HashSet);
        if fixed_rs && let Some(last) = args.last_mut() {
            if !self.unify(*last, rs) {
                let tn = self.tn(*last);
                self.err(
                    "L0612",
                    span,
                    format!("`new` and `with_capacity` build a map with `RandomState`, not `{tn}`"),
                    "Use `with_hasher` for another hasher.",
                );
            }
            *last = rs;
        }
        let t = mk_hash(&mut self.tys, k, &args);
        let s = *args.last().unwrap_or(&UNIT);
        Some(match b {
            B::HashNew | B::HashDefault => {
                if b == B::HashDefault {
                    self.require(self.p.gx.lang.default, s, span);
                }
                (vec![], t)
            }
            B::HashWithCapacity => (vec![USIZE], t),
            B::HashWithHasher => (vec![s], t),
            B::HashWithCapacityAndHasher => (vec![USIZE, s], t),
            _ => return None,
        })
    }
}

/// True for the hash constructor builtins (`hash_ctor_sig`).
pub fn is_hash_ctor(b: Builtin) -> bool {
    matches!(
        b,
        Builtin::HashNew | Builtin::HashWithCapacity | Builtin::HashWithHasher | Builtin::HashWithCapacityAndHasher | Builtin::HashDefault
    )
}

/// The constructor builtin a hash type's associated fn names.
pub fn hash_ctor_builtin(k: HashTy, item: &str) -> Option<Builtin> {
    let table = matches!(k, HashTy::HashMap | HashTy::HashSet);
    Some(match item {
        "new" if table || k == HashTy::RandomState || k == HashTy::DefaultHasher => Builtin::HashNew,
        "with_capacity" if table => Builtin::HashWithCapacity,
        "with_hasher" if table => Builtin::HashWithHasher,
        "with_capacity_and_hasher" if table => Builtin::HashWithCapacityAndHasher,
        "default" if k != HashTy::Entry => Builtin::HashDefault,
        _ => return None,
    })
}

/// Builds the type of one hash struct at fresh args (a constructor
/// path without written args).
pub fn fresh_hash_ty(cx: &mut Ctx, k: HashTy) -> Ty {
    let args: Vec<Ty> = (0..k.n_args()).map(|_| cx.new_var(false)).collect();
    mk_hash(&mut cx.tys, k, &args)
}
