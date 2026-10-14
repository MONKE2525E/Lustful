// The `std::sync` and `std::thread` surface in body checking (W-THREADS,
// ARCH 7.3). The types are builtin Adts (ty/sync.rs); their associated
// fns, methods, and free fns type here as `Builtin::Sync` calls, and
// codegen emits them (cgen/sync.rs) over the runtime (runtime/sync.c).
//
// Every name here is std's exact stable surface. A method lust lacks on
// a known type rejects with L0640 (rule zero: never fall through to a
// user method of the same name on a std type).
use super::*;
use crate::ty::sync::{AtomicVal, SyncTy, atomic_of, sync_ty};

/// An atomic read-modify-write method (`fetch_add` and kin).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FetchOp {
    Add,
    Sub,
    And,
    Nand,
    Or,
    Xor,
    Max,
    Min,
}

/// One sync or thread builtin call (`Builtin::Sync`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SyncOp {
    /// `AtomicX::new(v)` (a `const fn`).
    AtomicNew(SyncTy),
    /// `AtomicX::from(v)` (not const).
    AtomicFrom(SyncTy),
    /// `AtomicX::default()`: the zero value.
    AtomicDefault(SyncTy),
    AtomicLoad,
    AtomicStore,
    AtomicSwap,
    AtomicCompareExchange,
    AtomicCompareExchangeWeak,
    AtomicFetch(FetchOp),
    /// `AtomicBool::fetch_not`.
    AtomicFetchNot,
    AtomicIntoInner,
    AtomicGetMut,
    /// `atomic::fence(order)`.
    Fence,
    /// `atomic::compiler_fence(order)`.
    CompilerFence,
    /// `hint::spin_loop()`.
    SpinLoop,
    /// `Arc::new(v)`.
    ArcNew,
    ArcStrongCount,
    ArcWeakCount,
    ArcPtrEq,
    ArcDowngrade,
    ArcGetMut,
    ArcMakeMut,
    ArcTryUnwrap,
    ArcIntoInner,
    ArcUnwrapOrClone,
    /// `sync::Weak::new()`.
    ArcWeakNew,
    ArcWeakUpgrade,
    ArcWeakStrongCount,
    ArcWeakWeakCount,
    ArcWeakPtrEq,
}

impl SyncOp {
    /// One of each op, for the capabilities table.
    pub const ALL: [SyncOp; 37] = [
        SyncOp::AtomicNew(SyncTy::AtomicUsize),
        SyncOp::AtomicFrom(SyncTy::AtomicUsize),
        SyncOp::AtomicDefault(SyncTy::AtomicUsize),
        SyncOp::AtomicLoad,
        SyncOp::AtomicStore,
        SyncOp::AtomicSwap,
        SyncOp::AtomicCompareExchange,
        SyncOp::AtomicCompareExchangeWeak,
        SyncOp::AtomicFetch(FetchOp::Add),
        SyncOp::AtomicFetch(FetchOp::Sub),
        SyncOp::AtomicFetch(FetchOp::And),
        SyncOp::AtomicFetch(FetchOp::Nand),
        SyncOp::AtomicFetch(FetchOp::Or),
        SyncOp::AtomicFetch(FetchOp::Xor),
        SyncOp::AtomicFetch(FetchOp::Max),
        SyncOp::AtomicFetch(FetchOp::Min),
        SyncOp::AtomicFetchNot,
        SyncOp::AtomicIntoInner,
        SyncOp::AtomicGetMut,
        SyncOp::Fence,
        SyncOp::CompilerFence,
        SyncOp::SpinLoop,
        SyncOp::ArcNew,
        SyncOp::ArcStrongCount,
        SyncOp::ArcWeakCount,
        SyncOp::ArcPtrEq,
        SyncOp::ArcDowngrade,
        SyncOp::ArcGetMut,
        SyncOp::ArcMakeMut,
        SyncOp::ArcTryUnwrap,
        SyncOp::ArcIntoInner,
        SyncOp::ArcUnwrapOrClone,
        SyncOp::ArcWeakNew,
        SyncOp::ArcWeakUpgrade,
        SyncOp::ArcWeakStrongCount,
        SyncOp::ArcWeakWeakCount,
        SyncOp::ArcWeakPtrEq,
    ];

    /// (types, names, how it is called) for `lust capabilities`.
    pub fn info(self) -> (&'static [&'static str], &'static [&'static str], u8) {
        const ATOMICS: &[&str] = &["std::sync::atomic::Atomic{Bool,I8,U8,I16,U16,I32,U32,I64,U64,Isize,Usize}"];
        const INTS: &[&str] = &["std::sync::atomic::Atomic{I8,U8,I16,U16,I32,U32,I64,U64,Isize,Usize}"];
        let (m, a, f) = (0u8, 1u8, 2u8);
        match self {
            SyncOp::AtomicNew(_) => (ATOMICS, &["new"], a),
            SyncOp::AtomicFrom(_) => (ATOMICS, &["from"], a),
            SyncOp::AtomicDefault(_) => (ATOMICS, &["default"], a),
            SyncOp::AtomicLoad => (ATOMICS, &["load"], m),
            SyncOp::AtomicStore => (ATOMICS, &["store"], m),
            SyncOp::AtomicSwap => (ATOMICS, &["swap"], m),
            SyncOp::AtomicCompareExchange => (ATOMICS, &["compare_exchange"], m),
            SyncOp::AtomicCompareExchangeWeak => (ATOMICS, &["compare_exchange_weak"], m),
            SyncOp::AtomicFetch(FetchOp::Add) => (INTS, &["fetch_add"], m),
            SyncOp::AtomicFetch(FetchOp::Sub) => (INTS, &["fetch_sub"], m),
            SyncOp::AtomicFetch(FetchOp::And) => (ATOMICS, &["fetch_and"], m),
            SyncOp::AtomicFetch(FetchOp::Nand) => (ATOMICS, &["fetch_nand"], m),
            SyncOp::AtomicFetch(FetchOp::Or) => (ATOMICS, &["fetch_or"], m),
            SyncOp::AtomicFetch(FetchOp::Xor) => (ATOMICS, &["fetch_xor"], m),
            SyncOp::AtomicFetch(FetchOp::Max) => (INTS, &["fetch_max"], m),
            SyncOp::AtomicFetch(FetchOp::Min) => (INTS, &["fetch_min"], m),
            SyncOp::AtomicFetchNot => (&["std::sync::atomic::AtomicBool"], &["fetch_not"], m),
            SyncOp::AtomicIntoInner => (ATOMICS, &["into_inner"], m),
            SyncOp::AtomicGetMut => (ATOMICS, &["get_mut"], m),
            SyncOp::Fence => (&["std::sync::atomic"], &["fence"], f),
            SyncOp::CompilerFence => (&["std::sync::atomic"], &["compiler_fence"], f),
            SyncOp::SpinLoop => (&["std::hint"], &["spin_loop"], f),
            SyncOp::ArcNew => (&["std::sync::Arc<T>"], &["new"], a),
            SyncOp::ArcStrongCount => (&["std::sync::Arc<T>"], &["strong_count"], a),
            SyncOp::ArcWeakCount => (&["std::sync::Arc<T>"], &["weak_count"], a),
            SyncOp::ArcPtrEq => (&["std::sync::Arc<T>"], &["ptr_eq"], a),
            SyncOp::ArcDowngrade => (&["std::sync::Arc<T>"], &["downgrade"], a),
            SyncOp::ArcGetMut => (&["std::sync::Arc<T>"], &["get_mut"], a),
            SyncOp::ArcMakeMut => (&["std::sync::Arc<T>"], &["make_mut"], a),
            SyncOp::ArcTryUnwrap => (&["std::sync::Arc<T>"], &["try_unwrap"], a),
            SyncOp::ArcIntoInner => (&["std::sync::Arc<T>"], &["into_inner"], a),
            SyncOp::ArcUnwrapOrClone => (&["std::sync::Arc<T>"], &["unwrap_or_clone"], a),
            SyncOp::ArcWeakNew => (&["std::sync::Weak<T>"], &["new"], a),
            SyncOp::ArcWeakUpgrade => (&["std::sync::Weak<T>"], &["upgrade"], m),
            SyncOp::ArcWeakStrongCount => (&["std::sync::Weak<T>"], &["strong_count"], m),
            SyncOp::ArcWeakWeakCount => (&["std::sync::Weak<T>"], &["weak_count"], m),
            SyncOp::ArcWeakPtrEq => (&["std::sync::Weak<T>"], &["ptr_eq"], m),
        }
    }
}

/// A std trait a builtin answers by structure (the collect glue walks).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SyncGlue {
    Debug,
    Default,
}

/// Whether a sync type has the std impl of `g` (None when `t` is not a
/// sync type). Every atomic is `Debug` and `Default` (and not `Clone`,
/// `PartialEq`, or `Hash`, which the walks answer by default).
pub fn sync_glue(tys: &impl TyIntern, t: Ty, g: SyncGlue) -> Option<bool> {
    let k = crate::ty::sync::sync_kind(tys, t)?;
    // `Arc` and `sync::Weak` answer through the smart-pointer and weak
    // paths of the walks, like `Rc` and `rc::Weak`.
    k.atomic_value()?;
    Some(matches!(g, SyncGlue::Debug | SyncGlue::Default))
}

/// The sync type a written type path names: its full std path
/// (`std::sync::atomic::AtomicUsize`). A bare name never reaches check:
/// the resolver rewrites an imported one (a `use`, a fn-body glob, or a
/// module glob) to its full path, and one with no import is L0102.
pub fn sync_type_named(interner: &Interner, segs: &[ast::PathSeg]) -> Option<SyncTy> {
    if segs.len() < 2 {
        return None;
    }
    let path: Vec<&str> = segs.iter().map(|s| interner.get(s.name)).collect();
    SyncTy::by_path(&path)
}

/// Rejects a type argument lust cannot give a sync type yet: an
/// unsized `T` in `Arc<T>` or `Weak<T>` (`Arc<str>`, `Arc<[T]>`,
/// `Arc<dyn Trait>`), as for `Rc`.
pub fn check_sync_arg(tys: &impl TyIntern, k: SyncTy, e: Ty, span: Span) -> Result<(), Diag> {
    if matches!(k, SyncTy::Arc | SyncTy::ArcWeak) && matches!(tys.kind(e), TyKind::Slice(_) | TyKind::Str | TyKind::Dyn(..)) {
        return Err(crate::diag::not_yet("L0641", span, &format!("an {} of an unsized type", k.name())));
    }
    Ok(())
}

/// The free fn a std path names, if it is one of the sync free fns.
pub fn sync_free_fn(path: &[&str]) -> Option<SyncOp> {
    match path {
        ["std" | "core", "sync", "atomic", "fence"] => Some(SyncOp::Fence),
        ["std" | "core", "sync", "atomic", "compiler_fence"] => Some(SyncOp::CompilerFence),
        ["std" | "core", "hint", "spin_loop"] => Some(SyncOp::SpinLoop),
        _ => None,
    }
}

impl<'p, 'a> Ctx<'p, 'a> {
    /// The associated fns of the sync types (`AtomicUsize::new`). None
    /// when the path's type is none of these (the caller goes on); a
    /// known type with an item lust lacks rejects here. A user type of
    /// the same name wins, except on a std path (`std_ty`).
    pub(super) fn sync_assoc(&mut self, names: &[Sym], std_ty: bool, span: Span) -> Option<Option<Res>> {
        let (&item, ty_path) = names.split_last()?;
        if !std_ty {
            return None;
        }
        let path: Vec<&str> = ty_path.iter().map(|n| self.name(*n)).collect();
        let k = SyncTy::by_path(&path)?;
        let i = self.name(item).to_string();
        let op = match (k, k.atomic_value(), i.as_str()) {
            (_, Some(_), "new") => SyncOp::AtomicNew(k),
            (_, Some(_), "from") => SyncOp::AtomicFrom(k),
            (_, Some(_), "default") => SyncOp::AtomicDefault(k),
            (SyncTy::Arc | SyncTy::ArcWeak, _, "clone") => return Some(Some(Res::Builtin(Builtin::Clone))),
            (SyncTy::Arc, _, "new") => SyncOp::ArcNew,
            (SyncTy::Arc, _, "strong_count") => SyncOp::ArcStrongCount,
            (SyncTy::Arc, _, "weak_count") => SyncOp::ArcWeakCount,
            (SyncTy::Arc, _, "ptr_eq") => SyncOp::ArcPtrEq,
            (SyncTy::Arc, _, "downgrade") => SyncOp::ArcDowngrade,
            (SyncTy::Arc, _, "get_mut") => SyncOp::ArcGetMut,
            (SyncTy::Arc, _, "make_mut") => SyncOp::ArcMakeMut,
            (SyncTy::Arc, _, "try_unwrap") => SyncOp::ArcTryUnwrap,
            (SyncTy::Arc, _, "into_inner") => SyncOp::ArcIntoInner,
            (SyncTy::Arc, _, "unwrap_or_clone") => SyncOp::ArcUnwrapOrClone,
            (SyncTy::ArcWeak, _, "new") => SyncOp::ArcWeakNew,
            // `sync::Weak`'s methods called by path (`Weak::upgrade(&w)`).
            (SyncTy::ArcWeak, _, "upgrade") => SyncOp::ArcWeakUpgrade,
            (SyncTy::ArcWeak, _, "strong_count") => SyncOp::ArcWeakStrongCount,
            (SyncTy::ArcWeak, _, "weak_count") => SyncOp::ArcWeakWeakCount,
            (SyncTy::ArcWeak, _, "ptr_eq") => SyncOp::ArcWeakPtrEq,
            _ => {
                self.err(
                    "L0640",
                    span,
                    format!("`{}::{i}` is not implemented in lust yet", k.name()),
                    "Lust supports `new`, `from`, and `default` on the atomics, and `Arc`'s and `Weak`'s counting fns.",
                );
                return Some(None);
            }
        };
        Some(Some(Res::Builtin(Builtin::Sync(op))))
    }

    /// Parameter and return types of a `Builtin::Sync` associated or free
    /// fn call.
    pub(super) fn sync_call_sig(&mut self, op: SyncOp, callee: ExprId, span: Span) -> (Vec<Ty>, Ty) {
        let ord = crate::check::generics::atomic_ordering_ty(&mut self.tys);
        // `Arc<T>` and `sync::Weak<T>` ops: the element type comes from
        // turbofish on the type segment when written (`Arc::<u8>::new`).
        let written = match self.p.ast.expr(callee) {
            Expr::Path(segs) if segs.len() >= 2 => segs[segs.len() - 2].type_args(),
            _ => Vec::new(),
        };
        let elem = match written.first() {
            Some(&g) => self.resolve_written(g),
            None => self.new_var(false),
        };
        let arc = sync_ty(&mut self.tys, SyncTy::Arc, &[elem]);
        let weak = sync_ty(&mut self.tys, SyncTy::ArcWeak, &[elem]);
        let arc_ref = self.tys.mk_ref(false, arc);
        let arc_mut = self.tys.mk_ref(true, arc);
        let weak_ref = self.tys.mk_ref(false, weak);
        match op {
            SyncOp::ArcNew => (vec![elem], arc),
            SyncOp::ArcStrongCount | SyncOp::ArcWeakCount => (vec![arc_ref], USIZE),
            SyncOp::ArcPtrEq => (vec![arc_ref, arc_ref], BOOL),
            SyncOp::ArcDowngrade => (vec![arc_ref], weak),
            SyncOp::ArcGetMut => {
                let r = self.tys.mk_ref(true, elem);
                (vec![arc_mut], self.tys.mk_option(r))
            }
            SyncOp::ArcMakeMut => {
                self.deferred_clone.push((elem, span));
                (vec![arc_mut], self.tys.mk_ref(true, elem))
            }
            SyncOp::ArcTryUnwrap => (vec![arc], self.tys.mk_result(elem, arc)),
            SyncOp::ArcIntoInner => (vec![arc], self.tys.mk_option(elem)),
            SyncOp::ArcUnwrapOrClone => {
                self.deferred_clone.push((elem, span));
                (vec![arc], elem)
            }
            SyncOp::ArcWeakNew => (vec![], weak),
            SyncOp::ArcWeakUpgrade => (vec![weak_ref], self.tys.mk_option(arc)),
            SyncOp::ArcWeakStrongCount | SyncOp::ArcWeakWeakCount => (vec![weak_ref], USIZE),
            SyncOp::ArcWeakPtrEq => (vec![weak_ref, weak_ref], BOOL),
            SyncOp::AtomicNew(k) | SyncOp::AtomicFrom(k) => {
                let v = k.atomic_value().expect("an atomic").ty();
                (vec![v], sync_ty(&mut self.tys, k, &[]))
            }
            SyncOp::AtomicDefault(k) => (vec![], sync_ty(&mut self.tys, k, &[])),
            SyncOp::Fence | SyncOp::CompilerFence => (vec![ord], UNIT),
            SyncOp::SpinLoop => (vec![], UNIT),
            _ => unreachable!("sync methods type in sync_method"),
        }
    }

    /// Methods on the sync types (after autoderef). None when the
    /// receiver is none of these.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn sync_method(&mut self, e: ExprId, recv: ExprId, base: Ty, derefs: u8, name: Sym, span: Span, args: &[ExprId]) -> Option<Ty> {
        if let Some(el) = self.tys.arc_weak_elem(base) {
            let w_ref = self.tys.mk_ref(false, base);
            let (op, params, ret) = match self.name(name) {
                "upgrade" => {
                    let arc = sync_ty(&mut self.tys, SyncTy::Arc, &[el]);
                    (SyncOp::ArcWeakUpgrade, vec![], self.tys.mk_option(arc))
                }
                "strong_count" => (SyncOp::ArcWeakStrongCount, vec![], USIZE),
                "weak_count" => (SyncOp::ArcWeakWeakCount, vec![], USIZE),
                "ptr_eq" => (SyncOp::ArcWeakPtrEq, vec![w_ref], BOOL),
                "as_ptr" | "into_raw" => {
                    let n = self.name(name).to_string();
                    self.err("L0640", span, format!("`Weak::{n}` is not implemented in lust yet"), "Use `upgrade` and the counts.");
                    return Some(self.iter_bail(args));
                }
                _ => return None,
            };
            self.check_packed_borrow(recv, span);
            self.set_res(e, Res::BuiltinMethod { b: Builtin::Sync(op), derefs, autoref: Autoref::Ref });
            self.check_args(&params, args, span);
            return Some(ret);
        }
        let (k, v) = atomic_of(&self.tys, base)?;
        let n = self.name(name).to_string();
        let vt = v.ty();
        let ord = crate::check::generics::atomic_ordering_ty(&mut self.tys);
        let is_int = matches!(v, AtomicVal::Int(_));
        let fetch = |f| (SyncOp::AtomicFetch(f), Autoref::Ref, vec![vt, ord], vt);
        let (op, autoref, params, ret) = match n.as_str() {
            "load" => (SyncOp::AtomicLoad, Autoref::Ref, vec![ord], vt),
            "store" => (SyncOp::AtomicStore, Autoref::Ref, vec![vt, ord], UNIT),
            "swap" => (SyncOp::AtomicSwap, Autoref::Ref, vec![vt, ord], vt),
            "compare_exchange" | "compare_exchange_weak" => {
                let op = if n == "compare_exchange" { SyncOp::AtomicCompareExchange } else { SyncOp::AtomicCompareExchangeWeak };
                let res = self.tys.mk_result(vt, vt);
                (op, Autoref::Ref, vec![vt, vt, ord, ord], res)
            }
            "fetch_add" if is_int => fetch(FetchOp::Add),
            "fetch_sub" if is_int => fetch(FetchOp::Sub),
            "fetch_max" if is_int => fetch(FetchOp::Max),
            "fetch_min" if is_int => fetch(FetchOp::Min),
            "fetch_and" => fetch(FetchOp::And),
            "fetch_nand" => fetch(FetchOp::Nand),
            "fetch_or" => fetch(FetchOp::Or),
            "fetch_xor" => fetch(FetchOp::Xor),
            "fetch_not" if !is_int => (SyncOp::AtomicFetchNot, Autoref::Ref, vec![ord], vt),
            "into_inner" => (SyncOp::AtomicIntoInner, Autoref::None, vec![], vt),
            "get_mut" => {
                let r = self.tys.mk_ref(true, vt);
                (SyncOp::AtomicGetMut, Autoref::RefMut, vec![], r)
            }
            // Stable std methods lust does not have yet.
            "fetch_update" | "as_ptr" | "compare_and_swap" | "from_ptr" | "update" | "try_update" => {
                self.err("L0640", span, format!("`{}::{n}` is not implemented in lust yet", k.name()), "Use `load`, `store`, or `compare_exchange` in a loop.");
                return Some(self.iter_bail(args));
            }
            _ => return None,
        };
        if autoref != Autoref::None {
            self.check_packed_borrow(recv, span);
        }
        self.set_res(e, Res::BuiltinMethod { b: Builtin::Sync(op), derefs, autoref });
        self.check_args(&params, args, span);
        self.lint_atomic_ordering(op, args);
        Some(ret)
    }

    /// The `atomic::Ordering` variant an argument names directly
    /// (`Ordering::Relaxed`, its full path, or an imported variant), as
    /// its discriminant: 0 Relaxed, 1 Release, 2 Acquire, 3 AcqRel,
    /// 4 SeqCst. None for any other expression (a variable, a const).
    fn literal_atomic_ordering(&self, arg: ExprId) -> Option<u32> {
        if !matches!(self.p.ast.expr(arg), Expr::Path(_)) {
            return None;
        }
        let Res::Variant(a, v) = self.out.expr_res[self.ei(arg)] else { return None };
        (self.p.tys.local_adt_of(crate::check::generics::atomic_ordering_def()) == Some(a)).then_some(v)
    }

    /// rustc's deny-by-default `invalid_atomic_ordering` lint: a load
    /// with `Release` or `AcqRel`, a store with `Acquire` or `AcqRel`, a
    /// fence with `Relaxed`, and a compare-exchange failure ordering of
    /// `Release` or `AcqRel`, each written as the variant itself, do
    /// not compile. Through a variable they panic at run time instead.
    pub(super) fn lint_atomic_ordering(&mut self, op: SyncOp, args: &[ExprId]) {
        let (at, bad, msg): (usize, &[u32], &str) = match op {
            SyncOp::AtomicLoad => (0, &[1, 3], "atomic loads cannot have `Release` or `AcqRel` ordering"),
            SyncOp::AtomicStore => (1, &[2, 3], "atomic stores cannot have `Acquire` or `AcqRel` ordering"),
            SyncOp::AtomicCompareExchange | SyncOp::AtomicCompareExchangeWeak => {
                (3, &[1, 3], "`compare_exchange`'s failure ordering may not be `Release` or `AcqRel`")
            }
            SyncOp::Fence | SyncOp::CompilerFence => (0, &[0], "memory fences cannot have `Relaxed` ordering"),
            _ => return,
        };
        if let Some(&arg) = args.get(at)
            && let Some(v) = self.literal_atomic_ordering(arg)
            && bad.contains(&v)
        {
            let span = self.span(arg);
            self.err("L0542", span, msg, "Use an ordering this operation allows (rustc `invalid_atomic_ordering`).");
        }
    }
}

/// The std impls of the sync types, as synthetic impl records for trait
/// selection (`T: Default` bounds, derives over sync fields): every
/// atomic is `Debug`, `Default`, and `From<V>` of its value.
pub fn add_sync_impls(p: &mut crate::check::collect::Program, ordinal: &mut u32, span: Span) {
    use crate::check::generics::insert_synthetic;
    use crate::traits::index::Synthetic;
    let lang = p.gx.lang;
    let g0 = Generics::default();
    // `Arc<T>` as alloc writes it, like `Rc<T>`: Clone with no bound on
    // `T`, the value traits through `T`, `Deref<Target = T>`, `AsRef<T>`,
    // `Borrow<T>`. `sync::Weak<T>`: Clone, Debug, Default.
    let p0 = p.tys.intern(TyKind::Param(crate::ty::ParamId(0)));
    let one = Generics { parent: None, params: vec![ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span }], predicates: Vec::new() };
    let arc = sync_ty(&mut p.tys, SyncTy::Arc, &[p0]);
    let weak = sync_ty(&mut p.tys, SyncTy::ArcWeak, &[p0]);
    let bound = |p: &mut crate::check::collect::Program, tr: DefId| -> Generics {
        let mut a = vec![GenericArg::Ty(p0)];
        if tr == lang.partial_eq || tr == lang.partial_ord {
            a.push(GenericArg::Ty(p0));
        }
        let args = p.tys.intern_args(&a);
        let mut g = one.clone();
        g.predicates = vec![Predicate::Trait(Binder::plain(TraitRef { def: tr, args, bindings: EMPTY_BINDINGS }))];
        g
    };
    insert_synthetic(p, ordinal, lang.clone, arc, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    for tr in [lang.debug, lang.display, lang.eq, lang.hash, lang.default, lang.partial_eq, lang.partial_ord, lang.ord] {
        let g = bound(p, tr);
        let rhs: Vec<Ty> = if tr == lang.partial_eq || tr == lang.partial_ord { vec![arc] } else { Vec::new() };
        insert_synthetic(p, ordinal, tr, arc, &rhs, g, Vec::new(), Synthetic::Lang, false, span);
    }
    insert_synthetic(p, ordinal, lang.deref, arc, &[], one.clone(), vec![(lang.assoc_target, p0)], Synthetic::Lang, false, span);
    for tr in [lang.as_ref, lang.borrow] {
        insert_synthetic(p, ordinal, tr, arc, &[p0], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    for tr in [lang.clone, lang.debug, lang.default] {
        insert_synthetic(p, ordinal, tr, weak, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    for k in SyncTy::ALL {
        let Some(v) = k.atomic_value() else { continue };
        let t = sync_ty(&mut p.tys, k, &[]);
        for tr in [lang.debug, lang.default] {
            insert_synthetic(p, ordinal, tr, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        insert_synthetic(p, ordinal, lang.from, t, &[v.ty()], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
}

/// The auto trait facts (`Send`, `Sync`, `Unpin`) of the std builtin
/// types, as std's own impls give them (ARCH 2.7): Some(answer) for a
/// builtin with a fixed rule, None for a type the caller walks by
/// structure (`Vec`, `Option`, `Box`, `Result`, user Adts). Every
/// builtin is `Unpin`. Checked against rustc 1.99 by the probes in
/// tests/pass and tests/fail (`send_sync_*`).
pub fn builtin_auto(
    p: &crate::check::collect::Program,
    tys: &mut impl TyIntern,
    env: &[Predicate],
    trait_def: DefId,
    t: Ty,
    seen: &mut Vec<Ty>,
) -> Option<Option<bool>> {
    use crate::check::collect::auto_structural;
    use crate::ty::BuiltinTy as B;
    let lang = &p.gx.lang;
    let b = tys.builtin_of(t)?;
    if trait_def == lang.unpin && !matches!(b, B::Vec | B::Option | B::Boxed | B::Result) {
        return Some(Some(true));
    }
    let send = trait_def == lang.send;
    let elem = tys.adt_first_ty_arg(t);
    let each = |tys: &mut _, parts: Vec<Ty>, seen: &mut Vec<Ty>| -> Option<bool> {
        seen.push(t);
        let mut unknown = false;
        for (part, tr) in parts.into_iter().map(|x| (x, trait_def)) {
            match auto_structural(p, tys, env, tr, part, seen) {
                Some(false) => return Some(false),
                None => unknown = true,
                Some(true) => {}
            }
        }
        if unknown { None } else { Some(true) }
    };
    Some(match b {
        B::String | B::Chars | B::ExitCode => Some(true),
        // `env::Args`, `Rc`, `rc::Weak`, the `RefCell` guards, and the
        // `fmt` types are neither `Send` nor `Sync`.
        B::Args | B::Rc | B::Weak | B::RefGuard | B::RefMutGuard | B::Fmt(_) => Some(false),
        // `Cell<T>` and `RefCell<T>` are `Send` when `T` is; never `Sync`.
        B::Cell | B::RefCell => {
            if send {
                each(tys, elem.into_iter().collect(), seen)
            } else {
                Some(false)
            }
        }
        // `Arc<T>` and `sync::Weak<T>` are `Send` and `Sync` exactly when
        // `T` is both (std's unsafe impls).
        B::Sync(SyncTy::Arc | SyncTy::ArcWeak) => {
            let Some(e) = elem else { return Some(None) };
            seen.push(t);
            let mut unknown = false;
            for tr in [lang.send, lang.sync] {
                match auto_structural(p, tys, env, tr, e, seen) {
                    Some(false) => return Some(Some(false)),
                    None => unknown = true,
                    Some(true) => {}
                }
            }
            if unknown { None } else { Some(true) }
        }
        B::Sync(k) => match k.atomic_value() {
            Some(_) => Some(true),
            None => None,
        },
        B::Iter(k) => {
            let Some((_, args)) = crate::ty::iter::iter_parts(tys, t) else { return Some(None) };
            let mut parts = Vec::new();
            for f in k.fields() {
                use crate::ty::iter::Field as F;
                match *f {
                    F::Arg(i) | F::OptArg(i) | F::VecArg(i) => parts.push(args[i as usize]),
                    F::Usize | F::Bool => {}
                    F::SliceRef(i, m) => {
                        let sl = tys.intern(TyKind::Slice(args[i as usize]));
                        parts.push(tys.mk_ref(m, sl));
                    }
                    // The peeked item: not modelled, so not proven.
                    F::PeekSlot(_) => return Some(None),
                }
            }
            each(tys, parts, seen)
        }
        B::Vec | B::Option | B::Boxed | B::Result => return None,
    })
}
