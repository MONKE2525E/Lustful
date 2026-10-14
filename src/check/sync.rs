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
}

impl SyncOp {
    /// One of each op, for the capabilities table.
    pub const ALL: [SyncOp; 22] = [
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
    Some(match (k.atomic_value(), g) {
        (Some(_), SyncGlue::Debug | SyncGlue::Default) => true,
        (None, _) => false,
    })
}

/// The sync type a written type path names: its full std path
/// (`std::sync::atomic::AtomicUsize`), or a bare name when `bare_ok`
/// (no user type has it; a module glob of the std module imports it,
/// which the resolver checked).
pub fn sync_type_named(interner: &Interner, segs: &[ast::PathSeg], bare_ok: bool) -> Option<SyncTy> {
    if segs.len() > 1 {
        let path: Vec<&str> = segs.iter().map(|s| interner.get(s.name)).collect();
        return SyncTy::by_path(&path);
    }
    let n = interner.get(segs.first()?.name);
    if !bare_ok {
        return None;
    }
    SyncTy::ALL.iter().copied().find(|k| k.name() == n)
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
        let p = self.p;
        let (&item, ty_path) = names.split_last()?;
        let k = if std_ty {
            let path: Vec<&str> = ty_path.iter().map(|n| self.name(*n)).collect();
            SyncTy::by_path(&path)?
        } else {
            let &[t] = ty_path else { return None };
            if p.type_names.contains_key(&t) {
                return None;
            }
            let n = self.name(t);
            SyncTy::ALL.iter().copied().find(|k| k.name() == n)?
        };
        let i = self.name(item).to_string();
        let op = match (k.atomic_value(), i.as_str()) {
            (Some(_), "new") => SyncOp::AtomicNew(k),
            (Some(_), "from") => SyncOp::AtomicFrom(k),
            (Some(_), "default") => SyncOp::AtomicDefault(k),
            _ => {
                self.err(
                    "L0640",
                    span,
                    format!("`{}::{i}` is not implemented in lust yet", k.name()),
                    "Lust supports `new`, `from`, and `default` on the atomics.",
                );
                return Some(None);
            }
        };
        Some(Some(Res::Builtin(Builtin::Sync(op))))
    }

    /// Parameter and return types of a `Builtin::Sync` associated or free
    /// fn call.
    pub(super) fn sync_call_sig(&mut self, op: SyncOp) -> (Vec<Ty>, Ty) {
        let ord = crate::check::generics::atomic_ordering_ty(&mut self.tys);
        match op {
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
