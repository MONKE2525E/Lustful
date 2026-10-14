// Builtin iterator types (W-STD-A phase 3; docs/ARCH.md 3.4 and 4.3).
//
// ARCH puts the std iterator structs in `library/core` source. That
// needs lifetime params on structs (`slice::Iter<'a, T>`) and closures
// stored in Adts, which the checker does not have yet, so until then
// each std iterator struct is a builtin Adt with its own def. A value
// is laid out as a tuple of the fields real std declares, in
// declaration order, so drop order matches Rust. Check types the
// methods (`check/iter.rs`), borrowck sees each method as one opaque
// builtin call, and codegen first expands the calls into plain IR
// with Rust 1.99's `next` semantics (`lower/iter.rs`).
//
// Type args are the std struct's own args, plus the item type last
// for the adapters whose item a closure returns (`Map`, `FilterMap`):
// item types then never need a closure signature lookup. `str::Chars`
// predates this family and stays its own builtin (`BuiltinTy::Chars`),
// but it is an iterator source here too.
use super::*;

/// One std iterator struct lust knows by def.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IterKind {
    /// `core::slice::Iter<T>`: args `[T]`, item `&T`.
    SliceIter,
    /// `core::slice::IterMut<T>`: args `[T]`, item `&mut T`.
    SliceIterMut,
    /// `alloc::vec::IntoIter<T>`: args `[T]`, item `T`.
    VecIntoIter,
    /// `core::ops::Range<T>` over an integer: args `[T]`, item `T`.
    Range,
    /// `core::ops::RangeInclusive<T>` over an integer: args `[T]`.
    RangeInclusive,
    /// `Map<I, F>`: args `[I, F, B]` with `B` the closure output.
    Map,
    /// `Filter<I, P>`: args `[I, P]`.
    Filter,
    /// `Enumerate<I>`: args `[I]`, item `(usize, I::Item)`.
    Enumerate,
    /// `Rev<I>`: args `[I]`.
    Rev,
    /// `Take<I>`: args `[I]`.
    Take,
    /// `Skip<I>`: args `[I]`.
    Skip,
    /// `Chain<A, B>`: args `[A, B]`.
    Chain,
    /// `Zip<A, B>`: args `[A, B]`, item `(A::Item, B::Item)`.
    Zip,
    /// `Copied<I>`: args `[I, T]` with `T` the item (`I::Item = &T`).
    Copied,
    /// `Cloned<I>`: args `[I, T]` with `T` the item (`I::Item = &T`).
    Cloned,
    /// `FilterMap<I, F>`: args `[I, F, B]` with `F` returning `Option<B>`.
    FilterMap,
    /// `TakeWhile<I, P>`: args `[I, P]`.
    TakeWhile,
    /// `SkipWhile<I, P>`: args `[I, P]`.
    SkipWhile,
    /// `StepBy<I>`: args `[I]`.
    StepBy,
    /// `Peekable<I>`: args `[I]`.
    Peekable,
    /// `Inspect<I, F>`: args `[I, F]`.
    Inspect,
    /// `std::sync::mpsc::Iter<'a, T>` (`rx.iter()`, `for x in &rx`):
    /// args `[T]`, item `T`; blocks in `recv` (W-THREADS).
    RecvIter,
    /// `std::sync::mpsc::TryIter<'a, T>` (`rx.try_iter()`): args `[T]`.
    RecvTryIter,
    /// `std::sync::mpsc::IntoIter<T>` (`for x in rx`): args `[T]`.
    RecvIntoIter,
    // The hashed-collection iterators (W-STD-B; cgen/hash.rs). Map
    // kinds take args `[K, V]`, set kinds `[T]`. Their state is the
    // hash core's raw iterator (`fields` is empty: `next` and the
    // length are builtin calls).
    /// `hash_map::Iter<K, V>`: item `(&K, &V)`.
    MapIter,
    /// `hash_map::IterMut<K, V>`: item `(&K, &mut V)`.
    MapIterMut,
    /// `hash_map::Keys<K, V>`: item `&K`.
    MapKeys,
    /// `hash_map::Values<K, V>`: item `&V`.
    MapValues,
    /// `hash_map::ValuesMut<K, V>`: item `&mut V`.
    MapValuesMut,
    /// `hash_map::IntoIter<K, V>`: item `(K, V)`.
    MapIntoIter,
    /// `hash_map::IntoKeys<K, V>`: item `K`.
    MapIntoKeys,
    /// `hash_map::IntoValues<K, V>`: item `V`.
    MapIntoValues,
    /// `hash_set::Iter<T>`: item `&T`.
    SetIter,
    /// `hash_set::IntoIter<T>`: item `T`.
    SetIntoIter,
    /// `array::IntoIter<T, N>` (W-STD-B): args `[T, A]` with `A = [T;
    /// N]`, item `T`; Copy elements only (check/iter.rs), so no element
    /// of the stored array needs a drop.
    ArrayIntoIter,
    /// `iter::RepeatN<T>` (W-STD-B): args `[T]`, item `T`; Copy `T` only.
    RepeatN,
    /// Any other iterator, reached through its own `Iterator::next`
    /// (W-STD-B, check/iter.rs `by_next_item`): args `[I, Item]`, the
    /// iterator value itself as the one field. A user type with an
    /// `Iterator` impl, or in a template a type parameter or projection
    /// with an `Iterator` bound; adapters and consumers wrap it once.
    /// Never named in source: messages print `I`.
    ByNext,
    /// `core::slice::Windows<T>` (W-STD-B): args `[T]`, item `&[T]`;
    /// (the slice left, the window size).
    Windows,
}

/// One stored field of a builtin iterator, over the type's args.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Field {
    /// The type arg at this index.
    Arg(u8),
    /// `usize`.
    Usize,
    /// `bool`.
    Bool,
    /// `Option<arg>`.
    OptArg(u8),
    /// `&[arg]`, or `&mut [arg]` when the flag is set.
    SliceRef(u8, bool),
    /// `Vec<arg>`.
    VecArg(u8),
    /// `Option<Option<item of arg>>`: the peeked slot of `Peekable`.
    PeekSlot(u8),
    /// `&Receiver<arg>`, or `Receiver<arg>` by value when the flag is
    /// set (the mpsc iterators, W-THREADS).
    Recv(u8, bool),
}

impl IterKind {
    pub const ALL: [IterKind; 38] = [
        IterKind::SliceIter,
        IterKind::SliceIterMut,
        IterKind::VecIntoIter,
        IterKind::Range,
        IterKind::RangeInclusive,
        IterKind::Map,
        IterKind::Filter,
        IterKind::Enumerate,
        IterKind::Rev,
        IterKind::Take,
        IterKind::Skip,
        IterKind::Chain,
        IterKind::Zip,
        IterKind::Copied,
        IterKind::Cloned,
        IterKind::FilterMap,
        IterKind::TakeWhile,
        IterKind::SkipWhile,
        IterKind::StepBy,
        IterKind::Peekable,
        IterKind::Inspect,
        IterKind::RecvIter,
        IterKind::RecvTryIter,
        IterKind::RecvIntoIter,
        IterKind::MapIter,
        IterKind::MapIterMut,
        IterKind::MapKeys,
        IterKind::MapValues,
        IterKind::MapValuesMut,
        IterKind::MapIntoIter,
        IterKind::MapIntoKeys,
        IterKind::MapIntoValues,
        IterKind::SetIter,
        IterKind::SetIntoIter,
        IterKind::ArrayIntoIter,
        IterKind::RepeatN,
        IterKind::ByNext,
        IterKind::Windows,
    ];

    /// True for the hashed-collection iterators.
    pub fn is_hash(self) -> bool {
        (IterKind::MapIter as usize..=IterKind::SetIntoIter as usize).contains(&(self as usize))
    }

    /// True for the hash iterators that own their table (by-value
    /// `into_iter`, `into_keys`, `into_values`).
    pub fn is_hash_owning(self) -> bool {
        matches!(self, IterKind::MapIntoIter | IterKind::MapIntoKeys | IterKind::MapIntoValues | IterKind::SetIntoIter)
    }

    /// The std module path and struct name: the def hash input and
    /// the printed name.
    pub fn path(self) -> (&'static [&'static str], &'static str) {
        use IterKind as K;
        const ADAPT: &[&str] = &["core", "iter", "adapters"];
        const HMAP: &[&str] = &["std", "collections", "hash", "map"];
        const HSET: &[&str] = &["std", "collections", "hash", "set"];
        match self {
            K::SliceIter => (&["core", "slice"], "Iter"),
            K::SliceIterMut => (&["core", "slice"], "IterMut"),
            K::VecIntoIter => (&["alloc", "vec"], "IntoIter"),
            K::Range => (&["core", "ops"], "Range"),
            K::RangeInclusive => (&["core", "ops"], "RangeInclusive"),
            K::Map => (ADAPT, "Map"),
            K::Filter => (ADAPT, "Filter"),
            K::Enumerate => (ADAPT, "Enumerate"),
            K::Rev => (ADAPT, "Rev"),
            K::Take => (ADAPT, "Take"),
            K::Skip => (ADAPT, "Skip"),
            K::Chain => (ADAPT, "Chain"),
            K::Zip => (ADAPT, "Zip"),
            K::Copied => (ADAPT, "Copied"),
            K::Cloned => (ADAPT, "Cloned"),
            K::FilterMap => (ADAPT, "FilterMap"),
            K::TakeWhile => (ADAPT, "TakeWhile"),
            K::SkipWhile => (ADAPT, "SkipWhile"),
            K::StepBy => (ADAPT, "StepBy"),
            K::Peekable => (ADAPT, "Peekable"),
            K::Inspect => (ADAPT, "Inspect"),
            K::RecvIter => (&["std", "sync", "mpsc"], "Iter"),
            K::RecvTryIter => (&["std", "sync", "mpsc"], "TryIter"),
            K::RecvIntoIter => (&["std", "sync", "mpsc"], "IntoIter"),
            K::MapIter => (HMAP, "Iter"),
            K::MapIterMut => (HMAP, "IterMut"),
            K::MapKeys => (HMAP, "Keys"),
            K::MapValues => (HMAP, "Values"),
            K::MapValuesMut => (HMAP, "ValuesMut"),
            K::MapIntoIter => (HMAP, "IntoIter"),
            K::MapIntoKeys => (HMAP, "IntoKeys"),
            K::MapIntoValues => (HMAP, "IntoValues"),
            K::SetIter => (HSET, "Iter"),
            K::SetIntoIter => (HSET, "IntoIter"),
            K::ArrayIntoIter => (&["core", "array", "iter"], "IntoIter"),
            K::RepeatN => (&["core", "iter", "sources", "repeat_n"], "RepeatN"),
            K::ByNext => (&["core", "iter", "lust"], "ByNext"),
            K::Windows => (&["core", "slice"], "Windows"),
        }
    }

    /// How many type args the builtin type takes (see the kind docs).
    pub fn n_args(self) -> usize {
        use IterKind as K;
        match self {
            K::Map | K::FilterMap => 3,
            K::Filter | K::Chain | K::Zip | K::TakeWhile | K::SkipWhile | K::Inspect | K::Copied | K::Cloned | K::ArrayIntoIter | K::ByNext => 2,
            K::MapIter
            | K::MapIterMut
            | K::MapKeys
            | K::MapValues
            | K::MapValuesMut
            | K::MapIntoIter
            | K::MapIntoKeys
            | K::MapIntoValues => 2,
            _ => 1,
        }
    }

    /// The printed path, as rustc's diagnostics name the type.
    pub fn display(self) -> &'static str {
        use IterKind as K;
        match self {
            K::SliceIter => "std::slice::Iter",
            K::SliceIterMut => "std::slice::IterMut",
            K::VecIntoIter => "std::vec::IntoIter",
            K::Range => "std::ops::Range",
            K::RangeInclusive => "std::ops::RangeInclusive",
            K::Map => "std::iter::Map",
            K::Filter => "std::iter::Filter",
            K::Enumerate => "std::iter::Enumerate",
            K::Rev => "std::iter::Rev",
            K::Take => "std::iter::Take",
            K::Skip => "std::iter::Skip",
            K::Chain => "std::iter::Chain",
            K::Zip => "std::iter::Zip",
            K::Copied => "std::iter::Copied",
            K::Cloned => "std::iter::Cloned",
            K::FilterMap => "std::iter::FilterMap",
            K::TakeWhile => "std::iter::TakeWhile",
            K::SkipWhile => "std::iter::SkipWhile",
            K::StepBy => "std::iter::StepBy",
            K::Peekable => "std::iter::Peekable",
            K::Inspect => "std::iter::Inspect",
            K::RecvIter => "std::sync::mpsc::Iter",
            K::RecvTryIter => "std::sync::mpsc::TryIter",
            K::RecvIntoIter => "std::sync::mpsc::IntoIter",
            K::MapIter => "std::collections::hash_map::Iter",
            K::MapIterMut => "std::collections::hash_map::IterMut",
            K::MapKeys => "std::collections::hash_map::Keys",
            K::MapValues => "std::collections::hash_map::Values",
            K::MapValuesMut => "std::collections::hash_map::ValuesMut",
            K::MapIntoIter => "std::collections::hash_map::IntoIter",
            K::MapIntoKeys => "std::collections::hash_map::IntoKeys",
            K::MapIntoValues => "std::collections::hash_map::IntoValues",
            K::SetIter => "std::collections::hash_set::Iter",
            K::SetIntoIter => "std::collections::hash_set::IntoIter",
            K::ArrayIntoIter => "std::array::IntoIter",
            K::RepeatN => "std::iter::RepeatN",
            K::ByNext => "",
            K::Windows => "std::slice::Windows",
        }
    }

    /// How many leading args the printed name shows (the item args
    /// lust adds stay hidden).
    pub fn shown_args(self) -> usize {
        match self {
            IterKind::Map | IterKind::FilterMap => 2,
            IterKind::Copied | IterKind::Cloned | IterKind::ArrayIntoIter => 1,
            k => k.n_args(),
        }
    }

    /// The stored fields, in std declaration order. `vec::IntoIter`
    /// is (buffer, front, back): the buffer's own length is never
    /// changed, and elements in `front..back` are the ones still owned.
    pub fn fields(self) -> &'static [Field] {
        use Field as F;
        use IterKind as K;
        match self {
            K::SliceIter => &[F::SliceRef(0, false)],
            K::SliceIterMut => &[F::SliceRef(0, true)],
            K::VecIntoIter => &[F::VecArg(0), F::Usize, F::Usize],
            K::Range => &[F::Arg(0), F::Arg(0)],
            K::RangeInclusive => &[F::Arg(0), F::Arg(0), F::Bool],
            K::Map | K::Filter | K::FilterMap | K::Inspect => &[F::Arg(0), F::Arg(1)],
            // `index` and `len` serve the random-access form only.
            K::Zip => &[F::Arg(0), F::Arg(1), F::Usize, F::Usize],
            K::Enumerate | K::Take | K::Skip => &[F::Arg(0), F::Usize],
            K::Rev | K::Copied | K::Cloned => &[F::Arg(0)],
            K::Chain => &[F::OptArg(0), F::OptArg(1)],
            K::TakeWhile | K::SkipWhile => &[F::Arg(0), F::Bool, F::Arg(1)],
            K::StepBy => &[F::Arg(0), F::Usize, F::Bool],
            K::Peekable => &[F::Arg(0), F::PeekSlot(0)],
            K::RecvIter | K::RecvTryIter => &[F::Recv(0, false)],
            K::RecvIntoIter => &[F::Recv(0, true)],
            // The hash core's iterator state (cgen/hash.rs), never a place.
            K::MapIter
            | K::MapIterMut
            | K::MapKeys
            | K::MapValues
            | K::MapValuesMut
            | K::MapIntoIter
            | K::MapIntoKeys
            | K::MapIntoValues
            | K::SetIter
            | K::SetIntoIter => &[],
            // (array, front, back): elements in `front..back` remain.
            K::ArrayIntoIter => &[F::Arg(1), F::Usize, F::Usize],
            // (element, count left).
            K::RepeatN => &[F::Arg(0), F::Usize],
            K::ByNext => &[F::Arg(0)],
            K::Windows => &[F::SliceRef(0, false), F::Usize],
        }
    }
}

/// The def of one builtin iterator struct (see `BuiltinDefs::iters`).
pub(super) fn iter_def(k: IterKind) -> DefId {
    let (module, name) = k.path();
    builtin_def(module, name)
}

/// The kind and type args of a builtin iterator type.
pub fn iter_parts(tys: &impl TyIntern, t: Ty) -> Option<(IterKind, Vec<Ty>)> {
    let Some(BuiltinTy::Iter(k)) = tys.builtin_of(t) else { return None };
    let (_, a) = tys.adt_parts(t)?;
    Some((k, tys.args(a).iter().map(|g| g.as_ty().unwrap_or(ERROR)).collect()))
}

/// A builtin iterator type from its kind and args.
pub fn mk_iter(tys: &mut impl TyIntern, k: IterKind, args: &[Ty]) -> Ty {
    debug_assert_eq!(args.len(), k.n_args());
    let def = tys.builtins().iters[k as usize];
    let a: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
    tys.mk_adt(def, &a)
}

/// True for the types `item_ty` answers: builtin iterators and `Chars`.
pub fn is_iter(tys: &impl TyIntern, t: Ty) -> bool {
    matches!(tys.builtin_of(t), Some(BuiltinTy::Iter(_) | BuiltinTy::Chars))
}

/// The item type of a builtin iterator type or `Chars`.
pub fn item_ty(tys: &mut impl TyIntern, t: Ty) -> Option<Ty> {
    use IterKind as K;
    if tys.is_chars_ty(t) {
        return Some(CHAR);
    }
    let (k, a) = iter_parts(tys, t)?;
    Some(match k {
        K::SliceIter => tys.mk_ref(false, a[0]),
        K::SliceIterMut => tys.mk_ref(true, a[0]),
        K::VecIntoIter | K::Range | K::RangeInclusive | K::RecvIter | K::RecvTryIter | K::RecvIntoIter => a[0],
        K::Map | K::FilterMap => a[2],
        K::Filter | K::Rev | K::Take | K::Skip | K::Chain | K::TakeWhile | K::SkipWhile | K::StepBy | K::Peekable | K::Inspect => {
            item_ty(tys, a[0])?
        }
        K::Enumerate => {
            let inner = item_ty(tys, a[0])?;
            let ts = tys.intern_tys(&[USIZE, inner]);
            tys.intern(TyKind::Tuple(ts))
        }
        K::Zip => {
            let x = item_ty(tys, a[0])?;
            let y = item_ty(tys, a[1])?;
            let ts = tys.intern_tys(&[x, y]);
            tys.intern(TyKind::Tuple(ts))
        }
        K::Copied | K::Cloned => a[1],
        K::MapIter | K::MapIterMut => {
            let kr = tys.mk_ref(false, a[0]);
            let vr = tys.mk_ref(k == K::MapIterMut, a[1]);
            let ts = tys.intern_tys(&[kr, vr]);
            tys.intern(TyKind::Tuple(ts))
        }
        K::MapKeys | K::SetIter => tys.mk_ref(false, a[0]),
        K::MapValues => tys.mk_ref(false, a[1]),
        K::MapValuesMut => tys.mk_ref(true, a[1]),
        K::MapIntoIter => {
            let ts = tys.intern_tys(&[a[0], a[1]]);
            tys.intern(TyKind::Tuple(ts))
        }
        K::MapIntoKeys | K::SetIntoIter => a[0],
        K::MapIntoValues => a[1],
        K::ArrayIntoIter | K::RepeatN => a[0],
        K::ByNext => a[1],
        K::Windows => {
            let s = tys.intern(TyKind::Slice(a[0]));
            tys.mk_ref(false, s)
        }
    })
}

/// The hash iterator a `for` loop over `t` runs (W-STD-B): a map or set
/// by value (`into_iter`), `&` of one (`iter`), or `&mut` of a map
/// (`iter_mut`). `Some(None)` for `&mut` of a set (no `IntoIterator`
/// impl), None when `t` is none of these.
pub fn hash_for_iter(tys: &mut impl TyIntern, t: Ty) -> Option<Option<Ty>> {
    use crate::ty::hash::{HashTy, hash_parts};
    let (m, inner) = match tys.kind(t) {
        TyKind::Ref(_, m, inner) => (Some(m.is_mut()), inner),
        _ => (None, t),
    };
    let (k, a) = hash_parts(tys, inner)?;
    let (kind, args) = match (k, m) {
        (HashTy::HashMap, None) => (IterKind::MapIntoIter, vec![a[0], a[1]]),
        (HashTy::HashMap, Some(false)) => (IterKind::MapIter, vec![a[0], a[1]]),
        (HashTy::HashMap, Some(true)) => (IterKind::MapIterMut, vec![a[0], a[1]]),
        (HashTy::HashSet, None) => (IterKind::SetIntoIter, vec![a[0]]),
        (HashTy::HashSet, Some(false)) => (IterKind::SetIter, vec![a[0]]),
        (HashTy::HashSet, Some(true)) => return Some(None),
        _ => return None,
    };
    Some(Some(mk_iter(tys, kind, &args)))
}

/// The owning std iterator a full std type path names (W-STD-B):
/// `vec::IntoIter<T>` and the hash `IntoIter`, `IntoKeys`, and
/// `IntoValues`. The borrowing iterators (`slice::Iter<'a, T>`) carry a
/// lifetime the region signatures do not model yet, so they stay
/// unknown types.
pub fn owning_by_path(path: &[&str]) -> Option<IterKind> {
    Some(match path {
        ["std" | "alloc", "vec", "IntoIter"] => IterKind::VecIntoIter,
        ["std", "collections", "hash_map", "IntoIter"] => IterKind::MapIntoIter,
        ["std", "collections", "hash_map", "IntoKeys"] => IterKind::MapIntoKeys,
        ["std", "collections", "hash_map", "IntoValues"] => IterKind::MapIntoValues,
        ["std", "collections", "hash_set", "IntoIter"] => IterKind::SetIntoIter,
        _ => return None,
    })
}

/// The iterator an `IntoIterator` argument (`extend`) turns into: a
/// builtin iterator as itself, a Vec by value as `vec::IntoIter`, `&X`
/// or `&mut X` over a Vec, slice, or array as a slice iterator, and a
/// map or set as its `hash_for_iter` iterator. None for other types.
pub fn as_iter_ty(tys: &mut impl TyIntern, t: Ty) -> Option<Ty> {
    if is_iter(tys, t) {
        return Some(t);
    }
    // An array by value (`array::IntoIter`; the caller checks the
    // element is Copy).
    if let TyKind::Array(e, _) = tys.kind(t) {
        return Some(mk_iter(tys, IterKind::ArrayIntoIter, &[e, t]));
    }
    if let Some(it) = hash_for_iter(tys, t) {
        return it;
    }
    if let Some(el) = tys.vec_elem(t) {
        return Some(mk_iter(tys, IterKind::VecIntoIter, &[el]));
    }
    let TyKind::Ref(_, m, inner) = tys.kind(t) else { return None };
    let el = match tys.kind(inner) {
        TyKind::Slice(el) | TyKind::Array(el, _) => el,
        _ => tys.vec_elem(inner)?,
    };
    Some(mk_iter(tys, if m.is_mut() { IterKind::SliceIterMut } else { IterKind::SliceIter }, &[el]))
}

/// The semantic type of one stored field.
pub fn field_ty(tys: &mut impl TyIntern, f: Field, args: &[Ty]) -> Ty {
    match f {
        Field::Arg(i) => args[i as usize],
        Field::Usize => USIZE,
        Field::Bool => BOOL,
        Field::OptArg(i) => tys.mk_option(args[i as usize]),
        Field::SliceRef(i, m) => {
            let s = tys.intern(TyKind::Slice(args[i as usize]));
            tys.mk_ref(m, s)
        }
        Field::VecArg(i) => tys.mk_vec(args[i as usize]),
        Field::PeekSlot(i) => {
            let item = item_ty(tys, args[i as usize]).unwrap_or(ERROR);
            let inner = tys.mk_option(item);
            tys.mk_option(inner)
        }
        Field::Recv(i, owned) => {
            let r = super::sync::sync_ty(tys, super::sync::SyncTy::Receiver, &[args[i as usize]]);
            if owned { r } else { tys.mk_ref(false, r) }
        }
    }
}

/// The stored field types of a builtin iterator type, in order.
pub fn field_tys(tys: &mut impl TyIntern, t: Ty) -> Option<Vec<Ty>> {
    let (k, a) = iter_parts(tys, t)?;
    Some(k.fields().iter().map(|&f| field_ty(tys, f, &a)).collect())
}

/// True if a builtin iterator type can hold a reference: the slice
/// iterators always do; every other kind does when one of its args
/// does (an arg covers every field and the item, see the kind docs).
pub fn iter_holds_ref(k: IterKind, args: &[Ty], arg_holds: &dyn Fn(Ty) -> bool) -> bool {
    matches!(
        k,
        IterKind::SliceIter
            | IterKind::SliceIterMut
            | IterKind::MapIter
            | IterKind::MapIterMut
            | IterKind::MapKeys
            | IterKind::MapValues
            | IterKind::MapValuesMut
            | IterKind::SetIter
    ) || args.iter().any(|&a| arg_holds(a))
}
