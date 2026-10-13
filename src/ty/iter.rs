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
}

impl IterKind {
    pub const ALL: [IterKind; 21] = [
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
    ];

    /// The std module path and struct name: the def hash input and
    /// the printed name.
    pub fn path(self) -> (&'static [&'static str], &'static str) {
        use IterKind as K;
        const ADAPT: &[&str] = &["core", "iter", "adapters"];
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
        }
    }

    /// How many type args the builtin type takes (see the kind docs).
    pub fn n_args(self) -> usize {
        use IterKind as K;
        match self {
            K::Map | K::FilterMap => 3,
            K::Filter | K::Chain | K::Zip | K::TakeWhile | K::SkipWhile | K::Inspect | K::Copied | K::Cloned => 2,
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
        }
    }

    /// How many leading args the printed name shows (the item args
    /// lust adds stay hidden).
    pub fn shown_args(self) -> usize {
        match self {
            IterKind::Map | IterKind::FilterMap => 2,
            IterKind::Copied | IterKind::Cloned => 1,
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
        K::VecIntoIter | K::Range | K::RangeInclusive => a[0],
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
    })
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
    matches!(k, IterKind::SliceIter | IterKind::SliceIterMut) || args.iter().any(|&a| arg_holds(a))
}
