// C backend. Each function is generated on its own (in parallel). Type helpers ("glue": drop, clone,
// eq, debug) are requested by structural type and generated once, after all functions.
use crate::ast::{BinOp, FmtKind, FmtSpec, UnOp};
use crate::check::Builtin;
use crate::check::collect::*;
use crate::diag::{SourceMap, Span};
use crate::ir::*;
use crate::ty::lang::{self, SigTy};
use crate::ty::layout::{self, EnumTag, Layout, Niche, ReprKind};
use crate::ty::iter::IterKind;
use crate::ty::*;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

mod clonefrom;
mod fmt;
mod sync;
mod hash;
mod split;
mod unwind;
mod own;
use unwind::Unw;

/// A body-independent type, so glue can be shared across functions.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CTy {
    Unit,
    Bool,
    Char,
    Int(IntTy),
    Str,
    String,
    Vec(Box<CTy>),
    Option(Box<CTy>),
    /// `Result<T, E>`: variant 0 is `Ok(T)`, variant 1 is `Err(E)`.
    Result(Box<CTy>, Box<CTy>),
    Ref(Box<CTy>),
    /// A raw pointer (w-cinterop): the same C pointer as `Ref`, but its
    /// glue compares, orders, hashes, and prints the address itself.
    Ptr(Box<CTy>),
    Adt(AdtId),
    Args,
    Chars,
    /// A tuple, emitted as a generated struct with fields f0, f1, ... (W-CORELANG).
    Tuple(Vec<CTy>),
    /// An array, emitted as a generated struct holding `v[len]` (W-CORELANG).
    Array(Box<CTy>, u64),
    /// A slice reference value or slice place: a generated fat struct holding
    /// `ptr` and `len` (W-CORELANG), the same role `lust_str` plays for `&str`.
    Slice(Box<CTy>),
    /// A float, as a C `float` or `double` (W-CORELANG).
    Float(FloatTy),
    /// A function pointer value: parameter types and return type.
    /// Emitted as a generated typedef that carries the out-pointer
    /// return convention for large returns (W-CGEN).
    FnPtr(Vec<CTy>, Box<CTy>),
    /// A `Box<T>`: a plain owning `T*` (never null, so it keeps
    /// the pointer niche).
    Boxed(Box<CTy>),
    /// An `Rc<T>`: a pointer to the generated counted header
    /// (`strong`, `weak`, then the value), also never null.
    Rc(Box<CTy>),
    /// A `&dyn Trait` or `&mut dyn Trait` value, or a dyn place (the
    /// fat value stands for it, as for slices): the runtime's
    /// `lust_dyn` (data pointer and vtable, ARCH 2.8).
    Dyn,
    /// A `Box<dyn Trait>`: an owning `lust_dyn` whose data points at
    /// the heap value (distinct from `Boxed(Dyn)`, a `Box<&dyn Tr>`).
    BoxDyn,
    /// An `Rc<dyn Trait>`: an owning `lust_dyn` whose data points at
    /// the value inside the Rc allocation, right after its two counts.
    RcDyn,
    /// A `rc::Weak<T>`: the same counted-header pointer as `Rc<T>`, or
    /// `UINTPTR_MAX` for `Weak::new()` (W-STD-A).
    Weak(Box<CTy>),
    /// A `rc::Weak<dyn Trait>` (false) or `sync::Weak<dyn Trait>`
    /// (true): the `lust_dyn` of the `Rc<dyn Trait>` or `Arc<dyn
    /// Trait>` it came from, its data `UINTPTR_MAX` when dangling
    /// (cgen/own.rs).
    WeakDyn(bool),
    /// A `RefCell<T>`: the generated struct `RCL_..` of the borrow
    /// flag `f0` (as Rust's `isize`) and the value `f1`.
    RefCell(Box<CTy>),
    /// A `Cell<T>`: the value itself in C; its own type for glue.
    Cell(Box<CTy>),
    /// A `Ref<T>` (false) or `RefMut<T>` (true) guard: a pointer to the
    /// `RefCell`'s struct; drop gives the borrow back.
    Guard(Box<CTy>, bool),
    /// A `vec::IntoIter<T>` (W-STD-A): the runtime's `lust_VecIter`,
    /// the moved-in buffer plus the front index of what it still owns.
    VecIter(Box<CTy>),
    /// An `array::IntoIter<T, N>` (fx-array-iter): a generated struct
    /// of the array itself and the front and back indexes of what it
    /// still owns (`f0`, `f1`, `f2`, as the tuple form held them).
    /// Its own type so drop and clone glue touch only that range.
    ArrayIter(Box<CTy>, u64),
    /// A `vec::Drain<T>`: the runtime's `lust_VecDrain`, a pointer to
    /// the drained Vec plus its range bookkeeping.
    VecDrain(Box<CTy>),
    /// A `string::Drain`: the same runtime struct over the String.
    StrDrain,
    /// A `core::fmt` struct (W-STD-B): the runtime's `lust_Formatter`
    /// or Debug builder (src/runtime/fmt.h).
    Fmt(crate::ty::fmt::FmtTy),
    /// A `process::ExitCode`: its status byte as a `uint8_t`.
    ExitCode,
    /// A `Box<[T]>`: the slice's fat `{ptr, len}` struct, owning its
    /// elements and buffer; a deref is the slice place itself.
    BoxSlice(Box<CTy>),
    /// An owning pointer to an unsized value (w-unsized, cgen/own.rs):
    /// `Box<str>`, `Rc<str>`, `Arc<[T]>`, `Arc<dyn Tr>`. The second
    /// part is the pointee place (`Str`, `Slice(T)`, or `Dyn`), and the
    /// C value is that place's fat form; a deref is the place itself.
    /// The Rc and Arc forms point at the value, with the two counts in
    /// the 16 bytes before it.
    Own(own::Owner, Box<CTy>),
    /// A `RefCell<dyn Tr>` place, or a reference to one (w-unsized,
    /// cgen/own.rs): `lust_dyn` whose data points at the cell (borrow
    /// flag first, then the value) and whose vtable is the value's.
    DynCell,
    /// A `Ref<dyn Tr>` (false) or `RefMut<dyn Tr>` (true): the same fat
    /// form as `DynCell`; a deref is the value's dyn place.
    DynGuard(bool),
    /// A `Mutex<dyn Tr>` place or reference, and a `MutexGuard<dyn Tr>`
    /// (true): `lust_dyn` whose data points at the lock (the futex word,
    /// the poison byte, then the value), with the value's vtable.
    DynLock(bool),
    /// A `std::sync` or `std::thread` type and its type argument (`Unit`
    /// for the atomics), emitted by cgen/sync.rs (W-THREADS).
    Sync(crate::ty::sync::SyncTy, Box<CTy>),
    /// An unsized newtype (W-SHIM: `OsStr`, `Path`) and a reference to
    /// it: the C form of its unsized field (the second part), as `Str`
    /// stands for both `str` and `&str`. The Adt keeps its identity for
    /// glue (Debug, PartialEq, Ord call the newtype's own impls).
    Unsized(AdtId, Box<CTy>),
    /// `std::thread::AccessError` (W-TLS): a unit struct (`lust_Unit`)
    /// whose Debug text is its name.
    AccessError,
    /// A hashed collection or std hasher (W-STD-B, cgen/hash.rs), with
    /// its type args: `HashMap [K, V, S]` and `HashSet [T, S]` are a
    /// generated `{ lust_hash_table t; S s; }`; the hashers are runtime
    /// structs.
    Hash(crate::ty::hash::HashTy, Vec<CTy>),
}

/// One step of a move path in codegen (see `FnGen::move_paths`): a
/// field of a struct, tuple, `Option` payload, or of the variant a
/// `Downcast` chose; a variant view; or an array element at a
/// constant index.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Step {
    Field(u32),
    Downcast(u32),
    Elem(u64),
    /// Through a `Box`: the one deref a move can go through.
    Deref,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Glue {
    Drop,
    Clone,
    /// `void clonefrom_T(T *d, T *s)`: `Clone::clone_from` by
    /// structure or core's body (cgen/clonefrom.rs).
    CloneFrom,
    Eq,
    Debug,
    /// Three-way comparison by structure: `int8_t cmp_T(T *a, T *b)`
    /// gives -1 (less), 0 (equal), 1 (greater), or 2 (unordered: a
    /// float NaN decided it), as derived and core `PartialOrd` order.
    Cmp,
    /// Like `Cmp`, but `PartialOrd::partial_cmp` order where it can
    /// differ from `Ord::cmp`: a written `partial_cmp` is called even
    /// when an `Ord` impl exists, and composite types compare their
    /// parts with `PCmp`. Only the sort adapters ask for it (std's
    /// sort compares with `lt`).
    PCmp,
    /// `T default_T(void)`: the value derived and core `Default` build.
    Default,
    /// Display of a type with a user `impl Display` (cgen/fmt.rs).
    Display,
    /// The slow path of a `thread_local!` access, keyed by the cell
    /// type `(u8, T)` (state byte, value; runtime/thread.c):
    /// `C *tlsinit_C(C *c, void *init)` makes the value with `init` (an
    /// `fn() -> T` pointer) and returns the cell, or NULL once destroyed.
    TlsInit,
    /// `void tlsdtor_C(void *c)`: a cell's thread-exit destructor (state
    /// destroyed, then the value's drop), keyed like `TlsInit`.
    TlsDtor,
    /// The hashed collections (cgen/hash.rs, W-STD-B): `hv_<T,H,..>`
    /// feeds a value to a hasher (key `(T, H, &[u8])`); per table,
    /// `hk_` hashes a key with the map's builder, `hof_`/`heq_`/`hcl_`
    /// are the core's hash-of, equality, and clone callbacks; per
    /// (table, lookup type Q), `hkq_` and `heqq_` (key `(table, Q)`).
    HashValue,
    HashKey,
    HashOf,
    HashEq,
    HashClone,
    HashKeyQ,
    HashEqQ,
    /// `heqe_`: the Entry search's equality, `stored == probe`.
    HashEqEntry,
    /// `hdr_`: the core's element drop callback.
    HashDrop,
    /// `hone_`: `BuildHasher::hash_one` of a value with a builder (key
    /// `(S, T)`).
    HashOne,
}

/// Maps a semantic type to its body-independent C form. Builtin Adts reach this
/// through the v2 compat helpers; kinds the subset cannot form yet map to `Unit`,
/// as inference leftovers did before. They gain real C forms with their features.
pub fn cty(tys: &impl TyIntern, t: Ty) -> CTy {
    match tys.kind(t) {
        TyKind::Bool => CTy::Bool,
        TyKind::Char => CTy::Char,
        TyKind::Int(i) => CTy::Int(i),
        TyKind::Float(f) => CTy::Float(f),
        TyKind::FnPtr(sig) => {
            let b = tys.sig(sig);
            CTy::FnPtr(tys.tys_of(b.value.inputs).iter().map(|&e| cty(tys, e)).collect(), Box::new(cty(tys, b.value.output)))
        }
        TyKind::FnDef(..) => CTy::Unit,
        TyKind::Str => CTy::Str,
        TyKind::Tuple(ts) => CTy::Tuple(tys.tys_of(ts).iter().map(|&e| cty(tys, e)).collect()),
        // A closure value is exactly a tuple of its captures (ARCH 4.5);
        // a closure with no captures is zero-sized like `()`.
        TyKind::Closure(_, a) => {
            let fields: Vec<CTy> = tys.args(a).iter().filter_map(|g| g.as_ty()).map(|e| cty(tys, e)).collect();
            if fields.is_empty() { CTy::Unit } else { CTy::Tuple(fields) }
        }
        TyKind::Array(e, c) => {
            let n = match tys.const_kind(c) {
                ConstKind::Int(n) => n as u64,
                _ => 0,
            };
            CTy::Array(Box::new(cty(tys, e)), n)
        }
        TyKind::Slice(e) => CTy::Slice(Box::new(cty(tys, e))),
        TyKind::Dyn(..) => CTy::Dyn,
        TyKind::Ref(_, _, e) => ref_cty(tys, e),
        TyKind::RawPtr(_, e) => CTy::Ptr(Box::new(cty(tys, e))),
        // An unsized newtype is laid out as its field (W-SHIM).
        TyKind::Adt(d, _) if let Some(f) = tys.unsized_field(d) => match tys.local_adt(t) {
            Some(a) => CTy::Unsized(a, Box::new(cty(tys, f))),
            None => cty(tys, f),
        },
        TyKind::Adt(..) => match tys.builtin_of(t) {
            Some(BuiltinTy::String) => CTy::String,
            Some(BuiltinTy::Vec) => CTy::Vec(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            _ if let Some(o) = own::own_cty(tys, t) => o,
            _ if let Some(w) = own::weak_dyn_cty(tys, t) => w,
            Some(BuiltinTy::Boxed | BuiltinTy::Rc) if tys.adt_first_ty_arg(t).is_some_and(|e| matches!(tys.kind(e), TyKind::Dyn(..))) => {
                if tys.builtin_of(t) == Some(BuiltinTy::Boxed) { CTy::BoxDyn } else { CTy::RcDyn }
            }
            Some(BuiltinTy::Boxed) => match tys.boxed_slice_elem(t) {
                Some(e) => CTy::BoxSlice(Box::new(cty(tys, e))),
                None => CTy::Boxed(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            },
            Some(BuiltinTy::Rc) => CTy::Rc(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::Option) => CTy::Option(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::Result) => {
                let (a, b) = tys.result_args(t).unwrap_or((ERROR, ERROR));
                CTy::Result(Box::new(cty(tys, a)), Box::new(cty(tys, b)))
            }
            Some(BuiltinTy::Chars) => CTy::Chars,
            Some(BuiltinTy::Args) => CTy::Args,
            Some(BuiltinTy::ExitCode) => CTy::ExitCode,
            Some(BuiltinTy::Iter(k)) => iter_cty(tys, t, k),
            Some(BuiltinTy::Fmt(k)) => CTy::Fmt(k),
            Some(BuiltinTy::Weak) => CTy::Weak(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::RefCell) if crate::check::own::dyn_cell_elem(tys, t).is_some() => CTy::DynCell,
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::Mutex)) if crate::check::own::dyn_lock_elem(tys, t).is_some() => CTy::DynLock(false),
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::MutexGuard)) if tys.adt_first_ty_arg(t).is_some_and(|e| matches!(tys.kind(e), TyKind::Dyn(..))) => {
                CTy::DynLock(true)
            }
            Some(BuiltinTy::RefGuard | BuiltinTy::RefMutGuard) if tys.adt_first_ty_arg(t).is_some_and(|e| matches!(tys.kind(e), TyKind::Dyn(..))) => {
                CTy::DynGuard(tys.builtin_of(t) == Some(BuiltinTy::RefMutGuard))
            }
            Some(BuiltinTy::RefCell) => CTy::RefCell(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::Cell) => CTy::Cell(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::RefGuard) => CTy::Guard(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR))), false),
            Some(BuiltinTy::RefMutGuard) => CTy::Guard(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR))), true),
            Some(BuiltinTy::Sync(k)) => CTy::Sync(k, Box::new(tys.adt_first_ty_arg(t).map_or(CTy::Unit, |e| cty(tys, e)))),
            // A `thread_local!` key is its slot word (runtime/thread.c);
            // `AccessError` is a unit struct.
            Some(BuiltinTy::LocalKey) => CTy::Int(IntTy::U64),
            Some(BuiltinTy::AccessError) => CTy::AccessError,
            Some(BuiltinTy::Hash(k)) => {
                let args = tys
                    .adt_parts(t)
                    .map(|(_, a)| tys.args(a).iter().filter_map(|g| g.as_ty()).map(|e| cty(tys, e)).collect())
                    .unwrap_or_default();
                CTy::Hash(k, args)
            }
            None => match tys.local_adt(t) {
                Some(a) => CTy::Adt(a),
                None => CTy::Unit,
            },
        },
        _ => CTy::Unit,
    }
}

/// The C form of a reference to `e`: a slice or dyn reference is its
/// fat value, a reference to an unsized newtype is the newtype's own
/// fat form (W-SHIM), anything else a pointer.
fn ref_cty(tys: &impl TyIntern, e: Ty) -> CTy {
    match tys.kind(e) {
        TyKind::Slice(el) => CTy::Slice(Box::new(cty(tys, el))),
        TyKind::Dyn(..) => CTy::Dyn,
        TyKind::Adt(d, _) if tys.unsized_field(d).is_some() => cty(tys, e),
        _ if crate::check::own::dyn_cell_elem(tys, e).is_some() => CTy::DynCell,
        _ if crate::check::own::dyn_lock_elem(tys, e).is_some() => CTy::DynLock(false),
        _ => CTy::Ref(Box::new(cty(tys, e))),
    }
}

/// The C form of a builtin iterator (ty/iter.rs): a tuple of its
/// stored fields, built structurally (no type interning here), or the
/// runtime's `lust_VecIter` for `vec::IntoIter`.
fn iter_cty(tys: &impl TyIntern, t: Ty, k: IterKind) -> CTy {
    use crate::ty::iter::Field;
    let args: Vec<Ty> = tys.adt_parts(t).map(|(_, a)| tys.args(a).iter().map(|g| g.as_ty().unwrap_or(ERROR)).collect()).unwrap_or_default();
    let arg = |i: u8| args.get(i as usize).copied().unwrap_or(ERROR);
    if k == IterKind::VecIntoIter {
        return CTy::VecIter(Box::new(cty(tys, arg(0))));
    }
    if k == IterKind::ArrayIntoIter {
        let n = match tys.kind(arg(1)) {
            crate::ty::TyKind::Array(_, c) => match tys.const_kind(c) {
                crate::ty::ConstKind::Int(n) => n as u64,
                _ => 0,
            },
            _ => 0,
        };
        return CTy::ArrayIter(Box::new(cty(tys, arg(0))), n);
    }
    // The hash iterators' state is the core's (cgen/hash.rs).
    if k.is_hash() {
        return CTy::Hash(crate::ty::hash::HashTy::of_iter(k), args.iter().map(|&a| cty(tys, a)).collect());
    }
    if k == IterKind::VecDrain {
        return CTy::VecDrain(Box::new(cty(tys, arg(0))));
    }
    if k == IterKind::StringDrain {
        return CTy::StrDrain;
    }
    let fields = k
        .fields()
        .iter()
        .map(|&f| match f {
            Field::Arg(i) => cty(tys, arg(i)),
            Field::Usize => CTy::Int(IntTy::Usize),
            Field::Bool => CTy::Bool,
            Field::OptArg(i) => CTy::Option(Box::new(cty(tys, arg(i)))),
            Field::OptRef(i, _) => CTy::Option(Box::new(CTy::Ref(Box::new(cty(tys, arg(i)))))),
            Field::SliceRef(i, _) => CTy::Slice(Box::new(cty(tys, arg(i)))),
            Field::VecArg(i) => CTy::Vec(Box::new(cty(tys, arg(i)))),
            Field::VecRefMut(i) => CTy::Ref(Box::new(CTy::Vec(Box::new(cty(tys, arg(i)))))),
            Field::StringRefMut => CTy::Ref(Box::new(CTy::String)),
            Field::PeekSlot(i) => CTy::Option(Box::new(CTy::Option(Box::new(iter_item_cty(tys, arg(i)))))),
            Field::Recv(i, owned) => {
                let r = CTy::Sync(crate::ty::sync::SyncTy::Receiver, Box::new(cty(tys, arg(i))));
                if owned { r } else { CTy::Ref(Box::new(r)) }
            }
            Field::Chars => CTy::Chars,
            Field::Str => CTy::Ref(Box::new(CTy::Str)),
        })
        .collect();
    CTy::Tuple(fields)
}

/// The C form of an iterator type's item, built without interning.
fn iter_item_cty(tys: &impl TyIntern, t: Ty) -> CTy {
    use IterKind as K;
    if tys.is_chars_ty(t) {
        return CTy::Char;
    }
    let Some((k, a)) = crate::ty::iter::iter_parts(tys, t) else { return CTy::Unit };
    let ref_to = |e: Ty| match tys.kind(e) {
        TyKind::Slice(el) => CTy::Slice(Box::new(cty(tys, el))),
        _ => CTy::Ref(Box::new(cty(tys, e))),
    };
    match k {
        K::SliceIter | K::SliceIterMut => ref_to(a[0]),
        K::Windows => CTy::Slice(Box::new(cty(tys, a[0]))),
        K::CharIndices => CTy::Tuple(vec![CTy::Int(IntTy::Usize), CTy::Char]),
        K::Flatten => iter_item_cty(tys, a[1]),
        K::OptionIntoIter => cty(tys, a[0]),
        K::VecIntoIter | K::Range | K::RangeInclusive | K::VecDrain => cty(tys, a[0]),
        K::StringDrain => CTy::Char,
        K::Map | K::FilterMap => cty(tys, a[2]),
        K::Enumerate => CTy::Tuple(vec![CTy::Int(IntTy::Usize), iter_item_cty(tys, a[0])]),
        K::Zip => CTy::Tuple(vec![iter_item_cty(tys, a[0]), iter_item_cty(tys, a[1])]),
        K::Copied | K::Cloned => cty(tys, a[1]),
        K::MapIter | K::MapIterMut => CTy::Tuple(vec![CTy::Ref(Box::new(cty(tys, a[0]))), CTy::Ref(Box::new(cty(tys, a[1])))]),
        K::MapKeys | K::SetIter => CTy::Ref(Box::new(cty(tys, a[0]))),
        K::MapValues | K::MapValuesMut => CTy::Ref(Box::new(cty(tys, a[1]))),
        K::MapIntoIter => CTy::Tuple(vec![cty(tys, a[0]), cty(tys, a[1])]),
        K::MapIntoKeys | K::SetIntoIter | K::RepeatN | K::ArrayIntoIter => cty(tys, a[0]),
        K::MapIntoValues | K::ByNext => cty(tys, a[1]),
        K::StrSplit => CTy::Ref(Box::new(CTy::Str)),
        _ => iter_item_cty(tys, a[0]),
    }
}

/// The pointee of a reference CTy (a `&Rc<T>` argument's `Rc<T>`).
fn deref_cty(t: &CTy) -> CTy {
    match t {
        CTy::Ref(inner) => (**inner).clone(),
        other => other.clone(),
    }
}

fn int_c(i: IntTy) -> &'static str {
    match i {
        IntTy::I8 => "int8_t",
        IntTy::I16 => "int16_t",
        IntTy::I32 => "int32_t",
        IntTy::I64 | IntTy::Isize => "int64_t",
        IntTy::U8 => "uint8_t",
        IntTy::U16 => "uint16_t",
        IntTy::U32 => "uint32_t",
        IntTy::U64 | IntTy::Usize => "uint64_t",
        // tcc has no __int128: the runtime's two-word structs (runtime.h).
        IntTy::I128 => "lust_i128",
        IntTy::U128 => "lust_u128",
    }
}

fn is128(i: IntTy) -> bool {
    matches!(i, IntTy::I128 | IntTy::U128)
}

/// A `lust_loc` naming a line of Rust 1.99's own std source, for a panic
/// rustc reports there (no `#[track_caller]`): `file` indexes
/// `lust_std_files` in panic.c (0 core/src/num/mod.rs, 1
/// core/src/char/methods.rs, 2 core/src/char/convert.rs, 3
/// alloc/src/vec/mod.rs, 4 core/src/cmp.rs, 5
/// core/src/iter/adapters/step_by.rs, 6
/// alloc/src/vec/spec_from_iter_nested.rs, 7
/// core/src/iter/traits/accum.rs, 8 core/src/iter/range.rs, 9
/// core/src/cell.rs, 10 std/src/thread/local.rs, 11 core/src/ops/arith.rs, 12
/// core/src/slice/index.rs, 13 core/src/iter/traits/exact_size.rs),
/// plus 0x40 for `pow`. Lowering names one with `Span::std_site`.
fn std_loc(file: u64, line: u64, col: u64) -> String {
    format!("{}ull", ((0xFF_FF00u64 + file) << 40) | (line << 20) | col)
}

/// The std location of an integer method that panics inside core
/// (`abs`, `pow`, signed wrapping/overflowing/saturating division):
/// the `int_impl!` or `uint_impl!` line for its type in
/// core/src/num/mod.rs.
fn num_loc(i: IntTy, pow: bool) -> String {
    let line = match i {
        IntTy::I8 => 379,
        IntTy::I16 => 404,
        IntTy::I32 => 429,
        IntTy::I64 => 454,
        IntTy::I128 => 479,
        IntTy::Isize => 559,
        IntTy::U8 => 586,
        IntTy::U16 => 1234,
        IntTy::U32 => 1290,
        IntTy::U64 => 1322,
        IntTy::U128 => 1354,
        IntTy::Usize => 1452,
    };
    std_loc(if pow { 0x40 } else { 0 }, line, 5)
}

/// Suffix of the runtime's checked-math helpers for this type.
fn int_fn(i: IntTy) -> &'static str {
    match i {
        IntTy::I8 => "i8",
        IntTy::I16 => "i16",
        IntTy::I32 => "i32",
        IntTy::I64 | IntTy::Isize => "i64",
        IntTy::U8 => "u8",
        IntTy::U16 => "u16",
        IntTy::U32 => "u32",
        IntTy::U64 | IntTy::Usize => "u64",
        IntTy::I128 => "i128",
        IntTy::U128 => "u128",
    }
}

pub fn ctype(t: &CTy) -> String {
    match t {
        CTy::Unit => "lust_Unit".into(),
        CTy::Bool => "uint8_t".into(),
        CTy::Char => "uint32_t".into(),
        CTy::Int(i) => int_c(*i).into(),
        CTy::Str => "lust_str".into(),
        CTy::String => "lust_String".into(),
        CTy::Vec(_) => "lust_Vec".into(),
        CTy::Ref(inner) if **inner == CTy::Str => "lust_str".into(),
        // `Box<dyn Tr>` and `Rc<dyn Tr>` are owning fat pointers whose
        // data points at the value (ARCH 2.8).
        CTy::BoxDyn | CTy::RcDyn | CTy::WeakDyn(_) => "lust_dyn".into(),
        CTy::Boxed(inner) => format!("{}*", ctype(inner)),
        CTy::Rc(inner) => format!("RcI_{}*", mangle(inner)),
        CTy::VecIter(_) => "lust_VecIter".into(),
        CTy::ArrayIter(..) => format!("AI_{}", mangle(t)),
        CTy::VecDrain(_) | CTy::StrDrain => "lust_VecDrain".into(),
        CTy::Weak(inner) => format!("RcI_{}*", mangle(inner)),
        CTy::RefCell(inner) => format!("RCL_{}", mangle(inner)),
        CTy::Cell(inner) => ctype(inner),
        CTy::Guard(inner, _) => format!("RCL_{}*", mangle(inner)),
        CTy::Ref(inner) => format!("{}*", ctype(inner)),
        CTy::Ptr(inner) => format!("{}*", ctype(inner)),
        CTy::Adt(a) => format!("A{}", a.0),
        CTy::Option(_) => format!("O_{}", mangle(t)),
        CTy::Result(..) => format!("R_{}", mangle(t)),
        CTy::Args => "lust_Args".into(),
        CTy::ExitCode => "uint8_t".into(),
        CTy::AccessError => "lust_Unit".into(),
        CTy::BoxSlice(e) => ctype(&CTy::Slice(e.clone())),
        CTy::Own(_, x) => ctype(x),
        CTy::DynCell | CTy::DynGuard(_) | CTy::DynLock(_) => "lust_dyn".into(),
        CTy::Sync(k, e) => sync::sync_ctype(*k, e),
        CTy::Chars => "lust_Chars".into(),
        CTy::Tuple(_) => format!("Tup_{}", mangle(t)),
        CTy::Array(..) => format!("Arr_{}", mangle(t)),
        CTy::Slice(_) => format!("Sl_{}", mangle(t)),
        CTy::Float(f) => (*f).name().replace("f64", "double").replace("f32", "float"),
        CTy::FnPtr(..) => format!("Fp_{}", mangle(t)),
        CTy::Dyn => "lust_dyn".into(),
        CTy::Fmt(k) => fmt_ctype(*k).into(),
        CTy::Unsized(_, inner) => ctype(inner),
        CTy::Hash(k, _) => hash::hash_ctype(*k, &mangle(t)),
    }
}

/// The (size, align) of the runtime struct of one `core::fmt` type
/// (src/runtime/fmt.h, x86_64 and aarch64 alike).
fn fmt_size_align(k: crate::ty::fmt::FmtTy) -> (u64, u64) {
    use crate::ty::fmt::FmtTy as F;
    match k {
        F::Formatter | F::Arguments | F::DebugTuple => (24, 8),
        F::DebugStruct | F::DebugList | F::DebugSet | F::DebugMap => (16, 8),
    }
}

/// The runtime struct of one `core::fmt` type.
fn fmt_ctype(k: crate::ty::fmt::FmtTy) -> &'static str {
    use crate::ty::fmt::FmtTy as F;
    match k {
        F::Formatter => "lust_Formatter",
        // A `format_args!` value is formatted when it is made (W-SHIM:
        // `io::Write::write_fmt`); it holds the text.
        F::Arguments => "lust_String",
        F::DebugStruct => "lust_DebugStruct",
        F::DebugTuple => "lust_DebugTuple",
        F::DebugList | F::DebugSet => "lust_DebugList",
        F::DebugMap => "lust_DebugMap",
    }
}

/// The C name fragment of `t`, used in type names (`O_<m>`, `Tup_<m>`) and glue names
/// (`drop_<m>`, `clone_<m>`). It must be injective: two different types with one fragment
/// give two C definitions with one name. Every type constructor gets its own token, every
/// token ends in `_` and has no other `_`, and each token fixes how many child tokens follow
/// (tuples and fn pointers encode their arity, arrays their length). So the fragment is a
/// prefix (Polish) code: splitting on `_` gives one token list, which parses one way only.
fn mangle(t: &CTy) -> String {
    let mut s = String::new();
    mangle_into(t, &mut s);
    s
}

/// Appends the tokens of `t` to `s` (see `mangle`).
fn mangle_into(t: &CTy, s: &mut String) {
    let tok = |s: &mut String, code: &str, kids: &[&CTy]| {
        s.push_str(code);
        s.push('_');
        kids.iter().for_each(|k| mangle_into(k, s));
    };
    match t {
        CTy::Unit => tok(s, "u", &[]),
        CTy::Bool => tok(s, "b", &[]),
        CTy::Char => tok(s, "c", &[]),
        CTy::Int(i) => tok(s, i.name(), &[]),
        CTy::Float(f) => tok(s, f.name(), &[]),
        CTy::Str => tok(s, "str", &[]),
        CTy::String => tok(s, "S", &[]),
        CTy::Args => tok(s, "Args", &[]),
        CTy::Chars => tok(s, "Chars", &[]),
        CTy::Dyn => tok(s, "dyn", &[]),
        CTy::BoxDyn => tok(s, "Bxdyn", &[]),
        CTy::RcDyn => tok(s, "Rcdyn", &[]),
        CTy::WeakDyn(arc) => tok(s, if *arc { "AWkdyn" } else { "Wkdyn" }, &[]),
        CTy::ExitCode => tok(s, "XC", &[]),
        CTy::AccessError => tok(s, "AE", &[]),
        CTy::Fmt(k) => tok(s, &format!("Fmt{}", *k as u8), &[]),
        // The kind fixes how many type arguments follow.
        CTy::Hash(k, args) => tok(s, &format!("H{}", *k as u8), &args.iter().collect::<Vec<_>>()),
        CTy::Adt(a) => tok(s, &format!("A{}", a.0), &[]),
        CTy::Vec(e) => tok(s, "V", &[e]),
        CTy::Boxed(e) => tok(s, "Bx", &[e]),
        CTy::Rc(e) => tok(s, "Rc", &[e]),
        CTy::VecIter(e) => tok(s, "VI", &[e]),
        CTy::ArrayIter(e, n) => tok(s, &format!("AI{n}"), &[e]),
        CTy::VecDrain(e) => tok(s, "VD", &[e]),
        CTy::StrDrain => tok(s, "SDr", &[]),
        CTy::Weak(e) => tok(s, "Wk", &[e]),
        CTy::RefCell(e) => tok(s, "RCL", &[e]),
        CTy::Cell(e) => tok(s, "Cl", &[e]),
        CTy::Guard(e, m) => tok(s, if *m { "GdM" } else { "Gd" }, &[e]),
        CTy::BoxSlice(e) => tok(s, "BS", &[e]),
        CTy::Own(k, e) => tok(s, k.code(), &[e]),
        CTy::DynCell => tok(s, "DCl", &[]),
        CTy::DynGuard(m) => tok(s, if *m { "DGdM" } else { "DGd" }, &[]),
        CTy::DynLock(g) => tok(s, if *g { "DLkG" } else { "DLk" }, &[]),
        CTy::Sync(k, e) => tok(s, &format!("Sy{}", *k as u32), &[e]),
        CTy::Ref(e) => tok(s, "R", &[e]),
        CTy::Ptr(e) => tok(s, "P", &[e]),
        CTy::Option(e) => tok(s, "O", &[e]),
        CTy::Result(a, b) => tok(s, "Re", &[a, b]),
        CTy::Slice(e) => tok(s, "sl", &[e]),
        CTy::Array(e, n) => tok(s, &format!("Y{n}"), &[e]),
        CTy::Tuple(es) => tok(s, &format!("T{}", es.len()), &es.iter().collect::<Vec<_>>()),
        CTy::FnPtr(ps, r) => tok(s, &format!("fp{}", ps.len()), &ps.iter().chain([&**r]).collect::<Vec<_>>()),
        CTy::Unsized(a, e) => tok(s, &format!("N{}", a.0), &[e]),
    }
}

/// Adds the named C types (structs, enums, Options) that `t` uses, including inside Vec and refs.
/// A `lust_str` expression for a `&str` or `&String` receiver.
fn str_of(v: &str, t: &CTy) -> String {
    match t {
        CTy::Ref(inner) if **inner == CTy::String => format!("lust_string_as_str({v})"),
        _ => v.to_string(),
    }
}

fn collect_types(t: &CTy, out: &mut HashSet<CTy>) {
    match t {
        CTy::Adt(_) => {
            out.insert(t.clone());
        }
        CTy::Option(e) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::Result(a, b) => {
            out.insert(t.clone());
            collect_types(a, out);
            collect_types(b, out);
        }
        CTy::Tuple(es) => {
            out.insert(t.clone());
            es.iter().for_each(|e| collect_types(e, out));
        }
        CTy::Array(e, _) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::Slice(e) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::FnPtr(ps, r) => {
            out.insert(t.clone());
            ps.iter().for_each(|e| collect_types(e, out));
            collect_types(r, out);
        }
        CTy::Vec(e) | CTy::Ref(e) | CTy::Boxed(e) | CTy::VecIter(e) | CTy::VecDrain(e) | CTy::Cell(e) | CTy::Unsized(_, e) | CTy::Own(_, e) => collect_types(e, out),
        CTy::ArrayIter(e, n) => {
            out.insert(t.clone());
            collect_types(&CTy::Array(e.clone(), *n), out);
        }
        CTy::Weak(e) => {
            out.insert(CTy::Rc(e.clone()));
            collect_types(e, out);
        }
        CTy::BoxSlice(e) => {
            out.insert(CTy::Slice(e.clone()));
            collect_types(e, out);
        }
        CTy::RefCell(e) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::Guard(e, _) => {
            out.insert(CTy::RefCell(e.clone()));
            collect_types(e, out);
        }
        CTy::Rc(e) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::Sync(k, e) => sync::sync_collect_types(*k, e, out),
        // Every hash type, so a unit that names one gets the core's
        // declarations (`type_decls`).
        CTy::Hash(k, args) => {
            out.insert(t.clone());
            if hash::has_struct(*k) {
                collect_types(&hash::elem_cty(t), out);
            }
            // The hash glue passes `&[u8]` to `Hasher::write`.
            if hash::is_table(*k) {
                collect_types(&CTy::Slice(Box::new(CTy::Int(IntTy::U8))), out);
            }
            args.iter().for_each(|e| collect_types(e, out));
        }
        _ => {}
    }
}

/// Named types that `t` holds by value, so their C definitions must come first.
fn by_value_deps(t: &CTy, out: &mut Vec<CTy>) {
    match t {
        CTy::Adt(_) | CTy::Option(_) | CTy::Result(..) | CTy::Tuple(_) | CTy::Array(..) | CTy::Slice(_) | CTy::FnPtr(..) | CTy::RefCell(_) | CTy::ArrayIter(..) => {
            out.push(t.clone())
        }
        // `Rc`, `Weak`, and the `RefCell` guards are pointers to forward-
        // declared structs, so a recursive `Option<Rc<Node>>` field works.
        CTy::Cell(e) => by_value_deps(e, out),
        CTy::BoxSlice(e) => out.push(CTy::Slice(e.clone())),
        CTy::Own(_, e) => by_value_deps(e, out),
        // A lock holds its value; a `PoisonError` is its value's C type.
        CTy::Sync(k, _) if k.is_cell_struct() => out.push(t.clone()),
        CTy::Sync(crate::ty::sync::SyncTy::PoisonError | crate::ty::sync::SyncTy::SendError, e) => by_value_deps(e, out),
        // A pointer to a fn pointer still names its typedef, which has
        // no forward form (a closure capturing a fn pointer by ref, a
        // `Box<fn()>` inside an `Option` or a lock).
        CTy::Ref(inner) | CTy::Boxed(inner) if matches!(**inner, CTy::FnPtr(..) | CTy::Ref(_) | CTy::Boxed(_)) => by_value_deps(inner, out),
        CTy::Unsized(_, inner) => by_value_deps(inner, out),
        CTy::Hash(k, _) if hash::has_struct(*k) => out.push(t.clone()),
        _ => {}
    }
}

fn is_copy_c(p: &Program, t: &CTy) -> bool {
    match t {
        CTy::Unit
        | CTy::Bool
        | CTy::Char
        | CTy::Int(_)
        | CTy::Float(_)
        | CTy::FnPtr(..)
        | CTy::Ref(_)
        | CTy::Ptr(_)
        | CTy::Args
        | CTy::ExitCode
        | CTy::AccessError
        | CTy::Chars
        | CTy::Slice(_)
        | CTy::Unsized(..)
        | CTy::DynCell
        | CTy::DynLock(false)
        | CTy::Dyn => true,
        CTy::Option(e) => is_copy_c(p, e),
        CTy::Result(a, b) => is_copy_c(p, a) && is_copy_c(p, b),
        CTy::Tuple(es) => es.iter().all(|e| is_copy_c(p, e)),
        CTy::Array(e, _) => is_copy_c(p, e),
        CTy::ArrayIter(e, _) => is_copy_c(p, e),
        CTy::Adt(a) => p.adt(*a).derives.copy,
        _ => false,
    }
}

/// True when a type holds no `Cell` or `RefCell` inline (Rust's
/// `Freeze`): pointers and buffers do not count, only by-value fields.
fn is_freeze_c(p: &Program, t: &CTy, seen: &mut HashSet<AdtId>) -> bool {
    match t {
        CTy::Cell(_) | CTy::RefCell(_) => false,
        // Every sync type holds an `UnsafeCell` inline.
        CTy::Sync(..) => false,
        CTy::Tuple(es) => es.iter().all(|e| is_freeze_c(p, e, seen)),
        CTy::Array(e, _) | CTy::Option(e) | CTy::ArrayIter(e, _) => is_freeze_c(p, e, seen),
        CTy::Result(a, b) => is_freeze_c(p, a, seen) && is_freeze_c(p, b, seen),
        CTy::Adt(a) => {
            if !seen.insert(*a) {
                return true;
            }
            p.adt(*a).variants.iter().all(|v| v.fields.iter().all(|f| is_freeze_c(p, &cty(&p.tys, f.ty), seen)))
        }
        _ => true,
    }
}

fn needs_drop_c(p: &Program, t: &CTy) -> bool {
    match t {
        CTy::String | CTy::Vec(_) | CTy::Boxed(_) | CTy::BoxSlice(_) | CTy::Own(..) | CTy::DynGuard(_) | CTy::DynLock(true) | CTy::Rc(_) | CTy::BoxDyn | CTy::RcDyn | CTy::WeakDyn(_) | CTy::VecIter(_) | CTy::VecDrain(_) | CTy::StrDrain | CTy::Weak(_) | CTy::Guard(..) => true,
        CTy::RefCell(e) | CTy::Cell(e) => needs_drop_c(p, e),
        CTy::Sync(k, e) => sync::sync_needs_drop(p, *k, e),
        CTy::Hash(k, a) => {
            hash::is_table(*k)
                || k.is_owning_iter()
                || (*k == crate::ty::hash::HashTy::Entry && a.first().is_some_and(|k| needs_drop_c(p, k)))
        }
        CTy::Option(e) => needs_drop_c(p, e),
        CTy::Result(a, b) => needs_drop_c(p, a) || needs_drop_c(p, b),
        CTy::Tuple(es) => es.iter().any(|e| needs_drop_c(p, e)),
        CTy::Array(e, _) => needs_drop_c(p, e),
        CTy::ArrayIter(e, _) => needs_drop_c(p, e),
        CTy::Adt(a) => {
            p.gx.drop_methods.contains_key(a) || p.adt(*a).variants.iter().any(|v| v.fields.iter().any(|f| needs_drop(p, &p.tys, f.ty)))
        }
        _ => false,
    }
}

fn c_string_lit(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() + 2);
    s.push('"');
    for &b in bytes {
        match b {
            b'"' => s.push_str("\\\""),
            b'\\' => s.push_str("\\\\"),
            b'?' => s.push_str("\\077"),
            0x20..=0x7e => s.push(b as char),
            _ => {
                let _ = write!(s, "\\{:03o}", b);
            }
        }
    }
    s.push('"');
    s
}

/// A byte blob as C string literal text, for one array initializer.
/// Adjacent literals of at most 256 source bytes each: C joins them
/// into one literal, and no single literal grows to megabyte size.
fn c_bytes_lit(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() + bytes.len() / 64 + 2);
    s.push('"');
    let mut n = 0usize;
    for &b in bytes {
        if n == 256 {
            s.push_str("\" \"");
            n = 0;
        }
        n += 1;
        match b {
            b'"' => s.push_str("\\\""),
            b'\\' => s.push_str("\\\\"),
            b'?' => s.push_str("\\077"),
            0x20..=0x7e => s.push(b as char),
            _ => {
                let _ = write!(s, "\\{:03o}", b);
            }
        }
    }
    s.push('"');
    s
}

/// One blob as a C array value: a single generated array struct
/// whose `v` member takes the whole byte string at once.
fn bytes_array_lit(p: &Program, t: &CTy, bytes: &[u8]) -> String {
    if bytes.is_empty() { zero_lit(p, t) } else { format!("(({}){{ .v = {} }})", ctype(t), c_bytes_lit(bytes)) }
}

/// The generated code for one function, plus the glue it needs.
#[derive(Default)]
pub struct FnOut {
    pub code: String,
    pub glue: HashSet<(Glue, CTy)>,
    /// Named C types (structs, enums, Options) this function's code needs declared.
    pub types: HashSet<CTy>,
    /// A code generation failure the driver must report instead of
    /// using `code` (see `FnGen::bad_move`).
    pub error: Option<String>,
}

struct FnGen<'b, 'p> {
    p: &'p Program,
    body: &'b Body<'p>,
    out: String,
    glue: HashSet<(Glue, CTy)>,
    local_cty: Vec<CTy>,
    local_drop: Vec<bool>,
    /// Per local, the field paths the body moves out of it (partial
    /// moves) whose value needs a drop. Each has a C flag
    /// `m{local}_{index}` that a move clears; drops of the local
    /// read the flags and drop only what it still owns (Rust's drop
    /// elaboration). A zeroed field cannot stand for "moved": a type
    /// with a user `Drop` impl would run it on the zero value.
    move_paths: Vec<Vec<Vec<Step>>>,
    /// The body moves part of a drop-needing local in a way drop
    /// elaboration cannot track (through a reference or a
    /// non-constant index, or along a path that does not fit the
    /// local's type). The borrow checker rejects every such move
    /// today, so this is a backstop: it turns a silent double drop
    /// into a compile error if a future move form (for example a
    /// `Box` deref move) reaches code generation first.
    bad_move: bool,
    /// The first fn this body calls, takes as a fn pointer, or puts
    /// in a vtable that has no generated body (`has_generated_body`).
    /// Its slot would stay empty, so the call would read garbage or
    /// jump to null: `gen_fn` reports it as an internal error instead.
    bad_callee: Option<LocalDefId>,
    /// Locals that hold one constant array index (see
    /// `borrowck::const_index_locals`): a move out of `a[c]` is a
    /// partial move like a field move.
    const_index: std::collections::HashMap<Local, u64>,
    /// The panic location of each index local (see `Proj::Index`).
    index_spans: Vec<Option<Span>>,
    map: &'b SourceMap,
    /// Types in the signatures of called functions, needed for the call casts.
    sig_types: HashSet<CTy>,
    /// Line of the function's `fn` keyword. Locations are stored relative to it, so the C for
    /// an unchanged function stays valid when code above it moves.
    base_line: u32,
    /// LocalDefId to table slot. Slots are stable across edits; local ids are not.
    slots: &'b [u32],
    tmp: u32,
    /// This function's return value uses the out-pointer ABI (`ret_is_large`).
    ret_large: bool,
    /// Vtable statics this function's unsizing coercions use, by vtable
    /// id, to their C names. Each function emits its own copies (named
    /// by its slot), so a unit never defines one twice.
    vtables: HashMap<u32, String>,
    /// Vtable statics and their method shims, emitted ahead of the function.
    prelude: String,
    /// Comparator adapters emitted so far (`sort_adapter`), for names.
    adapters: u32,
    /// panic=unwind state (cgen/unwind.rs); all empty under abort.
    /// The cleanup blocks, the cleanup entry of each statement by
    /// (block, index), and the action of the statement or call being
    /// emitted now.
    cleanup: Vec<bool>,
    stmt_unw: HashMap<(u32, u32), u32>,
    /// Per local, the one byte string blob it only holds
    /// (`ir::byte_blob_locals`): declared `static const` and never
    /// assigned, so a borrow of it has static storage.
    byte_blobs: Vec<Option<crate::ast::ByteBlob>>,
    unw: Option<Unw>,
    /// The value being assigned comes from a `Call` terminator.
    unw_call: bool,
}

/// A layout with no field or niche detail, for runtime struct types whose
/// C form is fixed in runtime.h (`lust_String`, `lust_Vec`, and kin).
fn plain_layout(size: u64, align: u64) -> Layout {
    Layout { size, align, field_offsets: Vec::new(), variant_offsets: Vec::new(), niche: None, enum_tag: None, uninhabited: false }
}

/// True when `type_decls` can emit an enum of this layout with the exact
/// Rust size: the tag or niche scalar is a C integer of at most 8 bytes,
/// or a 16-byte two-word 128-bit struct. Niche tag values may wrap the
/// scalar range; the readers below compare with wrapping arithmetic.
fn enum_is_exact(l: &Layout, variants: usize) -> bool {
    match l.enum_tag {
        Some(EnumTag::Explicit { size, .. }) => size <= 16,
        Some(EnumTag::NicheFilled { niche, .. }) => matches!(niche.scalar_size, 1 | 2 | 4 | 8 | 16),
        Some(EnumTag::None(_)) => true,
        None => false,
    }
}

/// The bit mask of a tag or niche scalar of `size` bytes.
fn scalar_mask(size: u64) -> u128 {
    if size * 8 >= 128 { u128::MAX } else { (1u128 << (size * 8)) - 1 }
}

/// The niche scalar bit pattern that stands for the `k`-th non-niche
/// variant (in the order of `NicheFilled`): successive values from
/// `niche.start`, wrapping at the top of the scalar range.
fn niche_val(niche: Niche, k: u128) -> u128 {
    niche.start.wrapping_add(k) & scalar_mask(niche.scalar_size)
}

/// A C literal for the raw bit pattern `bits` of a tag or niche scalar.
fn scalar_lit(bits: u128, size: u64, signed: bool) -> String {
    let ct = tag_c_type(size, signed);
    if size >= 16 {
        return format!("(({ct}){{{}ULL, {}ULL}})", bits as u64, (bits >> 64) as u64);
    }
    if signed && (bits >> (size * 8 - 1)) & 1 == 1 {
        let v = (bits as i128) - (1i128 << (size * 8));
        if v == i64::MIN as i128 { format!("(({ct})(-9223372036854775807LL - 1))") } else { format!("(({ct})({v}LL))") }
    } else {
        format!("(({ct})({bits}ULL))")
    }
}

/// The Rust layout of a CTy, when this file can emit a C type of exactly
/// that size, alignment, and field offsets. `None` means the type keeps
/// the legacy declaration-order emission below, with its old (wrong)
/// sizes: today that is by-value cycles, and enum shapes
/// `enum_is_exact` rejects. Every `Some` result is checked in the
/// emitted C by _Static_assert on sizeof and _Alignof (see `type_decls`).
///
/// The layout is computed over CTy, not over `Ty`, so glue types that
/// never existed as a semantic type (an Option of a reference, say) get
/// one too. The fat-pointer and String/Vec pointer niches are sound
/// because empty buffers and empty slices always carry the dangling
/// aligned pointer (see lust_string_new and lust_vec_with_capacity),
/// never null. Each Adt's layout is computed once per call (`Seen::done`):
/// a struct DAG whose fields share sub-types would otherwise cost one walk
/// per path.
fn c_layout(p: &Program, t: &CTy) -> Option<Layout> {
    /// The Adts on the walk (a by-value cycle has no layout) and the
    /// finished ones.
    #[derive(Default)]
    struct Seen {
        on: HashSet<AdtId>,
        done: HashMap<AdtId, Layout>,
    }
    fn go(p: &Program, t: &CTy, seen: &mut Seen) -> Option<Layout> {
        match t {
            CTy::Unit => Some(layout::zst_layout(1)),
            CTy::Bool => Some(layout::bool_layout()),
            CTy::Char => Some(layout::char_layout()),
            CTy::Int(i) => Some(layout::int_layout(*i)),
            CTy::Float(f) => Some(layout::float_layout(*f)),
            CTy::FnPtr(..) => Some(layout::ptr_layout()),
            CTy::Str => Some(layout::fat_ptr_layout()),
            CTy::String | CTy::Vec(_) => {
                // (ptr, len, cap) in runtime order; the pointer word is
                // never null (empty buffers dangle), and the capacity
                // word is capped at isize::MAX: both are niches, and
                // the capacity is the larger one.
                layout::struct_layout(
                    &[layout::ptr_layout(), layout::int_layout(IntTy::Usize), layout::cap_layout()],
                    layout::Repr { kind: ReprKind::C, ..layout::Repr::default() },
                )
                .ok()
            }
            CTy::Chars => Some(plain_layout(24, 8)),
            CTy::Fmt(k) => {
                let (size, align) = fmt_size_align(*k);
                Some(plain_layout(size, align))
            }
            // The C structs of cgen/hash.rs (`struct_fields`) and the
            // runtime's hasher types.
            CTy::Hash(k, args) => {
                use crate::ty::hash::HashTy;
                let c = layout::Repr { kind: ReprKind::C, ..layout::Repr::default() };
                match k {
                    HashTy::RandomState => Some(plain_layout(16, 8)),
                    HashTy::DefaultHasher => Some(plain_layout(72, 8)),
                    HashTy::BuildHasherDefault => Some(layout::zst_layout(1)),
                    HashTy::Entry => {
                        let key = go(p, args.first()?, seen)?;
                        layout::struct_layout(&[layout::ptr_layout(), layout::int_layout(IntTy::U64), layout::ptr_layout(), key], c).ok()
                    }
                    HashTy::HashMap | HashTy::HashSet => layout::struct_layout(&[plain_layout(64, 8), go(p, args.last()?, seen)?], c).ok(),
                    // `{ lust_hash_iter it; }`, owning: `{ table; it; }`.
                    HashTy::IterPairs | HashTy::IterKeys | HashTy::IterValues => Some(plain_layout(40, 8)),
                    HashTy::IntoPairs | HashTy::IntoKeys | HashTy::IntoValues => Some(plain_layout(104, 8)),
                }
            }
            CTy::Args => Some(plain_layout(8, 8)),
            CTy::ExitCode => Some(plain_layout(1, 1)),
            // A lock: its words, the poison flag, then the value (no
            // niche: `UnsafeCell`). `PoisonError<T>` is laid out as `T`.
            CTy::Sync(k, e) if k.is_cell_struct() => {
                let mut v = go(p, e, seen)?;
                v.niche = None;
                let mut fields: Vec<Layout> = sync::cell_words(*k).iter().map(|&i| layout::int_layout(i)).collect();
                fields.push(v);
                layout::struct_layout(&fields, layout::Repr { kind: ReprKind::C, ..layout::Repr::default() }).ok()
            }
            CTy::Sync(crate::ty::sync::SyncTy::PoisonError | crate::ty::sync::SyncTy::SendError, e) => go(p, e, seen),
            CTy::Sync(k, _) => sync::sync_layout(*k),
            CTy::AccessError => Some(plain_layout(0, 1)),
            CTy::Weak(_) | CTy::Guard(..) => Some(layout::ptr_layout()),
            // `UnsafeCell` hides the value's niche, as in Rust.
            CTy::Cell(e) => go(p, e, seen).map(|mut l| {
                l.niche = None;
                l
            }),
            CTy::RefCell(e) => {
                let mut v = go(p, e, seen)?;
                v.niche = None;
                layout::struct_layout(&[layout::int_layout(IntTy::Isize), v], layout::Repr { kind: ReprKind::C, ..layout::Repr::default() }).ok()
            }
            CTy::VecIter(_) => layout::struct_layout(
                &[layout::ptr_layout(), layout::int_layout(IntTy::Usize), layout::int_layout(IntTy::Usize), layout::int_layout(IntTy::Usize)],
                layout::Repr { kind: ReprKind::C, ..layout::Repr::default() },
            )
            .ok(),
            CTy::VecDrain(_) | CTy::StrDrain => layout::struct_layout(
                &[
                    layout::ptr_layout(),
                    layout::int_layout(IntTy::Usize),
                    layout::int_layout(IntTy::Usize),
                    layout::int_layout(IntTy::Usize),
                    layout::int_layout(IntTy::Usize),
                    layout::int_layout(IntTy::Usize),
                ],
                layout::Repr { kind: ReprKind::C, ..layout::Repr::default() },
            )
            .ok(),
            CTy::Ref(inner) if **inner == CTy::Str => Some(layout::fat_ptr_layout()),
            CTy::BoxDyn | CTy::RcDyn | CTy::WeakDyn(_) => Some(layout::fat_ptr_layout()),
            CTy::Boxed(_) | CTy::Rc(_) => Some(layout::ptr_layout()),
            CTy::Ref(_) => Some(layout::ptr_layout()),
            // A raw pointer may be null: no niche (w-cinterop).
            CTy::Ptr(_) => Some(layout::raw_ptr_layout()),
            CTy::Slice(_) | CTy::BoxSlice(_) | CTy::Own(..) | CTy::DynCell | CTy::DynGuard(_) | CTy::DynLock(_) | CTy::Dyn | CTy::Unsized(..) => {
                Some(layout::fat_ptr_layout())
            }
            CTy::Tuple(es) => {
                let fields: Option<Vec<Layout>> = es.iter().map(|e| go(p, e, seen)).collect();
                layout::tuple_layout(&fields?).ok()
            }
            // As the tuple of its stored fields (array, front, back).
            CTy::ArrayIter(e, n) => {
                let arr = go(p, &CTy::Array(e.clone(), *n), seen)?;
                layout::tuple_layout(&[arr, layout::int_layout(IntTy::Usize), layout::int_layout(IntTy::Usize)]).ok()
            }
            CTy::Array(e, 0) => Some(plain_layout(0, go(p, e, seen).map_or(1, |l| l.align))),
            CTy::Array(e, n) => layout::array_layout(&go(p, e, seen)?, *n).ok(),
            CTy::Option(e) => {
                let l = layout::enum_layout(&[vec![], vec![go(p, e, seen)?]], &[0, 1], layout::Repr::default()).ok()?;
                enum_is_exact(&l, 2).then_some(l)
            }
            CTy::Result(a, b) => {
                let l = layout::enum_layout(&[vec![go(p, a, seen)?], vec![go(p, b, seen)?]], &[0, 1], layout::Repr::default()).ok()?;
                enum_is_exact(&l, 2).then_some(l)
            }
            CTy::Adt(a) => {
                if let Some(l) = seen.done.get(a) {
                    return Some(l.clone());
                }
                if !seen.on.insert(*a) {
                    return None;
                }
                let adt = p.adt(*a);
                let r = if adt.is_enum {
                    let mut variants = Vec::with_capacity(adt.variants.len());
                    for v in &adt.variants {
                        let mut fields = Vec::with_capacity(v.fields.len());
                        for f in &v.fields {
                            fields.push(go(p, &cty(&p.tys, f.ty), seen)?);
                        }
                        variants.push(fields);
                    }
                    let discs: Vec<i128> = adt.variants.iter().map(|v| v.disc).collect();
                    match layout::enum_layout(&variants, &discs, adt.repr) {
                        Ok(l) if enum_is_exact(&l, adt.variants.len()) => Some(l),
                        _ => None,
                    }
                } else {
                    let mut fields = Vec::with_capacity(adt.variants[0].fields.len());
                    for f in &adt.variants[0].fields {
                        fields.push(go(p, &cty(&p.tys, f.ty), seen)?);
                    }
                    layout::struct_layout(&fields, adt.repr).ok()
                };
                seen.on.remove(a);
                if let Some(l) = &r {
                    seen.done.insert(*a, l.clone());
                }
                r
            }
        }
    }
    go(p, t, &mut Seen::default())
}

/// C integer type for an explicit enum tag or a niche scalar of `size`
/// bytes. Niche scalars are read and written as unsigned bit patterns.
fn tag_c_type(size: u64, signed: bool) -> &'static str {
    match (size, signed) {
        (1, false) => "uint8_t",
        (1, true) => "int8_t",
        (2, false) => "uint16_t",
        (2, true) => "int16_t",
        (4, false) => "uint32_t",
        (4, true) => "int32_t",
        (16, false) => "lust_u128",
        (16, true) => "lust_i128",
        (_, false) => "uint64_t",
        (_, true) => "int64_t",
    }
}

/// A zero compound literal of type `t`, in value position. Types the
/// layout path emits as structs or unions take the `{}` form: tcc
/// rejects `{0}` when the first member is an empty struct (size 0, or
/// a `lust_Unit` payload first in a niche-filled `Result<(), String>`).
/// Scalars keep `{0}`, which tcc needs for them.
fn zero_lit(p: &Program, t: &CTy) -> String {
    let ct = ctype(t);
    let aggregate = c_layout(p, t).is_some_and(|l| l.size == 0 || !l.field_offsets.is_empty() || !l.variant_offsets.is_empty());
    if aggregate { format!("(({ct}){{}})") } else { format!("(({ct}){{0}})") }
}

/// The discriminant values of an enum or Option CTy, in variant order.
fn adt_discs(p: &Program, t: &CTy) -> Vec<i128> {
    match t {
        CTy::Option(_) | CTy::Result(..) => vec![0, 1],
        CTy::Adt(a) => p.adt(*a).variants.iter().map(|v| v.disc).collect(),
        _ => Vec::new(),
    }
}

/// True when every discriminant equals its variant index, so a stored
/// tag value reads back as the index with no mapping.
fn discs_sequential(discs: &[i128]) -> bool {
    discs.iter().enumerate().all(|(i, &d)| d == i as i128)
}

/// A C literal for one discriminant value, cast to the tag type.
fn disc_lit(disc: i128, size: u64, signed: bool) -> String {
    scalar_lit((disc as u128) & scalar_mask(size), size, signed)
}

/// The C expression that reads the variant index of an enum or Option
/// value at the pointer expression `ptr`. The layout path stores the
/// discriminant value in the tag: sequential discriminants read
/// inline, the rest go through the generated `disc_` mapping helper.
/// Legacy types store the variant index in `tag` directly.
fn disc_call(p: &Program, t: &CTy, ptr: &str) -> String {
    match c_layout(p, t) {
        Some(l) => match l.enum_tag {
            // A 16-byte tag is a C struct: it cannot be read as one
            // integer, so it always goes through the helper.
            Some(EnumTag::Explicit { size, .. }) if size <= 8 && discs_sequential(&adt_discs(p, t)) => {
                format!("(({ptr})->u._tag)")
            }
            Some(EnumTag::Explicit { .. }) | Some(EnumTag::NicheFilled { .. }) => format!("disc_{}({ptr})", mangle(t)),
            Some(EnumTag::None(vi)) => vi.to_string(),
            _ => "0".into(),
        },
        None => format!("({ptr})->tag"),
    }
}

/// The `Utf8Error` value inside a std `FromUtf8Error` or `Utf8Error`
/// value `e` (synthetic std Adts, check/collect.rs); None for any other
/// type.
fn utf8_error_part(p: &Program, t: &CTy, e: &str) -> Option<String> {
    let CTy::Adt(a) = t else { return None };
    if p.tys.local_adt_of(crate::check::generics::from_utf8_error_def()) == Some(*a) {
        Some(format!("({e}).f1"))
    } else if p.tys.local_adt_of(crate::check::generics::utf8_error_def()) == Some(*a) {
        Some(format!("({e})"))
    } else {
        None
    }
}

/// The C field access for field `fi` of variant `vi` in the enum or
/// Option value expression `e`. Only Options differ between the layout
/// and legacy shapes; Adt enums keep `.u.v{vi}.f{fi}` in both.
fn variant_field(p: &Program, t: &CTy, e: &str, vi: usize, fi: usize) -> String {
    match t {
        CTy::Option(_) if c_layout(p, t).is_none() => format!("{e}.v"),
        _ => format!("{e}.u.v{vi}.f{fi}"),
    }
}

/// A C statement (no trailing newline) that stores variant `vi`'s
/// discriminant into the enum or Option value expression `e`. Empty
/// when the variant is the niche variant (its payload writes the niche
/// scalar) or the enum stores no tag.
fn disc_set(p: &Program, t: &CTy, e: &str, vi: usize) -> String {
    let Some(l) = c_layout(p, t) else { return format!("{e}.tag = {vi};") };
    match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => format!("{e}.u._tag = {};", disc_lit(adt_discs(p, t)[vi], size, signed)),
        Some(EnumTag::NicheFilled { variant, niche }) => {
            if vi == variant {
                String::new()
            } else {
                let k = (0..vi).filter(|&i| i != variant).count() as u128;
                format!("{e}.u._n._s = {};", scalar_lit(niche_val(niche, k), niche.scalar_size, false))
            }
        }
        _ => String::new(),
    }
}

/// Size and alignment of a CTy as the emitted C types lay it out under
/// the legacy emission: declaration order, natural alignment, a uint32
/// tag first in enums and Options. Used for the types `c_layout`
/// rejects, and only for the return-ABI threshold below, so it must
/// match the legacy C structs this file emits, nothing else.
fn c_size_align_legacy(p: &Program, t: &CTy) -> (u64, u64) {
    fn go(p: &Program, t: &CTy, seen: &mut HashSet<AdtId>) -> (u64, u64) {
        fn align_up(x: u64, a: u64) -> u64 {
            (x + a - 1) / a * a
        }
        fn fields(p: &Program, v: &Variant, seen: &mut HashSet<AdtId>) -> (u64, u64) {
            let (mut size, mut align) = (0u64, 1u64);
            for f in &v.fields {
                let (fs, fa) = go(p, &cty(&p.tys, f.ty), seen);
                size = align_up(size, fa) + fs;
                align = align.max(fa);
            }
            (align_up(size, align), align)
        }
        match t {
            CTy::Unit => (0, 1),
            CTy::Bool => (1, 1),
            CTy::Char => (4, 4),
            CTy::Int(i) => {
                let s = (i.bits() / 8) as u64;
                (s, if is128(*i) { 16 } else { s.min(8) })
            }
            CTy::Float(f) => match f {
                FloatTy::F32 => (4, 4),
                FloatTy::F64 => (8, 8),
            },
            CTy::FnPtr(..) => (8, 8),
            CTy::Str => (16, 8),
            CTy::String | CTy::Vec(_) | CTy::Chars => (24, 8),
            CTy::VecIter(_) => (32, 8),
            CTy::VecDrain(_) | CTy::StrDrain => (48, 8),
            CTy::Weak(_) | CTy::Guard(..) => (8, 8),
            CTy::Cell(e) => go(p, e, seen),
            CTy::RefCell(e) => {
                let (es, ea) = go(p, e, seen);
                let align = ea.max(8);
                (align_up(align_up(8, ea) + es, align), align)
            }
            CTy::Args => (8, 8),
            CTy::Fmt(k) => fmt_size_align(*k),
            CTy::ExitCode => (1, 1),
            CTy::Sync(k, e) if k.is_cell_struct() => {
                let (es, ea) = go(p, e, seen);
                let at = sync::cell_words(*k).iter().map(|i| i.bits() as u64 / 8).sum::<u64>();
                let align = ea.max(4);
                (align_up(align_up(at, ea) + es, align), align)
            }
            CTy::Sync(crate::ty::sync::SyncTy::PoisonError | crate::ty::sync::SyncTy::SendError, e) => go(p, e, seen),
            CTy::Sync(k, _) => sync::sync_layout(*k).map_or((8, 8), |l| (l.size, l.align)),
            CTy::AccessError => (0, 1),
            CTy::Hash(k, args) => match k {
                crate::ty::hash::HashTy::RandomState => (16, 8),
                crate::ty::hash::HashTy::DefaultHasher => (72, 8),
                crate::ty::hash::HashTy::BuildHasherDefault => (0, 1),
                k if k.is_owning_iter() => (104, 8),
                k if k.is_iter_form() => (40, 8),
                crate::ty::hash::HashTy::Entry => {
                    // `{ table ptr, hash, slot ptr, K key }`
                    let (ks, ka) = args.first().map_or((0, 1), |k| go(p, k, seen));
                    let align = ka.max(8);
                    (align_up(align_up(24, ka) + ks, align), align)
                }
                _ => {
                    // `{ lust_hash_table t (8 words); S s; }`
                    let (ss, sa) = args.last().map_or((0, 1), |s| go(p, s, seen));
                    let align = sa.max(8);
                    (align_up(64 + ss, align), align)
                }
            },
            CTy::Ref(inner) if **inner == CTy::Str => (16, 8),
            CTy::BoxDyn | CTy::RcDyn | CTy::WeakDyn(_) => (16, 8),
            CTy::Boxed(_) | CTy::Rc(_) => (8, 8),
            CTy::Ref(_) | CTy::Ptr(_) => (8, 8),
            CTy::Option(e) => {
                let (es, ea) = go(p, e, seen);
                let align = ea.max(4);
                (align_up(align_up(4, ea) + es, align), align)
            }
            CTy::Result(a, b) => {
                // Legacy shape: a uint32 tag, then a union of the two
                // payloads, like a legacy two-variant Adt enum.
                let (as_, aa) = go(p, a, seen);
                let (bs, ba) = go(p, b, seen);
                let (es, ea) = (as_.max(bs), aa.max(ba));
                let align = ea.max(4);
                (align_up(align_up(4, ea) + es, align), align)
            }
            CTy::Tuple(es) => {
                if es.is_empty() {
                    (1, 1) // the emitted `uint8_t unused`
                } else {
                    let (mut size, mut align) = (0u64, 1u64);
                    for e in es {
                        let (fs, fa) = go(p, e, seen);
                        size = align_up(size, fa) + fs;
                        align = align.max(fa);
                    }
                    (align_up(size, align), align)
                }
            }
            CTy::Array(e, n) => {
                let (es, ea) = go(p, e, seen);
                (es * (*n).max(1), ea)
            }
            CTy::ArrayIter(e, n) => {
                let (es, ea) = go(p, e, seen);
                let align = ea.max(8);
                (align_up(align_up(es * (*n).max(1), 8) + 16, align), align)
            }
            CTy::Slice(_) | CTy::BoxSlice(_) | CTy::Own(..) | CTy::DynCell | CTy::DynGuard(_) | CTy::DynLock(_) | CTy::Dyn | CTy::Unsized(..) => (16, 8),
            CTy::Adt(a) => {
                if !seen.insert(*a) {
                    // A by-value cycle has no finite size; check rejects
                    // it long before here. Report huge, never loop.
                    return (u64::MAX / 2, 8);
                }
                let adt = p.adt(*a);
                let r = if adt.is_enum {
                    let (mut usize_, mut ualign) = (0u64, 1u64);
                    for v in &adt.variants {
                        if !v.fields.is_empty() {
                            let (vs, va) = fields(p, v, seen);
                            usize_ = usize_.max(vs);
                            ualign = ualign.max(va);
                        }
                    }
                    if usize_ == 0 {
                        (4, 4)
                    } else {
                        let align = ualign.max(4);
                        (align_up(align_up(4, ualign) + usize_, align), align)
                    }
                } else if adt.variants[0].fields.is_empty() {
                    (1, 1) // the emitted `uint8_t unused`
                } else {
                    fields(p, &adt.variants[0], seen)
                };
                seen.remove(a);
                r
            }
        }
    }
    go(p, t, &mut HashSet::new())
}

/// Size and alignment of a CTy as the emitted C types lay it out: the
/// Rust layout when `c_layout` is exact, the legacy layout otherwise.
fn c_size_align(p: &Program, t: &CTy) -> (u64, u64) {
    match c_layout(p, t) {
        Some(l) => (l.size, l.align),
        None => c_size_align_legacy(p, t),
    }
}

/// Returns over 32 bytes go through a hidden out-pointer (ARCH 4.5);
/// parameters stay by value, which keeps the slot cast simple.
fn ret_is_large(p: &Program, f: LocalDefId) -> bool {
    ret_by_out(p, &cty(&p.tys, p.fn_info(f).ret))
}

/// True when a C function returns `t` through a hidden out-pointer:
/// over 32 bytes, or a zero-sized type that holds a zero-length array
/// (`[T; 0]`, also in a tuple or struct). tcc 0.9.28 crashes in a
/// function that returns such a struct by value (see `param_dropped`
/// for the same bug on parameters, and `zst_out_glue` for glue).
fn ret_by_out(p: &Program, t: &CTy) -> bool {
    let size = c_size_align(p, t).0;
    size > 32 || (size == 0 && has_zero_len_array(p, t))
}

/// True when a zero-sized type holds a zero-length array.
fn has_zero_len_array(p: &Program, t: &CTy) -> bool {
    match t {
        CTy::Array(_, 0) => true,
        CTy::Array(e, _) => has_zero_len_array(p, e),
        CTy::ArrayIter(e, n) => *n == 0 || has_zero_len_array(p, e),
        CTy::Tuple(es) => es.iter().any(|e| has_zero_len_array(p, e)),
        CTy::Adt(a) => p.adt(*a).variants.iter().any(|v| v.fields.iter().any(|f| has_zero_len_array(p, &cty(&p.tys, f.ty)))),
        _ => false,
    }
}

/// True when a by-value parameter of C type `t` is dropped from the C
/// signature and from every call. A zero-sized value carries no bits,
/// so the callee makes its local from a zero literal instead (see
/// `FnGen::function`). This is not optional: tcc 0.9.28 misplaces the
/// parameters after a zero-sized struct parameter that has a
/// zero-length array member, such as `[T; 0]` or `[[T; 0]; N]`, so
/// the callee reads garbage. Drop glue still runs once, in the
/// callee, through the local's drop flag.
fn param_dropped(p: &Program, t: &CTy) -> bool {
    c_size_align(p, t).0 == 0
}

/// True when `f` gets C of its own: a plain fn, an instance, or a
/// closure body fn, with a source body. A template or a trait
/// method stub is never generated, and an instance of a trait method
/// declaration has nothing to generate, so their slots stay empty.
fn has_generated_body(p: &Program, f: LocalDefId) -> bool {
    use crate::check::generics::FnClass;
    let concrete = matches!(p.gx.fn_class.get(f.0 as usize), None | Some(FnClass::Plain | FnClass::Instance | FnClass::Closure));
    concrete && p.fn_def(f).body.is_some()
}

/// The driver-facing message for `FnGen::bad_callee`: `f` (the body
/// being generated or its callee) has no generated body.
fn no_body_error(p: &Program, body: &Body, f: LocalDefId) -> String {
    let class = p.gx.fn_class.get(f.0 as usize).copied().unwrap_or_default();
    format!(
        "internal: code generation for `{}`: `{}` ({class:?}) has no generated body, so its fn slot would be empty",
        p.display_path(p.fn_info(body.fn_id).name),
        p.display_path(p.fn_info(f).name)
    )
}

/// `(RET (*)(PARAMS))`, the cast that calls function `f` through the table.
/// A large return becomes `(void (*)(RET*, PARAMS))` (see `ret_is_large`).
fn fn_ptr_cast(p: &Program, f: LocalDefId) -> String {
    let info = p.fn_info(f);
    let ret = ctype(&cty(&p.tys, info.ret));
    let mut params: Vec<String> = Vec::new();
    if ret_is_large(p, f) {
        params.push(format!("{ret}*"));
    }
    params.extend(info.params.iter().map(|&t| cty(&p.tys, t)).filter(|t| !param_dropped(p, t)).map(|t| ctype(&t)));
    // `#[track_caller]`: the caller's location (check/caller.rs).
    if crate::check::caller::is_track_caller(p, f) {
        params.push("lust_loc".to_string());
    }
    let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    if ret_is_large(p, f) { format!("(void (*)({params}))") } else { format!("({ret} (*)({params}))") }
}

/// The C signature of function `f`, defined under the C name `f<slot>`.
fn fn_sig(p: &Program, f: LocalDefId, slot: u32) -> String {
    let info = p.fn_info(f);
    let ret = ctype(&cty(&p.tys, info.ret));
    let mut params: Vec<String> = Vec::new();
    if ret_is_large(p, f) {
        params.push(format!("{ret} *out"));
    }
    params.extend(
        info.params
            .iter()
            .enumerate()
            .map(|(i, &t)| (i, cty(&p.tys, t)))
            .filter(|(_, t)| !param_dropped(p, t))
            .map(|(i, t)| format!("{} p{}", ctype(&t), i + 1)),
    );
    // `#[track_caller]`: the caller's location, which `FnGen::loc`
    // reports for every panic in the body (check/caller.rs).
    if crate::check::caller::is_track_caller(p, f) {
        params.push("lust_loc ltc".to_string());
    }
    let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    if ret_is_large(p, f) { format!("void f{slot}({params})") } else { format!("{ret} f{slot}({params})") }
}

/// The slot trampoline for function `f` (ARCH 4.5): a tiny forwarder
/// with a stable address, stored in fn pointer values through
/// `lust_tramps`. It forwards through `lust_fns`, so an overlay swap
/// of the body keeps old fn pointer values calling the new body.
/// Emitted in the function's own unit today; the table-unit home in
/// 4.5 needs the driver to pass signatures to `table_unit`.
fn trampoline(p: &Program, f: LocalDefId, slot: u32) -> String {
    let info = p.fn_info(f);
    let ret = ctype(&cty(&p.tys, info.ret));
    let cast = fn_ptr_cast(p, f);
    // The body fn of a closure that captures nothing (W-CHECK-G): a fn
    // pointer to it takes only the call args, so the trampoline supplies
    // the zero-sized env (by reference for `Fn` and `FnMut`).
    if p.gx.closure_fns.contains_key(&f)
        && let Some(&env_ty) = info.params.first()
    {
        let env_c = cty(&p.tys, env_ty);
        let by_ref = matches!(env_c, CTy::Ref(ref inner) if **inner == CTy::Unit);
        if by_ref || env_c == CTy::Unit {
            let kept: Vec<usize> =
                (1..info.params.len()).filter(|&i| !param_dropped(p, &cty(&p.tys, info.params[i]))).collect();
            let names: Vec<String> = kept.iter().map(|i| format!("p{}", i + 1)).collect();
            let decls: Vec<String> =
                kept.iter().map(|&i| format!("{} p{}", ctype(&cty(&p.tys, info.params[i])), i + 1)).collect();
            // A by-value Unit env is a dropped parameter; a by-ref env stays.
            let mut all: Vec<String> = if by_ref { vec!["&env".to_string()] } else { Vec::new() };
            all.extend(names);
            if ret_is_large(p, f) {
                let mut params = vec![format!("{ret} *out")];
                params.extend(decls);
                let rest = if all.is_empty() { String::new() } else { format!(", {}", all.join(", ")) };
                return format!(
                    "static void tramp{slot}({}) {{ lust_Unit env; ({cast}lust_fns[{slot}])(out{rest}); }}\n",
                    params.join(", ")
                );
            }
            let params = if decls.is_empty() { "void".to_string() } else { decls.join(", ") };
            return format!(
                "static {ret} tramp{slot}({params}) {{ lust_Unit env; return ({cast}lust_fns[{slot}])({}); }}\n",
                all.join(", ")
            );
        }
    }
    let kept: Vec<usize> = (0..info.params.len()).filter(|&i| !param_dropped(p, &cty(&p.tys, info.params[i]))).collect();
    let mut names: Vec<String> = kept.iter().map(|i| format!("p{}", i + 1)).collect();
    let decls: Vec<String> = kept.iter().map(|&i| format!("{} p{}", ctype(&cty(&p.tys, info.params[i])), i + 1)).collect();
    // Check never lets a `#[track_caller]` fn become a value; this keeps
    // the trampoline well formed all the same.
    if crate::check::caller::is_track_caller(p, f) {
        names.push("0".to_string());
    }
    if ret_is_large(p, f) {
        let mut params = vec![format!("{ret} *out")];
        params.extend(decls);
        let mut all = vec!["out".to_string()];
        all.extend(names);
        format!("static void tramp{slot}({}) {{ ({cast}lust_fns[{slot}])({}); }}\n", params.join(", "), all.join(", "))
    } else {
        let params = if decls.is_empty() { "void".to_string() } else { decls.join(", ") };
        format!("static {ret} tramp{slot}({params}) {{ return ({cast}lust_fns[{slot}])({}); }}\n", names.join(", "))
    }
}

/// Generates C for one function body. `base_line` is the line of its `fn` keyword, in the
/// file that defines it; `slots` maps every LocalDefId to its slot in `lust_fns`.
pub fn gen_fn(p: &Program, body: &Body, map: &SourceMap, base_line: u32, slots: &[u32]) -> FnOut {
    if !has_generated_body(p, body.fn_id) {
        return FnOut { error: Some(no_body_error(p, body, body.fn_id)), ..Default::default() };
    }
    // `LocalKey` calls become plain IR first (lower/tls.rs); their
    // closures never hold iterator builtins the next step would miss.
    let tls_expanded;
    let body = match crate::lower::tls::expand(p, body) {
        Ok(Some(b)) => {
            tls_expanded = b;
            &tls_expanded
        }
        Ok(None) => body,
        Err(e) => return FnOut { error: Some(e), ..Default::default() },
    };
    // Iterator builtins become plain IR first (W-STD-A, lower/iter.rs).
    let expanded;
    let body = match crate::lower::iter::expand(p, body) {
        Ok(Some(b)) => {
            expanded = b;
            &expanded
        }
        Ok(None) => body,
        Err(e) => return FnOut { error: Some(e), ..Default::default() },
    };
    let local_cty: Vec<CTy> = body.locals.iter().map(|l| cty(&body.tys, l.ty)).collect();
    let local_drop = local_cty.iter().map(|t| needs_drop_c(p, t)).collect();
    let n_locals = local_cty.len();
    let mut g = FnGen {
        p,
        body,
        out: String::new(),
        glue: HashSet::new(),
        local_cty,
        local_drop,
        move_paths: vec![Vec::new(); n_locals],
        bad_move: false,
        bad_callee: None,
        const_index: crate::borrowck::const_index_locals(body),
        index_spans: index_spans(body),
        map,
        sig_types: HashSet::new(),
        base_line,
        slots,
        tmp: 0,
        ret_large: ret_is_large(p, body.fn_id),
        vtables: HashMap::new(),
        prelude: String::new(),
        adapters: 0,
        cleanup: if p.unwind { unwind::cleanup_blocks(body) } else { Vec::new() },
        byte_blobs: crate::ir::byte_blob_locals(body),
        stmt_unw: body.stmt_unwind.iter().map(|&(b, i, u)| ((b.0, i), u.0)).collect(),
        unw: None,
        unw_call: false,
    };
    g.collect_move_paths();
    if g.bad_move {
        return FnOut { error: Some(bad_move_error(p, body)), ..Default::default() };
    }
    g.function();
    if g.bad_move {
        return FnOut { error: Some(bad_move_error(p, body)), ..Default::default() };
    }
    if let Some(f) = g.bad_callee {
        return FnOut { error: Some(no_body_error(p, body, f)), ..Default::default() };
    }
    if !g.prelude.is_empty() {
        g.out = std::mem::take(&mut g.prelude) + &g.out;
    }
    g.out.push_str(&trampoline(p, body.fn_id, g.slots[body.fn_id.0 as usize]));
    // A `main` returning `Result` gets a Termination entry in its
    // unit (see `fn_unit`): it needs the error type's Debug glue
    // and the Result's own drop glue.
    if Some(body.fn_id) == p.main
        && let Some((_, err_t)) = p.tys.result_args(p.fn_info(body.fn_id).ret)
    {
        let rc = cty(&p.tys, p.fn_info(body.fn_id).ret);
        g.want(Glue::Debug, &cty(&p.tys, err_t));
        if needs_drop_c(p, &rc) {
            g.want(Glue::Drop, &rc);
        }
    }
    let mut types = std::mem::take(&mut g.sig_types);
    for t in &g.local_cty {
        collect_types(t, &mut types);
    }
    for (_, t) in &g.glue {
        collect_types(t, &mut types);
    }
    FnOut { code: g.out, glue: g.glue, types, error: None }
}

/// The driver-facing message for `FnGen::bad_move`.
fn bad_move_error(p: &Program, body: &Body) -> String {
    format!(
        "internal: code generation for `{}`: a move out of part of a value reached code generation in a form drop elaboration cannot track (through a reference or a non-constant index)",
        p.name(p.fn_info(body.fn_id).name)
    )
}

/// The span of each local's last plain assignment, where a self-copy
/// `l = copy l` wins: the panic location of an index local
/// (`Proj::Index`, lowering's `mark_index_loc`).
fn index_spans(body: &Body) -> Vec<Option<Span>> {
    let mut out: Vec<Option<Span>> = vec![None; body.locals.len()];
    let mut fixed = vec![false; body.locals.len()];
    for b in &body.blocks {
        for st in &b.stmts {
            if let StmtKind::Assign(p, rv) = &st.kind
                && p.proj.is_empty()
                && let Some(slot) = out.get_mut(p.local as usize)
            {
                let l = p.local as usize;
                let self_copy = matches!(rv, Rvalue::Use(Operand::Copy(q)) if q.local == p.local && q.proj.is_empty());
                if self_copy || !fixed[l] {
                    *slot = Some(st.span);
                }
                fixed[l] |= self_copy;
            }
        }
    }
    out
}

impl FnGen<'_, '_> {
    /// The packed panic location of index local `l`, else `loc`.
    fn index_loc(&self, l: Local, loc: &str) -> String {
        match self.index_spans.get(l as usize).copied().flatten() {
            Some(sp) => self.loc(sp),
            None => loc.to_string(),
        }
    }
    /// A packed source location, relative to the function's first line. See `lust_loc`.
    /// The runtime prints one file path for the whole program (`lust_file`), so the packed
    /// value carries line and column only; an expanded span reports at its call site.
    fn loc(&self, span: Span) -> String {
        // A panic rustc reports inside std keeps std's line, also in a
        // `#[track_caller]` fn.
        if span.file == crate::diag::FileId::STD_SITE {
            return std_loc(span.lo as u64, (span.hi >> 12) as u64, (span.hi & 0xFFF) as u64);
        }
        // In a `#[track_caller]` fn every panic reports the caller's
        // location, as rustc does (check/caller.rs).
        if crate::check::caller::is_track_caller(self.p, self.body.fn_id) {
            return "ltc".to_string();
        }
        let (l, c) = self.map.line_display_col(self.map.call_site(span));
        let rel = l.saturating_sub(self.base_line).min(0xFFFFF) as u64;
        let slot = self.slots[self.body.fn_id.0 as usize] as u64;
        format!("{}u", (slot << 40) | (rel << 20) | c.min(0xFFFFF) as u64)
    }
    fn tmp(&mut self) -> String {
        self.tmp += 1;
        format!("t{}", self.tmp)
    }
    fn want(&mut self, g: Glue, t: &CTy) {
        self.glue.insert((g, t.clone()));
    }

    fn function(&mut self) {
        let p = self.p;
        let fid = self.body.fn_id;
        let slot = self.slots[fid.0 as usize];
        let _ = writeln!(self.out, "/* {} */\nstatic {} {{", p.display_path(p.fn_info(fid).name), fn_sig(p, fid, slot));
        // Locals grouped by C type. No initializers: the borrow checker proves every read is
        // after a write. Drop flags start at 0, except for parameters, which own their values.
        let mut by_type: Vec<(String, Vec<String>)> = Vec::new();
        let mut flags = Vec::new();
        for (i, t) in self.local_cty.iter().enumerate() {
            // A byte string temp gets static storage below, not a frame local.
            if self.byte_blobs.get(i).is_some_and(|b| b.is_some()) {
                continue;
            }
            let is_param = i >= 1 && i <= self.body.arg_count;
            // A dropped parameter (see `param_dropped`) has no `p{i}`; its
            // local is the one possible value of a zero-sized type.
            let decl = if is_param && param_dropped(p, t) {
                format!("l{i} = {}", zero_lit(p, t))
            } else if is_param {
                format!("l{i} = p{i}")
            } else {
                format!("l{i}")
            };
            let ct = ctype(t);
            if self.body.promoted.contains(&(i as Local)) {
                // A promoted constant (`&5` borrowed for `'static`): static
                // storage, written with the same value each time it runs.
                let _ = writeln!(self.out, "  static {ct} {decl};");
            } else {
                match by_type.iter_mut().find(|(c, _)| *c == ct) {
                    Some((_, v)) => v.push(decl),
                    None => by_type.push((ct, vec![decl])),
                }
            }
            if self.local_drop[i] {
                flags.push(format!("d{i} = {}", is_param as u8));
            }
            for k in 0..self.move_paths[i].len() {
                flags.push(format!("m{i}_{k} = 1"));
            }
        }
        for (ct, names) in &by_type {
            // In C, `T* a, b` makes only `a` a pointer, so every declarator gets its own stars.
            let base = ct.trim_end_matches('*');
            let stars = &ct[base.len()..];
            let decls: Vec<String> = names.iter().map(|n| format!("{stars}{n}")).collect();
            let _ = writeln!(self.out, "  {base} {};", decls.join(", "));
        }
        // Byte string temps: static storage, initialized once, never
        // assigned (the matching assignments are skipped in `stmt`).
        for (i, b) in self.byte_blobs.iter().enumerate() {
            if let Some(b) = b {
                let ct = ctype(&self.local_cty[i]);
                let init = if b.is_empty() { "{0}".to_string() } else { format!("{{ .v = {} }}", c_bytes_lit(b.as_slice())) };
                let _ = writeln!(self.out, "  static {ct} l{i} = {init};");
            }
        }
        if !flags.is_empty() {
            let _ = writeln!(self.out, "  uint8_t {};", flags.join(", "));
        }
        if p.unwind {
            // A call made while its thread has a pending exception comes
            // from code that runs on after a panic (glue, a runtime
            // callback): it returns at once, as if never called.
            let _ = writeln!(self.out, "  lust_exc ex;
  if (lust_unw_pending && lust_unw_mine()) {}", self.unwind_return());
        }
        let n = self.body.blocks.len();
        let mut reachable = vec![false; n];
        let mut stack = vec![0usize];
        while let Some(b) = stack.pop() {
            if std::mem::replace(&mut reachable[b], true) {
                continue;
            }
            stack.extend(succ(&self.body.blocks[b].term).into_iter().map(|s| s.0 as usize));
            stack.extend(self.body.stmt_unwind.iter().filter(|e| e.0.0 as usize == b).map(|e| e.2.0 as usize));
        }
        let order: Vec<usize> = (0..n).filter(|&b| reachable[b]).collect();
        for (k, &bi) in order.iter().enumerate() {
            let _ = writeln!(self.out, "bb{bi}:;");
            let block = self.body.block(Bb(bi as u32));
            for (si, s) in block.stmts.iter().enumerate() {
                self.unw = self.stmt_action(bi, si).filter(|_| !matches!(s.kind, StmtKind::StorageDead(_) | StmtKind::FakeRead(_)));
                let mark = self.out.len();
                self.stmt(&s.kind, s.span);
                if let Some(u) = self.unw.take() {
                    let check = u.check();
                    let text = unwind::wrap_calls(&self.out[mark..], &check);
                    self.out.truncate(mark);
                    self.out.push_str(&text);
                    let _ = writeln!(self.out, "  {check}");
                }
            }
            self.unw = self.stmt_action(bi, block.stmts.len());
            let next = order.get(k + 1).copied();
            if let Terminator::Goto(t) = &block.term
                && Some(t.0 as usize) == next
            {
                continue;
            }
            self.term(&block.term, block.term_span, next);
        }
        self.out.push_str("}\n\n");
    }

    /// The unwind action of statement `si` of block `bi` (`si` equal to
    /// the statement count is the terminator): abort in a cleanup
    /// block, else its cleanup entry, if lowering gave it one.
    fn stmt_action(&self, bi: usize, si: usize) -> Option<Unw> {
        if !self.p.unwind {
            return None;
        }
        if self.cleanup[bi] {
            return Some(Unw::Abort);
        }
        self.stmt_unw.get(&(bi as u32, si as u32)).map(|&u| Unw::Goto(u))
    }

    /// `return <placeholder>;` for a frame that leaves by unwinding: the
    /// caller never reads the value.
    fn unwind_return(&self) -> String {
        if self.ret_large {
            return "return;".into();
        }
        let rt = cty(&self.p.tys, self.p.fn_info(self.body.fn_id).ret);
        format!("return {};", zero_lit(self.p, &rt))
    }

    /// For an assignment to `dest` of a type that needs drop: the C
    /// statements that drop the old value first, and the ones that
    /// mark the place owned again after the write. Each starts with
    /// a space. A whole local drops through its flag and elaboration;
    /// a part drops through elaboration when moves went through it
    /// (Rust lets a moved field be assigned again), else always.
    fn drop_old_value(&mut self, dest: &Place, d: &str, dt: &CTy) -> (String, String) {
        let l = dest.local;
        if dest.proj.is_empty() {
            let old = self.elab_drop(l, &[]);
            return (format!(" if (d{l}) {{{old} }}"), format!(" d{l} = 1;{}", self.reset_move_flags(l, &[])));
        }
        if let Some(path) = self.steps_of(dest)
            && self.move_paths[l as usize].iter().any(|p| p.starts_with(&path))
        {
            return (self.elab_drop(l, &path), self.reset_move_flags(l, &path));
        }
        self.want(Glue::Drop, dt);
        (format!(" drop_{}(&{d});", mangle(dt)), String::new())
    }

    // ---------- Drop elaboration ----------

    /// The move path of a place: its projections as `Step`s, or None
    /// when it goes through a reference or a non-constant index.
    /// A deref through a `Box` is a step (moving out of a box is
    /// legal); a deref through a reference is not.
    fn steps_of(&self, pl: &Place) -> Option<Vec<Step>> {
        let mut steps: Vec<Step> = Vec::new();
        for pr in &pl.proj {
            let step = match pr {
                Proj::Field(i) => Step::Field(*i),
                Proj::Downcast(v) => Step::Downcast(*v),
                Proj::Index(l) => Step::Elem(*self.const_index.get(l)?),
                Proj::Deref => {
                    let (_, t) = self.path_place(pl.local, &steps)?;
                    if !matches!(t, CTy::Boxed(_)) {
                        return None;
                    }
                    Step::Deref
                }
            };
            steps.push(step);
        }
        Some(steps)
    }

    /// Fills `move_paths` from every `Move` of a part of a local.
    /// The statement and terminator matches are exhaustive, like
    /// the rvalue scan, so a new IR variant cannot hide a move from
    /// drop elaboration. A part move with no trackable path sets
    /// `bad_move` instead of being skipped.
    fn collect_move_paths(&mut self) {
        let body = self.body;
        let mut moved: Vec<&Place> = Vec::new();
        for b in &body.blocks {
            for s in &b.stmts {
                match &s.kind {
                    StmtKind::Assign(_, rv) => rvalue_moves(rv, &mut moved),
                    StmtKind::Print { parts, .. } => parts_moves(parts, &mut moved),
                    StmtKind::Drop(_) | StmtKind::StorageDead(_) | StmtKind::FakeRead(_) => {}
                }
            }
            match &b.term {
                Terminator::If(o, ..) | Terminator::Switch(o, ..) => operand_moves(o, &mut moved),
                // `dest` is a write and an `Indirect` target reads a
                // Copy fn pointer local: neither moves a place.
                Terminator::Call { args, .. } => args.iter().for_each(|o| operand_moves(o, &mut moved)),
                Terminator::Panic(parts) => parts_moves(parts, &mut moved),
                Terminator::Goto(_) | Terminator::Return | Terminator::Unreachable => {}
            }
        }
        for pl in moved {
            if pl.proj.is_empty() {
                continue;
            }
            let l = pl.local as usize;
            if !self.local_drop[l] {
                continue;
            }
            let Some(path) = self.steps_of(pl) else {
                self.bad_move = true;
                continue;
            };
            match self.path_place(pl.local, &path) {
                Some((_, t)) if needs_drop_c(self.p, &t) => {
                    if !self.move_paths[l].contains(&path) {
                        self.move_paths[l].push(path);
                    }
                }
                Some(_) => {}
                None => self.bad_move = true,
            }
        }
    }

    /// The C expression and type of one move path of local `l`
    /// (`place` for the projections a path can hold), or None when
    /// a step does not fit the type it steps into. Callers turn
    /// None into `bad_move`: a move path that does not fit its
    /// local's type must not reach drop elaboration.
    fn path_place(&self, l: Local, path: &[Step]) -> Option<(String, CTy)> {
        let mut e = format!("l{l}");
        let mut t = self.local_cty[l as usize].clone();
        let mut variant: Option<u32> = None;
        for step in path {
            match (*step, t.clone()) {
                (Step::Downcast(v), _) => variant = Some(v),
                (Step::Field(i), CTy::Adt(a)) => {
                    let v = variant.take();
                    e = match v {
                        Some(v) => format!("{e}.u.v{v}.f{i}"),
                        None => format!("{e}.f{i}"),
                    };
                    let f = self.p.adt(a).variants.get(v.unwrap_or(0) as usize)?.fields.get(i as usize)?;
                    t = cty(&self.p.tys, f.ty);
                }
                (Step::Field(i), CTy::Tuple(es)) => {
                    e = format!("{e}.f{i}");
                    t = es.get(i as usize)?.clone();
                }
                (Step::Field(i), CTy::ArrayIter(el, n)) => {
                    e = format!("{e}.f{i}");
                    t = match i {
                        0 => CTy::Array(el, n),
                        1 | 2 => CTy::Int(IntTy::Usize),
                        _ => return None,
                    };
                }
                (Step::Field(_), CTy::Option(inner)) => {
                    variant = None;
                    e = variant_field(self.p, &t, &e, 1, 0);
                    t = *inner;
                }
                (Step::Field(_), CTy::Result(a, b)) => {
                    let v = variant.take().unwrap_or(0);
                    e = variant_field(self.p, &t, &e, v as usize, 0);
                    t = if v == 0 { *a } else { *b };
                }
                (Step::Elem(c), CTy::Array(el, n)) => {
                    if c >= n {
                        return None;
                    }
                    e = format!("{e}.v[{c}]");
                    t = *el;
                }
                (Step::Deref, CTy::Boxed(inner)) => {
                    e = format!("(*{e})");
                    t = *inner;
                }
                _ => return None,
            }
        }
        Some((e, t))
    }

    /// The flag index of one moved path of local `l`.
    fn move_flag(&self, l: Local, path: &[Step]) -> Option<usize> {
        self.move_paths[l as usize].iter().position(|p| p == path)
    }

    /// C statements that set every move flag of `l` at or below
    /// `prefix` (the part an assignment just filled again).
    fn reset_move_flags(&self, l: Local, prefix: &[Step]) -> String {
        let mut s = String::new();
        for (k, path) in self.move_paths[l as usize].iter().enumerate() {
            if path.starts_with(prefix) {
                let _ = write!(s, " m{l}_{k} = 1;");
            }
        }
        s
    }

    /// C statements that drop the part of local `l` at `prefix` that
    /// the function still owns: a moved path drops only while its
    /// flag is set, a place above moved paths drops part by part in
    /// Rust's order (an enum only in the variant the paths go
    /// through), and any other place drops whole. Rust forbids moving
    /// out of a type with a `Drop` impl (E0509, borrowck), so no place
    /// split here has one.
    fn elab_drop(&mut self, l: Local, prefix: &[Step]) -> String {
        let paths = &self.move_paths[l as usize];
        let own = paths.iter().position(|p| p == prefix);
        let deeper = paths.iter().any(|p| p.len() > prefix.len() && p.starts_with(prefix));
        // Every prefix here is a prefix of a path `collect_move_paths`
        // verified, or one step below such a prefix taken from the
        // type at that prefix (`elab_parts`), so None cannot happen
        // for a body the scan accepted. Flag it anyway: the driver
        // reports `bad_move` and discards this function's code.
        let Some((e, t)) = self.path_place(l, prefix) else {
            self.bad_move = true;
            return String::new();
        };
        let inner = if deeper {
            self.elab_parts(l, prefix, &e, &t)
        } else if needs_drop_c(self.p, &t) {
            self.want(Glue::Drop, &t);
            format!(" drop_{}(&{e});", mangle(&t))
        } else {
            String::new()
        };
        match own {
            Some(k) => format!(" if (m{l}_{k}) {{{inner} }}"),
            None => inner,
        }
    }

    /// `elab_drop` one level down: the fields of a struct, tuple, or
    /// (after a `Downcast`) enum variant in order, the elements of an
    /// array in order, or a switch over the enum variants the moved
    /// paths go through.
    fn elab_parts(&mut self, l: Local, prefix: &[Step], e: &str, t: &CTy) -> String {
        let next_steps: Vec<Step> = {
            let mut v: Vec<Step> = Vec::new();
            for p in &self.move_paths[l as usize] {
                if p.len() > prefix.len() && p.starts_with(prefix) && !v.contains(&p[prefix.len()]) {
                    v.push(p[prefix.len()]);
                }
            }
            v
        };
        let sub = |s: Step| {
            let mut p = prefix.to_vec();
            p.push(s);
            p
        };
        let mut out = String::new();
        let variant = match prefix.last() {
            Some(Step::Downcast(v)) => Some(*v as usize),
            _ => None,
        };
        let is_enum = match t {
            CTy::Adt(a) => self.p.adt(*a).is_enum,
            CTy::Option(_) | CTy::Result(..) => true,
            _ => false,
        };
        match t {
            CTy::Array(el, n) if variant.is_none() => {
                // rustc's open drop of an array (`open_drop_for_array`):
                // a run of elements with no move path drops as one
                // subslice (in index order), an element with one drops
                // on its own, and the runs and elements go in reverse.
                let kept: Vec<u64> = next_steps.iter().filter_map(|s| if let Step::Elem(c) = s { Some(*c) } else { None }).collect();
                let mut parts: Vec<Result<(u64, u64), u64>> = Vec::new();
                let (mut dropping, mut start) = (true, 0);
                for i in 0..*n {
                    let keep = kept.contains(&i);
                    if dropping && keep {
                        parts.push(Ok((start, i)));
                        dropping = false;
                    } else if !dropping && !keep {
                        dropping = true;
                        start = i;
                    }
                    if keep {
                        parts.push(Err(i));
                    }
                }
                if dropping {
                    parts.push(Ok((start, *n)));
                }
                for part in parts.into_iter().rev() {
                    match part {
                        Ok((a, b)) if b > a => {
                            let i = self.tmp();
                            self.want(Glue::Drop, el);
                            let _ = write!(out, " for (uint64_t {i} = {a}; {i} < {b}; {i}++) drop_{}(&{e}.v[{i}]);", mangle(el));
                        }
                        Ok(_) => {}
                        Err(c) => out += &self.elab_drop(l, &sub(Step::Elem(c))),
                    }
                }
            }
            // An `array::IntoIter`'s still-owned part is a range, not
            // a set of move paths: its glue drops exactly that range.
            CTy::ArrayIter(..) => {
                if needs_drop_c(self.p, t) {
                    self.want(Glue::Drop, t);
                    let _ = write!(out, " drop_{}(&{e});", mangle(t));
                }
            }
            CTy::Boxed(inner) => {
                // Drop the still-owned part behind the pointer,
                // then free the allocation itself.
                out += &self.elab_drop(l, &sub(Step::Deref));
                let et = ctype(inner);
                let _ = write!(out, " lust_dealloc((void*){e}, sizeof({et}), _Alignof({et}));");
            }
            _ if is_enum && variant.is_none() => {
                let _ = write!(out, " switch ({}) {{", disc_call(self.p, t, &format!("(&{e})")));
                for s in next_steps {
                    if let Step::Downcast(v) = s {
                        let body = self.elab_drop(l, &sub(s));
                        let _ = write!(out, " case {v}: {{{body} }} break;");
                    }
                }
                self.want(Glue::Drop, t);
                let _ = write!(out, " default: drop_{}(&{e}); break; }}", mangle(t));
            }
            _ => {
                let n = match t {
                    CTy::Tuple(es) => es.len(),
                    CTy::Adt(a) => self.p.adt(*a).variants.get(variant.unwrap_or(0)).map_or(0, |v| v.fields.len()),
                    CTy::Option(_) => usize::from(variant == Some(1)),
                    CTy::Result(..) => usize::from(variant.is_some()),
                    _ => 0,
                };
                for f in 0..n {
                    out += &self.elab_drop(l, &sub(Step::Field(f as u32)));
                }
            }
        }
        out
    }

    // ---------- Places and operands ----------

    fn place(&mut self, pl: &Place, loc: &str) -> (String, CTy) {
        let mut e = format!("l{}", pl.local);
        let mut t = self.local_cty[pl.local as usize].clone();
        let mut variant: Option<u32> = None;
        for pr in &pl.proj {
            match (pr, t.clone()) {
                (Proj::Deref, CTy::Ref(inner)) => {
                    if *inner == CTy::Str {
                        // A `str` place is represented by its fat `&str` value.
                        t = CTy::Str;
                    } else {
                        e = format!("(*{e})");
                        t = *inner;
                    }
                }
                // The dyn place behind an owning fat pointer is its fat
                // value, as behind `&dyn` (the data points at the value).
                (Proj::Deref, CTy::BoxDyn | CTy::RcDyn) => {
                    t = CTy::Dyn;
                }
                (Proj::Deref, CTy::Boxed(inner)) => {
                    e = format!("(*{e})");
                    t = *inner;
                }
                (Proj::Deref, CTy::Rc(inner) | CTy::Sync(crate::ty::sync::SyncTy::Arc, inner)) => {
                    e = format!("{e}->v");
                    t = *inner;
                }
                (Proj::Deref, CTy::Guard(inner, _)) => {
                    e = format!("{e}->f1");
                    t = *inner;
                }
                // A lock guard points at its lock (W-THREADS).
                (Proj::Deref, CTy::Sync(k, inner)) if k.guard().is_some() => {
                    e = format!("{e}->v");
                    t = *inner;
                }
                (Proj::Field(i), CTy::Adt(a)) => {
                    let v = variant.take();
                    e = match v {
                        Some(v) => format!("{e}.u.v{v}.f{i}"),
                        None => format!("{e}.f{i}"),
                    };
                    let fty = self.p.adt(a).variants[v.unwrap_or(0) as usize].fields[*i as usize].ty;
                    t = cty(&self.p.tys, fty);
                }
                (Proj::Downcast(_), CTy::Option(_)) => {}
                (Proj::Field(_), CTy::Option(inner)) => {
                    e = variant_field(self.p, &t, &e, 1, 0);
                    t = *inner;
                }
                (Proj::Downcast(v), CTy::Result(..)) => variant = Some(*v),
                (Proj::Field(_), CTy::Result(ok_t, err_t)) => {
                    let v = variant.take().unwrap_or(0);
                    e = variant_field(self.p, &t, &e, v as usize, 0);
                    t = if v == 0 { *ok_t } else { *err_t };
                }
                (Proj::Downcast(v), _) => variant = Some(*v),
                (Proj::Index(l), CTy::Vec(el)) => {
                    let loc = self.index_loc(*l, loc);
                    e = match self.unw {
                        Some(Unw::Goto(b)) => self.index_unw(&format!("{e}.len"), &format!("(({}*){e}.ptr)", ctype(&el)), *l, &loc, b),
                        _ => format!("(({}*){e}.ptr)[lust_bounds(l{l}, {e}.len, {loc})]", ctype(&el)),
                    };
                    t = *el;
                }
                (Proj::Field(i), CTy::Tuple(es)) => {
                    e = format!("{e}.f{i}");
                    t = es[*i as usize].clone();
                }
                (Proj::Field(i), CTy::ArrayIter(el, n)) => {
                    e = format!("{e}.f{i}");
                    t = match *i {
                        0 => CTy::Array(el, n),
                        _ => CTy::Int(IntTy::Usize),
                    };
                }
                (Proj::Index(l), CTy::Array(el, n)) => {
                    let loc = self.index_loc(*l, loc);
                    e = match self.unw {
                        Some(Unw::Goto(b)) => self.index_unw(&n.to_string(), &format!("{e}.v"), *l, &loc, b),
                        _ => format!("{e}.v[lust_bounds(l{l}, {n}, {loc})]"),
                    };
                    t = *el;
                }
                (Proj::Deref, CTy::Slice(_)) | (Proj::Deref, CTy::Dyn) => {
                    // A slice or dyn place is represented by its fat value, like `str`.
                }
                (Proj::Deref, CTy::Unsized(..)) => {}
                // A `&RefCell<dyn Tr>` (`&Mutex<dyn Tr>`) is the fat place too.
                (Proj::Deref, CTy::DynCell | CTy::DynLock(false)) => {}
                (Proj::Field(0), CTy::Unsized(_, inner)) => {
                    // The field of an unsized newtype (W-SHIM): the same fat value.
                    t = *inner;
                }
                (Proj::Deref, CTy::BoxSlice(el)) => {
                    // The boxed slice's fat value is its slice place too.
                    t = CTy::Slice(el);
                }
                // So is an owning fat pointer's (cgen/own.rs).
                (Proj::Deref, CTy::Own(_, x)) => {
                    t = *x;
                }
                // A `Ref<dyn Tr>`'s value sits after the cell's flag.
                (Proj::Deref, CTy::DynGuard(_)) => {
                    e = own::dyn_cell_value(&e);
                    t = CTy::Dyn;
                }
                (Proj::Deref, CTy::DynLock(true)) => {
                    e = own::dyn_lock_value(&e);
                    t = CTy::Dyn;
                }
                (Proj::Index(l), CTy::Slice(el)) => {
                    let loc = self.index_loc(*l, loc);
                    e = match self.unw {
                        Some(Unw::Goto(b)) => self.index_unw(&format!("{e}.len"), &format!("{e}.ptr"), *l, &loc, b),
                        _ => format!("{e}.ptr[lust_bounds(l{l}, {e}.len, {loc})]"),
                    };
                    t = *el;
                }
                (pr, t) => panic!("bad projection in codegen: {pr:?} on {t:?}"),
            }
        }
        (e, t)
    }

    /// An indexed element place under panic=unwind: a GNU statement
    /// expression whose failed bounds check panics and leaves for the
    /// cleanup at block `b` before any element is read.
    fn index_unw(&self, len: &str, base: &str, l: Local, loc: &str, b: u32) -> String {
        format!("(*({{ if (l{l} >= {len}) {{ lust_bounds(l{l}, {len}, {loc}); lust_unw_take(&ex); goto bb{b}; }} &{base}[l{l}]; }}))")
    }

    fn operand(&mut self, o: &Operand, loc: &str, post: &mut Vec<String>) -> (String, CTy) {
        match o {
            Operand::Copy(pl) => self.place(pl, loc),
            Operand::Move(pl) => {
                let (e, t) = self.place(pl, loc);
                if self.local_drop[pl.local as usize] {
                    if pl.proj.is_empty() {
                        // Moving the whole local: it owns nothing now.
                        post.push(format!("d{} = 0;", pl.local));
                    } else if let Some(path) = self.steps_of(pl)
                        && let Some(k) = self.move_flag(pl.local, &path)
                    {
                        // Moving one field out (a partial move, or an enum payload): the
                        // local's later drops skip this path (see `elab_drop`).
                        post.push(format!("m{}_{k} = 0;", pl.local));
                    }
                }
                (e, t)
            }
            Operand::Const(c) => match c {
                Const::Int(v, it) => {
                    let lit = if is128(*it) {
                        format!("(({}){{{}ULL, {}ULL}})", int_c(*it), *v as u64, (*v >> 64) as u64)
                    } else if *v < (1 << 31) {
                        v.to_string()
                    } else {
                        format!("(({}){}ULL)", int_c(*it), *v as u64)
                    };
                    (lit, CTy::Int(*it))
                }
                Const::Float(bits, f) => {
                    let lit = match f {
                        FloatTy::F64 => format!("(((union {{ uint64_t b; double d; }}){{ .b = {}ull }}).d)", bits),
                        FloatTy::F32 => format!("(((union {{ uint32_t b; float f; }}){{ .b = {}u }}).f)", *bits as u32),
                    };
                    (lit, CTy::Float(*f))
                }
                Const::Bool(b) => ((*b as u8).to_string(), CTy::Bool),
                Const::Char(c) => (format!("((uint32_t){})", *c as u32), CTy::Char),
                Const::Str(i) => {
                    let s = &self.p.ast.strings[*i as usize];
                    (format!("((lust_str){{(uint8_t*){}, {}}})", c_string_lit(s.as_bytes()), s.len()), CTy::Ref(Box::new(CTy::Str)))
                }
                Const::StrBytes(b) => {
                    (format!("((lust_str){{(uint8_t*){}, {}}})", c_string_lit(b.as_slice()), b.len()), CTy::Ref(Box::new(CTy::Str)))
                }
                Const::Bytes(b) => {
                    let t = CTy::Array(Box::new(CTy::Int(IntTy::U8)), b.len() as u64);
                    (bytes_array_lit(self.p, &t, b.as_slice()), t)
                }
                Const::Unit => ("((lust_Unit){})".into(), CTy::Unit),
            },
        }
    }

    // ---------- Statements ----------

    /// Stores a computed value into `dest`, dropping the old value first when
    /// the local owns one. Shared by `Assign` statements and `Call`
    /// terminators: `make_value` produces the value text (and may emit helper
    /// statements into the block this opens), and `mentions` says whether
    /// producing the value reads `dest` itself.
    fn emit_assign(
        &mut self,
        dest: &Place,
        mentions: bool,
        loc: &str,
        make_value: impl FnOnce(&mut Self, &str, &mut Vec<String>) -> String,
    ) {
        // Value generation may emit helper statements with temporaries, so open a C block lazily.
        let mark = self.out.len();
        self.out.push_str("  {\n");
        let body_start = self.out.len();
        let mut post = Vec::new();
        let value = make_value(self, loc, &mut post);
        let (d, dt) = self.place(dest, loc);
        let drop = needs_drop_c(self.p, &dt);
        // A statement whose destination is a whole local with nothing to
        // drop writes it directly: a value left there by a panic is never
        // read, and the statement's own check follows (`function`).
        let unw = self.unw.filter(|_| self.unw_call || drop || !dest.proj.is_empty());
        if let Some(u) = unw {
            // panic=unwind: the value goes to a temporary first and the
            // check runs before the old value drops or the place is
            // written, so a panic leaves the destination as it was.
            // A call owns its moved arguments from the start, so their
            // flags clear before it runs: a panic inside it must not drop
            // them again here. A statement moves only at its end.
            if self.unw_call {
                let flags: String = post.iter().map(|p| format!("    {p}\n")).collect();
                self.out.insert_str(body_start, &flags);
                post.clear();
            }
            let t = self.tmp();
            let _ = writeln!(self.out, "    {} {t} = {value};", ctype(&dt));
            for p in &post {
                let _ = writeln!(self.out, "    {p}");
            }
            let _ = writeln!(self.out, "    {}", u.check());
            if drop {
                let (drop_old, refill) = self.drop_old_value(dest, &d, &dt);
                // A drop that panics leaves the local unowned, so its
                // cleanup does not drop it again.
                let drop_old = if dest.proj.is_empty() { drop_old.replacen(" {", &format!(" {{ d{} = 0;", dest.local), 1) } else { drop_old };
                let _ = writeln!(self.out, "   {drop_old}\n    {d} = {t};\n   {refill}");
            } else {
                let _ = writeln!(self.out, "    {d} = {t};");
            }
            self.out.push_str("  }\n");
            return;
        }
        if drop && dest.proj.is_empty() && !mentions {
            // The old value is dropped before the new one is written. Safe because the
            // rvalue does not read the destination.
            let (drop_old, refill) = self.drop_old_value(dest, &d, &dt);
            if self.out.len() == body_start {
                self.out.truncate(mark);
                let _ = write!(self.out, " {drop_old} {d} = {value};{refill}");
                for p in &post {
                    let _ = write!(self.out, " {p}");
                }
                self.out.push('\n');
                return;
            }
            let _ = writeln!(self.out, "   {drop_old}\n    {d} = {value};\n   {refill}");
            for p in &post {
                let _ = writeln!(self.out, "    {p}");
            }
            self.out.push_str("  }\n");
            return;
        }
        if drop {
            let t = self.tmp();
            let _ = writeln!(self.out, "    {} {t} = {value};", ctype(&dt));
            for p in &post {
                let _ = writeln!(self.out, "    {p}");
            }
            let (drop_old, refill) = self.drop_old_value(dest, &d, &dt);
            let _ = writeln!(self.out, "   {drop_old}\n    {d} = {t};\n   {refill}");
        } else {
            // A plain local of str type is a compiler place temporary
            // holding the fat value itself; assigning it is a fat copy.
            // A projected str place would be an unsized byte copy.
            if dt == CTy::Str && !dest.proj.is_empty() {
                panic!("unsized assignment");
            }
            if self.out.len() == body_start && post.is_empty() {
                // No helper statements: a plain assignment needs no block.
                self.out.truncate(mark);
                let _ = writeln!(self.out, "  {d} = {value};");
                return;
            }
            let _ = writeln!(self.out, "    {d} = {value};");
            for p in &post {
                let _ = writeln!(self.out, "    {p}");
            }
        }
        self.out.push_str("  }\n");
    }

    fn stmt(&mut self, s: &StmtKind, span: Span) {
        let loc = self.loc(span);
        match s {
            // A byte string temp is a static initialized at its
            // declaration: its one blob assignment never runs.
            StmtKind::Assign(dest, Rvalue::Use(Operand::Const(Const::Bytes(b))))
                if dest.proj.is_empty()
                    && self.byte_blobs.get(dest.local as usize).is_some_and(|x| x.as_ref().is_some_and(|x| x.as_slice() == b.as_slice())) =>
            {
            }
            StmtKind::Assign(dest, rv) => {
                let mentions = rvalue_mentions(rv, dest.local);
                let dest_cty = self.place(dest, &loc).1;
                self.emit_assign(dest, mentions, &loc, |s, loc, post| match rv {
                    // A never value (which shares the unit C form) used
                    // where another type is expected never actually
                    // arrives: give the dead assignment a zero of the
                    // destination type.
                    Rvalue::Use(o) => {
                        let (v, vt) = s.operand(o, loc, post);
                        if vt == CTy::Unit && dest_cty != CTy::Unit { format!("({v}, {})", zero_lit(s.p, &dest_cty)) } else { v }
                    }
                    _ => s.rvalue(rv, loc, post),
                });
            }
            StmtKind::Drop(l) => {
                if self.local_drop[*l as usize] {
                    let what = self.elab_drop(*l, &[]);
                    let _ = writeln!(self.out, "  if (d{l}) {{ d{l} = 0;{what} }}");
                }
            }
            StmtKind::StorageDead(_) | StmtKind::FakeRead(_) => {}
            StmtKind::Print { stderr, newline, parts } => {
                self.out.push_str("  {\n");
                let mut post = Vec::new();
                self.print(parts, *newline, *stderr, &loc, &mut post);
                self.out.push_str("  }\n");
            }
        }
    }

    fn term(&mut self, t: &Terminator, span: Span, next_block: Option<usize>) {
        let loc = self.loc(span);
        let mut post = Vec::new();
        match t {
            Terminator::Goto(b) => {
                let _ = writeln!(self.out, "  goto bb{};", b.0);
            }
            Terminator::If(o, a, b) => {
                let (c, _) = self.operand(o, &loc, &mut post);
                let _ = writeln!(self.out, "  if ({c}) goto bb{}; else goto bb{};", a.0, b.0);
            }
            Terminator::Switch(o, cases, other) => {
                let (c, _) = self.operand(o, &loc, &mut post);
                let _ = write!(self.out, "  switch ({c}) {{");
                for (v, b) in cases {
                    let _ = write!(self.out, " case {v}: goto bb{};", b.0);
                }
                let _ = writeln!(self.out, " default: goto bb{}; }}", other.0);
            }
            Terminator::Call { target, args, dest, next, unwind } => {
                // Calls carry a cleanup (unwind) successor since
                // W-CORELANG. Under panic=abort the C form has no edge to
                // it: a panic in the callee aborts first. Under
                // panic=unwind the call is checked and the edge taken
                // (cgen/unwind.rs); a call without one (a catch
                // boundary) is not checked.
                if self.unw != Some(Unw::Abort) {
                    self.unw = unwind.filter(|_| self.p.unwind).map(|u| Unw::Goto(u.0));
                }
                let mark = self.out.len();
                self.unw_call = true;
                let mentions =
                    args.iter().any(|o| operand_mentions(o, dest.local)) || matches!(target, CallTarget::Indirect(c) if *c == dest.local);
                // A call to a never fn (unit C form) whose destination
                // has another type: the call never returns, so give the
                // dead assignment a zero of the destination type.
                let dest_cty = self.place(dest, &loc).1;
                let ret_unit = match target {
                    CallTarget::Fn(f) => cty(&self.p.tys, self.p.fn_info(*f).ret) == CTy::Unit,
                    CallTarget::Intrinsic(id) => lang::intrinsic(*id).ret == SigTy::Never,
                    CallTarget::Indirect(c) => matches!(&self.local_cty[*c as usize], CTy::FnPtr(_, r) if **r == CTy::Unit),
                    // `resume_unwind` and `panic_any` return `!` (W-UNWIND).
                    CallTarget::Builtin(Builtin::Sync(crate::check::sync::SyncOp::ResumeUnwind | crate::check::sync::SyncOp::PanicAny)) => true,
                    // Lowering gives a dyn call a destination of the
                    // method's own return type.
                    CallTarget::Builtin(_) | CallTarget::Dyn(_) => false,
                };
                if *target == CallTarget::Builtin(Builtin::DefaultGlue) {
                    // The default glue of the destination's type.
                    let v = match &dest_cty {
                        CTy::Unit | CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) => zero_lit(self.p, &dest_cty),
                        t => {
                            self.want(Glue::Default, t);
                            format!("default_{}()", mangle(t))
                        }
                    };
                    self.emit_assign(dest, mentions, &loc, |_, _, _| v);
                } else {
                    self.emit_assign(dest, mentions, &loc, |s, loc, post| {
                        let v = s.call_value(*target, args, &dest_cty, loc, post);
                        if ret_unit && dest_cty != CTy::Unit { format!("({v}, {})", zero_lit(s.p, &dest_cty)) } else { v }
                    });
                }
                self.unw_call = false;
                if let Some(u) = self.unw.take() {
                    let text = unwind::wrap_calls(&self.out[mark..], &u.check());
                    self.out.truncate(mark);
                    self.out.push_str(&text);
                }
                if Some(next.0 as usize) != next_block {
                    let _ = writeln!(self.out, "  goto bb{};", next.0);
                }
            }
            Terminator::Return => {
                if self.ret_large {
                    self.out.push_str("  *out = l0; return;\n")
                } else {
                    self.out.push_str("  return l0;\n")
                }
            }
            // The last block of a cleanup ladder: the frame gives its
            // exception back and leaves (panic=unwind).
            Terminator::Unreachable if self.unw == Some(Unw::Abort) => {
                let _ = writeln!(self.out, "  lust_unw_resume(&ex);\n  {}", self.unwind_return());
            }
            Terminator::Unreachable => self.out.push_str("  abort();\n"),
            Terminator::Panic(parts) => {
                self.out.push_str("  {\n");
                // A message with arguments formats inside the panic (std's
                // lazy payload): a panic while it formats aborts as a
                // nested panic, and a fmt error just ends the text.
                if parts.iter().any(|p| matches!(p, FmtPart::Arg { .. })) {
                    let _ = writeln!(self.out, "    lust_panic_begin({loc});");
                    let s = self.format(parts, &loc, &mut post, 4);
                    let _ = writeln!(self.out, "    lust_panic_fmt(&{s}, {loc});\n  }}");
                } else {
                    // No runtime argument: Rust's `&'static str` payload
                    // (W-STD-B's `fmt_parts` inlines literal arguments).
                    let s = self.format(parts, &loc, &mut post, 0);
                    let _ = writeln!(self.out, "    lust_panic_lit(&{s}, {loc});\n  }}");
                }
                if let Some(Unw::Goto(b)) = self.unw {
                    let _ = writeln!(self.out, "  lust_unw_take(&ex);\n  goto bb{b};");
                }
            }
        }
    }

    // ---------- Rvalues ----------

    /// Records `f` as `bad_callee` when its slot will have no C: every
    /// reference to another fn's slot goes through here first.
    fn note_callee(&mut self, f: LocalDefId) {
        if self.bad_callee.is_none() && !has_generated_body(self.p, f) {
            self.bad_callee = Some(f);
        }
    }

    /// The C text of one call's result value. Every user fn call goes through
    /// `lust_fns`, so a changed function can be swapped in without relinking
    /// its callers.
    fn call_value(&mut self, target: CallTarget, args: &[Operand], dest_cty: &CTy, loc: &str, post: &mut Vec<String>) -> String {
        match target {
            CallTarget::Fn(f) => {
                self.note_callee(f);
                let info = self.p.fn_info(f);
                for &t in info.params.iter().chain(std::iter::once(&info.ret)) {
                    let ct = cty(&self.p.tys, t);
                    collect_types(&ct, &mut self.sig_types);
                }
                let mut args: Vec<String> = args.iter().map(|o| self.operand(o, loc, post).0).collect();
                let dropped: Vec<bool> = info.params.iter().map(|&t| param_dropped(self.p, &cty(&self.p.tys, t))).collect();
                let mut i = 0;
                args.retain(|_| {
                    let keep = !dropped.get(i).copied().unwrap_or(false);
                    i += 1;
                    keep
                });
                // `#[track_caller]`: this call's location, or the one this
                // fn received when it is itself `#[track_caller]` (`loc`).
                if crate::check::caller::is_track_caller(self.p, f) {
                    args.push(loc.to_string());
                }
                if ret_is_large(self.p, f) {
                    let t = self.tmp();
                    let ret = ctype(&cty(&self.p.tys, info.ret));
                    let pre = if args.is_empty() { String::new() } else { format!(", {}", args.join(", ")) };
                    let _ =
                        writeln!(self.out, "    {ret} {t}; ({}lust_fns[{}])(&{t}{pre});", fn_ptr_cast(self.p, f), self.slots[f.0 as usize]);
                    t
                } else {
                    format!("({}lust_fns[{}])({})", fn_ptr_cast(self.p, f), self.slots[f.0 as usize], args.join(", "))
                }
            }
            // `mpsc::channel()`: the element type comes from the pair.
            CallTarget::Builtin(Builtin::Sync(op @ (crate::check::sync::SyncOp::Channel | crate::check::sync::SyncOp::SyncChannel))) => {
                let cap = if op == crate::check::sync::SyncOp::SyncChannel { format!("(int64_t){}", self.operand(&args[0], loc, post).0) } else { "-1".into() };
                self.channel_new(dest_cty, &cap)
            }
            // `Mutex::default()`: the lock's Default glue (W-THREADS).
            CallTarget::Builtin(Builtin::Sync(crate::check::sync::SyncOp::LockDefault(_) | crate::check::sync::SyncOp::SyncNew(crate::ty::sync::SyncTy::OnceLock))) => {
                self.want(Glue::Default, dest_cty);
                format!("default_{}()", mangle(dest_cty))
            }
            // A slice-to-array `TryFrom` (tf-slice): the destination
            // `Result` type tells the array length and whether the
            // Ok form is the array or a reference to it.
            CallTarget::Builtin(Builtin::SliceTryInto) => {
                let (sv, sct) = self.operand(&args[0], loc, post);
                let CTy::Result(ok, err) = dest_cty.clone() else { unreachable!() };
                let (arr, by_ref) = match &*ok {
                    CTy::Array(..) => ((*ok).clone(), false),
                    CTy::Ref(a) => ((**a).clone(), true),
                    _ => unreachable!(),
                };
                let CTy::Array(_, n) = &arr else { unreachable!() };
                let n = *n;
                let (ptr, len) = match &sct {
                    CTy::Slice(_) => (format!("{sv}.ptr"), format!("{sv}.len")),
                    CTy::Ref(inner) if matches!(&**inner, CTy::Slice(_)) => (format!("{sv}->ptr"), format!("{sv}->len")),
                    _ => unreachable!(),
                };
                let (ok_ct, err_ct) = (ctype(&ok), ctype(&err));
                let res = CTy::Result(ok, err);
                collect_types(&res, &mut self.sig_types);
                let (t, i) = (self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(self.p, &res, &t, 0, 0), variant_field(self.p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(self.p, &res, &t, 0), disc_set(self.p, &res, &t, 1));
                let ok_assign = if by_ref {
                    format!("{ok_f} = ({ok_ct}){ptr};")
                } else {
                    format!("for (uint64_t {i} = 0; {i} < {n}; {i}++) {ok_f}.v[{i}] = {ptr}[{i}];")
                };
                let te = self.tmp();
                let _ = writeln!(self.out, "    {} {t}; {err_ct} {te}; {te}.f0 = ((lust_Unit){{}});", ctype(&res));
                let _ = writeln!(self.out, "    if ({len} == {n}) {{ {ok_assign} {ok_d} }} else {{ {err_f} = {te}; {err_d} }}");
                t
            }
            CallTarget::Builtin(Builtin::Sync(crate::check::sync::SyncOp::ChanTrySend)) => self.chan_try_send(args, dest_cty, loc, post),
            CallTarget::Builtin(b) => match self.hash_builtin(b, args, dest_cty, loc, post) {
                Some(v) => v,
                None => match self.split_builtin(b, args, dest_cty, loc, post) {
                    Some(v) => v,
                    None => self.builtin(b, args, loc, post),
                },
            },
            CallTarget::Intrinsic(id) => self.intrinsic(id, args, loc, post),
            CallTarget::Dyn(k) => {
                // Through the vtable: entry `k` is a shim whose receiver
                // is the erased data pointer (see `vtable_shim`). The
                // return type is the destination's, which lowering made
                // the method's own.
                let (r, _) = self.operand(&args[0], loc, post);
                let rt = self.tmp();
                let _ = writeln!(self.out, "    lust_dyn {rt} = {r};");
                let mut vals: Vec<String> = Vec::new();
                let mut tys: Vec<String> = vec!["void *".into()];
                for o in &args[1..] {
                    let (v, t) = self.operand(o, loc, post);
                    collect_types(&t, &mut self.sig_types);
                    if !param_dropped(self.p, &t) {
                        tys.push(ctype(&t));
                        vals.push(v);
                    }
                }
                let ret = dest_cty.clone();
                collect_types(&ret, &mut self.sig_types);
                let rc = ctype(&ret);
                let pre: String = vals.iter().map(|v| format!(", {v}")).collect();
                if ret_by_out(self.p, &ret) {
                    let t = self.tmp();
                    let _ =
                        writeln!(self.out, "    {rc} {t}; ((void (*)({rc} *, {}))({rt}.vt[{k}]))(&{t}, {rt}.data{pre});", tys.join(", "));
                    t
                } else {
                    format!("(({rc} (*)({}))({rt}.vt[{k}]))({rt}.data{pre})", tys.join(", "))
                }
            }
            CallTarget::Indirect(callee) => {
                let ct = self.local_cty[callee as usize].clone();
                let CTy::FnPtr(ps, ret) = &ct else { panic!("indirect call through a non-fn-pointer local") };
                collect_types(&ct, &mut self.sig_types);
                let mut args: Vec<String> = args.iter().map(|o| self.operand(o, loc, post).0).collect();
                let dropped: Vec<bool> = ps.iter().map(|t| param_dropped(self.p, t)).collect();
                let mut i = 0;
                args.retain(|_| {
                    let keep = !dropped.get(i).copied().unwrap_or(false);
                    i += 1;
                    keep
                });
                if ret_by_out(self.p, ret) {
                    let t = self.tmp();
                    let rt = ctype(ret);
                    let pre = if args.is_empty() { String::new() } else { format!(", {}", args.join(", ")) };
                    let _ = writeln!(self.out, "    {rt} {t}; l{callee}(&{t}{pre});");
                    t
                } else {
                    format!("l{callee}({})", args.join(", "))
                }
            }
        }
    }

    /// Builds one enum or Option value as one compound literal that
    /// designates a single union member: the variant struct, which
    /// carries the explicit tag or the niche scalar as a member of
    /// its own, so tag and fields are set by the same designator.
    /// The same forms serve as constant initializers in `const_init`.
    fn make_variant(&mut self, t: &CTy, variant: usize, vals: &[String]) -> String {
        variant_lit(self.p, t, variant, vals)
    }

    fn rvalue(&mut self, rv: &Rvalue, loc: &str, post: &mut Vec<String>) -> String {
        match rv {
            Rvalue::Use(o) => self.operand(o, loc, post).0,
            Rvalue::Ref(_, pl) => {
                let (e, t) = self.place(pl, loc);
                // A slice place (a deref of a fat value, or a bare-slice
                // temporary from a range index) is already the fat value;
                // a place holding a slice reference takes an address as usual.
                // The C form cannot tell a `&[T]`/`&dyn` value from the
                // unsized place behind it, so ask the place's own type:
                // `&*r` for `r: &&dyn Tr` borrows the `&dyn` value.
                // An unsized newtype (`OsStr`, `Path`; W-SHIM) is laid out as
                // its slice field, so its place is a slice place too.
                let tys = &self.body.tys;
                let slice_like = |k: TyKind| match k {
                    TyKind::Slice(_) => true,
                    TyKind::Adt(d, _) => tys.unsized_field(d).is_some(),
                    _ => false,
                };
                let sem = self.place_sem_ty(pl).map(|ty| tys.kind(ty));
                let slice_place = matches!(t, CTy::Slice(_) | CTy::Unsized(..))
                    && match sem {
                        Some(k) => slice_like(k),
                        None => matches!(pl.proj.last(), Some(Proj::Deref)) || slice_like(tys.kind(self.body.locals[pl.local as usize].ty)),
                    };
                let dyn_place = t == CTy::Dyn
                    && match sem {
                        Some(k) => matches!(k, TyKind::Dyn(..)),
                        None => matches!(pl.proj.last(), Some(Proj::Deref)),
                    };
                // So is a `RefCell<dyn Tr>` place (cgen/own.rs).
                let cell_place = matches!(t, CTy::DynCell | CTy::DynLock(false))
                    && match self.place_sem_ty(pl) {
                        Some(ty) => crate::check::own::dyn_wrapped_elem(tys, ty).is_some(),
                        None => matches!(pl.proj.last(), Some(Proj::Deref)),
                    };
                if t == CTy::Str || slice_place || dyn_place || cell_place { e } else { format!("(&{e})") }
            }
            Rvalue::SliceOf(pl) => {
                let (e, t) = self.place(pl, loc);
                self.slice_of(&e, &t)
            }
            Rvalue::Subslice { base, lo, hi, inclusive, .. } => {
                let (e, t) = self.place(base, loc);
                let (ptr, len) = self.slice_ptr_len(&e, &t);
                let (lo_v, _) = self.operand(lo, loc, post);
                let ct = match &t {
                    CTy::Array(el, _) | CTy::Slice(el) | CTy::Vec(el) => ctype(&CTy::Slice(el.clone())),
                    _ => "lust_str".into(),
                };
                let (tmp, end) = (self.tmp(), self.tmp());
                let hi_v = match hi {
                    Some(h) => self.operand(h, loc, post).0,
                    None => len.clone(),
                };
                let incl = if *inclusive { 1 } else { 0 };
                // A str or String base slices to a str: the runtime
                // check also validates the char boundaries.
                let range_fn = if matches!(t, CTy::Str | CTy::String) { "lust_str_range" } else { "lust_slice_range" };
                let range_args = if range_fn == "lust_str_range" {
                    format!("{ptr}, {lo_v}, {hi_v}, {incl}, {len}, {loc}")
                } else {
                    format!("{lo_v}, {hi_v}, {incl}, {len}, {loc}")
                };
                let _ = writeln!(self.out, "    uint64_t {end} = {range_fn}({range_args});");
                let _ = writeln!(self.out, "    {ct} {tmp} = {{ {ptr} + {lo_v}, {end} - {lo_v} }};");
                tmp
            }
            Rvalue::Bin(op, a, b) => {
                let (a, at) = self.operand(a, loc, post);
                let (b, bt) = self.operand(b, loc, post);
                self.bin(*op, &a, &at, &b, &bt, loc)
            }
            Rvalue::Un(op, a) => {
                let (a, at) = self.operand(a, loc, post);
                match (op, &at) {
                    (UnOp::Neg, CTy::Float(_)) => format!("(-{a})"),
                    (UnOp::Neg, CTy::Int(i)) => format!("lust_neg_{}({a}, {loc})", int_fn(*i)),
                    (UnOp::Not, CTy::Bool) => format!("(!{a})"),
                    (UnOp::Not, CTy::Int(i)) if is128(*i) => format!("lust_{}_not({a})", int_fn(*i)),
                    (UnOp::Not, CTy::Int(i)) => format!("(({})~{a})", int_c(*i)),
                    _ => panic!("bad unary op"),
                }
            }
            Rvalue::Cast(o, to) => {
                let (a, from) = self.operand(o, loc, post);
                let to = cty(&self.body.tys, *to);
                // Casts to or from a 128-bit struct value are not C casts.
                match (&from, &to) {
                    // Float casts go through the runtime helpers so rounding
                    // and saturation match Rust exactly (src/runtime/float.h).
                    (CTy::Float(f), CTy::Float(g)) => {
                        if f == g {
                            a
                        } else if *f == FloatTy::F64 {
                            format!("lust_f64_to_f32({a})")
                        } else {
                            format!("lust_f32_to_f64({a})")
                        }
                    }
                    (CTy::Float(f), CTy::Int(ti)) if is128(*ti) => {
                        let t = self.tmp();
                        let _ = writeln!(self.out, "    {} {t}; lust_{}_to_{}({a}, &{t}.lo, &{t}.hi);", int_c(*ti), f.name(), int_fn(*ti));
                        t
                    }
                    (CTy::Float(f), CTy::Int(ti)) => format!("lust_{}_to_{}({a})", f.name(), int_fn(*ti)),
                    (CTy::Float(f), CTy::Char) => format!("((uint32_t)lust_{}_to_u32({a}))", f.name()),
                    (CTy::Int(fi), CTy::Float(g)) if is128(*fi) => {
                        format!("lust_{}_to_{}(({a}).lo, ({a}).hi)", int_fn(*fi), g.name())
                    }
                    (CTy::Int(fi), CTy::Float(g)) => {
                        if fi.signed() {
                            format!("lust_i64_to_{}((int64_t)({a}))", g.name())
                        } else {
                            format!("lust_u64_to_{}((uint64_t)({a}))", g.name())
                        }
                    }
                    (CTy::Bool | CTy::Char, CTy::Float(g)) => {
                        format!("lust_u64_to_{}((uint64_t)({a}))", g.name())
                    }
                    (CTy::Int(fi), CTy::Int(ti)) if is128(*fi) && is128(*ti) => {
                        if fi == ti {
                            a
                        } else {
                            format!("lust_{}_from_{}({a})", int_fn(*ti), int_fn(*fi))
                        }
                    }
                    (CTy::Int(fi), _) if is128(*fi) => format!("(({})(({a}).lo))", ctype(&to)),
                    (CTy::Adt(aid), CTy::Int(ti)) => {
                        // A fieldless enum cast to an integer gives its
                        // discriminant value. Layout types store the value
                        // in the tag, so read it back; legacy types store
                        // the variant index, so map index to value.
                        let adt = self.p.adt(*aid);
                        let ct = ctype(&to);
                        // A 16-byte tag is a two-word struct: a cast to a
                        // 128-bit int copies both words (the bit pattern
                        // is the discriminant), and a cast to a smaller
                        // int reads the low word.
                        let wide = match c_layout(self.p, &from) {
                            Some(l) if matches!(l.enum_tag, Some(EnumTag::Explicit { size, .. }) if size >= 16) => Some(if is128(*ti) {
                                format!("(({}){{({a}).u._tag.lo, ({a}).u._tag.hi}})", int_c(*ti))
                            } else {
                                format!("(({ct})(({a}).u._tag.lo))")
                            }),
                            _ => None,
                        };
                        let raw = match c_layout(self.p, &from) {
                            Some(l) => match l.enum_tag {
                                Some(EnumTag::Explicit { signed, .. }) => Some((format!("(({a}).u._tag)"), signed)),
                                _ => {
                                    let d = adt.variants.first().map_or(0, |v| v.disc);
                                    Some((disc_lit(d, 8, d < 0), d < 0))
                                }
                            },
                            None => None,
                        };
                        match (wide, raw) {
                            (Some(w), _) => w,
                            (None, Some((raw, raw_signed))) => {
                                if is128(*ti) {
                                    if raw_signed {
                                        format!("(({}){{(uint64_t)(int64_t)({raw}), (uint64_t)((int64_t)({raw}) >> 63)}})", int_c(*ti))
                                    } else {
                                        format!("(({}){{(uint64_t)({raw}), 0}})", int_c(*ti))
                                    }
                                } else {
                                    format!("(({ct})({raw}))")
                                }
                            }
                            (None, None) => {
                                let t = self.tmp();
                                let zero = if is128(*ti) { "{0, 0}" } else { "0" };
                                let _ = write!(self.out, "    {ct} {t} = {zero};\n    switch ({a}.tag) {{");
                                for (vi, v) in adt.variants.iter().enumerate() {
                                    let lit = if is128(*ti) {
                                        let bits = v.disc as u128;
                                        format!("(({ct}){{{}ULL, {}ULL}})", bits as u64, (bits >> 64) as u64)
                                    } else if v.disc < 0 {
                                        format!("(({ct})((int64_t){}))", v.disc)
                                    } else {
                                        format!("(({ct})((uint64_t){}ull))", v.disc as u128)
                                    };
                                    let _ = write!(self.out, " case {vi}: {t} = {lit}; break;");
                                }
                                let _ = writeln!(self.out, " }}");
                                t
                            }
                        }
                    }
                    (_, CTy::Int(ti)) if is128(*ti) => {
                        let signed = matches!(&from, CTy::Int(si) if si.signed());
                        if signed {
                            format!("(({}){{(uint64_t)(int64_t)({a}), (uint64_t)((int64_t)({a}) >> 63)}})", int_c(*ti))
                        } else {
                            format!("(({}){{(uint64_t)({a}), 0}})", int_c(*ti))
                        }
                    }
                    _ => format!("(({}){a})", ctype(&to)),
                }
            }
            Rvalue::Res(ty, is_ok, op) => {
                let t = cty(&self.body.tys, *ty);
                let (v, _) = self.operand(op, loc, post);
                self.make_variant(&t, (!*is_ok) as usize, &[v])
            }
            Rvalue::Opt(ty, op) => {
                let t = cty(&self.body.tys, *ty);
                match op {
                    Some(o) => {
                        let (v, _) = self.operand(o, loc, post);
                        self.make_variant(&t, 1, &[v])
                    }
                    None => self.make_variant(&t, 0, &[]),
                }
            }
            Rvalue::Aggregate(a, v, ops) => {
                let adt = self.p.adt(*a);
                let vals: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                if adt.is_enum {
                    self.make_variant(&CTy::Adt(*a), *v as usize, &vals)
                } else if vals.is_empty() {
                    zero_lit(self.p, &CTy::Adt(*a))
                } else {
                    let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                    format!("((A{}){{ {} }})", a.0, fields.join(", "))
                }
            }
            Rvalue::VecLit(elem, ops) => {
                let et = ctype(&cty(&self.body.tys, *elem));
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_Vec {t} = lust_vec_with_capacity({}, sizeof({et}), _Alignof({et}));", ops.len());
                for (i, o) in ops.iter().enumerate() {
                    let (v, _) = self.operand(o, loc, post);
                    let _ = writeln!(self.out, "    (({et}*){t}.ptr)[{i}] = {v};");
                }
                let _ = writeln!(self.out, "    {t}.len = {};", ops.len());
                t
            }
            Rvalue::VecRepeat(elem, x, n) => {
                let ec = cty(&self.body.tys, *elem);
                let et = ctype(&ec);
                let (xv, _) = self.operand(x, loc, post);
                let (nv, _) = self.operand(n, loc, post);
                let (t, xt, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {et} {xt} = {xv};\n    uint64_t {i}_n = {nv};");
                let _ = writeln!(self.out, "    lust_Vec {t} = lust_vec_with_capacity({i}_n, sizeof({et}), _Alignof({et}));");
                let clone = if is_copy_c(self.p, &ec) {
                    xt.to_string()
                } else {
                    self.want(Glue::Clone, &ec);
                    format!("clone_{}(&{xt})", mangle(&ec))
                };
                // Clone n-1 times, then move the original into the last slot (as Rust does).
                let _ = writeln!(self.out, "    for (uint64_t {i} = 0; {i} + 1 < {i}_n; {i}++) (({et}*){t}.ptr)[{i}] = {clone};");
                let _ = write!(self.out, "    if ({i}_n) (({et}*){t}.ptr)[{i}_n - 1] = {xt};");
                if needs_drop_c(self.p, &ec) {
                    self.want(Glue::Drop, &ec);
                    let _ = write!(self.out, " else drop_{}(&{xt});", mangle(&ec));
                }
                let _ = writeln!(self.out, "\n    {t}.len = {i}_n;");
                t
            }
            Rvalue::Eq { a, b, ty, ne } => {
                let (a, at) = self.operand(a, loc, post);
                let (b, bt) = self.operand(b, loc, post);
                // A slice operand is already the fat value (not a pointer to
                // it), so take its address for the glue call.
                let a = if matches!(at, CTy::Slice(_) | CTy::Unsized(..)) { format!("(&{a})") } else { a };
                let b = if matches!(bt, CTy::Slice(_) | CTy::Unsized(..)) { format!("(&{b})") } else { b };
                let t = cty(&self.body.tys, *ty);
                let e = self.eq_expr(&t, &a, &b);
                if *ne { format!("(!{e})") } else { e }
            }
            Rvalue::Cmp { op, a, b, ty } => {
                let (a, at) = self.operand(a, loc, post);
                let (b, bt) = self.operand(b, loc, post);
                let a = if matches!(at, CTy::Slice(_) | CTy::Unsized(..)) { format!("(&{a})") } else { a };
                let b = if matches!(bt, CTy::Slice(_) | CTy::Unsized(..)) { format!("(&{b})") } else { b };
                let t = cty(&self.body.tys, *ty);
                self.want(Glue::Cmp, &t);
                let c = format!("cmp_{}({a}, {b})", mangle(&t));
                // The code is -1, 0, 1, or 2 (unordered): every
                // operator is false on 2, as in `PartialOrd`.
                match op {
                    BinOp::Lt => format!("({c} == -1)"),
                    BinOp::Gt => format!("({c} == 1)"),
                    BinOp::Le => format!("((uint8_t)({c} + 1) <= 1)"),
                    _ => format!("((uint8_t){c} <= 1)"),
                }
            }
            Rvalue::StrCmp(op, a, b) => {
                let (a, _) = self.operand(a, loc, post);
                let (b, _) = self.operand(b, loc, post);
                match op {
                    BinOp::Eq => format!("lust_str_eq({a}, {b})"),
                    BinOp::Ne => format!("(!lust_str_eq({a}, {b}))"),
                    _ => format!("(lust_str_cmp({a}, {b}) {} 0)", op.symbol()),
                }
            }
            Rvalue::StringAdd(a, b) => {
                let (a, _) = self.operand(a, loc, post);
                let (b, _) = self.operand(b, loc, post);
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_String {t} = {a};\n    lust_string_push_str(&{t}, {b});");
                t
            }
            Rvalue::TupleAgg(ty, ops) => {
                let t = cty(&self.body.tys, *ty);
                let ct = ctype(&t);
                let vals: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                if vals.is_empty() {
                    zero_lit(self.p, &t)
                } else {
                    let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                    format!("(({ct}){{ {} }})", fields.join(", "))
                }
            }
            Rvalue::ArrayAgg(ty, ops) => {
                let t = cty(&self.body.tys, *ty);
                let ct = ctype(&t);
                let vals: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                if vals.is_empty() { zero_lit(self.p, &t) } else { format!("(({ct}){{ .v = {{ {} }} }})", vals.join(", ")) }
            }
            Rvalue::ArrayRepeat(ty, o, n) => {
                let at = cty(&self.body.tys, *ty);
                let ct = ctype(&at);
                let et = match &at {
                    CTy::Array(e, _) => ctype(e),
                    _ => "uint8_t".into(),
                };
                let (v, _) = self.operand(o, loc, post);
                let (t, xt, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {et} {xt} = {v};\n    {ct} {t};");
                let _ = writeln!(self.out, "    for (uint64_t {i} = 0; {i} < {n}; {i}++) {t}.v[{i}] = {xt};");
                t
            }
            Rvalue::Format(parts) => self.format(parts, loc, post, 0),
            Rvalue::WriteFmt(dst, parts, stream) => self.write_fmt(dst, parts, *stream, loc, post),
            Rvalue::Discriminant(pl) => {
                let (e, t) = self.place(pl, loc);
                disc_call(self.p, &t, &format!("(&{e})"))
            }
            Rvalue::StaticLoad(idx) => static_sym(self.p, *idx),
            Rvalue::StaticRef(idx) => format!("(&{})", static_sym(self.p, *idx)),
            Rvalue::LenOf(pl) => {
                let (e, t) = self.place(pl, loc);
                match &t {
                    CTy::Array(_, n) => n.to_string(),
                    CTy::Slice(_) | CTy::Vec(_) | CTy::String | CTy::Str => format!("{e}.len"),
                    CTy::Ref(inner) if **inner == CTy::Str => format!("{e}.len"),
                    _ => format!("({e})->len"),
                }
            }
            Rvalue::FnValue(f, ty) => {
                let t = cty(&self.body.tys, *ty);
                match t {
                    CTy::FnPtr(..) => {
                        self.note_callee(*f);
                        collect_types(&t, &mut self.sig_types);
                        format!("(({})lust_tramps[{}])", ctype(&t), self.slots[f.0 as usize])
                    }
                    // A bare fn item value is a zero-sized type.
                    CTy::Unit => "((lust_Unit){})".into(),
                    _ => "0".into(),
                }
            }
            Rvalue::MakeDyn { ptr, src, dyn_ty } => {
                let (v, ct) = self.operand(ptr, loc, post);
                // An Rc or Arc points the fat value at its value, after the counts.
                let at_value = matches!(ct, CTy::Rc(_) | CTy::Sync(crate::ty::sync::SyncTy::Arc, _));
                // `Box<[T; N]>`, `Rc<[T; N]>`, or `Arc<[T; N]>` to the
                // `[T]` form: the element pointer and the constant length.
                if let TyKind::Slice(e) = self.body.tys.kind(*dyn_ty) {
                    let n = match cty(&self.body.tys, *src) {
                        CTy::Array(_, n) => n,
                        other => unreachable!("an owning slice from {other:?}"),
                    };
                    let sl = CTy::Slice(Box::new(cty(&self.body.tys, e)));
                    collect_types(&sl, &mut self.sig_types);
                    let (st, et) = (ctype(&sl), ctype(&cty(&self.body.tys, e)));
                    let data = if at_value { format!("&({v})->v") } else { format!("({v})") };
                    return format!("(({st}){{ ({et}*)({data}), {n} }})");
                }
                let vid = crate::check::generics::vtable_for(self.p, &self.body.tys, *src, *dyn_ty)
                    .expect("mono builds a vtable for every unsizing coercion in a concrete body");
                let vt = self.vtable_sym(vid);
                // An `Rc<T>` source points the data at the value in its
                // allocation (`Rc<dyn Tr>` finds the counts before it);
                // a `Weak<T>` too, unless it dangles (`Weak::new()`).
                let data = match ct {
                    _ if at_value => format!("&({v})->v"),
                    CTy::Weak(_) | CTy::Sync(crate::ty::sync::SyncTy::ArcWeak, _) => {
                        format!("(({v}) == (void *)~(uintptr_t)0 ? (void *)~(uintptr_t)0 : (void *)&({v})->v)")
                    }
                    _ => format!("({v})"),
                };
                format!("((lust_dyn){{ (void *){data}, {vt} }})")
            }
            Rvalue::DynUpcast { ptr, path } => {
                let (v, _) = self.operand(ptr, loc, post);
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_dyn {t} = {v};");
                for k in path {
                    let _ = writeln!(self.out, "    {t}.vt = (const void *const *){t}.vt[{k}];");
                }
                t
            }
            Rvalue::DynMeta { ptr, word } => {
                let (v, _) = self.operand(ptr, loc, post);
                format!("((uint64_t)(uintptr_t)({v}).vt[{word}])")
            }
            Rvalue::DynData { ptr, ty } => {
                let (v, _) = self.operand(ptr, loc, post);
                let ct = cty(&self.body.tys, *ty);
                match &ct {
                    // An `Rc<T>` points at its allocation, the counts first.
                    CTy::Rc(e) => {
                        let rc = format!("RcI_{}", mangle(e));
                        format!("(({rc} *)((char *)({v}).data - (uintptr_t)&(({rc} *)0)->v))")
                    }
                    _ => format!("(({})({v}).data)", ctype(&ct)),
                }
            }
        }
    }

    /// The semantic type of a place, through derefs, fields, variants,
    /// and indexes. None for a projection this walk does not follow.
    fn place_sem_ty(&self, pl: &Place) -> Option<Ty> {
        let tys = &self.body.tys;
        let mut t = self.body.locals[pl.local as usize].ty;
        let mut variant = 0usize;
        for pr in &pl.proj {
            t = match (tys.kind(t), pr) {
                (TyKind::Ref(_, _, inner), Proj::Deref) => inner,
                (_, Proj::Downcast(v)) => {
                    variant = *v as usize;
                    continue;
                }
                (TyKind::Tuple(ts), Proj::Field(i)) => *tys.tys_of(ts).get(*i as usize)?,
                (TyKind::Adt(..), Proj::Field(i)) => match tys.local_adt(t) {
                    Some(a) => self.p.adt(a).variants.get(variant)?.fields.get(*i as usize)?.ty,
                    None => tys.option_elem(t)?,
                },
                (TyKind::Array(e, _) | TyKind::Slice(e), Proj::Index(_)) => e,
                (_, Proj::Index(_)) => tys.vec_elem(t)?,
                _ => return None,
            };
            variant = 0;
        }
        Some(t)
    }

    /// The C name of vtable `vid` in this function, emitting it (and the
    /// super vtables it points at) into the prelude on first use. See
    /// `check::object` for the word layout.
    fn vtable_sym(&mut self, vid: u32) -> String {
        if let Some(s) = self.vtables.get(&vid) {
            return s.clone();
        }
        let p = self.p;
        let vt = p.gx.vtables[vid as usize].clone();
        let supers: Vec<String> = vt.supers.iter().map(|&s| self.vtable_sym(s)).collect();
        let fslot = self.slots[self.body.fn_id.0 as usize];
        let name = format!("vt{fslot}_{vid}");
        let ct = cty(&p.tys, vt.self_ty);
        let drop = if needs_drop_c(p, &ct) {
            self.want(Glue::Drop, &ct);
            format!("(void *)drop_{}", mangle(&ct))
        } else {
            "0".to_string()
        };
        let (size, align) = match layout::layout_of_ty(&p.tys, p, vt.self_ty) {
            Ok(l) => (l.size, l.align),
            Err(()) => c_size_align(p, &ct),
        };
        let mut words = vec![drop, format!("(void *)(uintptr_t){size}"), format!("(void *)(uintptr_t){align}")];
        // The fmt header shims (`VT_FMT_DEBUG`, `VT_FMT_DISPLAY` in
        // check/object.rs): the concrete type's fmt glue behind a
        // principal with that supertrait, else 0.
        let info = p.gx.dyn_infos.get(&vt.principal.def);
        for (has, kind) in
            [(info.is_some_and(|i| i.fmt_debug), FmtKind::Debug), (info.is_some_and(|i| i.fmt_display), FmtKind::Display)]
        {
            if has {
                let shim = self.vt_fmt_shim(&name, &ct, kind);
                words.push(format!("(void *){shim}"));
            } else {
                words.push("0".to_string());
            }
        }
        words.extend(supers.iter().map(|s| format!("(void *){s}")));
        // A `dyn Any` vtable holds the value's type id (`object::VT_ANY_ID`).
        if vt.principal.def == p.gx.lang.any {
            let (lo, hi) = crate::check::any::type_id_words(p, &p.tys, vt.self_ty);
            words.extend([format!("(void *)(uintptr_t){lo}ull"), format!("(void *)(uintptr_t){hi}ull")]);
        }
        // A `dyn FnOnce` vtable's call entry consumes the value and
        // frees the box it lives in (ARCH 2.9): the only call is
        // through `Box<dyn FnOnce>` by value.
        let consume = (vt.principal.def == p.gx.lang.fn_once).then_some(vt.self_ty);
        if matches!(p.tys.kind(vt.self_ty), TyKind::FnDef(..) | TyKind::FnPtr(_)) {
            // A fn item or fn pointer as a `dyn Fn` value: no env.
            let shim = self.fn_value_shim(&name, &vt, consume.is_some());
            words.push(format!("(void *){shim}"));
        } else {
            for (j, &f) in vt.methods.iter().enumerate() {
                let shim = self.vtable_shim(&name, j, f, consume);
                words.push(format!("(void *){shim}"));
            }
        }
        let tn = crate::check::object::trait_name(p, vt.principal.def);
        let _ = writeln!(self.prelude, "/* vtable: {} as {tn} */", ty_name(p, &p.tys, vt.self_ty));
        let _ = writeln!(self.prelude, "static const void *const {name}[] = {{ {} }};", words.join(", "));
        self.vtables.insert(vid, name.clone());
        name
    }

    /// One fmt header shim: formats the erased value with the concrete
    /// type's own Debug or Display glue (`fmt_expr` on its C type), in
    /// the `int (void *self, lust_Formatter *f)` shape the fmt glue
    /// calls through `VT_FMT_DEBUG` / `VT_FMT_DISPLAY`.
    fn vt_fmt_shim(&mut self, vt_name: &str, ct: &CTy, kind: FmtKind) -> String {
        let name = format!("{vt_name}_fmt{}", if kind == FmtKind::Debug { "D" } else { "S" });
        collect_types(ct, &mut self.sig_types);
        let v = format!("(({ }*)self)", ctype(ct));
        let e = fmt::fmt_expr(ct, kind, "f", &v, &mut |g, t| self.want(g, t));
        let _ = writeln!(self.prelude, "static int {name}(void *self, lust_Formatter *f) {{ return {e}; }}");
        name
    }

    /// The call entry of a `dyn Fn` vtable whose value is a fn item (a
    /// zero-sized value: the shim calls the fn through `lust_fns[slot]`,
    /// ignoring the data pointer) or a fn pointer (the shim calls the
    /// pointer stored at the data pointer). With `consume` (a `dyn
    /// FnOnce`) the shim then frees the box.
    fn fn_value_shim(&mut self, vt_name: &str, vt: &crate::check::object::VtableData, consume: bool) -> String {
        let p = self.p;
        let name = format!("{vt_name}_m0");
        let ct = cty(&p.tys, vt.self_ty);
        let cts = ctype(&ct);
        let (params, ret, call) = match (p.tys.kind(vt.self_ty), &ct) {
            (TyKind::FnPtr(_), CTy::FnPtr(ps, r)) => {
                collect_types(&ct, &mut self.sig_types);
                (ps.clone(), (**r).clone(), format!("(*({cts}*)self)"))
            }
            _ => {
                let Some(&f) = vt.methods.first() else { return "0".to_string() };
                self.note_callee(f);
                let info = p.fn_info(f);
                let params: Vec<CTy> = info.params.iter().map(|&t| cty(&p.tys, t)).collect();
                for t in &params {
                    collect_types(t, &mut self.sig_types);
                }
                let call = format!("({}lust_fns[{}])", fn_ptr_cast(p, f), self.slots[f.0 as usize]);
                (params, cty(&p.tys, info.ret), call)
            }
        };
        collect_types(&ret, &mut self.sig_types);
        let rt = ctype(&ret);
        let decls: String = params.iter().enumerate().map(|(i, t)| format!(", {} a{i}", ctype(t))).collect();
        let names: Vec<String> = (0..params.len()).map(|i| format!("a{i}")).collect();
        let free = if consume { format!(" lust_dealloc(self, sizeof({cts}), _Alignof({cts}));") } else { String::new() };
        if ret_by_out(p, &ret) {
            let args: String = std::iter::once("out".to_string()).chain(names).collect::<Vec<_>>().join(", ");
            let _ = writeln!(self.prelude, "static void {name}({rt} *out, void *self{decls}) {{ {call}({args});{free} }}");
        } else {
            let args = names.join(", ");
            let _ = writeln!(self.prelude, "static {rt} {name}(void *self{decls}) {{ {rt} r = {call}({args});{free} (void)self; return r; }}");
        }
        name
    }

    /// One vtable method entry: a shim that takes the erased receiver and
    /// forwards through `lust_fns[slot]`, so the entry never names a body
    /// an overlay could replace (ARCH 4.5). Its C signature is the
    /// method's with `void *` for the receiver; dyn call sites cast the
    /// entry to that shape. With `consume` (the concrete type of a `dyn
    /// FnOnce` vtable) the shim takes the value out of the box (an
    /// `FnOnce` closure's by-value env) or drops it after the call (an
    /// `Fn`/`FnMut` closure's), then frees the box.
    fn vtable_shim(&mut self, vt_name: &str, j: usize, f: LocalDefId, consume: Option<Ty>) -> String {
        self.note_callee(f);
        let p = self.p;
        let info = p.fn_info(f);
        for &t in info.params.iter().chain(std::iter::once(&info.ret)) {
            collect_types(&cty(&p.tys, t), &mut self.sig_types);
        }
        let name = format!("{vt_name}_m{j}");
        let ret = ctype(&cty(&p.tys, info.ret));
        let cast = fn_ptr_cast(p, f);
        let slot = self.slots[f.0 as usize];
        let recv = ctype(&cty(&p.tys, info.params[0]));
        let recv_dropped = param_dropped(p, &cty(&p.tys, info.params[0]));
        let mut decls: Vec<String> = Vec::new();
        let mut rest: Vec<String> = Vec::new();
        for (i, &t) in info.params.iter().enumerate().skip(1) {
            if param_dropped(p, &cty(&p.tys, t)) {
                continue;
            }
            decls.push(format!("{} a{i}", ctype(&cty(&p.tys, t))));
            rest.push(format!("a{i}"));
        }
        let decls = decls.iter().map(|d| format!(", {d}")).collect::<String>();
        if let Some(self_ty) = consume {
            let ct = cty(&p.tys, self_ty);
            let cts = ctype(&ct);
            let by_value = !matches!(p.tys.kind(info.params[0]), TyKind::Ref(..));
            let env = if by_value { format!("*({cts}*)self") } else { format!("({recv})self") };
            let drop = if !by_value && needs_drop_c(p, &ct) {
                self.want(Glue::Drop, &ct);
                format!("drop_{}(({cts}*)self); ", mangle(&ct))
            } else {
                String::new()
            };
            let free = format!("lust_dealloc(self, sizeof({cts}), _Alignof({cts}));");
            let mut call: Vec<String> = Vec::new();
            if !recv_dropped {
                call.push(env);
            }
            call.extend(rest.iter().cloned());
            let call = call.join(", ");
            if ret_is_large(p, f) {
                let rest = if call.is_empty() { String::new() } else { format!(", {call}") };
                let _ = writeln!(
                    self.prelude,
                    "static void {name}({ret} *out, void *self{decls}) {{ ({cast}lust_fns[{slot}])(out{rest}); {drop}{free} }}"
                );
            } else {
                let _ = writeln!(
                    self.prelude,
                    "static {ret} {name}(void *self{decls}) {{ {ret} r = ({cast}lust_fns[{slot}])({call}); {drop}{free} return r; }}"
                );
            }
            return name;
        }
        let mut names: Vec<String> = Vec::new();
        if !recv_dropped {
            names.push(format!("({recv})self"));
        }
        names.extend(rest);
        let names = names.join(", ");
        if ret_is_large(p, f) {
            let rest = if names.is_empty() { String::new() } else { format!(", {names}") };
            let _ = writeln!(
                self.prelude,
                "static void {name}({ret} *out, void *self{decls}) {{ ({cast}lust_fns[{slot}])(out{rest}); }}"
            );
        } else {
            let _ = writeln!(
                self.prelude,
                "static {ret} {name}(void *self{decls}) {{ return ({cast}lust_fns[{slot}])({names}); }}"
            );
        }
        name
    }

    fn bin(&mut self, op: BinOp, a: &str, at: &CTy, b: &str, bt: &CTy, loc: &str) -> String {
        use BinOp::*;
        // 128-bit values are C structs: no C operators apply, so every
        // operation is a runtime helper call.
        if let CTy::Int(i) = at
            && is128(*i)
        {
            let f = int_fn(*i);
            if op.is_cmp() {
                return format!("(lust_{f}_cmp({a}, {b}) {} 0)", op.symbol());
            }
            return match op {
                Add => format!("lust_add_{f}({a}, {b}, {loc})"),
                Sub => format!("lust_sub_{f}({a}, {b}, {loc})"),
                Mul => format!("lust_mul_{f}({a}, {b}, {loc})"),
                Div => format!("lust_div_{f}({a}, {b}, {loc})"),
                Rem => format!("lust_rem_{f}({a}, {b}, {loc})"),
                BitAnd => format!("lust_{f}_and({a}, {b})"),
                BitOr => format!("lust_{f}_or({a}, {b})"),
                BitXor => format!("lust_{f}_xor({a}, {b})"),
                Shl | Shr => {
                    let amount = match bt {
                        CTy::Int(bi) if is128(*bi) => format!("({b}).lo"),
                        CTy::Int(bi) if bi.signed() => format!("(uint64_t)(int64_t)({b})"),
                        _ => format!("(uint64_t)({b})"),
                    };
                    let dir = if op == Shl { "left" } else { "right" };
                    let sh = format!("lust_shift_amount({amount}, 128, \"{dir}\", {loc})");
                    let how = if op == Shl { "shl" } else { "shr" };
                    format!("lust_{f}_{how}({a}, {sh})")
                }
                _ => unreachable!(),
            };
        }
        if op.is_cmp() {
            return format!("({a} {} {b})", op.symbol());
        }
        match at {
            CTy::Float(f) => {
                if op == Rem {
                    format!("lust_fmod_{}({a}, {b})", f.name())
                } else {
                    format!("(({})({a} {} {b}))", ctype(&CTy::Float(*f)), op.symbol())
                }
            }
            CTy::Bool => format!("((uint8_t)({a} {} {b}))", op.symbol()),
            CTy::Int(i) => {
                let (c, f) = (int_c(*i), int_fn(*i));
                match op {
                    Add => format!("lust_add_{f}({a}, {b}, {loc})"),
                    Sub => format!("lust_sub_{f}({a}, {b}, {loc})"),
                    Mul => format!("lust_mul_{f}({a}, {b}, {loc})"),
                    Div => format!("lust_div_{f}({a}, {b}, {loc})"),
                    Rem => format!("lust_rem_{f}({a}, {b}, {loc})"),
                    BitAnd | BitOr | BitXor => format!("(({c})({a} {} {b}))", op.symbol()),
                    Shl | Shr => {
                        let amount = match bt {
                            CTy::Int(bi) if is128(*bi) => format!("({b}).lo"),
                            CTy::Int(bi) if bi.signed() => format!("(uint64_t)(int64_t)({b})"),
                            _ => format!("(uint64_t)({b})"),
                        };
                        let dir = if op == Shl { "left" } else { "right" };
                        let sh = format!("lust_shift_amount({amount}, {}, \"{dir}\", {loc})", i.bits());
                        if op == Shl { format!("(({c})((uint64_t)({a}) << {sh}))") } else { format!("(({c})({a} >> {sh}))") }
                    }
                    _ => unreachable!(),
                }
            }
            _ => panic!("bad binary operand type"),
        }
    }

    /// `a` and `b` are pointers to values of type `t`.
    /// The data pointer and length C expressions of an array, Vec, or slice place.
    fn slice_ptr_len(&self, e: &str, t: &CTy) -> (String, String) {
        match t {
            CTy::Array(_, n) => (format!("{e}.v"), n.to_string()),
            CTy::Vec(el) => (format!("(({}*){e}.ptr)", ctype(el)), format!("{e}.len")),
            CTy::Slice(_) | CTy::Str | CTy::String => (format!("{e}.ptr"), format!("{e}.len")),
            _ => (format!("(({e}))"), "0".into()),
        }
    }

    /// A fat slice value over the whole of an array, Vec, or slice place.
    fn slice_of(&mut self, e: &str, t: &CTy) -> String {
        match t {
            CTy::Slice(_) => e.to_string(),
            CTy::Array(el, _) | CTy::Vec(el) => {
                let ct = ctype(&CTy::Slice(el.clone()));
                let (ptr, len) = self.slice_ptr_len(e, t);
                format!("(({ct}){{ {ptr}, {len} }})")
            }
            _ => e.to_string(),
        }
    }

    /// The closure body fn of a closure operand (a sort comparator or
    /// key): check gives these builtins closure args only.
    fn closure_arg(&self, o: &Operand) -> LocalDefId {
        let (Operand::Move(pl) | Operand::Copy(pl)) = o else { panic!("internal: a sort comparator is a closure value") };
        let mut t = self.body.locals[pl.local as usize].ty;
        for pr in &pl.proj {
            t = match (self.body.tys.kind(t), pr) {
                (TyKind::Ref(_, _, i), Proj::Deref) => i,
                _ => panic!("internal: a sort comparator place with projections"),
            };
        }
        match self.body.tys.kind(t) {
            TyKind::Closure(def, _) => self.p.gx.closures[&def].body_fn,
            _ => panic!("internal: a sort comparator is a closure value"),
        }
    }

    /// A call of closure body `f` on the env pointer `env` and the
    /// argument expressions, into a fresh variable of its return type
    /// (written to `out`): the large-return form takes `&var` first.
    fn closure_call_c(&mut self, out: &mut String, f: LocalDefId, env: &str, args: &[String]) -> (String, CTy) {
        let rt = cty(&self.p.tys, self.p.fn_info(f).ret);
        collect_types(&rt, &mut self.sig_types);
        for &t in &self.p.fn_info(f).params {
            collect_types(&cty(&self.p.tys, t), &mut self.sig_types);
        }
        let v = self.tmp();
        let call = format!("({}lust_fns[{}])", fn_ptr_cast(self.p, f), self.slots[f.0 as usize]);
        // A dropped parameter (a zero-sized env taken by value, or a
        // zero-sized argument) is not in the C signature, so it is
        // not passed here either (see `param_dropped`); the env is
        // the body fn's first parameter.
        let mut all: Vec<String> = vec![env.to_string()];
        all.extend(args.iter().cloned());
        let dropped: Vec<bool> = self.p.fn_info(f).params.iter().map(|&t| param_dropped(self.p, &cty(&self.p.tys, t))).collect();
        let mut i = 0;
        all.retain(|_| {
            let keep = !dropped.get(i).copied().unwrap_or(false);
            i += 1;
            keep
        });
        if ret_is_large(self.p, f) {
            let rest: String = all.iter().map(|a| format!(", {a}")).collect();
            let _ = writeln!(out, "  {} {v}; {call}(&{v}{rest});", ctype(&rt));
        } else {
            let _ = writeln!(out, "  {} {v} = {call}({});", ctype(&rt), all.join(", "));
        }
        (v, rt)
    }

    /// C statements (into `out`) comparing the values at pointer
    /// expressions `a` and `b` of an Ord type lust compares
    /// (check/collect.rs `has_total_ord`); returns the name of an int32_t
    /// that is negative, zero, or positive like `Ord::cmp`. With
    /// `partial`, the comparison is `PartialOrd::partial_cmp` (the
    /// sort adapters: std's sort compares with `lt`); the code 2
    /// (unordered) can then also reach the caller, whose `< 0` test
    /// is `lt`.
    fn cmp3_c(&mut self, out: &mut String, t: &CTy, a: &str, b: &str, partial: bool) -> String {
        if let CTy::Ref(inner) = t
            && **inner != CTy::Str
        {
            return self.cmp3_c(out, inner, &format!("(*{a})"), &format!("(*{b})"), partial);
        }
        let v = self.tmp();
        match t {
            CTy::Unit => {
                let _ = writeln!(out, "  int32_t {v} = 0;");
            }
            CTy::Int(i) if is128(*i) => {
                let f = if i.signed() { "lust_i128_cmp" } else { "lust_u128_cmp" };
                let _ = writeln!(out, "  int32_t {v} = {f}(*{a}, *{b});");
            }
            CTy::Int(_) | CTy::Bool | CTy::Char => {
                let _ = writeln!(out, "  int32_t {v} = (*{a} > *{b}) - (*{a} < *{b});");
            }
            CTy::String => {
                let _ = writeln!(out, "  int32_t {v} = lust_str_cmp(lust_string_as_str({a}), lust_string_as_str({b}));");
            }
            CTy::Ref(_) => {
                let _ = writeln!(out, "  int32_t {v} = lust_str_cmp(*{a}, *{b});");
            }
            CTy::Tuple(es) => {
                let _ = writeln!(out, "  int32_t {v} = 0;");
                for (i, e) in es.iter().enumerate() {
                    let _ = writeln!(out, "  if (!{v}) {{");
                    let c = self.cmp3_c(out, e, &format!("(&({a})->f{i})"), &format!("(&({b})->f{i})"), partial);
                    let _ = writeln!(out, "  {v} = {c}; }}");
                }
            }
            // A derived `Ord` (check/collect.rs `has_total_ord`), or,
            // for `partial`, its `PartialOrd` (check/collect.rs
            // `has_partial_cmp`).
            _ => {
                let (g, pre) = if partial { (Glue::PCmp, "pcmp") } else { (Glue::Cmp, "cmp") };
                self.want(g, t);
                let _ = writeln!(out, "  int32_t {v} = {pre}_{}({a}, {b});", mangle(t));
            }
        }
        v
    }

    /// The `is_less` adapter of one sort call (runtime/sort.h): `a.lt(b)`
    /// for `sort`, `compare(a, b) == Less` for `sort_by`, and
    /// `f(a).lt(&f(b))` for `sort_by_key` (the keys drop after, in
    /// reverse order of creation, as Rust's temporaries do).
    fn sort_adapter(&mut self, b: Builtin, elem: &CTy, clo: Option<LocalDefId>) -> String {
        use Builtin as B;
        let name = format!("lust_less_{}_{}", self.slots[self.body.fn_id.0 as usize], self.adapters);
        self.adapters += 1;
        let pt = ctype(&CTy::Ref(Box::new(elem.clone())));
        let (a, bb) = (format!("(({pt})a)"), format!("(({pt})b)"));
        let mut body = String::new();
        match (b, clo) {
            (B::SliceSortBy | B::SliceSortUnstableBy, Some(f)) => {
                let (r, rt) = self.closure_call_c(&mut body, f, "ctx", &[a, bb]);
                let _ = writeln!(body, "  return {} == 0;", disc_call(self.p, &rt, &format!("(&{r})")));
            }
            (B::SliceSortByKey | B::SliceSortUnstableByKey, Some(f)) => {
                let (ka, kt) = self.closure_call_c(&mut body, f, "ctx", &[a]);
                let (kb, _) = self.closure_call_c(&mut body, f, "ctx", &[bb]);
                let c = self.cmp3_c(&mut body, &kt, &format!("(&{ka})"), &format!("(&{kb})"), true);
                if needs_drop_c(self.p, &kt) {
                    self.want(Glue::Drop, &kt);
                    let _ = writeln!(body, "  drop_{0}(&{kb}); drop_{0}(&{ka});", mangle(&kt));
                }
                let _ = writeln!(body, "  return {c} < 0;");
            }
            _ => {
                let c = self.cmp3_c(&mut body, elem, &a, &bb, true);
                let _ = writeln!(body, "  return {c} < 0;");
            }
        }
        let _ = writeln!(self.prelude, "static uint8_t {name}(void *ctx, const void *a, const void *b) {{
{body}}}");
        name
    }

    /// The `cmp(ctx, p)` adapter of one binary search call: `p.cmp(x)`,
    /// `f(p)` as an Ordering, or `f(p).cmp(b)` with ctx `{&f, b}`.
    fn search_adapter(&mut self, b: Builtin, elem: &CTy, clo: Option<LocalDefId>) -> String {
        use Builtin as B;
        let name = format!("lust_bcmp_{}_{}", self.slots[self.body.fn_id.0 as usize], self.adapters);
        self.adapters += 1;
        let pt = ctype(&CTy::Ref(Box::new(elem.clone())));
        let p = format!("(({pt})p)");
        let mut body = String::new();
        match (b, clo) {
            (B::SliceBinarySearchBy, Some(f)) => {
                let (r, rt) = self.closure_call_c(&mut body, f, "ctx", &[p]);
                let _ = writeln!(body, "  return (int32_t){} - 1;", disc_call(self.p, &rt, &format!("(&{r})")));
            }
            (B::SliceBinarySearchByKey, Some(f)) => {
                let (k, kt) = self.closure_call_c(&mut body, f, "((void**)ctx)[0]", &[p]);
                let kp = ctype(&CTy::Ref(Box::new(kt.clone())));
                let c = self.cmp3_c(&mut body, &kt, &format!("(&{k})"), &format!("(({kp})((void**)ctx)[1])"), false);
                if needs_drop_c(self.p, &kt) {
                    self.want(Glue::Drop, &kt);
                    let _ = writeln!(body, "  drop_{}(&{k});", mangle(&kt));
                }
                let _ = writeln!(body, "  return {c};");
            }
            _ => {
                let c = self.cmp3_c(&mut body, elem, &p, &format!("(({pt})ctx)"), false);
                let _ = writeln!(body, "  return {c};");
            }
        }
        let _ = writeln!(self.prelude, "static int32_t {name}(void *ctx, const void *p) {{
{body}}}");
        name
    }

    fn eq_expr(&mut self, t: &CTy, a: &str, b: &str) -> String {
        match t {
            CTy::Unit => "1".into(),
            CTy::Int(i) if is128(*i) => format!("({a}->lo == {b}->lo && {a}->hi == {b}->hi)"),
            CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) | CTy::FnPtr(..) => format!("(*{a} == *{b})"),
            _ => {
                self.want(Glue::Eq, t);
                format!("eq_{}({a}, {b})", mangle(t))
            }
        }
    }

    /// Emits one intrinsic call as a plain runtime call (section 3.2: no
    /// IR node per family, codegen emits the C call direct). This is the
    /// second privilege line behind check: an intrinsic that reaches
    /// codegen from a crate its registry row does not allow is a
    /// compiler bug, so it stops here instead of emitting the call.
    fn intrinsic(&mut self, id: u32, ops: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        let def = lang::intrinsic(id);
        let krate = self.p.fn_shipped_crate(self.body.fn_id);
        assert!(
            def.allows(krate),
            "internal: intrinsic `core::intrinsics::{}` reached codegen from a crate that may not call it",
            def.name
        );
        assert!(def.implemented, "internal: intrinsic `core::intrinsics::{}` reached codegen with no body", def.name);
        let mut args: Vec<String> = Vec::new();
        for (o, sig) in ops.iter().zip(def.params) {
            let v = self.operand(o, loc, post).0;
            // A `&[u8]` reaches C as its pointer and its length.
            args.push(if *sig == SigTy::Bytes { format!("({v}).ptr, ({v}).len") } else { v });
        }
        if matches!(def.ret, SigTy::Never | SigTy::Unit) {
            // The C callee returns void (and for `!`, never returns). The
            // comma form still gives the assignment a value of the right
            // shape: `()`, or the dead continuation's.
            format!("({}({}), ((lust_Unit){{}}))", def.c_symbol, args.join(", "))
        } else if def.ret == SigTy::Bytes {
            // A `&[u8]` comes back as a lust_str: rebuild the slice value.
            let sl = ctype(&CTy::Slice(Box::new(CTy::Int(IntTy::U8))));
            format!("({{ lust_str __b = {}({}); ({sl}){{ .ptr = __b.ptr, .len = __b.len }}; }})", def.c_symbol, args.join(", "))
        } else {
            format!("{}({})", def.c_symbol, args.join(", "))
        }
    }

    fn builtin(&mut self, b: Builtin, ops: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        use Builtin as B;
        // `thread::spawn` reads its closure's body fn (cgen/sync.rs).
        if let B::Sync(
            op @ (crate::check::sync::SyncOp::ThreadSpawn
            | crate::check::sync::SyncOp::ScopeSpawn
            | crate::check::sync::SyncOp::ThreadScope
            | crate::check::sync::SyncOp::CondvarWaitWhile
            | crate::check::sync::SyncOp::OnceGetOrInit),
        ) = b
        {
            return self.thread_closure_call(op, ops, loc, post);
        }
        if b == B::Sync(crate::check::sync::SyncOp::CatchUnwind) {
            return self.catch_unwind_call(ops, loc, post);
        }
        let mut vals = Vec::new();
        let mut tys = Vec::new();
        for o in ops {
            let (v, t) = self.operand(o, loc, post);
            vals.push(v);
            tys.push(t);
        }
        let int_of = |t: &CTy| match t {
            CTy::Int(i) => *i,
            _ => IntTy::I64,
        };
        // The (element type, data pointer, length) C expressions of
        // a Vec, slice, or array operand, in whichever shape the
        // method receiver arrived: `&Vec` (pointer to lust_Vec),
        // `&[T]` (the fat slice value), `&&[T]` (pointer to it),
        // `&[T; N]` (pointer to the array), or a by-value array.
        if let Some(v) = self.fmt_builtin(b, &vals, &tys, loc) {
            return v;
        }
        // Owning fat pointers (cgen/own.rs): their counts, `ptr_eq`,
        // and the conversions that build one.
        if let Some(v) = self.own_builtin(b, &vals, &tys, loc) {
            return v;
        }
        if let B::Sync(op) = b {
            return self.sync_builtin(op, &vals, &tys, loc);
        }
        let slice_like = |t: &CTy, val: &str| -> (CTy, String, String) {
            match t {
                CTy::Ref(inner) => match &**inner {
                    CTy::Vec(e) => ((**e).clone(), format!("(({}*){val}->ptr)", ctype(e)), format!("{val}->len")),
                    CTy::Slice(e) => ((**e).clone(), format!("{val}->ptr"), format!("{val}->len")),
                    CTy::Array(e, n) => ((**e).clone(), format!("{val}->v"), format!("((uint64_t){n})")),
                    _ => unreachable!(),
                },
                CTy::Slice(e) => ((**e).clone(), format!("{val}.ptr"), format!("{val}.len")),
                CTy::Array(e, n) => ((**e).clone(), format!("{val}.v"), format!("((uint64_t){n})")),
                _ => unreachable!(),
            }
        };
        match b {
            B::Sync(_) => unreachable!("sync builtins emit in cgen/sync.rs"),
            B::OwnFrom(_) | B::OwnIntoString => unreachable!("owning pointer builtins emit in cgen/own.rs"),
            // Emitted by `fmt_builtin` above (cgen/fmt.rs).
            B::FmtWriteStr
            | B::FmtWriteChar
            | B::FmtPad
            | B::FmtPadIntegral
            | B::FmtWidth
            | B::FmtPrecision
            | B::FmtFill
            | B::FmtAlternate
            | B::FmtSignPlus
            | B::FmtSignMinus
            | B::FmtSignAwareZeroPad
            | B::FmtDebugStruct
            | B::FmtDebugTuple
            | B::FmtDebugList
            | B::FmtDebugSet
            | B::FmtDebugMap
            | B::DsField
            | B::DtField
            | B::DlEntry
            | B::DmEntry
            | B::DmKey
            | B::DmValue
            | B::FmtFinish
            | B::FmtFinishNonExhaustive
            | B::FmtWriteFmt
            | B::FmtCallDisplay
            | B::FmtCallDebug
            | B::ConvIdent
            | B::ConvStrBytes
            | B::ConvArraySlice
            | B::ConvDeref
            | B::ConvRcInner
            | B::CowIntoOwned
            | B::CowToMut
            | B::CowAddStr
            | B::CowAddAssignStr
            | B::CowDeref => unreachable!("fmt and conversion builtins emit in cgen/fmt.rs"),
            // The operand was moved into the call: no drop ever runs.
            B::MemForget => "((lust_Unit){})".into(),
            // Interior writes of std source cells (W-STD-C): the slot is
            // an `Option<T>` behind a shared reference. `once_init` runs
            // only on a `None` slot, so nothing is overwritten.
            B::OnceInit => {
                let CTy::Ref(opt) = &tys[0] else { unreachable!() };
                let some = self.make_variant(opt, 1, &[vals[1].clone()]);
                let _ = writeln!(self.out, "    *({}) = {some};", vals[0]);
                "((lust_Unit){})".into()
            }
            B::OnceTake => {
                let CTy::Ref(opt) = &tys[0] else { unreachable!() };
                let ot = ctype(opt);
                let (pa, old) = (self.tmp(), self.tmp());
                let none = self.make_variant(opt, 0, &[]);
                let _ = writeln!(self.out, "    {ot}* {pa} = {}; {ot} {old} = *{pa}; *{pa} = {none};", vals[0]);
                old
            }
            B::HashNew
            | B::HashWithCapacity
            | B::HashWithHasher
            | B::HashWithCapacityAndHasher
            | B::HashDefault
            | B::HashLen
            | B::HashIsEmpty
            | B::HashClear
            | B::HashCapacity
            | B::MapInsert
            | B::MapGet
            | B::MapGetMut
            | B::MapContainsKey
            | B::MapRemove
            | B::MapEntry
            | B::EntryOrInsert
            | B::EntryOrDefault
            | B::EntryKey
            | B::EntryOccupied
            | B::EntryIntoMut
            | B::EntryInsert
            | B::EntryGetMut
            | B::SetInsert
            | B::SetContains
            | B::SetRemove
            | B::SetGet
            | B::HashIterNew
            | B::HashIterNext
            | B::HashIterLen
            | B::HashExtendReserve
            | B::HashReserve
            | B::HashInto
            | B::HashOne
            | B::BuildHasher
            | B::HasherCall => unreachable!("hash builtins emit in cgen/hash.rs"),
            B::StrSplitNext | B::StrSplitNextBack | B::StrSplitUpper | B::StrSplitOnce | B::StrRSplitOnce | B::StrMatchesNext | B::StrMatchesNextBack | B::StrPatFind | B::StrPatRfind | B::StrPatContains | B::StrPatStartsWith | B::StrPatEndsWith | B::StrPatStripPrefix | B::StrPatStripSuffix | B::StrTrimMatches | B::StrTrimStartMatches | B::StrTrimEndMatches => {
                unreachable!("split builtins emit in cgen/split.rs")
            }
            B::HashExtend | B::VecExtend | B::StringExtend | B::IterArrayIntoIter | B::IterRepeatN | B::ArrayIterAsSlice | B::ArrayFromFn | B::StrMatches | B::StrEncodeUtf16 | B::StrParse => {
                unreachable!("expanded with its iterator (lower/iter.rs)")
            }
            B::ConvInto => unreachable!("expanded per conversion (lower/iter.rs)"),
            B::PrimFromCast => unreachable!("lowered as a cast (lower.rs)"),
            B::NonZeroNew => unreachable!("lowered as an aggregate (lower.rs)"),
            B::NonZeroGet => format!("(({0}).f0)", vals[0]),
            B::WaitTimedOut => format!("((*{0}).f0)", vals[0]),
            B::EntryOrInsertWith | B::EntryOrInsertWithKey | B::EntryAndModify => unreachable!("expanded with its closure (lower/iter.rs)"),
            B::MemDrop => {
                // The operand was moved into the call, so its own
                // drop flag is already clear; this is its one drop.
                if needs_drop_c(self.p, &tys[0]) {
                    self.want(Glue::Drop, &tys[0]);
                    let t = self.tmp();
                    let _ = writeln!(self.out, "    {} {t} = {};", ctype(&tys[0]), vals[0]);
                    let _ = writeln!(self.out, "    drop_{}(&{t});", mangle(&tys[0]));
                }
                "((lust_Unit){})".into()
            }
            B::StringNew => "lust_string_new()".into(),
            B::StringFrom => match &tys[0] {
                CTy::Char => {
                    // Rust allocates exactly the char's UTF-8 length.
                    let t = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    lust_String {t} = lust_string_with_capacity({0} < 0x80u ? 1 : {0} < 0x800u ? 2 : {0} < 0x10000u ? 3 : 4); lust_string_push_char(&{t}, {0});",
                        vals[0]
                    );
                    t
                }
                CTy::String => vals[0].clone(),
                _ => format!("lust_string_from({})", vals[0]),
            },
            B::StringWithCapacity => format!("lust_string_with_capacity({})", vals[0]),
            B::VecNew | B::VecWithCapacity => unreachable!("lowered to VecLit"),
            B::BoxNew => {
                let et = ctype(&tys[0]);
                let t = self.tmp();
                let _ = writeln!(self.out, "    {et} *{t} = ({et}*)lust_alloc(sizeof({et}), _Alignof({et})); *{t} = {};", vals[0]);
                t
            }
            // Leaking a box is just forgetting it: the moved
            // operand's drop flag is already clear, and the
            // pointer value is the `&mut T` result.
            B::BoxLeak => vals[0].clone(),
            B::RcNew => {
                let it = format!("RcI_{}", mangle(&tys[0]));
                let t = self.tmp();
                let _ = writeln!(
                    self.out,
                    "    {it} *{t} = ({it}*)lust_alloc(sizeof({it}), _Alignof({it})); {t}->strong = 1; {t}->weak = 1; {t}->v = {};",
                    vals[0]
                );
                t
            }
            // An `Rc<dyn Tr>`'s two counts sit right before its value; the
            // weak count holds the strong refs' implicit weak ref (W-STD-A).
            B::RcStrongCount | B::RcWeakCount if matches!(&tys[0], CTy::Ref(r) if **r == CTy::RcDyn) => {
                let h = own::counts(&CTy::Dyn, &format!("(*{})", vals[0]));
                if b == B::RcStrongCount { format!("{h}[0]") } else { format!("({h}[1] - 1)") }
            }
            B::RcStrongCount => format!("(*{})->strong", vals[0]),
            B::ExitCodeFrom => format!("((uint8_t){})", vals[0]),
            B::VecIntoBoxedSlice => {
                // Rust shrinks the buffer to the length first.
                let CTy::Vec(e) = &tys[0] else { unreachable!("into_boxed_slice on a Vec") };
                let (et, st) = (ctype(e), ctype(&CTy::Slice(e.clone())));
                let v = self.tmp();
                let _ = writeln!(self.out, "    lust_Vec {v} = {}; lust_vec_shrink_to(&{v}, 0, sizeof({et}), _Alignof({et}));", vals[0]);
                format!("(({st}){{ ({et}*){v}.ptr, {v}.len }})")
            }
            B::BoxSliceIntoVec => {
                // A zero-sized element's Vec reports capacity usize::MAX.
                let CTy::BoxSlice(e) = &tys[0] else { unreachable!("into_vec on a Box<[T]>") };
                let zst = c_layout(self.p, e).is_some_and(|l| l.size == 0);
                let cap = if zst { "0xffffffffffffffffULL".to_string() } else { format!("({}).len", vals[0]) };
                format!("((lust_Vec){{ (void*)({0}).ptr, ({0}).len, {cap} }})", vals[0])
            }
            B::BoxSliceIntoIter => format!("((lust_VecIter){{ (void*)({0}).ptr, ({0}).len, ({0}).len, 0 }})", vals[0]),
            B::ParseIntErrorKind => format!("(&({})->f0)", vals[0]),
            B::ParseInt(it) => {
                // The primitive int `FromStr` (tf-str): the runtime
                // parses into two words plus an `IntErrorKind` tag;
                // here they become the `Result` and its error struct.
                let p = self.p;
                let (Some(pie), Some(iek)) = (
                    p.tys.local_adt_of(crate::check::generics::parse_int_error_def()),
                    p.tys.local_adt_of(crate::check::generics::int_error_kind_def()),
                ) else {
                    unreachable!("parse type-checks only with std's error Adts")
                };
                let val_ty = CTy::Int(it);
                let res = CTy::Result(Box::new(val_ty.clone()), Box::new(CTy::Adt(pie)));
                collect_types(&res, &mut self.sig_types);
                let (t, lo, hi, kind) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(p, &res, &t, 0, 0), variant_field(p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(p, &res, &t, 0), disc_set(p, &res, &t, 1));
                let a = str_of(&vals[0], &tys[0]);
                let _ = writeln!(self.out, "    uint64_t {lo}, {hi}; int {kind}; {} {t};", ctype(&res));
                let _ = writeln!(
                    self.out,
                    "    if (lust_parse_int({a}, {}, {}, &{lo}, &{hi}, &{kind})) {{ {ok_f} = {}; {ok_d} }}",
                    u8::from(it.signed()),
                    it.bits(),
                    if it.bits() >= 128 { format!("(({}){{ {lo}, {hi} }})", ctype(&val_ty)) } else { format!("(({}){lo})", ctype(&val_ty)) }
                );
                let kct = CTy::Adt(iek);
                let kinds: Vec<String> = (0..4).map(|v| self.make_variant(&kct, v, &[])).collect();
                let _ = writeln!(
                    self.out,
                    "    else {{ {err_f}.f0 = {kind} == 0 ? {} : {kind} == 1 ? {} : {kind} == 2 ? {} : {}; {err_d} }}",
                    kinds[0], kinds[1], kinds[2], kinds[3]
                );
                t
            }
            B::ParseFloat(f) => {
                let p = self.p;
                let (Some(pfe), Some(fek)) = (
                    p.tys.local_adt_of(crate::check::generics::parse_float_error_def()),
                    p.tys.local_adt_of(crate::check::generics::float_error_kind_def()),
                ) else {
                    unreachable!("parse type-checks only with std's error Adts")
                };
                let val_ty = CTy::Float(f);
                let res = CTy::Result(Box::new(val_ty.clone()), Box::new(CTy::Adt(pfe)));
                collect_types(&res, &mut self.sig_types);
                let (t, v, kind) = (self.tmp(), self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(p, &res, &t, 0, 0), variant_field(p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(p, &res, &t, 0), disc_set(p, &res, &t, 1));
                let a = str_of(&vals[0], &tys[0]);
                let (ct, rf) = if f == FloatTy::F32 { ("float", "lust_str_parse_f32") } else { ("double", "lust_str_parse_f64") };
                let _ = writeln!(self.out, "    {ct} {v}; int {kind}; {} {t};", ctype(&res));
                let _ = writeln!(self.out, "    if ({rf}({a}, &{v}, &{kind})) {{ {ok_f} = {v}; {ok_d} }}");
                let kct = CTy::Adt(fek);
                let (k0, k1) = (self.make_variant(&kct, 0, &[]), self.make_variant(&kct, 1, &[]));
                let _ = writeln!(self.out, "    else {{ {err_f}.f0 = {kind} ? {k1} : {k0}; {err_d} }}");
                t
            }
            B::ParseBool => {
                let p = self.p;
                let Some(pbe) = p.tys.local_adt_of(crate::check::generics::parse_bool_error_def()) else {
                    unreachable!("parse type-checks only with std's error Adts")
                };
                let res = CTy::Result(Box::new(CTy::Bool), Box::new(CTy::Adt(pbe)));
                collect_types(&res, &mut self.sig_types);
                let (t, v) = (self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(p, &res, &t, 0, 0), variant_field(p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(p, &res, &t, 0), disc_set(p, &res, &t, 1));
                let a = str_of(&vals[0], &tys[0]);
                let _ = writeln!(self.out, "    uint8_t {v}; {} {t};", ctype(&res));
                let _ = writeln!(self.out, "    if (lust_parse_bool({a}, &{v})) {{ {ok_f} = {v}; {ok_d} }}");
                let _ = writeln!(self.out, "    else {{ {err_f} = (({}){{}}); {err_d} }}", ctype(&CTy::Adt(pbe)));
                t
            }
            B::ParseChar => {
                let p = self.p;
                let (Some(pce), Some(cek)) = (
                    p.tys.local_adt_of(crate::check::generics::parse_char_error_def()),
                    p.tys.local_adt_of(crate::check::generics::char_error_kind_def()),
                ) else {
                    unreachable!("parse type-checks only with std's error Adts")
                };
                let res = CTy::Result(Box::new(CTy::Char), Box::new(CTy::Adt(pce)));
                collect_types(&res, &mut self.sig_types);
                let (t, v, kind) = (self.tmp(), self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(p, &res, &t, 0, 0), variant_field(p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(p, &res, &t, 0), disc_set(p, &res, &t, 1));
                let a = str_of(&vals[0], &tys[0]);
                let _ = writeln!(self.out, "    uint32_t {v}; int {kind}; {} {t};", ctype(&res));
                let _ = writeln!(self.out, "    if (lust_parse_char({a}, &{v}, &{kind})) {{ {ok_f} = {v}; {ok_d} }}");
                let kct = CTy::Adt(cek);
                let (k0, k1) = (self.make_variant(&kct, 0, &[]), self.make_variant(&kct, 1, &[]));
                let _ = writeln!(self.out, "    else {{ {err_f}.f0 = {kind} ? {k1} : {k0}; {err_d} }}");
                t
            }
            B::StringFromUtf8 | B::StrFromUtf8 => {
                // Validate, then build `Ok(text)` or `Err(error)` with
                // Rust's `valid_up_to` and `error_len` (runtime core.c).
                let p = self.p;
                let string = b == B::StringFromUtf8;
                let (Some(fe), Some(ue)) = (p.tys.local_adt_of(crate::check::generics::from_utf8_error_def()), p.tys.local_adt_of(crate::check::generics::utf8_error_def()))
                else {
                    unreachable!("from_utf8 type-checks only with std's error Adts")
                };
                let (ok, err) = if string { (CTy::String, CTy::Adt(fe)) } else { (CTy::Ref(Box::new(CTy::Str)), CTy::Adt(ue)) };
                let res = CTy::Result(Box::new(ok), Box::new(err));
                let opt = CTy::Option(Box::new(CTy::Int(IntTy::U8)));
                let (t, vu, el) = (self.tmp(), self.tmp(), self.tmp());
                let (ok_f, err_f) = (variant_field(p, &res, &t, 0, 0), variant_field(p, &res, &t, 1, 0));
                let (ok_d, err_d) = (disc_set(p, &res, &t, 0), disc_set(p, &res, &t, 1));
                let (ptr, len, ok_val, bytes) = if string {
                    let v = self.tmp();
                    let _ = writeln!(self.out, "    lust_Vec {v} = {};", vals[0]);
                    (
                        format!("((const uint8_t*){v}.ptr)"),
                        format!("{v}.len"),
                        format!("(lust_String){{ (uint8_t*){v}.ptr, {v}.len, {v}.cap }}"),
                        Some(v),
                    )
                } else {
                    let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                    let ok_val = format!("(lust_str){{ (uint8_t*){ptr}, {len} }}");
                    (format!("((const uint8_t*){ptr})"), len, ok_val, None)
                };
                // The `Utf8Error` part of the error value.
                let u = if string { format!("{err_f}.f1") } else { err_f.clone() };
                let o = format!("{u}.f1");
                let (some_f, some_d, none_d) = (variant_field(p, &opt, &o, 1, 0), disc_set(p, &opt, &o, 1), disc_set(p, &opt, &o, 0));
                let rt = ctype(&res);
                let _ = writeln!(self.out, "    uint64_t {vu} = 0; uint8_t {el} = 0; {rt} {t};");
                let _ = writeln!(self.out, "    if (lust_utf8_check({ptr}, {len}, &{vu}, &{el})) {{ {ok_f} = {ok_val}; {ok_d} }}");
                let keep = bytes.map_or(String::new(), |v| format!("{err_f}.f0 = {v}; "));
                let _ = writeln!(
                    self.out,
                    "    else {{ {keep}{u}.f0 = {vu}; if ({el}) {{ {some_f} = {el}; {some_d} }} else {{ {none_d} }} {err_d} }}"
                );
                t
            }
            B::StringFromUtf8Lossy => {
                // `Cow::Borrowed` of the bytes as a `str` when they are
                // valid UTF-8, else `Cow::Owned` of the lossy text in a
                // String that starts with the input's capacity, as
                // std's `from_utf8_lossy` allocates (runtime sys.c
                // appends valid runs and U+FFFD replacements).
                let p = self.p;
                let a = p
                    .gx
                    .adt_instance_of
                    .iter()
                    .position(|o| {
                        matches!(o, Some((d, args)) if *d == crate::check::generics::cow_def()
                            && p.tys.args(*args).first().and_then(|g| g.as_ty()) == Some(STR))
                    })
                    .expect("from_utf8_lossy type-checks only with the Cow<str> instance");
                let cow = CTy::Adt(AdtId(a as u32));
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (t, vu, el, s) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let (f0, f1) = (variant_field(p, &cow, &t, 0, 0), variant_field(p, &cow, &t, 1, 0));
                let (d0, d1) = (disc_set(p, &cow, &t, 0), disc_set(p, &cow, &t, 1));
                let ct = ctype(&cow);
                let _ = writeln!(self.out, "    uint64_t {vu} = 0; uint8_t {el} = 0; {ct} {t};");
                let _ = writeln!(
                    self.out,
                    "    if (lust_utf8_check((const uint8_t*){ptr}, {len}, &{vu}, &{el})) {{ {f0} = (lust_str){{ (uint8_t*){ptr}, {len} }}; {d0} }}"
                );
                let _ = writeln!(
                    self.out,
                    "    else {{ lust_String {s} = lust_string_with_capacity({len}); lust_sys_utf8_lossy((const uint8_t*){ptr}, {len}, &{s}); {f1} = {s}; {d1} }}"
                );
                t
            }
            B::FromUtf8ErrorUtf8Error => format!("(*{}).f1", vals[0]),
            B::FromUtf8ErrorAsBytes => {
                let sl = ctype(&CTy::Slice(Box::new(CTy::Int(IntTy::U8))));
                format!("(({sl}){{ (uint8_t*)(*{0}).f0.ptr, (*{0}).f0.len }})", vals[0])
            }
            B::FromUtf8ErrorIntoBytes => format!("({}).f0", vals[0]),
            B::Utf8ErrorValidUpTo => format!("(*{}).f0", vals[0]),
            // `std::panic::Location` (check/caller.rs): a fresh value for
            // the packed location, which lives as long as the program.
            B::LocationCaller => {
                // One node per distinct location, kept on a per-site static
                // list: the value lives as long as the program, is shared by
                // equal locations, and stays reachable (no leak).
                let p = self.p;
                let a = p.tys.local_adt_of(crate::check::generics::location_def()).expect("Location is a std Adt");
                let ct = ctype(&CTy::Adt(a));
                let fslot = self.slots[self.body.fn_id.0 as usize];
                let (t, l, n) = (self.tmp(), self.tmp(), self.tmp());
                let node = format!("lc{fslot}_{n}");
                let _ = writeln!(self.prelude, "static struct {node} {{ lust_loc k; struct {node} *next; {ct} v; }} *{node}_head;");
                let _ = writeln!(
                    self.out,
                    "    lust_loc {l} = (lust_loc)({loc}); struct {node} *{n} = {node}_head; while ({n} && {n}->k != {l}) {n} = {n}->next;\n    if (!{n}) {{ {n} = (struct {node}*)lust_alloc(sizeof(struct {node}), _Alignof(struct {node})); {n}->k = {l}; {n}->next = {node}_head; {node}_head = {n}; uint64_t fl = 0; while (lust_file[fl]) fl++; {n}->v.f0 = (lust_str){{(uint8_t*)lust_file, fl}}; {n}->v.f1 = (uint32_t)(lust_fn_line[{l} >> 40] + (({l} >> 20) & 0xFFFFF)); {n}->v.f2 = (uint32_t)({l} & 0xFFFFF); }}\n    {ct} *{t} = &{n}->v;"
                );
                t
            }
            B::LocationFile => format!("(*{}).f0", vals[0]),
            B::LocationLine => format!("(*{}).f1", vals[0]),
            B::LocationColumn => format!("(*{}).f2", vals[0]),
            B::Utf8ErrorErrorLen => {
                let p = self.p;
                let (o8, o64) = (CTy::Option(Box::new(CTy::Int(IntTy::U8))), CTy::Option(Box::new(CTy::Int(IntTy::Usize))));
                let src = format!("(*{}).f1", vals[0]);
                let t = self.tmp();
                let disc = disc_call(p, &o8, &format!("&{src}"));
                let (some_f, some_d, none_d) = (variant_field(p, &o64, &t, 1, 0), disc_set(p, &o64, &t, 1), disc_set(p, &o64, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {} {t}; if ({disc}) {{ {some_f} = (uint64_t){}; {some_d} }} else {{ {none_d} }}",
                    ctype(&o64),
                    variant_field(p, &o8, &src, 1, 0)
                );
                t
            }
            B::RcWeakCount => format!("((*{})->weak - 1)", vals[0]),
            B::RcGetMut => {
                let inner = match &tys[0] { CTy::Ref(r) => (**r).clone(), _ => unreachable!() };
                let elem = match &inner { CTy::Rc(e) => (**e).clone(), _ => unreachable!() };
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(elem))));
                let ot = ctype(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let v = &vals[0];
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if ((*{v})->strong == 1 && (*{v})->weak == 1) {{ {field} = &(*{v})->v;{some} }}");
                t
            }
            B::RcMakeMut => {
                let inner = match &tys[0] { CTy::Ref(r) => (**r).clone(), _ => unreachable!() };
                let elem = match &inner { CTy::Rc(e) => (**e).clone(), _ => unreachable!() };
                let it = format!("RcI_{}", mangle(&elem));
                let v = &vals[0];
                let cloned = if is_copy_c(self.p, &elem) {
                    format!("(*{v})->v")
                } else {
                    self.want(Glue::Clone, &elem);
                    format!("clone_{}(&(*{v})->v)", mangle(&elem))
                };
                // Shared: clone the value into a fresh header and leave
                // the old count one lower. Unique but Weak-held: move
                // the value out and let the Weaks keep the old header
                // (strong 0, its implicit weak ref gone), as in Rust.
                let _ = writeln!(
                    self.out,
                    "    if ((*{v})->strong > 1) {{ {it} *n = ({it}*)lust_alloc(sizeof({it}), _Alignof({it})); n->strong = 1; n->weak = 1; n->v = {cloned}; (*{v})->strong--; *{v} = n; }}\n    else if ((*{v})->weak > 1) {{ {it} *n = ({it}*)lust_alloc(sizeof({it}), _Alignof({it})); n->strong = 1; n->weak = 1; n->v = (*{v})->v; (*{v})->strong = 0; (*{v})->weak--; *{v} = n; }}"
                );
                format!("&(*{v})->v")
            }
            B::DefaultGlue => unreachable!("the default glue call is emitted at its call terminator"),
            B::SliceTryInto => unreachable!("the slice-to-array call is emitted at its call terminator"),
            B::TlsWith
            | B::TlsTryWith
            | B::TlsWithBorrow
            | B::TlsWithBorrowMut
            | B::TlsSet
            | B::TlsGet
            | B::TlsTake
            | B::TlsReplace
            | B::TlsTryGet
            | B::TlsCloneRc => {
                unreachable!("lower/tls.rs expands LocalKey calls before codegen")
            }
            B::TlsAccess | B::TlsTryAccess | B::TlsInitWith => self.tls_builtin(b, &vals, &tys, loc),
            B::RcTryUnwrap => {
                let elem = match &tys[0] { CTy::Rc(e) => (**e).clone(), _ => unreachable!() };
                let res = CTy::Result(Box::new(elem.clone()), Box::new(CTy::Rc(Box::new(elem.clone()))));
                let rt = ctype(&res);
                let t = self.tmp();
                let v = &vals[0];
                let ok_f = variant_field(self.p, &res, &t, 0, 0);
                let err_f = variant_field(self.p, &res, &t, 1, 0);
                let set_ok = disc_set(self.p, &res, &t, 0);
                let set_err = disc_set(self.p, &res, &t, 1);
                let et = ctype(&elem);
                let it = format!("RcI_{}", mangle(&elem));
                let _ = writeln!(self.out, "    {rt} {t};");
                let _ = writeln!(
                    self.out,
                    "    if ({v}->strong == 1) {{ {set_ok} {ok_f} = {v}->v; {v}->strong = 0; if (--{v}->weak == 0) lust_dealloc((void*){v}, sizeof({it}), _Alignof({it})); }} else {{ {set_err} {err_f} = {v}; }}"
                );
                let _ = et;
                t
            }
            B::RcIntoInner | B::RcUnwrapOrClone => {
                // The last strong Rc gives up its value (the header stays
                // while Weak refs do); any other just drops its count:
                // into_inner answers None, unwrap_or_clone a clone.
                let CTy::Rc(elem) = &tys[0] else { unreachable!("into_inner on an Rc") };
                let elem = (**elem).clone();
                let it = format!("RcI_{}", mangle(&elem));
                let v = self.tmp();
                let _ = writeln!(self.out, "    {it}* {v} = {};", vals[0]);
                let free = format!("{v}->strong = 0; if (--{v}->weak == 0) lust_dealloc((void*){v}, sizeof({it}), _Alignof({it}));");
                if b == B::RcIntoInner {
                    let opt = CTy::Option(Box::new(elem.clone()));
                    let t = self.tmp();
                    let (f, some, none) = (variant_field(self.p, &opt, &t, 1, 0), disc_set(self.p, &opt, &t, 1), disc_set(self.p, &opt, &t, 0));
                    let _ = writeln!(
                        self.out,
                        "    {} {t}; if ({v}->strong == 1) {{ {f} = {v}->v; {some} {free} }} else {{ {v}->strong--; {none} }}",
                        ctype(&opt)
                    );
                    t
                } else {
                    let c = if is_copy_c(self.p, &elem) {
                        format!("{v}->v")
                    } else {
                        self.want(Glue::Clone, &elem);
                        format!("clone_{}(&{v}->v)", mangle(&elem))
                    };
                    let t = self.tmp();
                    let _ = writeln!(self.out, "    {} {t}; if ({v}->strong == 1) {{ {t} = {v}->v; {free} }} else {{ {t} = {c}; {v}->strong--; }}", ctype(&elem));
                    t
                }
            }
            B::EnvArgs => "((lust_Args){ (uint64_t)lust_argc })".into(),
            B::ArgsCount => format!("{}.n", vals[0]),
            B::StrLen => format!("{}.len", vals[0]),
            B::StrIsEmpty => format!("({}.len == 0)", vals[0]),
            B::StrToString => format!("lust_string_from({})", vals[0]),
            B::StringLen | B::VecLen => format!("({})->len", vals[0]),
            B::SliceLen => match &tys[0] {
                CTy::Slice(_) => format!("{}.len", vals[0]),
                CTy::Ref(inner) => match &**inner {
                    CTy::Array(_, n) => n.to_string(),
                    CTy::Slice(_) => format!("{}.len", vals[0]),
                    _ => format!("({})->len", vals[0]),
                },
                _ => format!("{}.len", vals[0]),
            },
            B::SliceIsEmpty => match &tys[0] {
                CTy::Slice(_) => format!("({}.len == 0)", vals[0]),
                CTy::Ref(inner) => match &**inner {
                    CTy::Array(_, n) => format!("({n} == 0)"),
                    CTy::Slice(_) => format!("({}.len == 0)", vals[0]),
                    _ => format!("(({})->len == 0)", vals[0]),
                },
                _ => format!("({}.len == 0)", vals[0]),
            },
            B::StringIsEmpty | B::VecIsEmpty => format!("(({})->len == 0)", vals[0]),
            B::StringPushStr => {
                let _ = writeln!(self.out, "    lust_string_push_str({}, {});", vals[0], vals[1]);
                "((lust_Unit){})".into()
            }
            B::StringPush => {
                let _ = writeln!(self.out, "    lust_string_push_char({}, {});", vals[0], vals[1]);
                "((lust_Unit){})".into()
            }
            B::StringAsStr | B::StringAsMutStr => format!("lust_string_as_str({})", vals[0]),
            B::StringCapacity => format!("({})->cap", vals[0]),
            B::StringReserve | B::StringReserveExact | B::StringShrinkToFit | B::StringShrinkTo => {
                let vv = &vals[0];
                let call = match b {
                    B::StringReserve => format!("lust_string_reserve({vv}, {})", vals[1]),
                    B::StringReserveExact => format!("lust_string_reserve_exact({vv}, {})", vals[1]),
                    B::StringShrinkToFit => format!("lust_string_shrink_to({vv}, 0)"),
                    _ => format!("lust_string_shrink_to({vv}, {})", vals[1]),
                };
                let _ = writeln!(self.out, "    {call};");
                "((lust_Unit){})".into()
            }
            B::StringPop => {
                let t = self.tmp();
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if ({0}->len) {{ {field} = lust_string_pop({0});{some} }}", vals[0]);
                t
            }
            B::StringRemove => format!("lust_string_remove({}, {}, {loc})", vals[0], vals[1]),
            B::StringInsert => {
                let _ = writeln!(self.out, "    lust_string_insert_char({}, {}, {}, {loc});", vals[0], vals[1], vals[2]);
                "((lust_Unit){})".into()
            }
            B::StringInsertStr => {
                let _ = writeln!(self.out, "    lust_string_insert_bytes({}, {}, ({2}).ptr, ({2}).len, {loc});", vals[0], vals[1], vals[2]);
                "((lust_Unit){})".into()
            }
            B::StringTruncate => {
                let _ = writeln!(self.out, "    lust_string_truncate({}, {}, {loc});", vals[0], vals[1]);
                "((lust_Unit){})".into()
            }
            B::StringClear => {
                let _ = writeln!(self.out, "    {}->len = 0;", vals[0]);
                "((lust_Unit){})".into()
            }
            B::CloneInto => {
                // `ToOwned::clone_into` on str (into a String) and on a
                // Copy slice (into a Vec): read the source into
                // temporaries, clear the target (its buffer stays),
                // then copy in, growing as push and extend grow.
                let dst = &vals[1];
                if matches!(&tys[0], CTy::Ref(inner) if **inner == CTy::Str) || matches!(&tys[0], CTy::Str) {
                    let s = self.tmp();
                    let _ = writeln!(self.out, "    lust_str {s} = {}; {dst}->len = 0; lust_string_push_str({dst}, {s});", vals[0]);
                } else {
                    let CTy::Ref(v) = &tys[1] else { unreachable!("clone_into target is a &mut Vec") };
                    let CTy::Vec(e) = &**v else { unreachable!("clone_into target is a &mut Vec") };
                    let et = ctype(e);
                    let (_, sptr, slen) = slice_like(&tys[0], &vals[0]);
                    let (sp, sn, i) = (self.tmp(), self.tmp(), self.tmp());
                    let _ = writeln!(
                        self.out,
                        "    {et} *{sp} = {sptr};\n    uint64_t {sn} = {slen};\n    {dst}->len = 0;\n    lust_vec_reserve({dst}, {sn}, sizeof({et}), _Alignof({et}));\n    for (uint64_t {i} = 0; {i} < {sn}; {i}++) (({et}*){dst}->ptr)[{dst}->len++] = {sp}[{i}];"
                    );
                }
                "((lust_Unit){})".into()
            }
            B::StringSplitOff => format!("lust_string_split_off({}, {}, {loc})", vals[0], vals[1]),
            B::StringAsBytes => {
                let sl = CTy::Slice(Box::new(CTy::Int(IntTy::U8)));
                let (st, t) = (ctype(&sl), self.tmp());
                let _ = writeln!(self.out, "    {st} {t} = {{ {0}->ptr, {0}->len }};", vals[0]);
                t
            }
            B::StringIntoBytes => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_Vec {t} = {{ (void*){0}.ptr, {0}.len, {0}.cap }};", vals[0]);
                t
            }
            B::StrStripPrefix | B::StrStripSuffix => {
                let a = str_of(&vals[0], &tys[0]);
                let (sa, sp) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    lust_str {sa} = {a}; lust_str {sp} = {};", vals[1]);
                let t = self.tmp();
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(CTy::Str))));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let (cond, val) = if b == B::StrStripPrefix {
                    (format!("lust_str_starts_with({sa}, {sp})"), format!("(lust_str){{ {sa}.ptr + {sp}.len, {sa}.len - {sp}.len }}"))
                } else {
                    (format!("lust_str_ends_with({sa}, {sp})"), format!("(lust_str){{ {sa}.ptr, {sa}.len - {sp}.len }}"))
                };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if ({cond}) {{ {field} = {val};{some} }}");
                t
            }
            B::StrTrimStart => format!("lust_str_trim_start({})", str_of(&vals[0], &tys[0])),
            B::StrTrimEnd => format!("lust_str_trim_end({})", str_of(&vals[0], &tys[0])),
            B::StrReplace => format!("lust_str_replace({}, {}, {})", str_of(&vals[0], &tys[0]), vals[1], vals[2]),
            B::StrRepeat => format!("lust_str_repeat({}, {}, {loc})", str_of(&vals[0], &tys[0]), vals[1]),
            B::StrIsCharBoundary => {
                let sa = self.tmp();
                let a = str_of(&vals[0], &tys[0]);
                let _ = writeln!(self.out, "    lust_str {sa} = {a};");
                format!("({0} <= {sa}.len && ({0} == {sa}.len || ({sa}.ptr[{0}] & 0xC0) != 0x80))", vals[1])
            }
            B::VecPush => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                // The value must be read before `lust_vec_push_slot` can reallocate the
                // buffer: `v.push(v[0])` in one C assignment could read the freed buffer.
                let t = self.tmp();
                let _ = writeln!(self.out, "    {et} {t} = {};", vals[1]);
                let _ = writeln!(self.out, "    *({et}*)lust_vec_push_slot({}, sizeof({et}), _Alignof({et})) = {t};", vals[0]);
                "((lust_Unit){})".into()
            }
            B::Clone => {
                let CTy::Ref(inner) = &tys[0] else { unreachable!() };
                if is_copy_c(self.p, inner) || **inner == CTy::Str {
                    format!("(*{})", vals[0])
                } else if matches!(**inner, CTy::RefCell(_)) {
                    // `RefCell::clone` is `#[track_caller]`: its borrow
                    // panics at this call, which the clone glue (called
                    // without a location) cannot name, so test here.
                    self.want(Glue::Clone, inner);
                    let t = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    {}* {t} = {}; if ({t}->f0 < 0) lust_panic_cstr_dyn(\"RefCell already mutably borrowed\", {loc});",
                        ctype(inner),
                        vals[0]
                    );
                    format!("clone_{}({t})", mangle(inner))
                } else {
                    self.want(Glue::Clone, inner);
                    format!("clone_{}({})", mangle(inner), vals[0])
                }
            }
            B::CloneFrom => {
                let CTy::Ref(inner) = &tys[0] else { unreachable!() };
                self.want(Glue::CloneFrom, inner);
                let _ = writeln!(self.out, "    clonefrom_{}({}, {});", mangle(inner), vals[0], vals[1]);
                "((lust_Unit){})".into()
            }
            B::ToString => {
                match tys[0].clone() {
                    CTy::Ref(inner) => self.to_string_value(&inner, &vals[0], loc),
                    // A dyn receiver arrives as the fat value itself
                    // (`Box<dyn Error>::to_string`, F3): spill it so
                    // the fmt shim reads it by address, as a format
                    // argument does.
                    t @ (CTy::Dyn | CTy::BoxDyn | CTy::RcDyn) => {
                        let tmp = self.tmp();
                        let _ = writeln!(self.out, "    {} {tmp} = {};", ctype(&t), vals[0]);
                        self.to_string_value(&t, &format!("(&{tmp})"), loc)
                    }
                    _ => unreachable!(),
                }
            }
            B::WrappingAdd | B::WrappingSub | B::WrappingMul => {
                let it = int_of(&tys[0]);
                if is128(it) {
                    let f = int_fn(it);
                    let how = match b {
                        B::WrappingAdd => "add",
                        B::WrappingSub => "sub",
                        _ => "mul",
                    };
                    format!("lust_{f}_{how}({}, {})", vals[0], vals[1])
                } else {
                    let c = int_c(it);
                    let op = match b {
                        B::WrappingAdd => "+",
                        B::WrappingSub => "-",
                        _ => "*",
                    };
                    format!("(({c})((uint64_t)({}) {op} (uint64_t)({})))", vals[0], vals[1])
                }
            }
            B::WrappingDiv
            | B::WrappingRem
            | B::WrappingNeg
            | B::WrappingPow
            | B::WrappingShl
            | B::WrappingShr
            | B::WrappingAbs
            | B::CheckedAdd
            | B::CheckedSub
            | B::CheckedMul
            | B::CheckedDiv
            | B::CheckedRem
            | B::CheckedNeg
            | B::CheckedAbs
            | B::CheckedPow
            | B::CheckedShl
            | B::CheckedShr
            | B::SaturatingAdd
            | B::SaturatingSub
            | B::SaturatingMul
            | B::SaturatingDiv
            | B::SaturatingNeg
            | B::SaturatingAbs
            | B::SaturatingPow
            | B::OverflowingAdd
            | B::OverflowingSub
            | B::OverflowingMul
            | B::OverflowingDiv
            | B::OverflowingRem
            | B::OverflowingNeg
            | B::OverflowingAbs
            | B::OverflowingPow
            | B::OverflowingShl
            | B::OverflowingShr
            | B::CountOnes
            | B::CountZeros
            | B::LeadingZeros
            | B::TrailingZeros
            | B::LeadingOnes
            | B::TrailingOnes
            | B::RotateLeft
            | B::RotateRight
            | B::SwapBytes
            | B::ReverseBits
            | B::DivCeil
            | B::DivEuclid
            | B::RemEuclid
            | B::Signum
            | B::IsPositive
            | B::IsNegative
            | B::IsPowerOfTwo
            | B::IsMultipleOf
            | B::NextMultipleOf
            | B::CheckedNextMultipleOf
            | B::UnsignedAbs
            | B::UnboundedShl
            | B::UnboundedShr
            | B::CastSigned
            | B::CastUnsigned
            | B::Isqrt
            | B::CheckedIsqrt
            | B::BitWidth
            | B::HighestOne
            | B::LowestOne
            | B::IsolateHighestOne
            | B::IsolateLowestOne
            | B::IntMidpoint
            | B::StrictAdd
            | B::StrictSub
            | B::StrictMul
            | B::StrictDiv
            | B::StrictRem
            | B::StrictDivEuclid
            | B::StrictRemEuclid
            | B::StrictNeg
            | B::StrictAbs
            | B::StrictPow
            | B::StrictShl
            | B::StrictShr
            | B::MixedCheckedAdd
            | B::MixedCheckedSub
            | B::MixedWrappingAdd
            | B::MixedWrappingSub
            | B::MixedSaturatingAdd
            | B::MixedSaturatingSub
            | B::MixedOverflowingAdd
            | B::MixedOverflowingSub
            | B::MixedStrictAdd
            | B::MixedStrictSub
            | B::CheckedSignedDiff
            | B::CarryingAdd
            | B::BorrowingSub
            | B::CarryingMul
            | B::CarryingMulAdd => self.int_method_c(b, &vals, &tys, loc),
            B::FloatSqrt
            | B::FloatPowi
            | B::FloatPowf
            | B::FloatExp
            | B::FloatLn
            | B::FloatLog
            | B::FloatLog2
            | B::FloatLog10
            | B::FloatMulAdd
            | B::FloatFloor
            | B::FloatCeil
            | B::FloatRound
            | B::FloatTrunc
            | B::FloatFract
            | B::FloatAbs
            | B::FloatSignum
            | B::FloatRecip
            | B::FloatMin
            | B::FloatMax
            | B::FloatIsNan
            | B::FloatIsInfinite
            | B::FloatIsFinite
            | B::FloatIsSignPositive
            | B::FloatIsSignNegative
            | B::FloatToBits
            | B::FloatCopysign
            | B::F32FromBits
            | B::F64FromBits => self.float_method_c(b, &vals, &tys),
            B::CharLenUtf8 => format!("((uint64_t)({0} < 0x80u ? 1 : {0} < 0x800u ? 2 : {0} < 0x10000u ? 3 : 4))", vals[0]),
            B::CharLenUtf16 => format!("((uint64_t)({0} < 0x10000u ? 1 : 2))", vals[0]),
            B::CharEncodeUtf8 | B::CharEncodeUtf16 => {
                let (d, n, t) = (self.tmp(), self.tmp(), self.tmp());
                let dt = ctype(&tys[1]);
                let (helper, sloc) = if b == B::CharEncodeUtf8 {
                    ("lust_char_encode_utf8", std_loc(1, 2518, 9))
                } else {
                    ("lust_char_encode_utf16", std_loc(1, 2612, 13))
                };
                let _ = writeln!(
                    self.out,
                    "    {dt} {d} = {}; uint64_t {n} = {helper}({}, {d}.ptr, {d}.len, {sloc});",
                    vals[1], vals[0]
                );
                if b == B::CharEncodeUtf8 {
                    let _ = writeln!(self.out, "    lust_str {t} = {{ {d}.ptr, {n} }};");
                } else {
                    let _ = writeln!(self.out, "    {dt} {t} = {{ {d}.ptr, {n} }};");
                }
                t
            }
            B::CharIsAscii => format!("(*{0} < 128u)", vals[0]),
            B::CharIsAsciiPunctuation => {
                format!(
                    "(((*{0} >= 33u && *{0} <= 47u) || (*{0} >= 58u && *{0} <= 64u) || (*{0} >= 91u && *{0} <= 96u) || (*{0} >= 123u && *{0} <= 126u)))",
                    vals[0]
                )
            }
            B::CharIsAsciiGraphic => format!("(*{0} >= 33u && *{0} <= 126u)", vals[0]),
            B::CharIsAsciiHexdigit => {
                format!("(((*{0} >= '0' && *{0} <= '9') || ((*{0} | 32) >= 'a' && (*{0} | 32) <= 'f')))", vals[0])
            }
            B::CharIsAsciiControl => format!("(*{0} < 32u || *{0} == 127u)", vals[0]),
            B::CharIsDigitRadix => format!("(lust_digit({}, {}, {}) != 0xFFFFFFFFu)", vals[0], vals[1], std_loc(1, 407, 9)),
            B::Abs => format!("lust_abs_{}({}, {})", int_fn(int_of(&tys[0])), vals[0], num_loc(int_of(&tys[0]), false)),
            B::Pow => format!("lust_pow_{}({}, {}, {})", int_fn(int_of(&tys[0])), vals[0], vals[1], num_loc(int_of(&tys[0]), true)),
            B::Min | B::Max => {
                let it = int_of(&tys[0]);
                if is128(it) {
                    let f = int_fn(it);
                    let rel = if b == B::Min { "<" } else { ">" };
                    format!("(lust_{f}_cmp({0}, {1}) {rel} 0 ? {0} : {1})", vals[0], vals[1])
                } else if b == B::Min {
                    format!("({0} < {1} ? {0} : {1})", vals[0], vals[1])
                } else {
                    format!("({0} > {1} ? {0} : {1})", vals[0], vals[1])
                }
            }
            B::CmpCode => {
                // Both operands are references to the compared type (a
                // slice operand is the fat value itself).
                let (t, a, b) = match &tys[0] {
                    CTy::Slice(_) => (tys[0].clone(), format!("(&{})", vals[0]), format!("(&{})", vals[1])),
                    CTy::Ref(inner) => ((**inner).clone(), vals[0].clone(), vals[1].clone()),
                    other => (other.clone(), format!("(&{})", vals[0]), format!("(&{})", vals[1])),
                };
                self.want(Glue::Cmp, &t);
                format!("cmp_{}({a}, {b})", mangle(&t))
            }
            // `vec::IntoIter` (W-STD-A): the moved-in buffer, then
            // `next` and `next_back` take from `front..len`.
            B::IterVecIntoIter => format!("((lust_VecIter){{ {0}.ptr, {0}.len, {0}.cap, 0 }})", vals[0]),
            B::VecIterLen => format!("({0}->len - {0}->front)", vals[0]),
            B::VecIterCap => format!("({0}->cap)", vals[0]),
            B::VecIterFront => format!("({0}->front)", vals[0]),
            B::CharsBytesLeft => format!("({0}->s.len - {0}->pos)", vals[0]),
            B::VecIterNext | B::VecIterNextBack => {
                let e = match &tys[0] {
                    CTy::Ref(inner) => match &**inner {
                        CTy::VecIter(e) => (**e).clone(),
                        _ => unreachable!("vec::IntoIter next takes &mut lust_VecIter"),
                    },
                    _ => unreachable!("vec::IntoIter next takes &mut lust_VecIter"),
                };
                let opt = CTy::Option(Box::new(e.clone()));
                let ot = ctype(&opt);
                let t = self.tmp();
                let v = &vals[0];
                let idx = if b == B::VecIterNext { format!("{v}->front++") } else { format!("--{v}->len") };
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    if ({v}->front < {v}->len) {{ {field} = (({}*){v}->ptr)[{idx}];{some} }}", ctype(&e));
                t
            }
            // The drains: construction checks the range in the
            // runtime; `next` and `next_back` take from `front..back`
            // of the drained buffer (as `vec::Drain` and
            // `string::Drain`).
            B::VecDrain => format!("lust_vec_drain({}, {}, {}, {}, {}, {loc})", vals[0], vals[1], vals[2], vals[3], vals[4]),
            B::StringDrain => format!("lust_string_drain({}, {}, {}, {}, {}, {loc})", vals[0], vals[1], vals[2], vals[3], vals[4]),
            B::VecDrainLen => format!("({0}->back - {0}->front)", vals[0]),
            B::VecDrainNext | B::VecDrainNextBack => {
                let e = match &tys[0] {
                    CTy::Ref(inner) => match &**inner {
                        CTy::VecDrain(e) => (**e).clone(),
                        _ => unreachable!("vec::Drain next takes &mut lust_VecDrain"),
                    },
                    _ => unreachable!("vec::Drain next takes &mut lust_VecDrain"),
                };
                let opt = CTy::Option(Box::new(e.clone()));
                let ot = ctype(&opt);
                let t = self.tmp();
                let v = &vals[0];
                let idx = if b == B::VecDrainNext { format!("{v}->front++") } else { format!("--{v}->back") };
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(
                    self.out,
                    "    if ({v}->front < {v}->back) {{ {field} = (({}*)((lust_Vec*){v}->vec)->ptr)[{idx}];{some} }}",
                    ctype(&e)
                );
                t
            }
            B::VecDrainAsSlice => {
                let e = match &tys[0] {
                    CTy::Ref(inner) => match &**inner {
                        CTy::VecDrain(e) => (**e).clone(),
                        _ => unreachable!("vec::Drain as_slice takes &lust_VecDrain"),
                    },
                    _ => unreachable!("vec::Drain as_slice takes &lust_VecDrain"),
                };
                let et = ctype(&e);
                let sl = CTy::Slice(Box::new(e));
                let (st, t) = (ctype(&sl), self.tmp());
                let vv = &vals[0];
                let _ = writeln!(self.out, "    {st} {t} = {{ (({et}*)((lust_Vec*){vv}->vec)->ptr) + {vv}->front, {vv}->back - {vv}->front }};");
                t
            }
            B::StrDrainNext | B::StrDrainNextBack => {
                let t = self.tmp();
                let it = &vals[0];
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                if b == B::StrDrainNext {
                    let _ = writeln!(
                        self.out,
                        "    if ({it}->front < {it}->back) {{ {field} = lust_utf8_next(((lust_String*){it}->vec)->ptr, &{it}->front);{some} }}"
                    );
                } else {
                    let _ = writeln!(
                        self.out,
                        "    if ({it}->front < {it}->back) {{ {field} = lust_utf8_prev(((lust_String*){it}->vec)->ptr, &{it}->back);{some} }}"
                    );
                }
                t
            }
            B::StrDrainAsStr => {
                let (t, vv) = (self.tmp(), &vals[0]);
                let _ = writeln!(self.out, "    lust_str {t} = {{ ((lust_String*){vv}->vec)->ptr + {vv}->front, {vv}->back - {vv}->front }};");
                t
            }
            // Expanded into plain IR before codegen (lower/iter.rs).
            B::IterLen | B::RangeStartBound | B::RangeEndBound | B::BoundAsRef | B::BoundMap | B::BoundCloned | B::RangeIsEmpty | B::RangeContains | B::RangeInclStart | B::RangeInclEnd => {
                unreachable!("iterator expansion left a builtin for codegen")
            }
            // `Rc` weak refs, `RefCell`, and `Cell` (W-STD-A, check/cells.rs).
            // The `RcI` header keeps Rust's counts: `weak` includes the one
            // implicit weak ref the strong refs hold; `Weak::new()` is the
            // dangling `UINTPTR_MAX` pointer.
            B::RcDowngrade => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t} = *{}; {t}->weak++;", ctype(&deref_cty(&tys[0])), vals[0]);
                t
            }
            // `Rc<dyn Tr>`: the addresses, not the vtables (ptr::addr_eq).
            B::RcPtrEq if matches!(&tys[0], CTy::Ref(r) if **r == CTy::RcDyn) => format!("((*{}).data == (*{}).data)", vals[0], vals[1]),
            B::RcPtrEq | B::WeakPtrEq => format!("(*{} == *{})", vals[0], vals[1]),
            B::WeakNew => "((void*)~(uint64_t)0)".into(),
            B::WeakUpgrade => {
                let w = deref_cty(&tys[0]);
                let CTy::Weak(e) = &w else { unreachable!("Weak::upgrade on a Weak") };
                let opt = CTy::Option(Box::new(CTy::Rc(e.clone())));
                collect_types(&opt, &mut self.sig_types);
                let (t, p) = (self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {} {p} = *{}; if ({p} != (void*)~(uint64_t)0 && {p}->strong > 0) {{ {p}->strong++; {field} = {p}; {some} }}",
                    ctype(&w),
                    vals[0]
                );
                t
            }
            B::WeakStrongCount => format!("(*{0} == (void*)~(uint64_t)0 ? (uint64_t)0 : (*{0})->strong)", vals[0]),
            B::WeakWeakCount => format!("(*{0} == (void*)~(uint64_t)0 || (*{0})->strong == 0 ? (uint64_t)0 : (*{0})->weak - 1)", vals[0]),
            B::RefCellNew => {
                let t = self.tmp();
                let rc = CTy::RefCell(Box::new(tys[0].clone()));
                collect_types(&rc, &mut self.sig_types);
                let _ = writeln!(self.out, "    {} {t}; {t}.f0 = 0; {t}.f1 = {};", ctype(&rc), vals[0]);
                t
            }
            B::RefCellBorrow => {
                let t = self.tmp();
                let rc = deref_cty(&tys[0]);
                let _ = writeln!(
                    self.out,
                    "    {}* {t} = {}; if ({t}->f0 < 0 || {t}->f0 == 0x7fffffffffffffffLL) lust_panic_cstr_dyn(\"RefCell already mutably borrowed\", {loc}); {t}->f0++;",
                    ctype(&rc),
                    vals[0]
                );
                t
            }
            B::RefCellBorrowMut => {
                let t = self.tmp();
                let rc = deref_cty(&tys[0]);
                let _ = writeln!(
                    self.out,
                    "    {}* {t} = {}; if ({t}->f0 != 0) lust_panic_cstr_dyn(\"RefCell already borrowed\", {loc}); {t}->f0 = -1;",
                    ctype(&rc),
                    vals[0]
                );
                t
            }
            // `try_borrow` (`try_borrow_mut`): `borrow`'s flag test, the
            // guard in `Ok`, else `Err` of the unit error struct (W-STD-B).
            B::RefCellTryBorrow | B::RefCellTryBorrowMut => {
                let m = b == B::RefCellTryBorrowMut;
                let rc = deref_cty(&tys[0]);
                let CTy::RefCell(el) = &rc else { unreachable!("try_borrow on a &RefCell") };
                let def = if m { crate::check::generics::borrow_mut_error_def() } else { crate::check::generics::borrow_error_def() };
                let err = CTy::Adt(self.p.tys.local_adt_of(def).expect("the RefCell error Adts always exist"));
                let res = CTy::Result(Box::new(CTy::Guard(el.clone(), m)), Box::new(err.clone()));
                collect_types(&res, &mut self.sig_types);
                let (p, t) = (self.tmp(), self.tmp());
                let ok = self.make_variant(&res, 0, std::slice::from_ref(&p));
                let fail = self.make_variant(&res, 1, &[zero_lit(self.p, &err)]);
                let (busy, take) = if m {
                    (format!("{p}->f0 != 0"), format!("{p}->f0 = -1"))
                } else {
                    (format!("{p}->f0 < 0 || {p}->f0 == 0x7fffffffffffffffLL"), format!("{p}->f0++"))
                };
                let _ = writeln!(
                    self.out,
                    "    {}* {p} = {}; {} {t}; if ({busy}) {t} = {fail}; else {{ {take}; {t} = {ok}; }}",
                    ctype(&rc),
                    vals[0],
                    ctype(&res)
                );
                t
            }
            B::RefCellIntoInner => format!("{}.f1", vals[0]),
            B::RefCellReplace => {
                let (c, old) = (self.tmp(), self.tmp());
                let rc = deref_cty(&tys[0]);
                let _ = writeln!(
                    self.out,
                    "    {}* {c} = {}; if ({c}->f0 != 0) lust_panic_cstr_dyn(\"RefCell already borrowed\", {loc}); {} {old} = {c}->f1; {c}->f1 = {};",
                    ctype(&rc),
                    vals[0],
                    ctype(&tys[1]),
                    vals[1]
                );
                old
            }
            B::RefCellSwap => {
                let (a, bb, tmp) = (self.tmp(), self.tmp(), self.tmp());
                let rc = deref_cty(&tys[0]);
                let CTy::RefCell(e) = &rc else { unreachable!("RefCell::swap on a RefCell") };
                let _ = writeln!(
                    self.out,
                    "    {rt}* {a} = {}; {rt}* {bb} = {}; if ({a}->f0 != 0) lust_panic_cstr_dyn(\"RefCell already borrowed\", {la}); {a}->f0 = -1; if ({bb}->f0 != 0) lust_panic_cstr_dyn(\"RefCell already borrowed\", {lb}); {et} {tmp} = {a}->f1; {a}->f1 = {bb}->f1; {bb}->f1 = {tmp}; {a}->f0 = 0;",
                    vals[0],
                    vals[1],
                    rt = ctype(&rc),
                    et = ctype(e),
                    // `swap` is not track_caller: its two `borrow_mut`s panic in cell.rs.
                    la = std_loc(9, 1083, 30),
                    lb = std_loc(9, 1083, 56)
                );
                "((lust_Unit){})".into()
            }
            B::RefCellGetMut => format!("(&({})->f1)", vals[0]),
            B::CellNew | B::CellIntoInner => vals[0].clone(),
            B::CellGet => format!("(*{})", vals[0]),
            B::CellGetMut => vals[0].clone(),
            B::CellTake | B::RefCellTake => {
                // `replace(T::default())` (core); RefCell's panics if borrowed.
                let CTy::Ref(cell) = &tys[0] else { unreachable!("take on a &Cell") };
                let el = match &**cell {
                    CTy::Cell(e) | CTy::RefCell(e) => (**e).clone(),
                    _ => unreachable!("take on a cell"),
                };
                let def = match &el {
                    CTy::Unit | CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) => zero_lit(self.p, &el),
                    t => {
                        self.want(Glue::Default, t);
                        format!("default_{}()", mangle(t))
                    }
                };
                let (c, old) = (self.tmp(), self.tmp());
                let et = ctype(&el);
                if b == B::RefCellTake {
                    let _ = writeln!(
                        self.out,
                        "    {}* {c} = {}; if ({c}->f0 != 0) lust_panic_cstr_dyn(\"RefCell already borrowed\", {}); {et} {old} = {c}->f1; {c}->f1 = {def};",
                        ctype(cell),
                        vals[0],
                        // `take` is not track_caller: its `replace` panics in cell.rs.
                        std_loc(9, 1434, 14)
                    );
                } else {
                    let _ = writeln!(self.out, "    {et}* {c} = {}; {et} {old} = *{c}; *{c} = {def};", vals[0]);
                }
                old
            }
            B::CellSet | B::CellReplace => {
                let (c, old) = (self.tmp(), self.tmp());
                let et = ctype(&tys[1]);
                let _ = writeln!(self.out, "    {et}* {c} = {}; {et} {old} = *{c}; *{c} = {};", vals[0], vals[1]);
                if b == B::CellReplace {
                    return old;
                }
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    let _ = writeln!(self.out, "    drop_{}(&{old});", mangle(&tys[1]));
                }
                "((lust_Unit){})".into()
            }
            B::CellSwap => {
                let (a, bb, tmp) = (self.tmp(), self.tmp(), self.tmp());
                let et = match deref_cty(&tys[0]) {
                    CTy::Cell(e) => ctype(&e),
                    other => ctype(&other),
                };
                let _ = writeln!(
                    self.out,
                    "    {et}* {a} = {}; {et}* {bb} = {}; if ({a} != {bb}) {{ {et} {tmp} = *{a}; *{a} = *{bb}; *{bb} = {tmp}; }}",
                    vals[0],
                    vals[1]
                );
                "((lust_Unit){})".into()
            }
            // The sort family (W-STD-A, runtime/sort.h): a comparator
            // adapter per call site, then Rust 1.99's driftsort or
            // ipnsort over the element bytes.
            B::SliceSort | B::SliceSortUnstable | B::SliceSortBy | B::SliceSortUnstableBy | B::SliceSortByKey | B::SliceSortUnstableByKey => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let size = c_size_align(self.p, &e).0;
                let clo = ops.get(1).map(|o| self.closure_arg(o));
                let adapter = self.sort_adapter(b, &e, clo);
                let ctx = match (vals.get(1), tys.get(1)) {
                    (Some(v), Some(t)) => {
                        let c = self.tmp();
                        let _ = writeln!(self.out, "    {} {c} = {v};", ctype(t));
                        Some((c, t.clone()))
                    }
                    _ => None,
                };
                let cx = ctx.as_ref().map_or("0".to_string(), |(c, _)| format!("(void*)&{c}"));
                // Rust picks the small sort by Copy-ness and freeze-ness
                // (no Cell or RefCell inline).
                let freeze = u8::from(is_freeze_c(self.p, &e, &mut HashSet::new()));
                if matches!(b, B::SliceSort | B::SliceSortBy | B::SliceSortByKey) {
                    let _ = writeln!(self.out, "    lust_sort_stable({ptr}, {len}, {size}, {freeze}, {cx}, {adapter});");
                } else {
                    let copy = u8::from(is_copy_c(self.p, &e));
                    let _ = writeln!(self.out, "    lust_sort_unstable({ptr}, {len}, {size}, {freeze}, {copy}, {cx}, {adapter});");
                }
                if let Some((c, t)) = ctx
                    && needs_drop_c(self.p, &t)
                {
                    self.want(Glue::Drop, &t);
                    let _ = writeln!(self.out, "    drop_{}(&{c});", mangle(&t));
                }
                "((lust_Unit){})".into()
            }
            B::SliceBinarySearch | B::SliceBinarySearchBy | B::SliceBinarySearchByKey => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let size = c_size_align(self.p, &e).0;
                let clo = match b {
                    B::SliceBinarySearchBy => Some(self.closure_arg(&ops[1])),
                    B::SliceBinarySearchByKey => Some(self.closure_arg(&ops[2])),
                    _ => None,
                };
                let adapter = self.search_adapter(b, &e, clo);
                let cx = match b {
                    B::SliceBinarySearch => format!("(void*){}", vals[1]),
                    B::SliceBinarySearchBy => {
                        let c = self.tmp();
                        let _ = writeln!(self.out, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                        format!("(void*)&{c}")
                    }
                    _ => {
                        let (c, k) = (self.tmp(), self.tmp());
                        let _ = writeln!(self.out, "    {} {c} = {};", ctype(&tys[2]), vals[2]);
                        let _ = writeln!(self.out, "    void *{k}[2] = {{ (void*)&{c}, (void*){} }};", vals[1]);
                        format!("(void*){k}")
                    }
                };
                let r = self.tmp();
                let _ = writeln!(self.out, "    int64_t {r} = lust_binary_search({ptr}, {len}, {size}, {cx}, {adapter});");
                let res = CTy::Result(Box::new(CTy::Int(IntTy::Usize)), Box::new(CTy::Int(IntTy::Usize)));
                collect_types(&res, &mut self.sig_types);
                let t = self.tmp();
                let (ok_f, err_f) = (variant_field(self.p, &res, &t, 0, 0), variant_field(self.p, &res, &t, 1, 0));
                let (set_ok, set_err) = (disc_set(self.p, &res, &t, 0), disc_set(self.p, &res, &t, 1));
                let _ = writeln!(self.out, "    {} {t};", ctype(&res));
                let _ = writeln!(
                    self.out,
                    "    if ({r} >= 0) {{ {set_ok} {ok_f} = (uint64_t){r}; }} else {{ {set_err} {err_f} = (uint64_t)(-{r} - 1); }}"
                );
                t
            }
            B::IterIter
            | B::IterIterMut
            | B::IterNext
            | B::IterMap
            | B::IterFilter
            | B::IterFilterMap
            | B::IterEnumerate
            | B::IterRev
            | B::IterTake
            | B::IterSkip
            | B::IterStepBy
            | B::IterChain
            | B::IterZip
            | B::IterCopied
            | B::IterCloned
            | B::IterTakeWhile
            | B::IterSkipWhile
            | B::IterPeekable
            | B::IterPeek
            | B::IterInspect
            | B::IterCount
            | B::IterLast
            | B::IterNth
            | B::IterAny
            | B::IterAll
            | B::IterFind
            | B::IterFindMap
            | B::IterPosition
            | B::IterRposition
            | B::IterWindows
            | B::IterChunks
            | B::IterUtf8Chunks
            | B::IterRemainder
            | B::IterFlatten
            | B::IterFlatMap
            | B::HashFromArray
            | B::DlEntries
            | B::DmEntries
            | B::StrSplit
            | B::IterSizeHint
            | B::IterNextBack
            | B::StrCharIndices
            | B::StrBytes
            | B::IterFold
            | B::IterForEach
            | B::IterMin
            | B::IterMax
            | B::IterMinByKey
            | B::IterMaxByKey
            | B::IterCollect
            | B::FromIter
            | B::IterSum
            | B::IterProduct
            | B::IterOptRes => unreachable!("iterator builtins are expanded before codegen (lower/iter.rs)"),
            B::VecPop | B::VecGet | B::VecFirst | B::VecLast | B::VecGetMut | B::VecFirstMut | B::VecLastMut => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (opt, r) = if b == B::VecPop {
                    (CTy::Option(Box::new(e.clone())), "")
                } else {
                    (CTy::Option(Box::new(CTy::Ref(Box::new(e.clone())))), "&")
                };
                let ot = ctype(&opt);
                let t = self.tmp();
                let v = &vals[0];
                let (cond, idx) = match b {
                    B::VecPop => (format!("{len} > 0"), format!("--{v}->len")),
                    B::VecGet | B::VecGetMut => (format!("{} < {len}", vals[1]), vals[1].clone()),
                    B::VecFirst | B::VecFirstMut => (format!("{len} > 0"), "0".into()),
                    _ => (format!("{len} > 0"), format!("{len} - 1")),
                };
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    if ({cond}) {{ {field} = {r}{ptr}[{idx}];{some} }}");
                t
            }
            B::VecContains => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (t, i) = (self.tmp(), self.tmp());
                let elem = format!("(&{ptr}[{i}])");
                let eq = self.eq_expr(&e, &elem, &vals[1]);
                let _ = writeln!(
                    self.out,
                    "    uint8_t {t} = 0;\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) if ({eq}) {{ {t} = 1; break; }}"
                );
                t
            }
            B::VecSwap => {
                // `Vec::swap` and `[T]::swap` share the builtin:
                // `slice_like` reads either receiver form.
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (et, t) = (ctype(&e), self.tmp());
                let (a, bb) = (&vals[1], &vals[2]);
                let _ = writeln!(
                    self.out,
                    "    lust_bounds({a}, {len}, {loc}); lust_bounds({bb}, {len}, {loc});\n    {et} {t} = {ptr}[{a}]; {ptr}[{a}] = {ptr}[{bb}]; {ptr}[{bb}] = {t};"
                );
                "((lust_Unit){})".into()
            }
            B::SliceStartsWith | B::SliceEndsWith => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (_, nptr, nlen) = slice_like(&tys[1], &vals[1]);
                let (t, i, off) = (self.tmp(), self.tmp(), self.tmp());
                let elem_a = format!("(&{ptr}[{off} + {i}])");
                let elem_b = format!("(&{nptr}[{i}])");
                let eq = self.eq_expr(&e, &elem_a, &elem_b);
                let off_expr = if b == B::SliceStartsWith { "0".to_string() } else { format!("{len} - {nlen}") };
                let _ = writeln!(
                    self.out,
                    "    uint64_t {off} = {nlen} <= {len} ? ({off_expr}) : 0;\n    uint8_t {t} = {nlen} <= {len};\n    for (uint64_t {i} = 0; {t} && {i} < {nlen}; {i}++) if (!({eq})) {{ {t} = 0; break; }}"
                );
                t
            }
            B::SliceFill => {
                // Core `clone_from`s into every element but the
                // last, which takes the value itself; an empty
                // slice drops the value. The clonefrom glue is
                // core's body per type (buffer reuse included).
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let et = ctype(&e);
                let (tv, i) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {et} {tv} = {};", vals[1]);
                if is_copy_c(self.p, &e) {
                    let _ = writeln!(self.out, "    for (uint64_t {i} = 0; {i} < {len}; {i}++) {ptr}[{i}] = {tv};");
                } else {
                    self.want(Glue::CloneFrom, &e);
                    let _ = writeln!(
                        self.out,
                        "    for (uint64_t {i} = 0; {i} + 1 < {len}; {i}++) clonefrom_{}(&{ptr}[{i}], &{tv});",
                        mangle(&e)
                    );
                    if needs_drop_c(self.p, &e) {
                        self.want(Glue::Drop, &e);
                        let jm = mangle(&e);
                        let _ = writeln!(
                            self.out,
                            "    if ({len} > 0) {{ drop_{jm}(&{ptr}[{len} - 1]); {ptr}[{len} - 1] = {tv}; }} else {{ drop_{jm}(&{tv}); }}"
                        );
                    } else {
                        let _ = writeln!(self.out, "    if ({len} > 0) {ptr}[{len} - 1] = {tv};");
                    }
                }
                "((lust_Unit){})".into()
            }
            B::SliceCopyFromSlice => {
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (_, sptr, slen) = slice_like(&tys[1], &vals[1]);
                let i = self.tmp();
                let _ = writeln!(
                    self.out,
                    "    if ({slen} != {len}) lust_panic_nn(\"copy_from_slice: source slice length (\", {slen}, \") does not match destination slice length (\", {len}, \")\", {loc});\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) {ptr}[{i}] = {sptr}[{i}];"
                );
                "((lust_Unit){})".into()
            }
            B::SliceCopyWithin => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let et = ctype(&e);
                let _ = writeln!(
                    self.out,
                    "    lust_slice_copy_within({ptr}, {len}, sizeof({et}), {}, {}, {}, {}, {}, {loc});",
                    vals[1], vals[2], vals[3], vals[4], vals[5]
                );
                "((lust_Unit){})".into()
            }
            B::SliceGetRange | B::SliceGetRangeMut => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let sl = CTy::Slice(Box::new(e));
                let opt = CTy::Option(Box::new(sl.clone()));
                collect_types(&opt, &mut self.sig_types);
                let (t, s0, e0) = (self.tmp(), self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {{ uint64_t {s0} = 0, {e0} = 0;\n      if (lust_range_bounds_get({len}, {}, {}, {}, {}, &{s0}, &{e0})) {{ {field} = ({}){{ {ptr} + {s0}, {e0} - {s0} }};{some} }} }}",
                    vals[1],
                    vals[2],
                    vals[3],
                    vals[4],
                    ctype(&sl)
                );
                t
            }
            B::SliceJoinStr | B::SliceConcatStr => {
                // Core's exact capacity: the sum of the parts (and
                // separators) is reserved once, then copied in.
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let view = |el: &str| -> String {
                    match &e {
                        CTy::String => format!("lust_string_as_str(&{el})"),
                        _ => el.to_string(),
                    }
                };
                let (t, i, tot) = (self.tmp(), self.tmp(), self.tmp());
                let sep = if b == B::SliceJoinStr { vals[1].clone() } else { "((lust_str){ (const uint8_t*)\"\", 0 })".to_string() };
                let _ = writeln!(
                    self.out,
                    "    uint64_t {tot} = 0;\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) {tot} += {}.len;\n    if ({len} > 1) {tot} += ({sep}).len * ({len} - 1);\n    lust_String {t} = lust_string_with_capacity({tot});\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) {{ if ({i}) lust_string_push_str(&{t}, {sep}); lust_string_push_str(&{t}, {}); }}",
                    view(&format!("{ptr}[{i}]")),
                    view(&format!("{ptr}[{i}]"))
                );
                t
            }
            B::SliceConcatVec | B::SliceJoinVecElem | B::SliceJoinVecSlice => {
                // The `Vec<T>` join/concat family: with_capacity of
                // the exact total, then each part cloned in order
                // (separators interleaved, as core's extend does).
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let inner = match &e {
                    CTy::Vec(i) | CTy::Slice(i) | CTy::BoxSlice(i) | CTy::Array(i, _) => (**i).clone(),
                    _ => unreachable!(),
                };
                let iet = ctype(&inner);
                // The (data, len) C text of one part element.
                let part = |el: &str| -> (String, String) {
                    match &e {
                        CTy::Vec(_) => (format!("(({iet}*){el}.ptr)"), format!("{el}.len")),
                        CTy::Array(_, n) => (format!("{el}.v"), format!("((uint64_t){n})")),
                        _ => (format!("{el}.ptr"), format!("{el}.len")),
                    }
                };
                let copy_inner = is_copy_c(self.p, &inner);
                let cloned = |src: String| -> String {
                    if copy_inner {
                        src
                    } else {
                        format!("clone_{}(&{src})", mangle(&inner))
                    }
                };
                if !copy_inner {
                    self.want(Glue::Clone, &inner);
                }
                let (t, i, j, tot) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let (sp1, sl1) = part(&format!("{ptr}[{i}]"));
                let mut body = String::new();
                let _ = writeln!(body, "    uint64_t {tot} = 0;");
                let _ = writeln!(body, "    for (uint64_t {i} = 0; {i} < {len}; {i}++) {tot} += {sl1};");
                match b {
                    B::SliceJoinVecElem => {
                        let _ = writeln!(body, "    if ({len} > 1) {tot} += {len} - 1;");
                    }
                    B::SliceJoinVecSlice => {
                        let (_, _, seplen) = slice_like(&tys[1], &vals[1]);
                        let _ = writeln!(body, "    if ({len} > 1) {tot} += ({seplen}) * ({len} - 1);");
                    }
                    _ => {}
                }
                let _ = writeln!(body, "    lust_Vec {t} = lust_vec_with_capacity({tot}, sizeof({iet}), _Alignof({iet}));");
                let _ = writeln!(body, "    for (uint64_t {i} = 0; {i} < {len}; {i}++) {{");
                match b {
                    B::SliceJoinVecElem => {
                        let sepv = if copy_inner {
                            format!("(*{})", vals[1])
                        } else {
                            format!("clone_{}({})", mangle(&inner), vals[1])
                        };
                        let _ = writeln!(body, "      if ({i}) (({iet}*){t}.ptr)[{t}.len++] = {sepv};");
                    }
                    B::SliceJoinVecSlice => {
                        let (_, sepptr, seplen) = slice_like(&tys[1], &vals[1]);
                        let sj = self.tmp();
                        let _ = writeln!(
                            body,
                            "      if ({i}) for (uint64_t {sj} = 0; {sj} < {seplen}; {sj}++) (({iet}*){t}.ptr)[{t}.len++] = {};",
                            cloned(format!("{sepptr}[{sj}]"))
                        );
                    }
                    _ => {}
                }
                let _ = writeln!(
                    body,
                    "      for (uint64_t {j} = 0; {j} < {sl1}; {j}++) (({iet}*){t}.ptr)[{t}.len++] = {};\n    }}",
                    cloned(format!("{sp1}[{j}]"))
                );
                let _ = write!(self.out, "{body}");
                t
            }
            B::VecClear | B::VecTruncate => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let n = if b == B::VecClear { "0".to_string() } else { vals[1].clone() };
                let vv = &vals[0];
                if needs_drop_c(self.p, e) {
                    self.want(Glue::Drop, e);
                    let i = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    for (uint64_t {i} = {n}; {i} < {vv}->len; {i}++) drop_{}(&(({}*){vv}->ptr)[{i}]);",
                        mangle(e),
                        ctype(e)
                    );
                }
                let _ = writeln!(self.out, "    if ({n} < {vv}->len) {vv}->len = {n};");
                "((lust_Unit){})".into()
            }
            B::VecInsert => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (ti, tx) = (self.tmp(), self.tmp());
                let (vv, i, x) = (&vals[0], &vals[1], &vals[2]);
                // Read the index and the value before the shift: both can
                // read the Vec itself, as in `v.insert(0, v[1])`.
                let _ = writeln!(
                    self.out,
                    "    uint64_t {ti} = {i}; {et} {tx} = {x};\n    lust_vec_insert_at({vv}, {ti}, sizeof({et}), _Alignof({et}), {loc});\n    (({et}*){vv}->ptr)[{ti}] = {tx};"
                );
                "((lust_Unit){})".into()
            }
            B::VecRemove => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let (et, t) = (ctype(e), self.tmp());
                let (vv, i) = (&vals[0], &vals[1]);
                let _ = writeln!(
                    self.out,
                    "    lust_vec_check_remove({vv}, {i}, {loc});\n    {et} {t} = (({et}*){vv}->ptr)[{i}];\n    lust_vec_remove_at({vv}, {i}, sizeof({et}));"
                );
                t
            }
            B::VecCapacity => format!("({})->cap", vals[0]),
            B::VecReserve | B::VecReserveExact | B::VecShrinkToFit | B::VecShrinkTo => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let vv = &vals[0];
                let call = match b {
                    B::VecReserve => format!("lust_vec_reserve({vv}, {}, sizeof({et}), _Alignof({et}))", vals[1]),
                    B::VecReserveExact => format!("lust_vec_reserve_exact({vv}, {}, sizeof({et}), _Alignof({et}))", vals[1]),
                    B::VecShrinkToFit => format!("lust_vec_shrink_to({vv}, 0, sizeof({et}), _Alignof({et}))"),
                    _ => format!("lust_vec_shrink_to({vv}, {}, sizeof({et}), _Alignof({et}))", vals[1]),
                };
                let _ = writeln!(self.out, "    {call};");
                "((lust_Unit){})".into()
            }
            B::VecSwapRemove => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let (et, t) = (ctype(e), self.tmp());
                let (vv, i) = (&vals[0], &vals[1]);
                let _ = writeln!(
                    self.out,
                    "    if ({i} >= {vv}->len) lust_panic_nn(\"swap_remove index (is \", {i}, \") should be < len (is \", {vv}->len, \")\", {});\n    {et} {t} = (({et}*){vv}->ptr)[{i}];\n    (({et}*){vv}->ptr)[{i}] = (({et}*){vv}->ptr)[{vv}->len - 1];\n    {vv}->len--;",
                    std_loc(3, 2258, 13)
                );
                t
            }
            B::VecAppend => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (vv, o) = (&vals[0], &vals[1]);
                let (n, i) = (self.tmp(), self.tmp());
                // Elements move bitwise; the source keeps its
                // buffer and capacity with length 0, as in Rust.
                let _ = writeln!(
                    self.out,
                    "    uint64_t {n} = {o}->len;\n    lust_vec_reserve({vv}, {n}, sizeof({et}), _Alignof({et}));\n    for (uint64_t {i} = 0; {i} < {n}; {i}++) (({et}*){vv}->ptr)[{vv}->len + {i}] = (({et}*){o}->ptr)[{i}];\n    {vv}->len += {n};\n    {o}->len = 0;"
                );
                "((lust_Unit){})".into()
            }
            B::VecExtendFromSlice => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (_, sptr, slen) = slice_like(&tys[1], &vals[1]);
                let (sp, sn, i) = (self.tmp(), self.tmp(), self.tmp());
                let vv = &vals[0];
                let cloned = if is_copy_c(self.p, e) {
                    format!("{sp}[{i}]")
                } else {
                    self.want(Glue::Clone, e);
                    format!("clone_{}(&{sp}[{i}])", mangle(e))
                };
                // The source pointer and length are read into
                // temporaries before the reserve can reallocate
                // (the receiver cannot alias the source in Rust,
                // but the operand text may name the same locals).
                let _ = writeln!(
                    self.out,
                    "    {et} *{sp} = {sptr};\n    uint64_t {sn} = {slen};\n    lust_vec_reserve({vv}, {sn}, sizeof({et}), _Alignof({et}));\n    for (uint64_t {i} = 0; {i} < {sn}; {i}++) (({et}*){vv}->ptr)[{vv}->len++] = {cloned};"
                );
                "((lust_Unit){})".into()
            }
            B::VecSplitOff => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let (et, t, i) = (ctype(e), self.tmp(), self.tmp());
                let (vv, at) = (&vals[0], &vals[1]);
                let _ = writeln!(
                    self.out,
                    "    if ({at} > {vv}->len) lust_panic_nn(\"`at` split index (is \", {at}, \") should be <= len (is \", {vv}->len, \")\", {loc});\n    lust_Vec {t} = lust_vec_with_capacity({vv}->len - {at}, sizeof({et}), _Alignof({et}));\n    for (uint64_t {i} = {at}; {i} < {vv}->len; {i}++) (({et}*){t}.ptr)[{i} - {at}] = (({et}*){vv}->ptr)[{i}];\n    {t}.len = {vv}->len - {at};\n    {vv}->len = {at};"
                );
                t
            }
            B::VecResize => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (vv, n) = (&vals[0], &vals[1]);
                let (tv, i) = (self.tmp(), self.tmp());
                // The value is read first: it may come from the
                // Vec the resize then reallocates or truncates.
                let _ = writeln!(self.out, "    {et} {tv} = {};", vals[2]);
                if needs_drop_c(self.p, e) {
                    self.want(Glue::Drop, e);
                    let i2 = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    if ({n} < {vv}->len) {{ for (uint64_t {i2} = {n}; {i2} < {vv}->len; {i2}++) drop_{}(&(({et}*){vv}->ptr)[{i2}]); }}\n    if ({n} <= {vv}->len) {{ drop_{}(&{tv}); }}",
                        mangle(e),
                        mangle(e)
                    );
                }
                let _ = writeln!(self.out, "    if ({n} <= {vv}->len) {{ {vv}->len = {n}; }} else {{");
                let _ = writeln!(self.out, "      lust_vec_reserve({vv}, {n} - {vv}->len, sizeof({et}), _Alignof({et}));");
                if is_copy_c(self.p, e) {
                    let _ = writeln!(self.out, "      while ({vv}->len < {n}) (({et}*){vv}->ptr)[{vv}->len++] = {tv};");
                } else {
                    self.want(Glue::Clone, e);
                    // Clones first, the value itself last, as Rust's
                    // `repeat_n` yields them: (count - 1) clones.
                    let _ = writeln!(
                        self.out,
                        "      for (uint64_t {i} = {vv}->len; {i} + 1 < {n}; {i}++) (({et}*){vv}->ptr)[{i}] = clone_{}(&{tv});\n      (({et}*){vv}->ptr)[{n} - 1] = {tv};\n      {vv}->len = {n};",
                        mangle(e)
                    );
                }
                let _ = writeln!(self.out, "    }}");
                "((lust_Unit){})".into()
            }
            B::VecDedup => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let vv = &vals[0];
                let (w, r) = (self.tmp(), self.tmp());
                let elem_r = format!("(&(({et}*){vv}->ptr)[{r}])");
                let elem_w = format!("(&(({et}*){vv}->ptr)[{w} - 1])");
                let eq = self.eq_expr(e, &elem_r, &elem_w);
                let drop_dup = if needs_drop_c(self.p, e) {
                    self.want(Glue::Drop, e);
                    format!("drop_{}(&(({et}*){vv}->ptr)[{r}]); ", mangle(e))
                } else {
                    String::new()
                };
                // A duplicate drops as soon as it is found, before
                // the next comparison, as in Rust.
                let _ = writeln!(
                    self.out,
                    "    if ({vv}->len > 1) {{\n      uint64_t {w} = 1;\n      for (uint64_t {r} = 1; {r} < {vv}->len; {r}++) {{\n        if ({eq}) {{ {drop_dup}}} else {{ if ({w} != {r}) (({et}*){vv}->ptr)[{w}] = (({et}*){vv}->ptr)[{r}]; {w}++; }}\n      }}\n      {vv}->len = {w};\n    }}"
                );
                "((lust_Unit){})".into()
            }
            B::VecRetain | B::VecRetainMut => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let vv = &vals[0];
                let f = self.closure_arg(&ops[1]);
                let (w, r, c) = (self.tmp(), self.tmp(), self.tmp());
                let mut body = String::new();
                let _ = writeln!(body, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                let _ = writeln!(body, "    uint64_t {w} = 0;");
                let _ = writeln!(body, "    for (uint64_t {r} = 0; {r} < {vv}->len; {r}++) {{");
                let elem_r = format!("(&(({et}*){vv}->ptr)[{r}])");
                let (keep, _) = self.closure_call_c(&mut body, f, &format!("&{c}"), &[elem_r]);
                // A removed element drops as soon as it is rejected,
                // before the predicate sees the next one, as in Rust.
                let drop_rej = if needs_drop_c(self.p, e) {
                    self.want(Glue::Drop, e);
                    format!("drop_{}(&(({et}*){vv}->ptr)[{r}]); ", mangle(e))
                } else {
                    String::new()
                };
                let _ = writeln!(
                    body,
                    "      if ({keep}) {{ if ({w} != {r}) (({et}*){vv}->ptr)[{w}] = (({et}*){vv}->ptr)[{r}]; {w}++; }} else {{ {drop_rej}}}"
                );
                let _ = writeln!(body, "    }}");
                let _ = writeln!(body, "    {vv}->len = {w};");
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    let _ = writeln!(body, "    drop_{}(&{c});", mangle(&tys[1]));
                }
                let _ = write!(self.out, "{body}");
                "((lust_Unit){})".into()
            }
            B::BoolThenSome | B::BoolThen => {
                let elem = if b == B::BoolThenSome {
                    tys[1].clone()
                } else {
                    cty(&self.p.tys, self.p.fn_info(self.closure_arg(&ops[1])).ret)
                };
                let opt = CTy::Option(Box::new(elem));
                collect_types(&opt, &mut self.sig_types);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                if b == B::BoolThenSome {
                    // The value is eager: it was evaluated as an
                    // argument whether the bool holds or not. On
                    // `false` it drops with the Option it never
                    // entered, as in Rust.
                    let _ = writeln!(self.out, "    if ({}) {{ {field} = {};{some} }}", vals[0], vals[1]);
                    if needs_drop_c(self.p, &tys[1]) {
                        self.want(Glue::Drop, &tys[1]);
                        let d = self.tmp();
                        let _ = writeln!(self.out, "    if (!{}) {{ {} {d} = {}; drop_{}(&{d}); }}", vals[0], ctype(&tys[1]), vals[1], mangle(&tys[1]));
                    }
                } else {
                    let f = self.closure_arg(&ops[1]);
                    let c = self.tmp();
                    let mut body = String::new();
                    let _ = writeln!(body, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                    let _ = writeln!(body, "    if ({}) {{", vals[0]);
                    let (v, _) = self.closure_call_c(&mut body, f, &format!("&{c}"), &[]);
                    let _ = writeln!(body, "      {field} = {v};{some}");
                    let _ = writeln!(body, "    }}");
                    if needs_drop_c(self.p, &tys[1]) {
                        self.want(Glue::Drop, &tys[1]);
                        let _ = writeln!(body, "    drop_{}(&{c});", mangle(&tys[1]));
                    }
                    let _ = write!(self.out, "{body}");
                }
                t
            }
            B::VecReverse => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let et = ctype(&e);
                let (i, t) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    for (uint64_t {i} = 0; {i} < {len} / 2; {i}++) {{ {et} {t} = {ptr}[{i}]; {ptr}[{i}] = {ptr}[{len} - 1 - {i}]; {ptr}[{len} - 1 - {i}] = {t}; }}"
                );
                "((lust_Unit){})".into()
            }
            // `slice::from_ref(&T)` and `from_mut` (fx-option-rest):
            // a one-element slice at the reference itself.
            B::SliceFromRef => {
                let CTy::Ref(e) = &tys[0] else { unreachable!() };
                let et = ctype(e);
                let sl = CTy::Slice(e.clone());
                let (st, t) = (ctype(&sl), self.tmp());
                let vv = &vals[0];
                let _ = writeln!(self.out, "    {st} {t} = {{ ({et}*){vv}, 1 }};");
                t
            }
            // The safe raw pointer surface (w-cinterop): every value is
            // the C address itself.
            B::PtrFromRef => vals[0].clone(),
            B::PtrNull => "((void*)0)".into(),
            B::PtrEqFn => format!("((void*)({}) == (void*)({}))", vals[0], vals[1]),
            B::PtrIsNull => format!("(({}) == 0)", vals[0]),
            B::PtrCast => format!("((void*)({}))", vals[0]),
            B::PtrAddr => format!("((uint64_t)(uintptr_t)({}))", vals[0]),
            B::PtrWithAddr => format!("((void*)(uintptr_t)({}))", vals[1]),
            // `Rc::as_ptr`: the payload behind the counts.
            B::SmartAsPtr => format!("(&(*{})->v)", vals[0]),
            B::SeqAsPtr => slice_like(&tys[0], &vals[0]).1,
            B::StrAsPtr => match &tys[0] {
                CTy::Ref(inner) if **inner == CTy::String => format!("({})->ptr", vals[0]),
                _ => format!("({}).ptr", vals[0]),
            },
            B::VecAsSlice | B::VecAsMutSlice => {
                // `Vec`, arrays, and slices all give the same
                // fat value (core's `as_slice` family).
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let sl = CTy::Slice(Box::new(e));
                let (st, t) = (ctype(&sl), self.tmp());
                let _ = writeln!(self.out, "    {st} {t} = {{ {ptr}, {len} }};");
                t
            }
            B::SliceToVec | B::VecFrom => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let et = ctype(&e);
                // `Vec::from([T; N])` moves its elements; the
                // slice forms clone them. Both allocate exactly.
                let moves = b == B::VecFrom && matches!(tys[0], CTy::Array(..));
                let (t, i) = (self.tmp(), self.tmp());
                let elem = if moves || is_copy_c(self.p, &e) {
                    format!("{ptr}[{i}]")
                } else {
                    self.want(Glue::Clone, &e);
                    format!("clone_{}(&{ptr}[{i}])", mangle(&e))
                };
                let _ = writeln!(
                    self.out,
                    "    lust_Vec {t} = lust_vec_with_capacity({len}, sizeof({et}), _Alignof({et}));\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) (({et}*){t}.ptr)[{i}] = {elem};\n    {t}.len = {len};"
                );
                t
            }
            B::StrFind | B::StrRfind => {
                let a = str_of(&vals[0], &tys[0]);
                let f = if b == B::StrFind { "lust_str_find" } else { "lust_str_rfind" };
                let opt = CTy::Option(Box::new(CTy::Int(IntTy::Usize)));
                collect_types(&opt, &mut self.sig_types);
                let (t, idx) = (self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    int64_t {idx} = {f}({a}, {});", vals[1]);
                let _ = writeln!(self.out, "    if ({idx} >= 0) {{ {field} = (uint64_t){idx};{some} }}");
                t
            }
            B::StrContains | B::StrStartsWith | B::StrEndsWith => {
                let a = str_of(&vals[0], &tys[0]);
                let f = match b {
                    B::StrContains => "lust_str_contains",
                    B::StrStartsWith => "lust_str_starts_with",
                    _ => "lust_str_ends_with",
                };
                format!("{f}({a}, {})", vals[1])
            }
            B::StrTrim => format!("lust_str_trim({})", str_of(&vals[0], &tys[0])),
            B::StrToAsciiLowercase => format!("lust_str_ascii_case({}, 0)", str_of(&vals[0], &tys[0])),
            B::StrToAsciiUppercase => format!("lust_str_ascii_case({}, 1)", str_of(&vals[0], &tys[0])),
            B::StringFromUtf16Lossy => {
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                format!("lust_string_from_utf16_lossy({ptr}, {len})")
            }
            B::StrToUppercase => format!("lust_str_case({}, 1)", str_of(&vals[0], &tys[0])),
            B::StrToLowercase => format!("lust_str_case({}, 0)", str_of(&vals[0], &tys[0])),
            B::StrChars => format!("lust_chars({})", str_of(&vals[0], &tys[0])),
            B::CharsNext => {
                let t = self.tmp();
                let it = &vals[0];
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ =
                    writeln!(self.out, "    if ({it}->pos < {it}->s.len) {{ {field} = lust_utf8_next({it}->s.ptr, &{it}->pos);{some} }}");
                t
            }
            B::CharsNextBack => {
                let t = self.tmp();
                let it = &vals[0];
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if ({it}->pos < {it}->s.len) {{ {field} = lust_utf8_prev({it}->s.ptr, &{it}->s.len);{some} }}");
                t
            }
            B::CharsCount => format!("lust_chars_count({})", vals[0]),
            // `Utf8Chunks::next` (tf-slice): the iterator is a
            // one-field tuple of the bytes left; a chunk is the
            // (valid, invalid) pair the runtime scan splits off.
            B::Utf8ChunksNext => {
                let it = &vals[0];
                let chunk = CTy::Tuple(vec![CTy::Ref(Box::new(CTy::Str)), CTy::Slice(Box::new(CTy::Int(IntTy::U8)))]);
                let opt = CTy::Option(Box::new(chunk.clone()));
                collect_types(&opt, &mut self.sig_types);
                let (t, vl, us) = (self.tmp(), self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    if ({it}->f0.len > 0) {{ uint64_t {vl} = 0, {us} = 0;\n      lust_utf8_chunk_step({it}->f0.ptr, {it}->f0.len, &{vl}, &{us});\n      {field}.f0 = (lust_str){{ {it}->f0.ptr, {vl} }};\n      {field}.f1 = ({}){{ {it}->f0.ptr + {vl}, {us} - {vl} }};{some}\n      {it}->f0.ptr += {us}; {it}->f0.len -= {us}; }}",
                    ctype(&CTy::Slice(Box::new(CTy::Int(IntTy::U8))))
                );
                t
            }
            B::Utf8ChunkValid => format!("(*{}).f0", vals[0]),
            B::Utf8ChunkInvalid => format!("(*{}).f1", vals[0]),
            B::CharIsDigit => format!("(*{0} >= '0' && *{0} <= '9')", vals[0]),
            B::CharIsAlphabetic => format!("((*{0} | 32) >= 'a' && (*{0} | 32) <= 'z')", vals[0]),
            B::CharIsAlphanumeric => format!("((*{0} >= '0' && *{0} <= '9') || ((*{0} | 32) >= 'a' && (*{0} | 32) <= 'z'))", vals[0]),
            B::CharIsWhitespace => format!("(*{0} == ' ' || *{0} == '\\t' || *{0} == '\\n' || *{0} == '\\r' || *{0} == 12)", vals[0]),
            B::CharIsUppercase => format!("(*{0} >= 'A' && *{0} <= 'Z')", vals[0]),
            B::CharIsLowercase => format!("(*{0} >= 'a' && *{0} <= 'z')", vals[0]),
            B::CharIsAlphabeticUnicode => format!("lust_char_is_alphabetic({})", vals[0]),
            B::CharIsNumericUnicode => format!("lust_char_is_numeric({})", vals[0]),
            B::CharIsAlphanumericUnicode => format!("lust_char_is_alphanumeric({})", vals[0]),
            B::CharIsLowercaseUnicode => format!("lust_char_is_lowercase({})", vals[0]),
            B::CharIsUppercaseUnicode => format!("lust_char_is_uppercase({})", vals[0]),
            B::CharIsWhitespaceUnicode => format!("lust_is_space({})", vals[0]),
            B::CharIsControlUnicode => format!("lust_char_is_control({})", vals[0]),
            B::CharFromU32 => {
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {{ uint32_t d = {}; if (d <= 0x10FFFFu && !(d >= 0xD800u && d <= 0xDFFFu)) {{ {field} = d;{some} }} }}",
                    vals[0]
                );
                t
            }
            B::CharFromDigit => {
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {{ uint32_t d = lust_from_digit({}, {}, {}); if (d != 0xFFFFFFFFu) {{ {field} = d;{some} }} }}",
                    vals[0],
                    vals[1],
                    std_loc(2, 332, 9)
                );
                t
            }
            B::CharToUppercase => format!("((*{0} >= 'a' && *{0} <= 'z') ? *{0} - 32 : *{0})", vals[0]),
            B::CharToLowercase => format!("((*{0} >= 'A' && *{0} <= 'Z') ? *{0} + 32 : *{0})", vals[0]),
            B::MakeAsciiLowercase | B::MakeAsciiUppercase => {
                let p = self.tmp();
                let et = ctype(match &tys[0] {
                    CTy::Ref(inner) => inner,
                    other => other,
                });
                let expr = if b == B::MakeAsciiLowercase {
                    format!("((*{p} >= 'A' && *{p} <= 'Z') ? *{p} + 32 : *{p})")
                } else {
                    format!("((*{p} >= 'a' && *{p} <= 'z') ? *{p} - 32 : *{p})")
                };
                let _ = writeln!(self.out, "    {et}* {p} = {}; *{p} = ({et}){expr};", vals[0]);
                "((lust_Unit){})".into()
            }
            B::CharToDigit => {
                let opt = CTy::Option(Box::new(CTy::Int(IntTy::U32)));
                let ot = ctype(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {{ uint32_t d = lust_digit({}, {}, {}); if (d != 0xFFFFFFFFu) {{ {field} = d;{some} }} }}",
                    vals[0],
                    vals[1],
                    std_loc(1, 407, 9)
                );
                t
            }
            B::MemSwap => {
                // A byte exchange through a stack temp: both places
                // stay initialized, so their drop flags are untouched.
                let CTy::Ref(inner) = &tys[0] else { unreachable!() };
                let et = ctype(inner);
                let (pa, pb, t) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {et}* {pa} = {}; {et}* {pb} = {}; {et} {t}; lust_memcpy(&{t}, {pa}, sizeof({et})); lust_memcpy({pa}, {pb}, sizeof({et})); lust_memcpy({pb}, &{t}, sizeof({et}));",
                    vals[0], vals[1]
                );
                "((lust_Unit){})".into()
            }
            B::MemReplace => {
                let CTy::Ref(inner) = &tys[0] else { unreachable!() };
                let et = ctype(inner);
                let (pa, nv, old) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {et}* {pa} = {}; {et} {nv} = {}; {et} {old}; lust_memcpy(&{old}, {pa}, sizeof({et})); lust_memcpy({pa}, &{nv}, sizeof({et}));",
                    vals[0], vals[1]
                );
                old
            }
            B::MemTake => unreachable!("take lowers to a default fill plus MemReplace"),
            B::CmpMax | B::CmpMin => {
                // Check limited these to primitive total orders. On
                // a tie the first argument wins, as `Ord::max` and
                // `Ord::min` specify (the loser would drop, but a
                // primitive has no destructor).
                let ct = ctype(&tys[0]);
                let (a, bb) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {ct} {a} = {}; {ct} {bb} = {};", vals[0], vals[1]);
                let ge = b == B::CmpMax;
                match &tys[0] {
                    CTy::Int(it) if is128(*it) => {
                        let f = if *it == IntTy::I128 { "lust_i128_cmp" } else { "lust_u128_cmp" };
                        if ge { format!("(({f}({a}, {bb}) >= 0) ? {a} : {bb})") } else { format!("(({f}({a}, {bb}) <= 0) ? {a} : {bb})") }
                    }
                    _ => {
                        if ge {
                            format!("(({a} >= {bb}) ? {a} : {bb})")
                        } else {
                            format!("(({a} <= {bb}) ? {a} : {bb})")
                        }
                    }
                }
            }
        }
    }

    // ---------- Formatting ----------

    /// The C for one inherent integer method (see the family arms in
    /// `builtin`). Widths up to 64 run through the generic word ops in
    /// core.c; 128-bit values use the two-word helpers for the subset
    /// the checker lets through.
    fn int_method_c(&mut self, b: Builtin, vals: &[String], tys: &[CTy], loc: &str) -> String {
        use Builtin as B;
        use std::fmt::Write as _;
        let it = match &tys[0] {
            CTy::Int(i) => *i,
            _ => IntTy::I64,
        };
        if is128(it) {
            return self.int128_method_c(b, vals, it, loc);
        }
        let bits = it.bits();
        let sgn = it.signed();
        let ct = int_c(it);
        let a = &vals[0];
        let ua = format!("((uint64_t)({a}))");
        let ub = if vals.len() > 1 { format!("((uint64_t)({}))", vals[1]) } else { String::new() };
        let mask = if bits >= 64 { "~0ull".to_string() } else { format!("((1ull << {bits}) - 1ull)") };
        let masked_a = format!("({ua} & {mask})");
        let div0 = |b: Builtin| -> &'static str {
            if matches!(b, B::WrappingRem | B::CheckedRem | B::SaturatingDiv) {
                "attempt to calculate the remainder with a divisor of zero"
            } else {
                "attempt to divide by zero"
            }
        };
        // A checked_op call into fresh (out, rc) temporaries. Returns
        // the statement text; rc is 1 ok, 0 overflow, -1 div by zero.
        let checked_call = |this: &mut Self, a64: &str, b64: &str, op: i32| -> (String, String) {
            let (o, rc) = (this.tmp(), this.tmp());
            let _ = write!(this.out, "    uint64_t {o}; int {rc} = lust_checked_op({a64}, {b64}, {bits}, {}, {op}, &{o});\n", sgn as i32);
            (o, rc)
        };
        match b {
            B::WrappingDiv | B::WrappingRem => {
                let op = if b == B::WrappingDiv { 3 } else { 4 };
                let (o, rc) = checked_call(self, &ua, &ub, op);
                let msg = div0(b);
                // The signed forms divide inside core; the unsigned ones at the caller.
                let at = if sgn { num_loc(it, false) } else { loc.to_string() };
                let _ = writeln!(self.out, "    if ({rc} < 0) lust_panic_cstr(\"{msg}\", {at});");
                format!("(({ct}){o})")
            }
            B::WrappingNeg => format!("(({ct})((0ull - {ua}) & {mask}))"),
            B::WrappingAbs => format!("(({a} < 0 ? ({ct})((0ull - {ua}) & {mask}) : {a}))"),
            B::WrappingPow => format!("(({ct})lust_wrapping_pow({ua}, {}, {bits}))", vals[1]),
            B::WrappingShl => format!("(({ct})(({masked_a} << ({} & {})) & {mask}))", vals[1], bits - 1),
            B::WrappingShr => {
                if sgn {
                    format!("(({ct})(((int64_t)({a}) >> ({} & {})) & (int64_t){mask}))", vals[1], bits - 1)
                } else {
                    format!("(({ct})({masked_a} >> ({} & {})))", vals[1], bits - 1)
                }
            }
            B::CheckedAdd | B::CheckedSub | B::CheckedMul | B::CheckedDiv | B::CheckedRem => {
                let op = match b {
                    B::CheckedAdd => 0,
                    B::CheckedSub => 1,
                    B::CheckedMul => 2,
                    B::CheckedDiv => 3,
                    _ => 4,
                };
                let (o, rc) = checked_call(self, &ua, &ub, op);
                self.int_option_c(&format!("(({ct}){o})"), &format!("{rc} == 1"), it)
            }
            B::CheckedNeg => {
                let (o, rc) = checked_call(self, "0ull", &ua, 1);
                self.int_option_c(&format!("(({ct}){o})"), &format!("{rc} == 1"), it)
            }
            B::CheckedAbs => {
                let x = self.tmp();
                let _ = writeln!(self.out, "    {ct} {x} = {a};");
                let (o, rc) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {o}; int {rc} = {x} >= 0 ? ({o} = (uint64_t){x}, 1) : lust_checked_op(0ull, (uint64_t){x}, {bits}, {}, 1, &{o});",
                    sgn as i32
                );
                self.int_option_c(&format!("(({ct}){o})"), &format!("{rc} == 1"), it)
            }
            B::CheckedPow => {
                let (o, rc) = (self.tmp(), self.tmp());
                let _ =
                    writeln!(self.out, "    uint64_t {o}; int {rc} = lust_checked_pow({ua}, {}, {bits}, {}, &{o});", vals[1], sgn as i32);
                self.int_option_c(&format!("(({ct}){o})"), &format!("{rc} == 1"), it)
            }
            B::CheckedShl | B::CheckedShr => {
                let amt = &vals[1];
                let r = if b == B::CheckedShl {
                    format!("(({ct})(({masked_a} << ({amt} & 63u)) & {mask}))")
                } else if sgn {
                    format!("(({ct})(((int64_t)({a}) >> ({amt} & 63u)) & (int64_t){mask}))")
                } else {
                    format!("(({ct})({masked_a} >> ({amt} & 63u)))")
                };
                self.int_option_c(&r, &format!("{amt} < {bits}u"), it)
            }
            B::StrictAdd | B::StrictSub | B::StrictMul | B::StrictDiv | B::StrictRem => {
                let (op, verb) = match b {
                    B::StrictAdd => (0, "add"),
                    B::StrictSub => (1, "subtract"),
                    B::StrictMul => (2, "multiply"),
                    B::StrictDiv => (3, "divide"),
                    _ => (4, "calculate the remainder"),
                };
                let (o, rc) = checked_call(self, &ua, &ub, op);
                let div0msg = if op == 4 {
                    "attempt to calculate the remainder with a divisor of zero"
                } else {
                    "attempt to divide by zero"
                };
                let _ = writeln!(self.out, "    if ({rc} < 0) lust_panic_cstr(\"{div0msg}\", {loc});");
                let _ = writeln!(self.out, "    if ({rc} == 0) lust_panic_cstr(\"attempt to {verb} with overflow\", {loc});");
                format!("(({ct}){o})")
            }
            B::StrictNeg => {
                let (o, rc) = checked_call(self, "0ull", &ua, 1);
                let _ = writeln!(self.out, "    if ({rc} == 0) lust_panic_cstr(\"attempt to negate with overflow\", {loc});");
                format!("(({ct}){o})")
            }
            B::StrictAbs => {
                let x = self.tmp();
                let _ = writeln!(self.out, "    {ct} {x} = {a};");
                let (o, rc) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {o}; int {rc} = {x} >= 0 ? ({o} = (uint64_t){x}, 1) : lust_checked_op(0ull, (uint64_t){x}, {bits}, {}, 1, &{o});",
                    sgn as i32
                );
                let _ = writeln!(self.out, "    if ({rc} == 0) lust_panic_cstr(\"attempt to negate with overflow\", {loc});");
                format!("(({ct}){o})")
            }
            B::StrictPow => {
                let (o, rc) = (self.tmp(), self.tmp());
                let _ =
                    writeln!(self.out, "    uint64_t {o}; int {rc} = lust_checked_pow({ua}, {}, {bits}, {}, &{o});", vals[1], sgn as i32);
                let _ = writeln!(self.out, "    if ({rc} == 0) lust_panic_cstr(\"attempt to exponentiate with overflow\", {loc});");
                format!("(({ct}){o})")
            }
            B::StrictShl | B::StrictShr => {
                let amt = &vals[1];
                let (msg, r) = if b == B::StrictShl {
                    ("attempt to shift left with overflow", format!("(({ct})(({masked_a} << ({amt} & 63u)) & {mask}))"))
                } else if sgn {
                    ("attempt to shift right with overflow", format!("(({ct})(((int64_t)({a}) >> ({amt} & 63u)) & (int64_t){mask}))"))
                } else {
                    ("attempt to shift right with overflow", format!("(({ct})({masked_a} >> ({amt} & 63u)))"))
                };
                let t = self.tmp();
                let _ = writeln!(self.out, "    if ({amt} >= {bits}u) lust_panic_cstr(\"{msg}\", {loc}); {ct} {t} = {r};");
                t
            }
            B::MixedCheckedAdd
            | B::MixedCheckedSub
            | B::MixedWrappingAdd
            | B::MixedWrappingSub
            | B::MixedSaturatingAdd
            | B::MixedSaturatingSub
            | B::MixedOverflowingAdd
            | B::MixedOverflowingSub
            | B::MixedStrictAdd
            | B::MixedStrictSub => self.mixed_op_c(b, vals, it, loc),
            B::CheckedSignedDiff => {
                let masked_b = format!("({ub} & {mask})");
                let sct = int_c(it.counterpart());
                let smax = format!("(({sct}){}ll)", if bits >= 64 { i64::MAX } else { (1i64 << (bits - 1)) - 1 });
                let (x, y) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    uint64_t {x} = {masked_a}, {y} = {masked_b};");
                let diff = format!("(({sct})(({x} - {y}) & {mask}))");
                let fits = format!(
                    "({x} >= {y} ? ({x} - {y}) <= (uint64_t){smax} : ({y} - {x}) <= (uint64_t){smax} + 1ull)"
                );
                self.int_option_c(&diff, &fits, it.counterpart())
            }
            B::CarryingAdd | B::BorrowingSub => {
                let masked_b = format!("({ub} & {mask})");
                let (x, y, t) = (self.tmp(), self.tmp(), self.tmp());
                let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
                let tt = ctype(&tup);
                let _ = writeln!(self.out, "    uint64_t {x} = {masked_a}, {y} = {masked_b};");
                if b == B::CarryingAdd {
                    let _ = writeln!(
                        self.out,
                        "    {tt} {t}; {{ uint64_t s = {x} + {y} + ({} ? 1ull : 0ull); {t}.f0 = ({ct})(s & {mask}); {t}.f1 = s > {mask} || s < {x} || ({} && s == {x} && {y} == {mask}); }}",
                        vals[2], vals[2]
                    );
                } else {
                    let _ = writeln!(
                        self.out,
                        "    {tt} {t}; {t}.f0 = ({ct})(({x} - {y} - ({} ? 1ull : 0ull)) & {mask}); {t}.f1 = {x} < {y} || ({} && {x} == {y});",
                        vals[2],
                        vals[2]
                    );
                }
                t
            }
            B::CarryingMul | B::CarryingMulAdd => {
                let masked_b = format!("({ub} & {mask})");
                let (p, t) = (self.tmp(), self.tmp());
                let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Int(it)]);
                let tt = ctype(&tup);
                let add = if b == B::CarryingMulAdd {
                    format!("lust_u128_add(lust_u128_add({p}, (lust_u128){{{}, 0}}), (lust_u128){{{}, 0}})", format!("({} & {mask})", vals[2]), format!("((uint64_t)({}) & {mask})", vals[3]))
                } else {
                    format!("lust_u128_add({p}, (lust_u128){{{}, 0}})", format!("({} & {mask})", vals[2]))
                };
                let hi = if bits >= 64 {
                    format!("{p}.hi")
                } else {
                    format!("(({p}.lo >> {bits}) | ({p}.hi << (64 - {bits})))")
                };
                let _ = writeln!(
                    self.out,
                    "    lust_u128 {p} = lust_u128_mul((lust_u128){{{masked_a}, 0}}, (lust_u128){{{masked_b}, 0}}); {p} = {add}; {tt} {t}; {t}.f0 = ({ct})({p}.lo & {mask}); {t}.f1 = ({ct})({hi} & {mask});",
                );
                t
            }
            _ => self.int_method_c2(b, vals, it, loc),
        }
    }

    /// One mixed-sign operation (`checked_add_unsigned` and kin):
    /// the receiver keeps its type, the argument has the other
    /// signedness at the same width. Computes the wrapped result
    /// and the overflow flag on the masked 64-bit forms, then
    /// shapes them by family: checked -> Option, wrapping -> the
    /// value, saturating -> clamped, overflowing -> (value, flag),
    /// strict -> panic on overflow.
    fn mixed_op_c(&mut self, b: Builtin, vals: &[String], it: IntTy, loc: &str) -> String {
        use Builtin as B;
        use std::fmt::Write as _;
        let bits = it.bits();
        let sgn = it.signed();
        let ct = int_c(it);
        let sub = matches!(b, B::MixedCheckedSub | B::MixedWrappingSub | B::MixedSaturatingSub | B::MixedOverflowingSub | B::MixedStrictSub);
        let (x, y, r, ovf) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
        let mask: String = if bits >= 64 { "~0ull".into() } else { format!("((1ull << {bits}) - 1ull)") };
        let max_u = if sgn {
            if bits >= 64 { "0x7FFFFFFFFFFFFFFFull".to_string() } else { format!("{}ull", (1u128 << (bits - 1)) - 1) }
        } else {
            mask.clone()
        };
        let min_u = if sgn { format!("(1ull << {})", bits - 1) } else { "0ull".to_string() };
        let _ = writeln!(self.out, "    {ct} {x} = {}; uint64_t {y} = (uint64_t)({}) & {mask};", vals[0], vals[1]);
        if sgn {
            // Signed receiver, unsigned magnitude argument.
            let (thr, op) = if sub { (format!("((uint64_t){x} - {min_u})"), "-") } else { (format!("({max_u} - (uint64_t){x})"), "+") };
            let _ = writeln!(self.out, "    uint64_t {r} = ((uint64_t){x} {op} {y}) & {mask}; int {ovf} = {y} > {thr};");
        } else {
            // Unsigned receiver, signed argument: its sign decides
            // which end can overflow. A negative argument's
            // magnitude is its two's-complement negation.
            let sct = int_c(it.counterpart());
            let (neg_room, pos_room) = if sub {
                (format!("({mask} - ({x} & {mask}))"), format!("({x} & {mask})"))
            } else {
                (format!("({x} & {mask})"), format!("({mask} - ({x} & {mask}))"))
            };
            let _ = writeln!(
                self.out,
                "    uint64_t {r} = (({x} {} {y}) & {mask}); int {ovf} = (({sct}){y} < 0) ? (((0ull - {y}) & {mask}) > {neg_room}) : ({y} > {pos_room});",
                if sub { "-" } else { "+" }
            );
        }
        let val = format!("(({ct}){r})");
        match b {
            B::MixedWrappingAdd | B::MixedWrappingSub => val,
            B::MixedCheckedAdd | B::MixedCheckedSub => self.int_option_c(&val, &format!("!{ovf}"), it),
            B::MixedOverflowingAdd | B::MixedOverflowingSub => {
                let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
                let tt = ctype(&tup);
                let t = self.tmp();
                let _ = writeln!(self.out, "    {tt} {t}; {t}.f0 = {val}; {t}.f1 = {ovf};");
                t
            }
            B::MixedSaturatingAdd | B::MixedSaturatingSub => {
                // One overflow direction per form, named by the
                // argument's sign for an unsigned receiver: adding
                // or subtracting an unsigned magnitude can only
                // pass the top (add) or the bottom (sub) end.
                let t = self.tmp();
                let hi = format!("(({ct}){max_u})");
                let lo = if sgn {
                    if bits >= 64 {
                        format!("(({ct})(-9223372036854775807ll - 1))")
                    } else {
                        format!("(({ct}){}ll)", -(1i128 << (bits - 1)))
                    }
                } else {
                    format!("(({ct})0)")
                };
                let clamp = if sgn {
                    if sub { lo } else { hi }
                } else if sub {
                    format!("((({}){} < 0) ? {hi} : {lo})", int_c(it.counterpart()), y)
                } else {
                    format!("((({}){} < 0) ? {lo} : {hi})", int_c(it.counterpart()), y)
                };
                let _ = writeln!(self.out, "    {ct} {t} = {ovf} ? {clamp} : {val};");
                t
            }
            _ => {
                let verb = if sub { "subtract" } else { "add" };
                let t = self.tmp();
                let _ = writeln!(self.out, "    if ({ovf}) lust_panic_cstr(\"attempt to {verb} with overflow\", {loc}); {ct} {t} = {val};");
                t
            }
        }
    }

    /// An Option<int> value holding `expr` when `cond` holds, else None.
    fn int_option_c(&mut self, expr: &str, cond: &str, it: IntTy) -> String {
        use std::fmt::Write as _;
        let opt = CTy::Option(Box::new(CTy::Int(it)));
        let ot = ctype(&opt);
        let t = self.tmp();
        let field = variant_field(self.p, &opt, &t, 1, 0);
        let some = disc_set(self.p, &opt, &t, 1);
        let some = if some.is_empty() { String::new() } else { format!(" {some}") };
        let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
        let _ = writeln!(self.out, "    if ({cond}) {{ {field} = {expr};{some} }}");
        t
    }

    /// The saturating, overflowing, and bit inspection families.
    fn int_method_c2(&mut self, b: Builtin, vals: &[String], it: IntTy, loc: &str) -> String {
        use Builtin as B;
        use std::fmt::Write as _;
        let bits = it.bits();
        let sgn = it.signed();
        let ct = int_c(it);
        let a = &vals[0];
        let ua = format!("((uint64_t)({a}))");
        let ub = if vals.len() > 1 { format!("((uint64_t)({}))", vals[1]) } else { String::new() };
        let mask: String = if bits >= 64 { "~0ull".into() } else { format!("((1ull << {bits}) - 1ull)") };
        let masked_a = format!("({ua} & {mask})");
        let max_lit = if sgn {
            if bits >= 64 { format!("(({ct})0x7FFFFFFFFFFFFFFFll)") } else { format!("(({ct}){}ll)", (1i128 << (bits - 1)) - 1) }
        } else if bits >= 64 {
            format!("(({ct})~0ull)")
        } else {
            format!("(({ct}){}ull)", (1u128 << bits) - 1)
        };
        let min_lit = if sgn {
            if bits >= 64 { format!("(({ct})(-9223372036854775807ll - 1))") } else { format!("(({ct}){}ll)", -(1i128 << (bits - 1))) }
        } else {
            format!("(({ct})0)")
        };
        let sa = format!("((int64_t)({a}))");
        let sb = if vals.len() > 1 { format!("((int64_t)({}))", vals[1]) } else { String::new() };
        let sat_op = |b: Builtin| -> Option<i32> {
            Some(match b {
                B::SaturatingAdd | B::OverflowingAdd => 0,
                B::SaturatingSub | B::OverflowingSub => 1,
                B::SaturatingMul | B::OverflowingMul => 2,
                B::SaturatingDiv | B::OverflowingDiv => 3,
                B::OverflowingRem => 4,
                _ => return None,
            })
        };
        if let Some(op) = sat_op(b) {
            let (o, rc) = (self.tmp(), self.tmp());
            let _ = writeln!(self.out, "    uint64_t {o}; int {rc} = lust_checked_op({ua}, {ub}, {bits}, {}, {op}, &{o});", sgn as i32);
            let div0msg = if op == 4 { "attempt to calculate the remainder with a divisor of zero" } else { "attempt to divide by zero" };
            // The signed forms divide inside core; the unsigned ones at the caller.
            let at = if sgn { num_loc(it, false) } else { loc.to_string() };
            let _ = writeln!(self.out, "    if ({rc} < 0) lust_panic_cstr(\"{div0msg}\", {at});");
            if matches!(b, B::SaturatingAdd | B::SaturatingSub | B::SaturatingMul | B::SaturatingDiv) {
                // Clamp to the endpoint the true result passes.
                let clamp = if !sgn {
                    if op == 1 { min_lit.clone() } else { max_lit.clone() }
                } else {
                    match op {
                        0 | 1 => format!("({sa} >= 0 ? {max_lit} : {min_lit})"),
                        2 => format!("((({sa} < 0) != ({sb} < 0)) ? {min_lit} : {max_lit})"),
                        _ => max_lit.clone(),
                    }
                };
                let t = self.tmp();
                let _ = writeln!(self.out, "    {ct} {t} = {rc} == 1 ? ({ct}){o} : {clamp};");
                return t;
            }
            // Overflowing: (wrapping result, overflowed).
            let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
            let tt = ctype(&tup);
            let t = self.tmp();
            let _ = writeln!(self.out, "    {tt} {t}; {t}.f0 = ({ct}){o}; {t}.f1 = {rc} == 0;");
            return t;
        }
        match b {
            B::SaturatingNeg | B::SaturatingAbs => {
                let x = self.tmp();
                let _ = writeln!(self.out, "    {ct} {x} = {a};");
                let t = self.tmp();
                let inner = if b == B::SaturatingNeg {
                    format!("{x} == {min_lit} ? {max_lit} : -{x}")
                } else {
                    format!("{x} == {min_lit} ? {max_lit} : ({x} < 0 ? -{x} : {x})")
                };
                let _ = writeln!(self.out, "    {ct} {t} = {inner};");
                t
            }
            B::OverflowingNeg | B::OverflowingAbs => {
                let (o, rc) = (self.tmp(), self.tmp());
                if b == B::OverflowingNeg {
                    let _ =
                        writeln!(self.out, "    uint64_t {o}; int {rc} = lust_checked_op(0ull, {ua}, {bits}, {}, 1, &{o});", sgn as i32);
                } else {
                    let x = self.tmp();
                    let _ = writeln!(self.out, "    {ct} {x} = {a};");
                    let _ = writeln!(
                        self.out,
                        "    uint64_t {o}; int {rc} = {x} >= 0 ? ({o} = (uint64_t){x}, 1) : lust_checked_op(0ull, (uint64_t){x}, {bits}, {}, 1, &{o});",
                        sgn as i32
                    );
                }
                let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
                let tt = ctype(&tup);
                let t = self.tmp();
                let _ = writeln!(self.out, "    {tt} {t}; {t}.f0 = ({ct}){o}; {t}.f1 = {rc} == 0;");
                t
            }
            B::SaturatingPow | B::OverflowingPow => {
                let (o, rc) = (self.tmp(), self.tmp());
                let _ =
                    writeln!(self.out, "    uint64_t {o}; int {rc} = lust_checked_pow({ua}, {}, {bits}, {}, &{o});", vals[1], sgn as i32);
                if b == B::SaturatingPow {
                    let clamp = if sgn { format!("(({sa} < 0 && ({} & 1u)) ? {min_lit} : {max_lit})", vals[1]) } else { max_lit.clone() };
                    let t = self.tmp();
                    let _ = writeln!(self.out, "    {ct} {t} = {rc} == 1 ? ({ct}){o} : {clamp};");
                    t
                } else {
                    let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
                    let tt = ctype(&tup);
                    let t = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    {tt} {t}; {t}.f0 = ({ct})lust_wrapping_pow({ua}, {}, {bits}); {t}.f1 = {rc} == 0;",
                        vals[1]
                    );
                    t
                }
            }
            B::OverflowingShl | B::OverflowingShr => {
                let amt = &vals[1];
                let r = if b == B::OverflowingShl {
                    format!("(({ct})(({masked_a} << ({amt} & {})) & {mask}))", bits - 1)
                } else if sgn {
                    format!("(({ct})(((int64_t)({a}) >> ({amt} & {})) & (int64_t){mask}))", bits - 1)
                } else {
                    format!("(({ct})({masked_a} >> ({amt} & {})))", bits - 1)
                };
                let tup = CTy::Tuple(vec![CTy::Int(it), CTy::Bool]);
                let tt = ctype(&tup);
                let t = self.tmp();
                let _ = writeln!(self.out, "    {tt} {t}; {t}.f0 = {r}; {t}.f1 = {amt} >= {bits}u;");
                t
            }
            B::CountOnes => format!("lust_count_ones64({masked_a})"),
            B::CountZeros => format!("({bits}u - lust_count_ones64({masked_a}))"),
            B::LeadingZeros => format!("lust_leading_zeros64({masked_a}, {bits})"),
            B::TrailingZeros => format!("lust_trailing_zeros64({masked_a}, {bits})"),
            B::LeadingOnes => format!("lust_leading_zeros64((~{ua}) & {mask}, {bits})"),
            B::TrailingOnes => format!("lust_trailing_zeros64((~{ua}) & {mask}, {bits})"),
            B::RotateLeft | B::RotateRight => {
                let (x, n) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    uint64_t {x} = {masked_a}; uint32_t {n} = {} & {};", vals[1], bits - 1);
                if b == B::RotateLeft {
                    format!("(({ct})((({x} << {n}) | ({x} >> (({bits} - {n}) & {}))) & {mask}))", bits - 1)
                } else {
                    format!("(({ct})((({x} >> {n}) | ({x} << (({bits} - {n}) & {}))) & {mask}))", bits - 1)
                }
            }
            B::SwapBytes => {
                let (x, r, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {x} = {masked_a}, {r} = 0; for (uint32_t {i} = 0; {i} < {bits} / 8; {i}++) {r} = ({r} << 8) | (({x} >> (8 * {i})) & 0xFFull);"
                );
                format!("(({ct}){r})")
            }
            B::ReverseBits => {
                let (x, r, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {x} = {masked_a}, {r} = 0; for (uint32_t {i} = 0; {i} < {bits}; {i}++) {r} |= (({x} >> {i}) & 1ull) << ({bits} - 1 - {i});"
                );
                format!("(({ct}){r})")
            }
            B::DivCeil => format!("(({ct})lust_div_ceil({ua}, {ub}, {bits}, {loc}))"),
            B::DivEuclid | B::StrictDivEuclid => format!("(({ct})lust_div_euclid({ua}, {ub}, {bits}, {}, {loc}))", sgn as i32),
            B::RemEuclid | B::StrictRemEuclid => format!("(({ct})lust_rem_euclid({ua}, {ub}, {bits}, {}, {loc}))", sgn as i32),
            B::Signum => format!("(({ct})(({a} > 0) - ({a} < 0)))"),
            B::IsPositive => format!("({a} > 0)"),
            B::IsNegative => format!("({a} < 0)"),
            B::IsPowerOfTwo => format!("({masked_a} != 0 && ({masked_a} & ({masked_a} - 1)) == 0)"),
            B::IsMultipleOf => {
                let masked_b = format!("({ub} & {mask})");
                format!("({masked_b} == 0 ? {masked_a} == 0 : ({masked_a} % {masked_b}) == 0)")
            }
            B::NextMultipleOf | B::CheckedNextMultipleOf => {
                let (x, y, add, t) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let nloc = num_loc(it, false);
                let _ = writeln!(self.out, "    uint64_t {x} = {masked_a}, {y} = ({ub} & {mask});");
                if b == B::NextMultipleOf {
                    let _ = writeln!(
                        self.out,
                        "    if ({y} == 0) lust_panic_cstr(\"attempt to calculate the remainder with a divisor of zero\", {nloc});"
                    );
                }
                let _ = writeln!(
                    self.out,
                    "    uint64_t {add} = {y} == 0 ? 0 : ({x} % {y} == 0 ? 0 : {y} - {x} % {y}); {ct} {t} = ({ct})(({x} + {add}) & {mask});"
                );
                if b == B::NextMultipleOf {
                    let _ = writeln!(self.out, "    if ({add} > ({mask}) - {x}) lust_panic_cstr(\"attempt to add with overflow\", {nloc});");
                    t
                } else {
                    self.int_option_c(&t, &format!("{y} != 0 && {add} <= ({mask}) - {x}"), it)
                }
            }
            B::UnsignedAbs => {
                let uct = int_c(it.counterpart());
                format!("(({uct})(({a} < 0 ? (0ull - {ua}) : {ua}) & {mask}))")
            }
            B::UnboundedShl => format!("(({}) >= {bits}u ? ({ct})0 : ({ct})(({masked_a} << {}) & {mask}))", vals[1], vals[1]),
            B::UnboundedShr => {
                if sgn {
                    format!("(({}) >= {bits}u ? ({ct})(({a} < 0) ? -1 : 0) : ({ct})(((int64_t)({a}) >> {}) & (int64_t){mask}))", vals[1], vals[1])
                } else {
                    format!("(({}) >= {bits}u ? ({ct})0 : ({ct})({masked_a} >> {}))", vals[1], vals[1])
                }
            }
            B::CastSigned | B::CastUnsigned => format!("(({})({a}))", int_c(it.counterpart())),
            B::BitWidth => format!("({bits}u - lust_leading_zeros64({masked_a}, {bits}))"),
            B::HighestOne => self.int_option_c(&format!("({bits}u - 1u - lust_leading_zeros64({masked_a}, {bits}))"), &format!("{masked_a} != 0"), IntTy::U32),
            B::LowestOne => self.int_option_c(&format!("lust_trailing_zeros64({masked_a}, {bits})"), &format!("{masked_a} != 0"), IntTy::U32),
            B::IsolateLowestOne => format!("(({ct})({masked_a} & (0ull - {masked_a}) & {mask}))"),
            B::IsolateHighestOne => {
                let (x, t) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {x} = {masked_a}; {ct} {t} = {x} == 0 ? ({ct})0 : ({ct})((1ull << ({bits} - 1 - lust_leading_zeros64({x}, {bits}))) & {mask});"
                );
                t
            }
            B::Isqrt | B::CheckedIsqrt => {
                let root = format!("lust_isqrt64({masked_a})");
                if b == B::CheckedIsqrt {
                    self.int_option_c(&format!("(({ct}){root})"), &format!("{a} >= 0"), it)
                } else if sgn {
                    let t = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    if ({a} < 0) lust_panic_cstr(\"argument of integer square root cannot be negative\", {loc}); {ct} {t} = ({ct}){root};"
                    );
                    t
                } else {
                    format!("(({ct}){root})")
                }
            }
            // `midpoint` rounds toward zero and cannot overflow:
            // opposite signs sum safely, equal signs go through the
            // unsigned bit trick on the magnitudes.
            B::IntMidpoint => {
                let masked_b = format!("({ub} & {mask})");
                if !sgn {
                    format!("(({ct})((({masked_a} & {masked_b}) + (({masked_a} ^ {masked_b}) >> 1)) & {mask}))")
                } else {
                    let (x, y, t) = (self.tmp(), self.tmp(), self.tmp());
                    let _ = writeln!(self.out, "    {ct} {x} = {a}, {y} = {};", vals[1]);
                    let _ = writeln!(
                        self.out,
                        "    {ct} {t} = ({x} < 0) != ({y} < 0) ? ({ct})(((int64_t){x} + (int64_t){y}) / 2) : {x} >= 0 ? ({ct})(((uint64_t){x} & (uint64_t){y}) + (((uint64_t){x} ^ (uint64_t){y}) >> 1)) : ({ct})(0ull - ((((0ull - (uint64_t){x}) & {mask}) & ((0ull - (uint64_t){y}) & {mask})) + ((((0ull - (uint64_t){x}) & {mask}) ^ ((0ull - (uint64_t){y}) & {mask})) >> 1)));"
                    );
                    t
                }
            }
            _ => "0".into(),
        }
    }

    /// The 128-bit subset of the integer methods (the checker keeps
    /// the checked, saturating, and overflowing families out for now).
    fn int128_method_c(&mut self, b: Builtin, vals: &[String], it: IntTy, loc: &str) -> String {
        use Builtin as B;
        use std::fmt::Write as _;
        let _ = loc;
        let ct = int_c(it);
        let f = int_fn(it);
        let a = &vals[0];
        let x = self.tmp();
        let _ = writeln!(self.out, "    {ct} {x} = {a};");
        // A uint64 byte swap of the word `w`, as an expression.
        fn bswap(w: &str) -> String {
            let mut parts = Vec::new();
            for i in 0..8 {
                parts.push(format!("(({w} >> {}) & 0xFFull) << {}", 8 * i, 56 - 8 * i));
            }
            format!("({})", parts.join(" | "))
        }
        match b {
            B::WrappingNeg => format!("lust_{f}_sub((({ct}){{0, 0}}), {x})"),
            B::WrappingShl => format!("lust_{f}_shl({x}, {} & 127u)", vals[1]),
            B::WrappingShr => format!("lust_{f}_shr({x}, {} & 127u)", vals[1]),
            B::WrappingAbs => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {ct} {t} = (int64_t){x}.hi < 0 ? lust_{f}_sub((({ct}){{0, 0}}), {x}) : {x};");
                t
            }
            B::CountOnes => format!("(lust_count_ones64({x}.lo) + lust_count_ones64({x}.hi))"),
            B::CountZeros => format!("(128u - lust_count_ones64({x}.lo) - lust_count_ones64({x}.hi))"),
            B::LeadingZeros => format!("({x}.hi != 0 ? lust_leading_zeros64({x}.hi, 64) : 64u + lust_leading_zeros64({x}.lo, 64))"),
            B::TrailingZeros => format!("({x}.lo != 0 ? lust_trailing_zeros64({x}.lo, 64) : 64u + lust_trailing_zeros64({x}.hi, 64))"),
            B::LeadingOnes => format!("({x}.hi != ~0ull ? lust_leading_zeros64(~{x}.hi, 64) : 64u + lust_leading_zeros64(~{x}.lo, 64))"),
            B::TrailingOnes => format!("({x}.lo != ~0ull ? lust_trailing_zeros64(~{x}.lo, 64) : 64u + lust_trailing_zeros64(~{x}.hi, 64))"),
            B::RotateLeft | B::RotateRight => {
                let n = self.tmp();
                let _ = writeln!(self.out, "    uint32_t {n} = {} & 127u;", vals[1]);
                let t = self.tmp();
                let (o1, o2) = if b == B::RotateLeft { ("shl", "shr") } else { ("shr", "shl") };
                if it.signed() {
                    // Rotate on the unsigned bit pattern: `lust_i128_shr` is
                    // arithmetic and would fill the high bits with the sign.
                    let _ = writeln!(
                        self.out,
                        "    {ct} {t} = lust_i128_from_u128(lust_u128_or(lust_u128_{o1}(lust_u128_from_i128({x}), {n}), lust_u128_{o2}(lust_u128_from_i128({x}), (128u - {n}) & 127u)));"
                    );
                } else {
                    let _ = writeln!(
                        self.out,
                        "    {ct} {t} = lust_u128_or(lust_{f}_{o1}({x}, {n}), lust_{f}_{o2}({x}, (128u - {n}) & 127u));"
                    );
                }
                t
            }
            B::SwapBytes => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {ct} {t}; {t}.lo = {}; {t}.hi = {};", bswap(&format!("{x}.hi")), bswap(&format!("{x}.lo")));
                t
            }
            B::ReverseBits => {
                let (r, i) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {ct} {r} = {{0, 0}}; for (uint32_t {i} = 0; {i} < 64; {i}++) {{ {r}.hi |= (({x}.lo >> {i}) & 1ull) << (63 - {i}); {r}.lo |= (({x}.hi >> {i}) & 1ull) << (63 - {i}); }}"
                );
                r
            }
            B::Signum => {
                let (t, c) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {ct} {t} = {{0, 0}}; int32_t {c} = lust_i128_cmp({x}, {t}); {t}.lo = (uint64_t)(int64_t){c}; {t}.hi = (uint64_t)((int64_t){c} >> 63);"
                );
                t
            }
            B::IsPositive => format!("((int64_t){x}.hi > 0 || ({x}.hi == 0 && {x}.lo != 0))"),
            B::IsNegative => format!("((int64_t){x}.hi < 0)"),
            B::IsPowerOfTwo => format!("(lust_count_ones64({x}.lo) + lust_count_ones64({x}.hi) == 1)"),
            B::IsMultipleOf => {
                let (y, r, t) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {ct} {y} = {}; {ct} {r} = {{0, 0}}; int {t} = ({y}.lo == 0 && {y}.hi == 0) ? ({x}.lo == 0 && {x}.hi == 0) : (lust_u128_divmod({x}, {y}, &{r}), {r}.lo == 0 && {r}.hi == 0);",
                    vals[1]
                );
                t
            }
            B::UnboundedShl => format!("(({}) >= 128u ? (({ct}){{0, 0}}) : lust_{f}_shl({x}, {}))", vals[1], vals[1]),
            B::UnboundedShr => {
                if it.signed() {
                    format!("(({}) >= 128u ? (({ct}){{(uint64_t)((int64_t){x}.hi >> 63), (uint64_t)((int64_t){x}.hi >> 63)}}) : lust_{f}_shr({x}, {}))", vals[1], vals[1])
                } else {
                    format!("(({}) >= 128u ? (({ct}){{0, 0}}) : lust_{f}_shr({x}, {}))", vals[1], vals[1])
                }
            }
            B::CastSigned => format!("lust_i128_from_u128({x})"),
            B::CastUnsigned => format!("lust_u128_from_i128({x})"),
            B::UnsignedAbs => {
                let t = self.tmp();
                let _ = writeln!(
                    self.out,
                    "    lust_u128 {t} = lust_u128_from_i128((int64_t){x}.hi < 0 ? lust_i128_sub(((lust_i128){{0, 0}}), {x}) : {x});"
                );
                t
            }
            B::NextMultipleOf | B::CheckedNextMultipleOf => {
                let (y, r, add, t) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                let nloc = num_loc(it, false);
                let _ = writeln!(self.out, "    {ct} {y} = {};", vals[1]);
                if b == B::NextMultipleOf {
                    let _ = writeln!(
                        self.out,
                        "    if ({y}.lo == 0 && {y}.hi == 0) lust_panic_cstr(\"attempt to calculate the remainder with a divisor of zero\", {nloc});"
                    );
                }
                let _ = writeln!(
                    self.out,
                    "    {ct} {r} = {{0, 0}}; if ({y}.lo != 0 || {y}.hi != 0) lust_u128_divmod({x}, {y}, &{r}); {ct} {add} = ({r}.lo == 0 && {r}.hi == 0) ? (({ct}){{0, 0}}) : lust_u128_sub({y}, {r}); {ct} {t} = lust_u128_add({x}, {add});"
                );
                if b == B::NextMultipleOf {
                    let _ = writeln!(
                        self.out,
                        "    if (lust_u128_cmp({t}, {x}) < 0) lust_panic_cstr(\"attempt to add with overflow\", {nloc});"
                    );
                    t
                } else {
                    self.int_option_c(&t, &format!("({y}.lo != 0 || {y}.hi != 0) && lust_u128_cmp({t}, {x}) >= 0"), it)
                }
            }
            B::BitWidth => format!("(128u - ({x}.hi != 0 ? lust_leading_zeros64({x}.hi, 64) : 64u + lust_leading_zeros64({x}.lo, 64)))"),
            B::HighestOne => self.int_option_c(
                &format!("(127u - ({x}.hi != 0 ? lust_leading_zeros64({x}.hi, 64) : 64u + lust_leading_zeros64({x}.lo, 64)))"),
                &format!("({x}.lo != 0 || {x}.hi != 0)"),
                IntTy::U32,
            ),
            B::LowestOne => self.int_option_c(
                &format!("({x}.lo != 0 ? lust_trailing_zeros64({x}.lo, 64) : 64u + lust_trailing_zeros64({x}.hi, 64))"),
                &format!("({x}.lo != 0 || {x}.hi != 0)"),
                IntTy::U32,
            ),
            B::IsolateLowestOne => format!("lust_{f}_and({x}, lust_{f}_sub((({ct}){{0, 0}}), {x}))"),
            B::IsolateHighestOne => {
                let (lz, t) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint32_t {lz} = {x}.hi != 0 ? lust_leading_zeros64({x}.hi, 64) : 64u + lust_leading_zeros64({x}.lo, 64); {ct} {t} = ({x}.lo == 0 && {x}.hi == 0) ? (({ct}){{0, 0}}) : lust_{f}_shl((({ct}){{1, 0}}), 127u - {lz});"
                );
                t
            }
            _ => "0".into(),
        }
    }

    /// The C for one inherent float method: mostly the libm call Rust
    /// lowers to, with lust wrappers where Rust's semantics differ.
    fn float_method_c(&mut self, b: Builtin, vals: &[String], tys: &[CTy]) -> String {
        use Builtin as B;
        if matches!(b, B::F32FromBits | B::F64FromBits) {
            return if b == B::F64FromBits {
                format!("lust_f64_from_bits_of({})", vals[0])
            } else {
                format!("lust_f32_from_bits_of({})", vals[0])
            };
        }
        let f = match &tys[0] {
            CTy::Float(f) => *f,
            _ => FloatTy::F64,
        };
        let a = &vals[0];
        let suf = if f == FloatTy::F32 { "f" } else { "" };
        let w = if f == FloatTy::F32 { "f32" } else { "f64" };
        let ct = ctype(&tys[0]);
        match b {
            B::FloatSqrt => format!("sqrt{suf}({a})"),
            B::FloatPowi => format!("lust_{w}_powi({a}, {})", vals[1]),
            B::FloatPowf => format!("pow{suf}({a}, {})", vals[1]),
            B::FloatExp => format!("exp{suf}({a})"),
            B::FloatLn => format!("log{suf}({a})"),
            B::FloatLog => format!("(log{suf}({a}) / log{suf}({}))", vals[1]),
            B::FloatLog2 => format!("log2{suf}({a})"),
            B::FloatLog10 => format!("log10{suf}({a})"),
            B::FloatMulAdd => format!("fma{suf}({a}, {}, {})", vals[1], vals[2]),
            B::FloatFloor => format!("floor{suf}({a})"),
            B::FloatCeil => format!("ceil{suf}({a})"),
            B::FloatRound => format!("round{suf}({a})"),
            B::FloatTrunc => format!("trunc{suf}({a})"),
            B::FloatFract => format!("(({a}) - trunc{suf}({a}))"),
            B::FloatAbs => format!("fabs{suf}({a})"),
            B::FloatSignum => format!("lust_{w}_signum({a})"),
            B::FloatRecip => format!("((({ct})1) / ({a}))"),
            B::FloatMin => format!("lust_{w}_min({a}, {})", vals[1]),
            B::FloatMax => format!("lust_{w}_max({a}, {})", vals[1]),
            B::FloatCopysign => format!("copysign{suf}({a}, {})", vals[1]),
            B::FloatIsNan => format!("({a} != {a})"),
            B::FloatIsInfinite => {
                if f == FloatTy::F32 {
                    format!("((lust_f32_to_bits({a}) & 0x7FFFFFFFul) == 0x7F800000ul)")
                } else {
                    format!("((lust_f64_to_bits({a}) & 0x7FFFFFFFFFFFFFFFull) == 0x7FF0000000000000ull)")
                }
            }
            B::FloatIsFinite => {
                if f == FloatTy::F32 {
                    format!("((lust_f32_to_bits({a}) & 0x7FFFFFFFul) < 0x7F800000ul)")
                } else {
                    format!("((lust_f64_to_bits({a}) & 0x7FFFFFFFFFFFFFFFull) < 0x7FF0000000000000ull)")
                }
            }
            B::FloatIsSignPositive => {
                if f == FloatTy::F32 {
                    format!("((lust_f32_to_bits({a}) >> 31) == 0)")
                } else {
                    format!("((lust_f64_to_bits({a}) >> 63) == 0)")
                }
            }
            B::FloatIsSignNegative => {
                if f == FloatTy::F32 {
                    format!("((lust_f32_to_bits({a}) >> 31) == 1)")
                } else {
                    format!("((lust_f64_to_bits({a}) >> 63) == 1)")
                }
            }
            B::FloatToBits => format!("lust_{w}_to_bits({a})"),
            _ => "0".into(),
        }
    }
}

// ---------- Compilation units ----------
//
// Unit 0 holds the globals and `main`. Unit 1 holds the shared glue
// (see `GlueSet`); other glue is static in the function units. Unit 4
// holds the per-slot location tables (`loc_unit`). The other units
// hold functions, in groups the driver sizes by C bytes and freezes
// between fresh bases, so an edit that keeps the program's shape
// recompiles only the units it touches (plus unit 0).

/// Function groups for units 2 and up, fixed slot counts. Kept for
/// tests that build units by hand; the driver groups by bytes below.
#[allow(dead_code)]
pub fn group_fns(n: usize, per_unit: usize) -> Vec<std::ops::Range<usize>> {
    (0..n).step_by(per_unit.max(1)).map(|a| a..(a + per_unit).min(n)).collect()
}

/// Function groups sized by generated C bytes: slots in order, a new
/// group when the next slot would push the current one past `target`
/// bytes. A single slot over the target forms its own group, and a
/// group holds at most 4096 slots so a run of empty slots (templates,
/// stubs) cannot make one unit's register function huge. Equal byte
/// sizes give tcc units of near equal cost, where a fixed slot count
/// makes one unit of large functions the tail of the whole compile.
pub fn group_fns_by_bytes(sizes: &[usize], target: usize) -> Vec<std::ops::Range<usize>> {
    let target = target.max(1);
    let mut groups = Vec::new();
    let (mut start, mut bytes) = (0usize, 0usize);
    for (i, &size) in sizes.iter().enumerate() {
        if i > start && (bytes + size > target || i - start >= 4096) {
            groups.push(start..i);
            start = i;
            bytes = 0;
        }
        bytes += size;
    }
    if start < sizes.len() {
        groups.push(start..sizes.len());
    }
    groups
}

/// All glue needed by a set of functions, closed over field types.
//
// Glue placement is hybrid. `shared` holds the keys that live once in the glue unit (unit 1):
// glue that many function units reach (see `compute_shared`). Every other key is emitted as a
// static copy in each function unit that reaches it, so an edit that needs new glue does not
// rebuild the glue unit. `shared` is None until the first `compute_shared`; before that, all
// glue lives in the glue unit, as before.
#[derive(Default)]
pub struct GlueSet {
    pub protos: HashMap<(Glue, CTy), String>,
    defs: String,
    /// Each key's definition on its own, so units can carry static copies of just what they reach.
    def_map: HashMap<(Glue, CTy), String>,
    /// The glue keys each key's definition calls.
    deps: HashMap<(Glue, CTy), Vec<(Glue, CTy)>>,
    /// C types each key's definition names beyond its key type: the signature of a written
    /// method it calls (`glue_callee`). A unit that defines the key must declare them.
    types: HashMap<(Glue, CTy), Vec<CTy>>,
    /// Keys that live in the shared glue unit. Frozen until the next `compute_shared`.
    pub shared: Option<HashSet<(Glue, CTy)>>,
    /// Keys the last `refresh` did not reach: their text may predate a type edit. `add`
    /// regenerates one when a body reaches it again.
    stale: HashSet<(Glue, CTy)>,
    /// Fn slots as of the last `add` or `refresh`: fn pointers in static
    /// data (`ConstValue::FnPtr`) name their slot's trampoline.
    slots: Vec<u32>,
}

impl GlueSet {
    /// Adds glue for `keys` and everything it needs: new keys, and keys the last `refresh` did
    /// not reach (`stale`), which are regenerated and compared as `refresh` does. Returns
    /// (shared unit content changed, an existing definition changed), as `refresh`. New glue
    /// that no unit shared at freeze time is not in `shared`, so it does not count as a shared
    /// change: the new glue is static in the function units that reach it.
    pub fn add<'k>(&mut self, p: &Program, slots: &[u32], keys: impl Iterator<Item = &'k (Glue, CTy)>) -> (bool, bool) {
        self.slots = slots.to_vec();
        let roots: Vec<(Glue, CTy)> = keys.filter(|k| !self.protos.contains_key(k) || self.stale.contains(k)).cloned().collect();
        self.regen(p, slots, roots, false).0
    }

    /// Regenerates every reached key's definition from the current
    /// program and replaces the stored text where it differs. A derived
    /// impl (Debug, Clone, Eq, Drop glue) is generated from the Adt's
    /// field and variant types, but its key is only the Adt id: a field
    /// type edit keeps the key, so `add` alone would keep the old text
    /// (a stale Debug body, or C that names a field the new layout form
    /// does not have). The driver calls this when type definitions may
    /// have changed. Returns (shared unit content changed, any existing
    /// definition changed); new keys are added as in `add`. Comparing
    /// the generated text is exact by construction: no second
    /// fingerprint of what `glue_def` reads to keep in sync.
    ///
    /// Keys that no live body reaches now are not regenerated (their
    /// Adt may be gone). They become `stale`, so the next `add` that
    /// reaches one regenerates it: a type edit in a version that does
    /// not use the glue must still reach the version that uses it again.
    pub fn refresh<'k>(&mut self, p: &Program, slots: &[u32], keys: impl Iterator<Item = &'k (Glue, CTy)>) -> (bool, bool) {
        self.slots = slots.to_vec();
        let (changed, seen) = self.regen(p, slots, keys.cloned().collect(), true);
        self.stale = self.protos.keys().filter(|k| !seen.contains(*k)).cloned().collect();
        changed
    }

    /// The walk behind `add` and `refresh`: generates each pending key and its deps. With `all`
    /// false, a key already stored and not stale is kept as is (and its deps are not walked).
    /// Returns the change flags and the keys walked.
    fn regen(&mut self, p: &Program, slots: &[u32], mut pending: Vec<(Glue, CTy)>, all: bool) -> ((bool, bool), HashSet<(Glue, CTy)>) {
        let mut seen: HashSet<(Glue, CTy)> = HashSet::new();
        let mut shared_changed = false;
        let mut regenerated = false;
        while let Some(g) = pending.pop() {
            if !seen.insert(g.clone()) {
                continue;
            }
            let is_new = !self.protos.contains_key(&g);
            let was_stale = self.stale.remove(&g);
            if !was_stale && !all && !is_new {
                continue;
            }
            // `glue_unit` leaves stale keys out, so a shared one coming back must rebuild it.
            shared_changed |= was_stale && self.is_shared(&g);
            let mut more = Vec::new();
            let mut proto = String::new();
            let mut def = String::new();
            let mut types = Vec::new();
            glue_def(p, slots, &g.0, &g.1, &mut proto, &mut def, &mut more, &mut types);
            let changed = is_new
                || self.def_map.get(&g) != Some(&def)
                || self.protos.get(&g) != Some(&proto)
                || self.deps.get(&g) != Some(&more)
                || self.types.get(&g) != Some(&types);
            if changed {
                regenerated |= !is_new;
                shared_changed |= self.shared.as_ref().is_none_or(|s| s.contains(&g));
                if is_new {
                    self.defs.push_str(&def);
                }
                self.def_map.insert(g.clone(), def);
                self.deps.insert(g.clone(), more.clone());
                self.types.insert(g.clone(), types);
                self.protos.insert(g, proto);
            }
            pending.extend(more);
        }
        if regenerated {
            // `defs` is the pre-hybrid concatenation; rebuild it from the
            // per-key map. Order does not matter: prototypes precede it.
            self.defs = self.def_map.values().cloned().collect();
        }
        ((shared_changed, regenerated), seen)
    }

    /// The glue keys a set of direct needs reaches, deps included.
    fn closure<'a>(&'a self, roots: impl Iterator<Item = &'a (Glue, CTy)>) -> HashSet<&'a (Glue, CTy)> {
        let mut seen = HashSet::new();
        let mut stack: Vec<&(Glue, CTy)> = roots.collect();
        while let Some(k) = stack.pop() {
            if seen.insert(k) {
                if let Some(deps) = self.deps.get(k) {
                    stack.extend(deps.iter());
                }
            }
        }
        seen
    }

    /// Picks the shared set: keys reached by at least `k` function units (`fns` is indexed by
    /// slot, `groups` are the units). The set is closed over deps, so the shared glue unit's
    /// definitions only call each other. Call this only on a fresh base, then keep it frozen:
    /// a key that turned shared later would need the base glue unit rebuilt.
    pub fn compute_shared(&mut self, fns: &[FnOut], groups: &[std::ops::Range<usize>], k: usize) {
        let mut count: HashMap<&(Glue, CTy), usize> = HashMap::new();
        for range in groups {
            for key in self.closure(fns[range.clone()].iter().flat_map(|f| f.glue.iter())) {
                *count.entry(key).or_default() += 1;
            }
        }
        let mut shared: HashSet<(Glue, CTy)> = count.into_iter().filter(|&(_, n)| n >= k).map(|(key, _)| key.clone()).collect();
        // Close over deps (the count already implies this, but keep the glue unit self-contained).
        let mut stack: Vec<(Glue, CTy)> = shared.iter().cloned().collect();
        while let Some(key) = stack.pop() {
            if let Some(deps) = self.deps.get(&key) {
                for dep in deps {
                    if shared.insert(dep.clone()) {
                        stack.push(dep.clone());
                    }
                }
            }
        }
        self.shared = Some(shared);
    }

    fn is_shared(&self, k: &(Glue, CTy)) -> bool {
        self.shared.as_ref().is_some_and(|s| s.contains(k))
    }

    /// Adds the C types that the definition of `k` names to `out`: its key type and the
    /// types in `types`. A unit that holds the definition must declare all of them.
    fn def_types(&self, k: &(Glue, CTy), out: &mut HashSet<CTy>) {
        collect_types(&k.1, out);
        self.types.get(k).into_iter().flatten().for_each(|t| collect_types(t, out));
    }
}

fn unit_header() -> String {
    let mut c = String::with_capacity(64 * 1024);
    c.push_str(runtime_decls());
    c.push('\n');
    c
}

/// The full runtime source, assembled from `src/runtime/`: runtime.h first, then core.c
/// with its `#include` lines replaced by the included text (panic.c inline; float.h and
/// hash.h at the end). Units compile from strings, so file includes cannot read files;
/// declaration units get float.h's prototypes only (`with_impls` false),
/// the runtime unit gets float.c's and hash.c's bodies too. The runtime stays one
/// amalgamated unit (see `runtime_unit`), so the split files are source fragments, not
/// separate translation units, and the includes are also what a plain C compiler
/// follows when a test harness includes runtime.h and core.c directly. The panic
/// include sits where the panic section belonged in the old single runtime.c: after
/// the string helpers it calls, before the checked math that calls it.
fn runtime_source(with_impls: bool) -> String {
    let header = include_str!("runtime/float.h");
    let header = if with_impls {
        let body = include_str!("runtime/float.c").replacen("#include \"ryu_tables.h\"", include_str!("runtime/ryu_tables.h"), 1);
        header.replacen("#include \"float.c\"", &body, 1)
    } else {
        header.replacen("#include \"float.c\"", "", 1)
    };
    let fmt = include_str!("runtime/fmt.h");
    let fmt = fmt.replacen("#include \"fmt.c\"", if with_impls { include_str!("runtime/fmt.c") } else { "" }, 1);
    // The hash core's declarations are not in the common unit header:
    // they cost about 26 KB of C per unit and no generated code calls
    // the core yet. The runtime unit carries header plus bodies, so
    // the symbols link; a unit whose code calls the core adds
    // `hash_decls()` to its header.
    let hash = if with_impls { hash_source(true) } else { String::new() };
    let deps = include_str!("runtime/deps.h").replacen("#include \"deps.c\"", if with_impls { include_str!("runtime/deps.c") } else { "" }, 1);
    let core = include_str!("runtime/core.c")
        .replacen("#include \"escape_table.h\"", include_str!("runtime/escape_table.h"), 1)
        .replacen("#include \"unicode_table.h\"", include_str!("runtime/unicode_table.h"), 1);
    // The Unicode case tables (W-STD-B) only where the bodies are.
    let core = core.replacen("#include \"case_tables.h\"", if with_impls { include_str!("runtime/case_tables.h") } else { "" }, 1);
    let (h, core, panic) = (include_str!("runtime/runtime.h"), core.as_str(), include_str!("runtime/panic.c"));
    let mut src = String::with_capacity(h.len() + core.len() + panic.len() + header.len() + hash.len());
    src.push_str(h);
    src.push_str(core);
    let src = src.replacen("#include \"panic.c\"\n", panic, 1);
    let src = src.replacen("#include \"thread.c\"\n", include_str!("runtime/thread.c"), 1);
    let src = src.replacen("#include \"float.h\"", &header, 1);
    let src = src.replacen("#include \"fmt.h\"", &fmt, 1);
    let src = src.replacen("#include \"sort.h\"", include_str!("runtime/sort.h"), 1);
    let src = src.replacen("#include \"hash.h\"", &hash, 1);
    let src = src.replacen("#include \"deps.h\"", &deps, 1);
    let src = src.replacen("#include \"sync.c\"\n", include_str!("runtime/sync.c"), 1);
    let stdc =
        include_str!("runtime/stdc.h").replacen("#include \"stdc.c\"", if with_impls { include_str!("runtime/stdc.c") } else { "" }, 1);
    let src = src.replacen("#include \"stdc.h\"", &stdc, 1);
    let sys = include_str!("runtime/sys.h").replacen("#include \"sys.c\"", if with_impls { include_str!("runtime/sys.c") } else { "" }, 1);
    let src = src.replacen("#include \"sys.h\"", &sys, 1);
    let sysio =
        include_str!("runtime/sysio.h").replacen("#include \"sysio.c\"", if with_impls { include_str!("runtime/sysio.c") } else { "" }, 1);
    let src = src.replacen("#include \"sysio.h\"", &sysio, 1);
    let sysnet =
        include_str!("runtime/sysnet.h").replacen("#include \"sysnet.c\"", if with_impls { include_str!("runtime/sysnet.c") } else { "" }, 1);
    let src = src.replacen("#include \"sysnet.h\"", &sysnet, 1);
    let sysx = include_str!("runtime/sysx.h").replacen("#include \"sysx.c\"", if with_impls { include_str!("runtime/sysx.c") } else { "" }, 1);
    src.replacen("#include \"sysx.h\"", &sysx, 1)
}

/// Removes C comments, replacing each with one space (the C meaning of a
/// comment). String and char literals pass through untouched. The
/// runtime header is about a third comments by bytes, and every unit
/// would otherwise make tcc lex them again.
fn strip_c_comments(src: &str) -> String {
    let b = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'"' | b'\'' => {
                let quote = b[i];
                let start = i;
                i += 1;
                while i < b.len() && b[i] != quote {
                    i += if b[i] == b'\\' { 2 } else { 1 };
                }
                i = (i + 1).min(b.len());
                out.push_str(&src[start..i]);
            }
            b'/' if i + 1 < b.len() && b[i + 1] == b'*' => {
                i += 2;
                while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                    i += 1;
                }
                i = (i + 2).min(b.len());
                out.push(' ');
            }
            b'/' if i + 1 < b.len() && b[i + 1] == b'/' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                out.push(' ');
            }
            _ => {
                let start = i;
                while i < b.len() && b[i] != b'"' && b[i] != b'\'' && b[i] != b'/' {
                    i += 1;
                }
                if i == start {
                    i += 1;
                    out.push('/');
                } else {
                    out.push_str(&src[start..i]);
                }
            }
        }
    }
    out
}

/// One conditional group in `strip_impl_blocks`.
enum ImplFrame {
    /// A conditional that does not decide on `LUST_IMPL`: its lines pass through.
    Other,
    /// A conditional decided on `LUST_IMPL` (undefined here): only the
    /// branch `active` names survives, and no directive lines remain.
    Impl { active: bool, taken: bool },
    /// A conditional nested inside a dropped branch: counts depth only.
    Dropped,
}

/// Whether the condition of a `#if`/`#ifdef`/`#ifndef`/`#elif` line is
/// decidable with `LUST_IMPL` undefined. `word` is the directive name,
/// `rest` what follows it. None when the condition does not mention
/// `LUST_IMPL`, or mentions it in a shape this does not evaluate: the
/// caller then leaves the group to the C preprocessor.
fn impl_cond(word: &str, rest: &str) -> Option<bool> {
    match word {
        "ifdef" | "ifndef" => {
            let name = rest.split_whitespace().next().unwrap_or("");
            (name == "LUST_IMPL").then_some(word == "ifndef")
        }
        "if" | "elif" => {
            if !rest.contains("LUST_IMPL") {
                return None;
            }
            let expr = rest.replace("defined(LUST_IMPL)", "0").replace("defined LUST_IMPL", "0");
            let compact: String = expr.chars().filter(|c| !c.is_whitespace()).collect();
            match compact.as_str() {
                "0" => Some(false),
                "!0" => Some(true),
                c if c.contains("0&&") || c.contains("&&0") => Some(false),
                c if c.contains("1||") || c.contains("||1") => Some(true),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Removes `#ifdef LUST_IMPL` groups (and the other decidable shapes,
/// see `impl_cond`) from runtime text, keeping any `#else` branch.
/// Declaration units never define `LUST_IMPL`, so tcc would skip these
/// groups line by line in every unit: about two thirds of the shared
/// header bytes (the runtime bodies and the Unicode tables). Cutting
/// them here, once, cuts every unit's C bytes and the work tcc does
/// to skip them. Groups this cannot decide pass through untouched.
fn strip_impl_blocks(src: &str) -> String {
    let mut out = String::with_capacity(src.len() / 2);
    let mut stack: Vec<ImplFrame> = Vec::new();
    let dropping = |stack: &[ImplFrame]| stack.iter().any(|f| matches!(f, ImplFrame::Dropped | ImplFrame::Impl { active: false, .. }));
    for line in src.split_inclusive('\n') {
        let trimmed = line.trim_start();
        if !trimmed.starts_with('#') {
            if !dropping(&stack) {
                out.push_str(line);
            }
            continue;
        }
        let after = trimmed[1..].trim_start();
        let word_end = after.find(|c: char| !c.is_ascii_alphabetic()).unwrap_or(after.len());
        let (word, rest) = (&after[..word_end], after[word_end..].trim());
        match word {
            "if" | "ifdef" | "ifndef" => {
                if dropping(&stack) {
                    stack.push(ImplFrame::Dropped);
                } else if let Some(v) = impl_cond(word, rest) {
                    stack.push(ImplFrame::Impl { active: v, taken: v });
                } else {
                    stack.push(ImplFrame::Other);
                    out.push_str(line);
                }
            }
            "elif" => {
                // Decide from a shared borrow first: the undecidable
                // case rewrites the frame itself.
                enum Act {
                    Decided(bool),
                    ToOther,
                    Off,
                    Emit,
                    Skip,
                }
                let act = match stack.last() {
                    Some(ImplFrame::Impl { taken, .. }) => match impl_cond(word, rest) {
                        Some(v) => Act::Decided(v),
                        // No earlier branch was kept, so this `elif` is
                        // an `if`: hand the rest of the group to the
                        // preprocessor as one.
                        None if !taken => Act::ToOther,
                        None => Act::Off,
                    },
                    Some(ImplFrame::Other) => Act::Emit,
                    _ => Act::Skip,
                };
                match act {
                    Act::Decided(v) => {
                        if let Some(ImplFrame::Impl { active, taken }) = stack.last_mut() {
                            *active = v && !*taken;
                            *taken |= *active;
                        }
                    }
                    Act::ToOther => {
                        *stack.last_mut().unwrap() = ImplFrame::Other;
                        out.push_str(&format!("#if {rest}\n"));
                    }
                    Act::Off => {
                        if let Some(ImplFrame::Impl { active, .. }) = stack.last_mut() {
                            *active = false;
                        }
                    }
                    Act::Emit => out.push_str(line),
                    Act::Skip => {}
                }
            }
            "else" => match stack.last_mut() {
                Some(ImplFrame::Impl { active, taken }) => {
                    *active = !*taken;
                    *taken = true;
                }
                Some(ImplFrame::Other) => out.push_str(line),
                _ => {}
            },
            "endif" => {
                if matches!(stack.pop(), Some(ImplFrame::Other)) {
                    out.push_str(line);
                }
            }
            _ => {
                if !dropping(&stack) {
                    out.push_str(line);
                }
            }
        }
    }
    out
}

/// The runtime without function bodies: `LUST_BODY(...)` regions are cut out once, so units do
/// not make tcc tokenize code that would expand to nothing.
fn runtime_decls() -> &'static str {
    static DECLS: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    DECLS.get_or_init(|| {
        let src = runtime_source(false);
        let mut out = String::with_capacity(src.len() / 2);
        let mut rest = src.as_str();
        // Skip the macro's own definition lines, which mention LUST_BODY without a body.
        while let Some(i) = rest.find("LUST_BODY(") {
            let line_start = rest[..i].rfind('\n').map_or(0, |n| n + 1);
            if rest[line_start..].starts_with("#define LUST_BODY") {
                let end = rest[i..].find('\n').map_or(rest.len(), |n| i + n);
                out.push_str(&rest[..end]);
                rest = &rest[end..];
                continue;
            }
            out.push_str(&rest[..i]);
            // Find the matching close paren of LUST_BODY( ... ).
            let mut depth = 0;
            let mut end = i;
            for (k, ch) in rest[i..].char_indices() {
                match ch {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            end = i + k + 1;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            out.push(';');
            rest = &rest[end..];
        }
        out.push_str(rest);
        let out = strip_impl_blocks(&out);
        // Units do not include <stdint.h> or <stddef.h>: tcc spends about 1 ms per unit parsing
        // the system headers behind them. The compiler's predefined types define the same names
        // (tcc and gcc both predefine them; on macOS arm64 tcc's __INT64_TYPE__ is long long,
        // which matches Apple's int64_t). The runtime unit keeps the real includes.
        strip_c_comments(&out.replacen(
            "#include <stdint.h>\n#include <stddef.h>\n",
            "typedef signed char int8_t; typedef unsigned char uint8_t; typedef short int16_t; typedef unsigned short uint16_t;\ntypedef int int32_t; typedef unsigned int uint32_t;\n#ifdef __INT64_TYPE__\ntypedef __INT64_TYPE__ int64_t; typedef unsigned __INT64_TYPE__ uint64_t;\n#else\ntypedef long long int64_t; typedef unsigned long long uint64_t;\n#endif\n#ifdef __SIZE_TYPE__\ntypedef __SIZE_TYPE__ size_t; typedef __PTRDIFF_TYPE__ ptrdiff_t; typedef __UINTPTR_TYPE__ uintptr_t; typedef __INTPTR_TYPE__ intptr_t;\n#else\ntypedef unsigned long size_t; typedef long ptrdiff_t; typedef unsigned long uintptr_t; typedef long intptr_t;\n#endif\n#define INT64_MIN (-9223372036854775807LL-1)\n#ifndef NULL\n#define NULL ((void*)0)\n#endif\n",
            1,
        ))
    })
}

/// The hash core text for splicing: hash.h, with hash.c inlined when
/// `with_bodies`. hash.h includes <stddef.h>/<stdint.h> for direct
/// inclusion by test harnesses; spliced copies drop both lines because
/// runtime.h already provided the types, and declaration units must
/// not re-read the system headers (see `runtime_decls`).
fn hash_source(with_bodies: bool) -> String {
    let hash = include_str!("runtime/hash.h").replacen("#include <stddef.h>\n#include <stdint.h>\n", "", 1);
    if with_bodies {
        hash.replacen("#include \"hash.c\"", include_str!("runtime/hash.c"), 1)
    } else {
        hash.replacen("#include \"hash.c\"", "", 1)
    }
}

/// Declarations for the erased hash core, for the header of a unit
/// whose generated code calls it (the std typed layer, when it lands).
/// Not part of the common unit header; see `runtime_source`.
#[allow(dead_code)]
pub fn hash_decls() -> String {
    hash_source(false)
}

/// The unit with the runtime's function definitions. It only changes when lust itself does.
pub fn runtime_unit() -> String {
    format!("#define LUST_IMPL 1\n{}", runtime_source(true))
}

/// The source files panic locations name: every file's path (index 0 is
/// the crate root) and each slot's file index.
pub struct SlotFiles<'a> {
    pub paths: &'a [&'a str],
    pub of_slot: &'a [u32],
}

/// The runtime setup `main_unit` emits for panics (`lust_unw_init`):
/// whether they unwind, the type ids of `&'static str` and `String`
/// (the message payloads' vtables carry them), and the slot of std's
/// hook runner when the program can install a hook (`set_hook`).
pub struct UnwindInit {
    pub unwind: bool,
    pub ids: [u64; 4],
    pub hook_runner: Option<u32>,
}

/// The `main_unit` argument for `p` (`slot_of` maps a fn to its slot).
/// Always given: a `panic_any` payload's text reads the `&str` and
/// `String` type ids even under panic=abort with no hook installed.
pub fn unwind_init(p: &Program, slot_of: impl Fn(LocalDefId) -> u32) -> Option<UnwindInit> {
    let runner = p
        .fns
        .iter()
        .position(|f| {
            p.interner.get(f.name).ends_with("__lust_run_hook")
                && p.std_source_span(f.def(&p.ast).name_span)
                && p.display_path(f.name) == "std::panic::__lust_run_hook"
        })
        .map(|i| slot_of(LocalDefId(i as u32)));
    let (a, b) = crate::check::any::type_id_words(p, &p.tys, REF_STR);
    let (c, d) = crate::check::any::type_id_words(p, &p.tys, STRING);
    Some(UnwindInit { unwind: p.unwind, ids: [a, b, c, d], hook_runner: runner })
}

/// The location unit: the per-slot line and file tables and
/// `lust_loc_init`, which points the runtime at them. Its own unit
/// (see the driver) so a build whose slot lines and files did not
/// change does not re-emit or recompile the arrays: the main unit
/// rebuilds on every build, and the arrays are most of its bytes on
/// a large program. The symbol is not static, so an overlay copy in
/// the executable replaces the base copy, as glue does.
pub fn loc_unit(files: &SlotFiles, slot_lines: &[u32]) -> String {
    let mut c = unit_header();
    let lines: Vec<String> = slot_lines.iter().map(|l| l.to_string()).collect();
    let _ = writeln!(c, "static const uint32_t lines[{}] = {{{}}};", lines.len().max(1), lines.join(","));
    let file = files.paths.first().copied().unwrap_or("");
    // A crate of one file needs no per-slot table (`lust_slot_file` NULL).
    let multi = files.of_slot.iter().any(|&f| f != 0);
    if multi {
        let paths: Vec<String> = files.paths.iter().map(|p| c_string_lit(p.as_bytes())).collect();
        let _ = writeln!(c, "static const char *const files[{}] = {{{}}};", paths.len().max(1), paths.join(","));
        let of: Vec<String> = files.of_slot.iter().map(|f| f.to_string()).collect();
        let _ = writeln!(c, "static const uint32_t slot_file[{}] = {{{}}};", of.len().max(1), of.join(","));
    }
    let _ = writeln!(
        c,
        "void lust_loc_init(void) {{\n  lust_file = {};\n  lust_fn_line = lines;{}\n}}",
        c_string_lit(file.as_bytes()),
        if multi { "\n  lust_files = files;\n  lust_slot_file = slot_file;" } else { "\n  lust_files = 0;\n  lust_slot_file = 0;" }
    );
    c
}

/// Unit 0: globals, overlay registration, and `main`. Rebuilt on every
/// build; the per-slot location tables live in `loc_unit`, which is
/// rebuilt only when they change. With `init` (see `unwind_init`) it
/// sets up the runtime's panic payloads and hook runner; under
/// panic=unwind a `main` that ends by a panic exits 101.
pub fn main_unit(main_slot: u32, overlays: &[usize], init: Option<UnwindInit>) -> String {
    let unwind = init.as_ref().is_some_and(|i| i.unwind);
    let (init, runner) = match init {
        Some(UnwindInit { unwind, ids: [a, b, c, d], hook_runner }) => (
            format!("\n  lust_unw_init({}, {a}ull, {b}ull, {c}ull, {d}ull);", unwind as u8),
            hook_runner.map_or(String::new(), |s| format!("\n  lust_hook_set_runner(lust_fns[{s}]);")),
        ),
        None => (String::new(), String::new()),
    };
    let mut c = unit_header();
    c.push_str("void lust_loc_init(void);\n");
    for u in overlays {
        let _ = writeln!(c, "void lust_overlay_u{u}(void);");
    }
    let _ = writeln!(
        c,
        "int main(int argc, char **argv) {{\n  lust_argc = argc;\n  lust_argv = argv;\n  lust_loc_init();{}\n  lust_rt_init();\n  lust_base_init();",
        init
    );
    for u in overlays {
        let _ = writeln!(c, "  lust_overlay_u{u}();");
    }
    c.push_str(runner.trim_start_matches('\n'));
    if !runner.is_empty() {
        c.push('\n');
    }
    let _ = writeln!(
        c,
        "  if (lust_main_entry_p) {{ int rc = lust_main_entry_p(); {} lust_tls_exit(); lust_flush(); return rc; }}\n  ((void (*)(void))lust_fns[{main_slot}])();\n  {}lust_tls_exit();\n  lust_flush();\n  return {};\n}}",
        if unwind { "if (lust_unw_main_exit()) rc = 101;" } else { "" },
        if unwind { "int rc = lust_unw_main_exit();\n  " } else { "" },
        if unwind { "rc" } else { "0" }
    );
    c
}

/// The function table (with room for `capacity` slots), and `lust_base_init`, which registers
/// every base function unit.
pub fn table_unit(capacity: usize, fn_units: &[usize]) -> String {
    let mut c = unit_header();
    let _ = writeln!(c, "lust_fnptr lust_fns[{}];", capacity.max(1));
    let _ = writeln!(c, "lust_fnptr lust_tramps[{}];", capacity.max(1));
    let _ = writeln!(c, "int (*lust_main_entry_p)(void);");
    for u in fn_units {
        let _ = writeln!(c, "void lust_register_u{u}(void);");
    }
    c.push_str("void lust_base_init(void) {\n");
    for u in fn_units {
        let _ = writeln!(c, "  lust_register_u{u}();");
    }
    c.push_str("}\n");
    c
}

/// The shared glue unit. With a frozen shared set it holds only those keys; the rest of the
/// glue is static in the function units (see `GlueSet`).
pub fn glue_unit(p: &Program, g: &GlueSet) -> String {
    let mut c = unit_header();
    let mut types = HashSet::new();
    for st in &p.statics {
        let t = cty(&p.tys, st.ty);
        collect_types(&t, &mut types);
        collect_promoted(p, &st.value, &t, &mut types);
    }
    if let Some(shared) = &g.shared {
        // A stale key (no live body reaches it) may name an Adt or fields that are gone.
        let mut keys: Vec<&(Glue, CTy)> = shared.iter().filter(|k| !g.stale.contains(*k)).collect();
        for k in &keys {
            g.def_types(k, &mut types);
        }
        type_decls(p, &mut c, &types);
        keys.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
        for k in &keys {
            c.push_str(&g.protos[*k]);
        }
        for k in &keys {
            c.push_str(&g.def_map[*k]);
        }
        c.push_str(&static_defs(p, &g.slots));
        return c;
    }
    for k in g.protos.keys() {
        g.def_types(k, &mut types);
    }
    type_decls(p, &mut c, &types);
    let mut protos: Vec<&String> = g.protos.values().collect();
    protos.sort();
    for proto in protos {
        c.push_str(proto);
    }
    c.push_str(&g.defs);
    c.push_str(&static_defs(p, &g.slots));
    c
}

/// One enum or Option value as a compound literal from its field value
/// texts, in field order. Shared by function codegen (`make_variant`)
/// and constant initializers (`const_init`), whose file-scope globals
/// need the same single-designator forms.
fn variant_lit(p: &Program, t: &CTy, variant: usize, vals: &[String]) -> String {
    let ct = ctype(t);
    let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
    match c_layout(p, t) {
        None => match t {
            CTy::Option(_) => {
                if vals.is_empty() {
                    format!("(({ct}){{ .tag = 0 }})")
                } else {
                    format!("(({ct}){{ .tag = 1, .v = {} }})", vals[0])
                }
            }
            _ => {
                if fields.is_empty() {
                    format!("(({ct}){{ .tag = {variant} }})")
                } else {
                    format!("(({ct}){{ .tag = {variant}, .u = {{ .v{variant} = {{ {} }} }} }})", fields.join(", "))
                }
            }
        },
        Some(l) => match l.enum_tag {
            Some(EnumTag::Explicit { size, signed }) => {
                let mut init = format!("._tag = {}", disc_lit(adt_discs(p, t)[variant], size, signed));
                if !fields.is_empty() {
                    init.push_str(", ");
                    init.push_str(&fields.join(", "));
                }
                format!("(({ct}){{ .u = {{ .v{variant} = {{ {init} }} }} }})")
            }
            Some(EnumTag::NicheFilled { variant: niche_variant, niche }) if variant != niche_variant => {
                // The variant struct carries the niche scalar as its
                // own `_s` member, so one literal sets tag and fields.
                let k = (0..variant).filter(|&i| i != niche_variant).count() as u128;
                let mut init = format!("._s = {}", scalar_lit(niche_val(niche, k), niche.scalar_size, false));
                if !fields.is_empty() {
                    init.push_str(", ");
                    init.push_str(&fields.join(", "));
                }
                format!("(({ct}){{ .u = {{ .v{variant} = {{ {init} }} }} }})")
            }
            _ => {
                if fields.is_empty() {
                    zero_lit(p, t)
                } else {
                    format!("(({ct}){{ .u = {{ .v{variant} = {{ {} }} }} }})", fields.join(", "))
                }
            }
        },
    }
}

/// The C initializer for one const value at the given C type. Referenced
/// aggregates are promoted to file-scope constants first, written to `pre`.
fn const_init(p: &Program, v: &crate::ty::consteval::ConstValue, t: &CTy, pre: &mut String, counter: &mut u32, slots: &[u32], pos: Option<&str>) -> String {
    if let (CV::Float(bits, f), CTy::Float(_)) = (v, t) {
        return match f {
            FloatTy::F64 => format!("(((union {{ uint64_t b; double d; }}){{ .b = {}ull }}).d)", bits),
            FloatTy::F32 => format!("(((union {{ uint32_t b; float f; }}){{ .b = {}u }}).f)", *bits as u32),
        };
    }
    use crate::ty::consteval::ConstValue as CV;
    match (v, t) {
        (CV::Int(i), CTy::Int(it)) => {
            if is128(*it) {
                format!("(({}){{{}ULL, {}ULL}})", int_c(*it), *i as u128 as u64, (*i as u128 >> 64) as u64)
            } else if *i < 0 {
                format!("(({})((int64_t){i}))", int_c(*it))
            } else {
                format!("(({})((uint64_t){}ull))", int_c(*it), *i as u128)
            }
        }
        (CV::Bool(b), _) => (*b as u8).to_string(),
        // An atomic's constant is its value (cgen/sync.rs).
        // `Vec::new()` and `String::new()`: an empty buffer, its pointer
        // dangling at the element's alignment (W-THREADS).
        (CV::Aggregate(vals), CTy::Vec(e)) if vals.is_empty() => format!("{{(void*)(uintptr_t){}, 0, 0}}", c_size_align(p, e).1.max(1)),
        (CV::Aggregate(vals), CTy::String) if vals.is_empty() => "{(uint8_t*)(uintptr_t)1, 0, 0}".into(),
        // A const lock: unlocked and unpoisoned around its value.
        (CV::Aggregate(vals), CTy::Sync(k, e)) if k.is_cell_struct() && vals.len() == 1 => {
            let words = vec!["0"; sync::cell_words(*k).len()].join(", ");
            format!("{{{words}, {}}}", const_init(p, &vals[0], e, pre, counter, slots, None))
        }
        // An empty `OnceLock`, a `Condvar`, a `Barrier::new(n)` (W-THREADS).
        (CV::Aggregate(vals), CTy::Sync(crate::ty::sync::SyncTy::OnceLock, _)) if vals.is_empty() => "{0}".into(),
        (CV::Aggregate(vals), CTy::Sync(crate::ty::sync::SyncTy::Condvar, _)) if vals.is_empty() => "0".into(),
        (CV::Aggregate(vals), CTy::Sync(crate::ty::sync::SyncTy::Barrier, _)) if vals.len() == 1 => {
            format!("{{0, 0, 0, 0, {}}}", const_init(p, &vals[0], &CTy::Int(IntTy::Usize), pre, counter, slots, None))
        }
        (CV::Int(i), CTy::Sync(k, _)) if let Some(crate::ty::sync::AtomicVal::Int(it)) = k.atomic_value() => const_init(p, &CV::Int(*i), &CTy::Int(it), pre, counter, slots, None),
        (CV::Char(c), _) => format!("((uint32_t){})", *c as u32),
        (CV::Unit, _) => "((lust_Unit){})".into(),
        (CV::Str(i), _) => {
            let s = &p.ast.strings[*i as usize];
            format!("((lust_str){{(uint8_t*){}, {}}})", c_string_lit(s.as_bytes()), s.len())
        }
        (CV::StaticRef(idx), CTy::Slice(_)) => {
            let st = &p.statics[*idx as usize];
            let sct = cty(&p.tys, st.ty);
            match sct {
                CTy::Array(_, n) => format!("(({}){{ {}.v, {n} }})", ctype(t), static_sym(p, *idx)),
                _ => zero_lit(p, t),
            }
        }
        (CV::StaticRef(idx), _) => format!("(&{})", static_sym(p, *idx)),
        (CV::StaticPlace(idx, path), _) => match static_place_c(p, *idx, path) {
            Some((e, CTy::Array(_, n))) if matches!(t, CTy::Slice(_)) => format!("(({}){{ {e}.v, {n} }})", ctype(t)),
            Some((e, _)) => format!("(&{e})"),
            // A place cgen cannot name: a promoted copy of its value.
            None => match crate::ty::consteval::value_at(&p.statics[*idx as usize].value, path) {
                Some(x) => const_init(p, &CV::Ref(Box::new(x.clone())), t, pre, counter, slots, None),
                None => panic!("internal: a static place {path:?} outside its static's value"),
            },
        },
        (CV::FnPtr(f), CTy::FnPtr(..)) => {
            // Runtime fn pointer values are `lust_tramps[slot]`, not a
            // constant; this unit gets its own copy of the slot's
            // trampoline (forwarding through `lust_fns`), whose address is.
            let f = LocalDefId(*f);
            let slot = *slots.get(f.0 as usize).expect("internal: a fn pointer in static data has no fn slot");
            let name = format!("stramp{slot}");
            if !pre.contains(&format!(" {name}(")) {
                pre.push_str(&trampoline(p, f, slot).replacen(&format!(" tramp{slot}("), &format!(" {name}("), 1));
            }
            format!("(({})&{name})", ctype(t))
        }
        (CV::Ref(inner), CTy::Slice(el)) => {
            // A slice over a promoted aggregate or blob.
            match &**inner {
                CV::Aggregate(vals) => {
                    let at = CTy::Array(el.clone(), vals.len() as u64);
                    let name = promoted_name(counter, pos);
                    let init = const_init(p, inner, &at, pre, counter, slots, pos.map(|_| name.as_str()));
                    let _ = writeln!(pre, "static const {} {name} = {init};", ctype(&at));
                    format!("(({}){{ {name}.v, {} }})", ctype(t), vals.len())
                }
                CV::Bytes(b) => {
                    let at = CTy::Array(el.clone(), b.len() as u64);
                    let init = const_init(p, inner, &at, pre, counter, slots, None);
                    let name = promoted_name(counter, pos);
                    let _ = writeln!(pre, "static const {} {name} = {init};", ctype(&at));
                    format!("(({}){{ {name}.v, {} }})", ctype(t), b.len())
                }
                _ => zero_lit(p, t),
            }
        }
        (CV::Ref(inner), CTy::Ref(inner_ct)) => {
            let name = promoted_name(counter, pos);
            let init = const_init(p, inner, inner_ct, pre, counter, slots, pos.map(|_| name.as_str()));
            let _ = writeln!(pre, "static const {} {name} = {init};", ctype(inner_ct));
            format!("(&{name})")
        }
        (CV::Aggregate(vals), CTy::Tuple(es)) => {
            if vals.is_empty() {
                zero_lit(p, t)
            } else {
                let parts: Vec<String> =
                    vals.iter().enumerate().map(|(i, x)| format!(".f{i} = {}", const_init(p, x, &es[i], pre, counter, slots, sub(pos, i).as_deref()))).collect();
                format!("(({}){{ {} }})", ctype(t), parts.join(", "))
            }
        }
        (CV::Aggregate(vals), CTy::Array(e, _)) => {
            if vals.is_empty() {
                zero_lit(p, t)
            } else {
                let parts: Vec<String> = vals.iter().enumerate().map(|(i, x)| const_init(p, x, e, pre, counter, slots, sub(pos, i).as_deref())).collect();
                format!("(({}){{ .v = {{ {} }} }})", ctype(t), parts.join(", "))
            }
        }
        (CV::Repeat(x, n), CTy::Array(e, _)) => {
            if *n == 0 {
                zero_lit(p, t)
            } else {
                // Every element is the one value: a promoted reference in it is one
                // allocation, named by element 0.
                let one = const_init(p, x, e, pre, counter, slots, sub(pos, 0).as_deref());
                let parts: Vec<String> = (0..*n).map(|_| one.clone()).collect();
                format!("(({}){{ .v = {{ {} }} }})", ctype(t), parts.join(", "))
            }
        }
        (CV::Aggregate(vals), CTy::Adt(a)) => {
            let adt = p.adt(*a);
            if vals.is_empty() {
                zero_lit(p, t)
            } else {
                let parts: Vec<String> = vals
                    .iter()
                    .enumerate()
                    .map(|(i, x)| format!(".f{i} = {}", const_init(p, x, &cty(&p.tys, adt.variants[0].fields[i].ty), pre, counter, slots, sub(pos, i).as_deref())))
                    .collect();
                format!("((A{}){{ {} }})", a.0, parts.join(", "))
            }
        }
        (CV::Variant(variant, vals), CTy::Adt(a)) => {
            let adt = p.adt(*a);
            let inits: Vec<String> = vals
                .iter()
                .enumerate()
                .map(|(i, x)| const_init(p, x, &cty(&p.tys, adt.variants[*variant as usize].fields[i].ty), pre, counter, slots, None))
                .collect();
            variant_lit(p, t, *variant as usize, &inits)
        }
        (CV::Variant(variant, vals), CTy::Option(e)) => {
            let inits: Vec<String> = vals.iter().map(|x| const_init(p, x, e, pre, counter, slots, None)).collect();
            variant_lit(p, t, *variant as usize, &inits)
        }
        (CV::Variant(variant, vals), CTy::Result(a, b)) => {
            let e = if *variant == 0 { a } else { b };
            let inits: Vec<String> = vals.iter().map(|x| const_init(p, x, e, pre, counter, slots, None)).collect();
            variant_lit(p, t, *variant as usize, &inits)
        }
        (CV::Aggregate(vals), CTy::Slice(e)) => {
            let at = CTy::Array(e.clone(), vals.len() as u64);
            let name = promoted_name(counter, pos);
            let init = const_init(p, v, &at, pre, counter, slots, pos.map(|_| name.as_str()));
            let _ = writeln!(pre, "static const {} {name} = {init};", ctype(&at));
            format!("(({}){{ {name}.v, {} }})", ctype(t), vals.len())
        }
        // One C array for the whole blob, at an array type; at a
        // slice type it is the promoted backing array, as an
        // aggregate slice backing is above.
        (CV::Bytes(b), CTy::Array(..)) => bytes_array_lit(p, t, b.as_slice()),
        (CV::Bytes(b), CTy::Slice(e)) => {
            let at = CTy::Array(e.clone(), b.len() as u64);
            let init = const_init(p, v, &at, pre, counter, slots, None);
            let name = promoted_name(counter, pos);
            let _ = writeln!(pre, "static const {} {name} = {init};", ctype(&at));
            format!("(({}){{ {name}.v, {} }})", ctype(t), b.len())
        }
        _ => zero_lit(p, t),
    }
}

/// The C name of a promoted value in static data. Inside a static's
/// value (`pos` is the position's name, see `static_pos`) it is named by
/// its path, so a `StaticPlace` in another static can name it
/// (`static_place_c`); elsewhere it gets a counter name.
fn promoted_name(counter: &mut u32, pos: Option<&str>) -> String {
    match pos {
        Some(at) => format!("{at}_d"),
        None => {
            *counter += 1;
            format!("lust_promoted_{counter}")
        }
    }
}

/// The position name of field or element `i` below position `pos`.
fn sub(pos: Option<&str>, i: usize) -> Option<String> {
    pos.map(|at| format!("{at}_{i}"))
}

/// The position name of static `idx`'s root value: the prefix of the
/// names of the promoted values inside it (`promoted_name`).
fn static_pos(p: &Program, idx: u32) -> String {
    format!("lust_sp{}", &static_sym(p, idx)["lust_static".len()..])
}

/// The C place of a `ConstValue::StaticPlace` and its C type: field and
/// element projections of the static's symbol, and a `Deref` step to the
/// promoted value the static holds there, by its path name. None for a
/// step this shape does not have.
fn static_place_c(p: &Program, idx: u32, path: &[crate::ty::consteval::StaticStep]) -> Option<(String, CTy)> {
    use crate::ty::consteval::{ConstValue as CV, StaticStep, value_at};
    let st = p.statics.get(idx as usize)?;
    // `v` follows the value along (None past a byte blob's element).
    let (mut e, mut pos, mut ct, mut v) = (static_sym(p, idx), static_pos(p, idx), cty(&p.tys, st.ty), Some(&st.value));
    for step in path {
        // A repeat's elements share element 0's promoted values.
        let at = match (step, v) {
            (StaticStep::Field(_) | StaticStep::Elem(_), Some(CV::Repeat(..))) => format!("{pos}_0"),
            (StaticStep::Field(i) | StaticStep::Elem(i), _) => format!("{pos}_{i}"),
            (StaticStep::Deref, _) => format!("{pos}_d"),
        };
        (e, ct) = match (step, ct) {
            (StaticStep::Field(i), CTy::Adt(a)) => (format!("{e}.f{i}"), cty(&p.tys, p.adt(a).variants.first()?.fields.get(*i as usize)?.ty)),
            (StaticStep::Field(i), CTy::Tuple(es)) => (format!("{e}.f{i}"), es.get(*i as usize)?.clone()),
            (StaticStep::Elem(i), CTy::Array(el, _)) => (format!("{e}.v[{i}]"), *el),
            (StaticStep::Deref, CTy::Ref(inner)) => (at.clone(), *inner),
            (StaticStep::Deref, CTy::Slice(el)) => {
                let n = match v? {
                    CV::Ref(inner) => match &**inner {
                        CV::Aggregate(vals) => vals.len() as u64,
                        CV::Bytes(b) => b.len() as u64,
                        _ => return None,
                    },
                    CV::Aggregate(vals) => vals.len() as u64,
                    CV::Bytes(b) => b.len() as u64,
                    _ => return None,
                };
                (at.clone(), CTy::Array(el, n))
            }
            _ => return None,
        };
        pos = at;
        v = v.and_then(|v| value_at(v, std::slice::from_ref(step)));
    }
    Some((e, ct))
}

/// The C symbol of one static. Named by the static's stable def hash,
/// never by its collect-order index: cached function code (a daemon
/// slot's `FnOut`, a disk unit object) names statics by symbol, and an
/// edit that inserts a static earlier in the file shifts every later
/// index. A position-based name would then read the wrong static
/// while every fingerprint still matches (the same reason fn slots
/// key on def identity, section 4.2).
fn static_sym(p: &Program, idx: u32) -> String {
    match p.static_defs.get(idx as usize) {
        Some(def) => format!("lust_static_{}", def.hash.0),
        None => format!("lust_static_{idx}"),
    }
}

/// The array types `const_init` synthesizes for slice values inside a
/// const value (a promoted backing array exists in no written type, so
/// collecting only the static types themselves misses it).
fn collect_promoted(p: &Program, v: &crate::ty::consteval::ConstValue, t: &CTy, out: &mut HashSet<CTy>) {
    use crate::ty::consteval::ConstValue as CV;
    match (v, t) {
        (CV::Ref(inner), CTy::Slice(el)) => {
            match &**inner {
                CV::Aggregate(vals) => {
                    let at = CTy::Array(el.clone(), vals.len() as u64);
                    collect_types(&at, out);
                    collect_promoted(p, inner, &at, out);
                }
                CV::Bytes(b) => {
                    let at = CTy::Array(el.clone(), b.len() as u64);
                    collect_types(&at, out);
                }
                _ => {}
            }
        }
        (CV::Aggregate(vals), CTy::Slice(e)) => {
            let at = CTy::Array(e.clone(), vals.len() as u64);
            collect_types(&at, out);
            for x in vals {
                collect_promoted(p, x, e, out);
            }
        }
        (CV::Bytes(b), CTy::Slice(e)) => {
            let at = CTy::Array(e.clone(), b.len() as u64);
            collect_types(&at, out);
        }
        (CV::Ref(inner), CTy::Ref(inner_ct)) => collect_promoted(p, inner, inner_ct, out),
        (CV::Aggregate(vals), CTy::Tuple(es)) => {
            for (x, e) in vals.iter().zip(es) {
                collect_promoted(p, x, e, out);
            }
        }
        (CV::Aggregate(vals), CTy::Array(e, _)) => {
            for x in vals {
                collect_promoted(p, x, e, out);
            }
        }
        (CV::Repeat(x, _), CTy::Array(e, _)) => collect_promoted(p, x, e, out),
        (CV::Aggregate(vals), CTy::Adt(a)) => {
            for (i, x) in vals.iter().enumerate() {
                collect_promoted(p, x, &cty(&p.tys, p.adt(*a).variants[0].fields[i].ty), out);
            }
        }
        (CV::Variant(variant, vals), CTy::Adt(a)) => {
            for (i, x) in vals.iter().enumerate() {
                collect_promoted(p, x, &cty(&p.tys, p.adt(*a).variants[*variant as usize].fields[i].ty), out);
            }
        }
        (CV::Variant(_, vals), CTy::Option(e)) => {
            for x in vals {
                collect_promoted(p, x, e, out);
            }
        }
        _ => {}
    }
}

/// Definitions of the program's statics as C globals (ARCH 2.13 static data).
/// The extern declarations come first: statics emit in stable def order,
/// so one static's initializer can name a later static (`static S: &[u8] = &A;`
/// before `A` in hash order), and C needs the name declared before use.
fn static_defs(p: &Program, slots: &[u32]) -> String {
    let mut pre = static_decls(p);
    let mut out = String::new();
    let mut counter = 0u32;
    for (i, st) in p.statics.iter().enumerate() {
        let ct = cty(&p.tys, st.ty);
        let init = const_init(p, &st.value, &ct, &mut pre, &mut counter, slots, Some(&static_pos(p, i as u32)));
        let _ = writeln!(out, "{} {} = {init};", ctype(&ct), static_sym(p, i as u32));
    }
    // Tentative definitions of the path-named promoted values first: one
    // static's data can point into another's (`static_place_c`), in any order.
    let mut fwd = String::new();
    for line in pre.lines() {
        if let Some(rest) = line.strip_prefix("static const ")
            && let Some((decl, _)) = rest.split_once(" = ")
            && decl.contains(" lust_sp_")
        {
            let _ = writeln!(fwd, "static const {decl};");
        }
    }
    format!("{fwd}{pre}{out}")
}

/// Extern declarations of the statics, for function units.
fn static_decls(p: &Program) -> String {
    static_decls_for(p, &HashSet::from_iter(0..p.statics.len()))
}

/// Extern declarations of the statics at `keep` indices, for function units.
fn static_decls_for(p: &Program, keep: &HashSet<usize>) -> String {
    let mut out = String::new();
    for (i, st) in p.statics.iter().enumerate() {
        if keep.contains(&i) {
            let _ = writeln!(out, "extern {} {};", ctype(&cty(&p.tys, st.ty)), static_sym(p, i as u32));
        }
    }
    out
}

/// The indices of the statics whose C symbol any of `texts` names.
/// Generated C names a static only by its symbol, so a text scan is
/// exact: a symbol inside a string literal only keeps one extra
/// declaration. Function units declare (and declare the types of)
/// only the statics they use, instead of every static in the program
/// in every unit.
fn used_statics<'a>(p: &Program, texts: impl Iterator<Item = &'a str>) -> HashSet<usize> {
    let mut syms: HashSet<&'a str> = HashSet::new();
    for text in texts {
        let mut rest = text;
        while let Some(i) = rest.find("lust_static_") {
            rest = &rest[i..];
            let end = rest.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_')).unwrap_or(rest.len());
            syms.insert(&rest[..end]);
            rest = &rest[end..];
            if rest.is_empty() {
                break;
            }
        }
    }
    (0..p.statics.len()).filter(|&i| syms.contains(static_sym(p, i as u32).as_str())).collect()
}

/// The unit for the slots in `range` (`fns` is indexed by slot; empty slots have no code). Its
/// functions are static; the function `register` stores them in `lust_fns`.
/// `main_slot` is the slot of `p.main` (not its `LocalDefId`: slots are
/// stable across edits, local ids are not).
pub fn fn_unit(p: &Program, fns: &[FnOut], range: std::ops::Range<usize>, g: &GlueSet, register: &str, main_slot: Option<u32>) -> String {
    let mut c = unit_header();
    let mut types = HashSet::new();
    let mut seen: HashSet<&(Glue, CTy)> = HashSet::new();
    for f in &fns[range.clone()] {
        types.extend(f.types.iter().cloned());
        seen.extend(f.glue.iter());
    }
    // The termination entry below names main's return type directly.
    // Declare it in this unit even when main's cached `FnOut` predates
    // the return-type edit (a warm unit must not name an undeclared
    // `Result` struct).
    let main_in_unit = main_slot.filter(|&s| range.contains(&(s as usize)) && fns.get(s as usize).is_some_and(|f| !f.code.is_empty()));
    let term_main = main_in_unit.and_then(|s| p.main.map(|m| (m, s))).filter(|&(m, _)| {
        let ret = p.fn_info(m).ret;
        p.tys.is_exit_code(ret) || p.tys.result_args(ret).is_some()
    });
    if let Some((m, _)) = term_main {
        collect_types(&cty(&p.tys, p.fn_info(m).ret), &mut types);
    }
    // With a frozen shared set, glue that is not shared is static in this unit: walk its deps
    // too, and stop at shared keys (their deps live in the glue unit). Shared keys still need
    // their prototype, and every reached key needs its C type declared.
    let hybrid = g.shared.is_some();
    if hybrid {
        let mut stack: Vec<&(Glue, CTy)> = seen.iter().copied().collect();
        while let Some(k) = stack.pop() {
            if g.is_shared(k) {
                collect_types(&k.1, &mut types);
            } else {
                g.def_types(k, &mut types);
                if let Some(deps) = g.deps.get(k) {
                    for dep in deps {
                        if seen.insert(dep) {
                            stack.push(dep);
                        }
                    }
                }
            }
        }
    }
    // Only the statics this unit's code (and its local glue) names:
    // their types and their extern declarations. Every static in
    // every unit was pure repetition in a program with many statics.
    let used = used_statics(
        p,
        fns[range.clone()]
            .iter()
            .map(|f| f.code.as_str())
            .chain(seen.iter().filter(|k| hybrid && !g.is_shared(k)).map(|k| g.def_map[*k].as_str())),
    );
    for &i in &used {
        collect_types(&cty(&p.tys, p.statics[i].ty), &mut types);
    }
    type_decls(p, &mut c, &types);
    c.push_str(&static_decls_for(p, &used));
    let mut keys: Vec<&(Glue, CTy)> = seen.iter().copied().collect();
    keys.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
    for k in &keys {
        if hybrid && !g.is_shared(k) {
            c.push_str("static ");
        }
        c.push_str(&g.protos[*k]);
    }
    if hybrid {
        for k in keys.iter().filter(|k| !g.is_shared(k)) {
            c.push_str("static ");
            c.push_str(&g.def_map[*k]);
        }
    }
    for f in &fns[range.clone()] {
        c.push_str(&f.code);
    }
    // Termination entry for a `main` returning `ExitCode` or
    // `Result<T, E>` (T `()` or `ExitCode`): call main through the
    // table; on Err print `Error: {err:?}` to stderr and exit 1, as
    // Rust does; an `ExitCode` is the exit status. Registered below
    // in `lust_main_entry_p`, which the main unit prefers over the
    // plain void call. The Debug and Drop glue it calls is wanted
    // by main's own FnOut (see `gen_fn`).
    if let Some((m, idx)) = term_main {
        let ret = p.fn_info(m).ret;
        let rc = cty(&p.tys, ret);
        let rt = ctype(&rc);
        let cast = fn_ptr_cast(p, m);
        let _ = writeln!(c, "static int lust_main_entry_impl(void) {{");
        if ret_is_large(p, m) {
            let _ = writeln!(c, "  {rt} r; ({cast}lust_fns[{idx}])(&r);");
        } else {
            let _ = writeln!(c, "  {rt} r = ({cast}lust_fns[{idx}])();");
        }
        if p.unwind {
            let _ = writeln!(c, "  if (lust_unw_pending && lust_unw_mine()) return 0;");
        }
        match p.tys.result_args(ret) {
            Some((ok_t, err_t)) => {
                let disc = disc_call(p, &rc, "(&r)");
                let field = variant_field(p, &rc, "r", 1, 0);
                let ec = cty(&p.tys, err_t);
                let ok = if p.tys.is_exit_code(ok_t) { format!(" else {{ rc = {}; }}", variant_field(p, &rc, "r", 0, 0)) } else { String::new() };
                let _ = writeln!(c, "  int rc = 0;");
                let _ = writeln!(
                    c,
                    "  if ({disc}) {{ lust_sink k; lust_print_begin(&k, 1); lust_Formatter f; lust_f_init(&f, &k); lust_f_write(&f, \"Error: \", 7); (void)dbg_{}(&f, &{field}); lust_f_write(&f, \"\\n\", 1); lust_print_end(1); rc = 1; }}{ok}",
                    mangle(&ec)
                );
            }
            None => {
                let _ = writeln!(c, "  int rc = r;");
            }
        }
        if needs_drop_c(p, &rc) {
            let _ = writeln!(c, "  drop_{}(&r);", mangle(&rc));
        }
        let _ = writeln!(c, "  return rc;\n}}");
    }
    let _ = writeln!(c, "void {register}(void) {{");
    for i in range.filter(|&i| !fns[i].code.is_empty()) {
        let _ = writeln!(c, "  lust_fns[{i}] = (lust_fnptr)f{i};");
        let _ = writeln!(c, "  lust_tramps[{i}] = (lust_fnptr)tramp{i};");
    }
    if term_main.is_some() {
        let _ = writeln!(c, "  lust_main_entry_p = lust_main_entry_impl;");
    } else if main_in_unit.is_some() {
        // This unit holds main and main now returns `()`: clear an
        // entry a base unit from an earlier build may have registered
        // for a `Result`/`ExitCode` main (overlays register after the
        // base, so this wins).
        let _ = writeln!(c, "  lust_main_entry_p = 0;");
    }
    c.push_str("}\n");
    c
}

/// The members of one C struct for fields at layout offsets: fields in
/// offset order with explicit padding byte arrays between them, so the
/// C offsets equal the layout offsets no matter what the C compiler
/// would pick on its own. `fields` holds (declaration, field layout,
/// offset) per field; `total` pads to the full size when given.
fn layout_members(fields: &[(String, Layout, u64)], total: Option<u64>, struct_align: u64) -> String {
    let mut order: Vec<usize> = (0..fields.len()).collect();
    order.sort_by(|&a, &b| fields[a].2.cmp(&fields[b].2).then(fields[b].1.align.cmp(&fields[a].1.align)).then(a.cmp(&b)));
    let mut members: Vec<String> = Vec::new();
    let mut cur = 0u64;
    let mut pad = 0u32;
    for &i in &order {
        let (decl, fl, off) = &fields[i];
        if *off > cur {
            members.push(format!("uint8_t _p{pad}[{}]", off - cur));
            pad += 1;
            cur = *off;
        }
        members.push(decl.clone());
        cur = cur.max(off + fl.size);
    }
    if let Some(sz) = total
        && sz > cur
    {
        members.push(format!("uint8_t _p{pad}[{}]", sz - cur));
    }
    let natural = fields.iter().map(|f| f.1.align).max().unwrap_or(1);
    if struct_align > natural && !members.is_empty() {
        members[0] = format!("_Alignas({struct_align}) {}", members[0]);
    }
    members.iter().map(|m| format!("{m}; ")).collect()
}

/// The compile-time layout proof for one emitted type: the C sizeof and
/// _Alignof must equal the layout the type was emitted from.
fn layout_assert(out: &mut String, ct: &str, l: &Layout) {
    let _ = writeln!(out, "_Static_assert(sizeof({ct}) == {} && _Alignof({ct}) == {}, \"layout\");", l.size, l.align);
}

/// One field's layout for `layout_members`, for a parent whose own
/// `c_layout` is already exact. A miss here means the parent check and
/// this one disagree; size 0 keeps the C layout assert as the failure.
fn field_layout(p: &Program, t: &CTy) -> Layout {
    c_layout(p, t).unwrap_or_else(|| plain_layout(0, 1))
}

/// Emits one layout-exact enum type (an Adt enum or an Option) plus its
/// `disc_<mangle>` reader. The shape is one union: a struct per variant
/// with fields at their absolute layout offsets, the tag scalar or a
/// niche view struct, and a size member that pins the total size and
/// alignment. `opener` is the declaration up to the opening brace.
fn emit_enum_decl(p: &Program, out: &mut String, opener: &str, t: &CTy, variants: &[Vec<CTy>], l: &Layout) {
    let ct = ctype(t);
    let _ = write!(out, "{opener} {{ union {{ ");
    // An explicit tag also appears as the first member of every variant
    // struct, so a value can be built with one compound literal that
    // designates a single union member (see `make_variant`).
    let explicit = match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => Some((size, signed)),
        _ => None,
    };
    // A niche tag scalar also appears as a member of every non-niche
    // variant struct (whose fields avoid its bytes by construction),
    // for the same single-designator reason.
    let niche = match l.enum_tag {
        Some(EnumTag::NicheFilled { variant, niche }) => Some((variant, niche)),
        _ => None,
    };
    for (vi, v) in variants.iter().enumerate() {
        let has_synth = explicit.is_some() || niche.is_some_and(|(nv, _)| vi != nv);
        if v.is_empty() && !has_synth {
            continue;
        }
        let mut fields: Vec<(String, Layout, u64)> = Vec::new();
        if let Some((size, signed)) = explicit {
            fields.push((format!("{} _tag", tag_c_type(size, signed)), plain_layout(size, size), 0));
        }
        if let Some((nv, n)) = niche
            && vi != nv
        {
            fields.push((format!("{} _s", tag_c_type(n.scalar_size, false)), plain_layout(n.scalar_size, n.scalar_size), n.offset));
        }
        fields
            .extend(v.iter().enumerate().map(|(fi, ft)| (format!("{} f{fi}", ctype(ft)), field_layout(p, ft), l.variant_offsets[vi][fi])));
        let _ = write!(out, "struct {{ {}}} v{vi}; ", layout_members(&fields, None, 1));
    }
    match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => {
            let _ = write!(out, "{} _tag; ", tag_c_type(size, signed));
        }
        Some(EnumTag::NicheFilled { niche: Niche { offset, scalar_size, .. }, .. }) => {
            let pad = if offset > 0 { format!("uint8_t _p[{offset}]; ") } else { String::new() };
            let _ = write!(out, "struct {{ {pad}{} _s; }} _n; ", tag_c_type(scalar_size, false));
        }
        _ => {}
    }
    if l.size > 0 {
        let al = if l.align > 1 { format!("_Alignas({}) ", l.align) } else { String::new() };
        let _ = write!(out, "{al}uint8_t _size[{}]; ", l.size);
    }
    out.push_str("} u; }");
    if opener.starts_with("typedef") {
        let _ = write!(out, " {ct}");
    }
    out.push_str(";\n");
    layout_assert(out, &ct, l);
    let m = mangle(t);
    match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => {
            let discs = adt_discs(p, t);
            if size >= 16 {
                // A two-word tag cannot switch: compare both words.
                let _ = write!(out, "static inline uint32_t disc_{m}(const {ct} *p) {{");
                for (vi, &d) in discs.iter().enumerate() {
                    let bits = d as u128;
                    let _ =
                        write!(out, " if (p->u._tag.lo == {}ULL && p->u._tag.hi == {}ULL) return {vi};", bits as u64, (bits >> 64) as u64);
                }
                let _ = writeln!(out, " return 0; }}");
            } else if !discs_sequential(&discs) {
                let _ = write!(out, "static inline uint32_t disc_{m}(const {ct} *p) {{ switch (p->u._tag) {{");
                for (vi, &d) in discs.iter().enumerate() {
                    let _ = write!(out, " case {}: return {vi};", disc_lit(d, size, signed));
                }
                let _ = writeln!(out, " default: return 0; }} }}");
            }
        }
        Some(EnumTag::NicheFilled { variant, niche }) => {
            let others: Vec<usize> = (0..variants.len()).filter(|&i| i != variant).collect();
            if niche.scalar_size >= 16 {
                let _ = write!(out, "static inline uint32_t disc_{m}(const {ct} *p) {{");
                for (k, &vi) in others.iter().enumerate() {
                    let bits = niche_val(niche, k as u128);
                    let _ = write!(
                        out,
                        " if (p->u._n._s.lo == {}ULL && p->u._n._s.hi == {}ULL) return {vi};",
                        bits as u64,
                        (bits >> 64) as u64
                    );
                }
                let _ = writeln!(out, " return {variant}; }}");
            } else {
                // Wrapping distance from the first niche value: values
                // that wrap past the top of the scalar range read back
                // as small distances.
                let start = niche.start as u64;
                let mask: u64 = if niche.scalar_size >= 8 { u64::MAX } else { (1u64 << (niche.scalar_size * 8)) - 1 };
                let ret = if others.len() == 1 {
                    format!("return {};", others[0])
                } else {
                    let map: Vec<String> = others.iter().map(|i| i.to_string()).collect();
                    format!("static const uint32_t map[{}] = {{{}}}; return map[d];", others.len(), map.join(","))
                };
                let _ = writeln!(
                    out,
                    "static inline uint32_t disc_{m}(const {ct} *p) {{ uint64_t s = p->u._n._s; uint64_t d = (s - {start}ULL) & {mask}ULL; if (d < {}ULL) {{ {ret} }} return {variant}; }}",
                    others.len()
                );
            }
        }
        _ => {}
    }
}

/// Declares the given types, plus every type they contain (by value or inside a Vec).
fn type_decls(p: &Program, out: &mut String, roots: &HashSet<CTy>) {
    // Close over field types.
    let mut wanted: HashSet<CTy> = HashSet::new();
    let mut stack: Vec<CTy> = roots.iter().cloned().collect();
    while let Some(t) = stack.pop() {
        if !wanted.insert(t.clone()) {
            continue;
        }
        let mut inner = HashSet::new();
        match &t {
            CTy::Adt(a) => p.adt(*a).variants.iter().flat_map(|v| &v.fields).for_each(|f| collect_types(&cty(&p.tys, f.ty), &mut inner)),
            CTy::Option(e) => collect_types(e, &mut inner),
            CTy::Result(a, b) => {
                collect_types(a, &mut inner);
                collect_types(b, &mut inner);
            }
            CTy::Tuple(es) => es.iter().for_each(|e| collect_types(e, &mut inner)),
            CTy::Array(e, _) => collect_types(e, &mut inner),
            CTy::ArrayIter(e, n) => collect_types(&CTy::Array(e.clone(), *n), &mut inner),
            CTy::Slice(e) => collect_types(e, &mut inner),
            CTy::Rc(e) | CTy::RefCell(e) => collect_types(e, &mut inner),
            CTy::FnPtr(ps, r) => {
                ps.iter().for_each(|e| collect_types(e, &mut inner));
                collect_types(r, &mut inner);
            }
            CTy::Hash(_, args) => {
                args.iter().for_each(|e| collect_types(e, &mut inner));
                collect_types(&hash::elem_cty(&t), &mut inner);
            }
            _ => {}
        }
        stack.extend(inner);
    }
    // The hash core's declarations, only in units that name a hash type
    // (see `runtime_source`).
    if wanted.iter().any(|t| matches!(t, CTy::Hash(..))) {
        out.push_str(&hash_decls());
    }
    let mut list: Vec<CTy> = wanted.into_iter().collect();
    list.sort_by_cached_key(mangle);
    for t in &list {
        if let CTy::Adt(a) = t {
            let _ = writeln!(out, "typedef struct A{0} A{0};", a.0);
        }
        // Every struct-typed C type too: a closure env holds references
        // (`&(captures..)`, `&Result<..>`) that can sit in a type emitted
        // before the referenced type's own definition.
        if let CTy::Tuple(_) | CTy::Option(_) | CTy::Result(..) | CTy::Array(..) | CTy::Slice(_) | CTy::ArrayIter(..) = t {
            let _ = writeln!(out, "typedef struct {0} {0};", ctype(t));
        }
        match t {
            CTy::Rc(e) => {
                let _ = writeln!(out, "typedef struct RcI_{0} RcI_{0};", mangle(e));
            }
            CTy::RefCell(e) => {
                let _ = writeln!(out, "typedef struct RCL_{0} RCL_{0};", mangle(e));
            }
            CTy::Sync(k, _) if k.is_cell_struct() => {
                let _ = writeln!(out, "typedef struct {0} {0};", ctype(t));
            }
            _ => {}
        }
        if let CTy::Hash(k, _) = t
            && hash::has_struct(*k)
        {
            let _ = writeln!(out, "typedef struct {0} {0};", ctype(t));
        }
    }
    // Each definition comes after the types it holds by value.
    fn emit(p: &Program, t: &CTy, emitted: &mut HashSet<CTy>, out: &mut String) {
        if !emitted.insert(t.clone()) {
            return;
        }
        let mut deps = Vec::new();
        match t {
            CTy::Adt(a) => p.adt(*a).variants.iter().flat_map(|v| &v.fields).for_each(|f| by_value_deps(&cty(&p.tys, f.ty), &mut deps)),
            CTy::Option(e) => by_value_deps(e, &mut deps),
            CTy::Result(a, b) => {
                by_value_deps(a, &mut deps);
                by_value_deps(b, &mut deps);
            }
            CTy::Tuple(es) => es.iter().for_each(|e| by_value_deps(e, &mut deps)),
            CTy::Array(e, _) => by_value_deps(e, &mut deps),
            CTy::ArrayIter(e, n) => by_value_deps(&CTy::Array(e.clone(), *n), &mut deps),
            // A slice holds `e*` only: every struct type has a forward
            // typedef above, so only a fn pointer typedef must come
            // first. Counting `e` itself made a false cycle for a
            // recursive `enum A { P(Arc<[A]>) }`, and the DFS start
            // order (ADT ids, which follow the file name) then decided
            // which side was incomplete.
            CTy::Slice(e) => by_value_deps(&CTy::Ref(e.clone()), &mut deps),
            CTy::Rc(e) | CTy::RefCell(e) => by_value_deps(e, &mut deps),
            CTy::Sync(k, e) if k.is_cell_struct() => by_value_deps(e, &mut deps),
            CTy::FnPtr(ps, r) => {
                ps.iter().for_each(|e| by_value_deps(e, &mut deps));
                by_value_deps(r, &mut deps);
            }
            CTy::Hash(_, args) => {
                // A table holds its builder by value; an Entry its key.
                if let Some(s) = args.last() {
                    by_value_deps(s, &mut deps);
                }
                if let Some(k) = args.first() {
                    by_value_deps(k, &mut deps);
                }
                by_value_deps(&hash::elem_cty(t), &mut deps);
            }
            _ => {}
        }
        for d in &deps {
            emit(p, d, emitted, out);
        }
        if let CTy::Hash(k, _) = t
            && hash::has_struct(*k)
        {
            let _ = writeln!(out, "struct {} {{ {} }};", ctype(t), hash::struct_fields(t));
            return;
        }
        match t {
            CTy::Option(e) => match c_layout(p, t) {
                Some(l) => emit_enum_decl(p, out, &format!("typedef struct {}", ctype(t)), t, &[vec![], vec![(**e).clone()]], &l),
                None => {
                    let _ = writeln!(out, "typedef struct {0} {{ uint32_t tag; {1} v; }} {0};", ctype(t), ctype(e));
                }
            },
            CTy::Result(a, b) => match c_layout(p, t) {
                Some(l) => {
                    emit_enum_decl(p, out, &format!("typedef struct {}", ctype(t)), t, &[vec![(**a).clone()], vec![(**b).clone()]], &l)
                }
                None => {
                    let _ = writeln!(
                        out,
                        "typedef struct {0} {{ uint32_t tag; union {{ struct {{ {1} f0; }} v0; struct {{ {2} f0; }} v1; }} u; }} {0};",
                        ctype(t),
                        ctype(a),
                        ctype(b)
                    );
                }
            },
            CTy::Tuple(es) => match c_layout(p, t) {
                Some(l) => {
                    let ct = ctype(t);
                    if es.is_empty() {
                        let _ = writeln!(out, "typedef struct {ct} {{ }} {ct};");
                    } else {
                        let fields: Vec<(String, Layout, u64)> = es
                            .iter()
                            .enumerate()
                            .map(|(i, e)| (format!("{} f{i}", ctype(e)), field_layout(p, e), l.field_offsets[i]))
                            .collect();
                        let _ = writeln!(out, "typedef struct {ct} {{ {}}} {ct};", layout_members(&fields, Some(l.size), l.align));
                    }
                    layout_assert(out, &ct, &l);
                }
                None => {
                    let fields: String = es.iter().enumerate().map(|(i, e)| format!("{} f{i}; ", ctype(e))).collect();
                    let fields = if fields.is_empty() { "uint8_t unused; ".to_string() } else { fields };
                    let _ = writeln!(out, "typedef struct {0} {{ {fields}}} {0};", ctype(t));
                }
            },
            CTy::Array(e, n) => match c_layout(p, t) {
                Some(l) => {
                    let ct = ctype(t);
                    let _ = writeln!(out, "typedef struct {ct} {{ {} v[{n}]; }} {ct};", ctype(e));
                    layout_assert(out, &ct, &l);
                }
                None => {
                    let _ = writeln!(out, "typedef struct {0} {{ {1} v[{2}]; }} {0};", ctype(t), ctype(e), (*n).max(1));
                }
            },
            CTy::ArrayIter(e, n) => {
                let at = CTy::Array(e.clone(), *n);
                let ct = ctype(t);
                match c_layout(p, t) {
                    Some(l) => {
                        let es = [at.clone(), CTy::Int(IntTy::Usize), CTy::Int(IntTy::Usize)];
                        let fields: Vec<(String, Layout, u64)> = es
                            .iter()
                            .enumerate()
                            .map(|(i, e)| (format!("{} f{i}", ctype(e)), field_layout(p, e), l.field_offsets[i]))
                            .collect();
                        let _ = writeln!(out, "typedef struct {ct} {{ {}}} {ct};", layout_members(&fields, Some(l.size), l.align));
                        layout_assert(out, &ct, &l);
                    }
                    None => {
                        let _ = writeln!(out, "typedef struct {ct} {{ {} f0; uint64_t f1; uint64_t f2; }} {ct};", ctype(&at));
                    }
                }
            },
            CTy::Slice(e) => {
                let _ = writeln!(out, "typedef struct {0} {{ {1}* ptr; uint64_t len; }} {0};", ctype(t), ctype(e));
                if let Some(l) = c_layout(p, t) {
                    layout_assert(out, &ctype(t), &l);
                }
            }
            CTy::Rc(e) => {
                let _ = writeln!(out, "typedef struct RcI_{0} {{ uint64_t strong; uint64_t weak; {1} v; }} RcI_{0};", mangle(e), ctype(e));
            }
            CTy::RefCell(e) => {
                let _ = writeln!(out, "typedef struct RCL_{0} {{ int64_t f0; {1} f1; }} RCL_{0};", mangle(e), ctype(e));
            }
            // `Mutex<T>`: the futex word, the poison flag, the value;
            // `RwLock<T>` adds the waiter count (runtime/sync.c).
            CTy::Sync(k, e) if k.is_cell_struct() => {
                // A Mutex has no `wn`: its second word is `poison`.
                let names: &[&str] = if *k == crate::ty::sync::SyncTy::Mutex { &["st", "poison"] } else { &["st", "wn", "poison"] };
                let words: String = names.iter().zip(sync::cell_words(*k)).map(|(n, i)| format!("{} {n}; ", int_c(*i))).collect();
                let _ = writeln!(out, "struct {0} {{ {words}{1} v; }};", ctype(t), ctype(e));
            }
            CTy::FnPtr(ps, r) => {
                let ct = ctype(t);
                let large = ret_by_out(p, r);
                let mut params: Vec<String> = Vec::new();
                if large {
                    params.push(format!("{}*", ctype(r)));
                }
                params.extend(ps.iter().filter(|t| !param_dropped(p, t)).map(ctype));
                let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
                if large {
                    let _ = writeln!(out, "typedef void (*{ct})({params});");
                } else {
                    let _ = writeln!(out, "typedef {} (*{ct})({params});", ctype(r));
                }
                if let Some(l) = c_layout(p, t) {
                    layout_assert(out, &ct, &l);
                }
            }
            CTy::Adt(a) => {
                let adt = p.adt(*a);
                let an = a.0;
                let _ = writeln!(out, "/* {} */", p.display_path(adt.name));
                let packed = adt.repr.pack;
                if let Some(n) = packed {
                    let _ = writeln!(out, "#pragma pack(push, {n})");
                }
                let layout = c_layout(p, t);
                if adt.is_enum {
                    match layout {
                        Some(l) => {
                            let variants: Vec<Vec<CTy>> =
                                adt.variants.iter().map(|v| v.fields.iter().map(|f| cty(&p.tys, f.ty)).collect()).collect();
                            emit_enum_decl(p, out, &format!("struct A{an}"), t, &variants, &l);
                        }
                        None => {
                            let fields = |v: &Variant| -> String {
                                v.fields.iter().enumerate().map(|(i, f)| format!("{} f{i}; ", ctype(&cty(&p.tys, f.ty)))).collect()
                            };
                            let _ = write!(out, "struct A{an} {{ uint32_t tag; ");
                            if adt.variants.iter().any(|v| !v.fields.is_empty()) {
                                out.push_str("union { ");
                                for (vi, v) in adt.variants.iter().enumerate() {
                                    if !v.fields.is_empty() {
                                        let _ = write!(out, "struct {{ {}}} v{vi}; ", fields(v));
                                    }
                                }
                                out.push_str("} u; ");
                            }
                            out.push_str("};\n");
                        }
                    }
                } else {
                    match layout {
                        Some(l) => {
                            let v = &adt.variants[0];
                            if v.fields.is_empty() && l.align > 1 {
                                let _ = writeln!(out, "struct A{an} {{ _Alignas({}) uint8_t _z[0]; }};", l.align);
                            } else if v.fields.is_empty() {
                                let _ = writeln!(out, "struct A{an} {{ }};");
                            } else {
                                let fields: Vec<(String, Layout, u64)> = v
                                    .fields
                                    .iter()
                                    .enumerate()
                                    .map(|(i, f)| {
                                        let ft = cty(&p.tys, f.ty);
                                        (format!("{} f{i}", ctype(&ft)), field_layout(p, &ft), l.field_offsets[i])
                                    })
                                    .collect();
                                let _ = writeln!(out, "struct A{an} {{ {}}};", layout_members(&fields, Some(l.size), l.align));
                            }
                            layout_assert(out, &format!("A{an}"), &l);
                        }
                        None => {
                            let f: String = adt.variants[0]
                                .fields
                                .iter()
                                .enumerate()
                                .map(|(i, f)| format!("{} f{i}; ", ctype(&cty(&p.tys, f.ty))))
                                .collect();
                            let f = if f.is_empty() { "uint8_t unused; ".to_string() } else { f };
                            let _ = writeln!(out, "struct A{an} {{ {f}}};");
                        }
                    }
                }
                if packed.is_some() {
                    out.push_str("#pragma pack(pop)\n");
                }
            }
            _ => {}
        }
    }
    let mut emitted = HashSet::new();
    for t in &list {
        emit(p, t, &mut emitted, out);
    }
    out.push('\n');
}

/// The body of a glue fn that returns what written impl method `f`
/// returns for `args` (the method's C arguments, comma separated),
/// called through the fn table with the large-return out pointer
/// when the method uses one (see `FnGen::call_value`).
fn written_glue_call(p: &Program, slots: &[u32], f: LocalDefId, args: &str, types: &mut Vec<CTy>) -> String {
    let callee = glue_callee(p, slots, f, types);
    if ret_is_large(p, f) {
        let ret = ctype(&cty(&p.tys, p.fn_info(f).ret));
        let pre = if args.is_empty() { String::new() } else { format!(", {args}") };
        format!("  {ret} r; {callee}(&r{pre});\n  return r;\n")
    } else {
        format!("  return {callee}({args});\n")
    }
}

/// `(CAST lust_fns[SLOT])`, the callee text for glue that calls written fn `f`. Adds the C
/// types of `f`'s signature to `types` (see `GlueSet::types`): the glue can be a static copy
/// in a unit whose own fns never name them.
fn glue_callee(p: &Program, slots: &[u32], f: LocalDefId, types: &mut Vec<CTy>) -> String {
    let info = p.fn_info(f);
    types.push(cty(&p.tys, info.ret));
    types.extend(info.params.iter().map(|&t| cty(&p.tys, t)));
    format!("({}lust_fns[{}])", fn_ptr_cast(p, f), slots[f.0 as usize])
}

/// Generates the prototype and definition of glue `g` for `t`. Pushes the glue keys the
/// definition calls to `more` and the extra C types it names to `types`.
#[allow(clippy::too_many_arguments)]
/// The drop glue step under panic=unwind (`lust_unw_dstep`): after a
/// call that may panic, the first exception moves into the glue's `ex`.
const UNW_DSTEP: &str = "  if (lust_unw_pending) lust_unw_dstep(&ex, &u);\n";

fn glue_def(
    p: &Program,
    slots: &[u32],
    g: &Glue,
    t: &CTy,
    protos: &mut String,
    defs: &mut String,
    more: &mut Vec<(Glue, CTy)>,
    types: &mut Vec<CTy>,
) {
    if matches!(g, Glue::Default | Glue::Clone) && c_size_align(p, t).0 == 0 && ret_by_out(p, t) {
        let (mut proto, mut def) = (String::new(), String::new());
        glue_def_value(p, slots, g, t, &mut proto, &mut def, more, types);
        zst_out_glue(g, t, &def, protos, defs);
        return;
    }
    glue_def_value(p, slots, g, t, protos, defs, more, types);
}

/// The `default` or `clone` glue of a zero-sized type that tcc cannot
/// return by value (`ret_by_out`), from its by-value definition `def`:
/// a function that writes through an out-pointer (each `return X;`
/// becomes `*o = X;`), and a macro of the glue's name, so every call
/// stays an expression.
fn zst_out_glue(g: &Glue, t: &CTy, def: &str, protos: &mut String, defs: &mut String) {
    let (m, ct) = (mangle(t), ctype(t));
    let (name, head, params, call) = match g {
        Glue::Default => (format!("default_{m}"), format!("{ct} default_{m}(void) {{"), format!("{ct} *o"), "&r_".to_string()),
        _ => (format!("clone_{m}"), format!("{ct} clone_{m}({ct} *p) {{"), format!("{ct} *o, {ct} *p"), "&r_, (p)".to_string()),
    };
    let arg = if matches!(g, Glue::Default) { "" } else { "p" };
    let _ = writeln!(protos, "void {name}_o({params});\n#define {name}({arg}) ({{ {ct} r_; {name}_o({call}); r_; }})");
    let mut body = def.replacen(&head, &format!("void {name}_o({params}) {{"), 1);
    while let Some(i) = body.find("return ") {
        let end = i + body[i..].find(';').unwrap_or(body.len() - i);
        let e = body[i + "return ".len()..end].to_string();
        body.replace_range(i..=end, &format!("{{ *o = {e}; return; }}"));
    }
    defs.push_str(&body);
}

/// `glue_def` for every glue whose value C returns directly.
#[allow(clippy::too_many_arguments)]
fn glue_def_value(
    p: &Program,
    slots: &[u32],
    g: &Glue,
    t: &CTy,
    protos: &mut String,
    defs: &mut String,
    more: &mut Vec<(Glue, CTy)>,
    types: &mut Vec<CTy>,
) {
    let m = mangle(t);
    let ct = ctype(t);
    let mut need = |g: Glue, t: &CTy| more.push((g, t.clone()));
    let mut body = String::new();
    // Discriminant reads and the Option payload access for the enum
    // shaped glue arms below (unused strings for other shapes).
    let disc_p = disc_call(p, t, "p");
    let pf = variant_field(p, t, "(*p)", 1, 0);
    // The `clonefrom` glue handles every shape itself (an owning
    // fat pointer takes the default body there).
    if matches!(g, Glue::CloneFrom) {
        clonefrom::clonefrom_glue(p, slots, t, protos, defs, &mut need, types);
        return;
    }
    // Owning fat pointers' glue (cgen/own.rs).
    if let CTy::Own(k, x) = t {
        own::own_glue_def(p, *g, *k, x, protos, defs, &mut need);
        return;
    }
    if let CTy::WeakDyn(arc) = t {
        own::weak_dyn_glue_def(*g, *arc, protos, defs);
        return;
    }
    if let (Glue::Drop, CTy::DynGuard(_) | CTy::DynLock(true)) = (g, t) {
        own::dyn_guard_drop(t, protos, defs);
        return;
    }
    // The sync types' glue (cgen/sync.rs).
    if let CTy::Sync(k, e) = t {
        sync::sync_glue_def(p, *g, *k, e, protos, defs, &mut need);
        return;
    }
    match g {
        Glue::CloneFrom => unreachable!("clonefrom glue returns above"),
        Glue::Drop => {
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            match t {
                CTy::String => body.push_str("  lust_string_drop(p);\n"),
                CTy::Hash(k, _) if hash::is_table(*k) => body.push_str(&hash::drop_body(p, t, &mut need)),
                CTy::Hash(k, _) if k.is_owning_iter() => body.push_str(&hash::iter_drop_body(p, t, &mut need)),
                // An occupied Entry dropped its key at `entry()`.
                CTy::Hash(crate::ty::hash::HashTy::Entry, a) => {
                    need(Glue::Drop, &a[0]);
                    let _ = writeln!(body, "  if (!p->slot) drop_{}(&p->key);", mangle(&a[0]));
                }
                CTy::Vec(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < p->len; i++) drop_{}(&(({}*)p->ptr)[i]);", mangle(e), ctype(e));
                    }
                    // An empty Vec never allocates; its pointer is the
                    // dangling aligned address, not a heap block. The
                    // zero-sized element form reports cap as usize::MAX,
                    // so that case is decided here, not at run time.
                    if c_layout(p, e).is_none_or(|l| l.size > 0) {
                        body.push_str("  if (p->cap) free(p->ptr);\n");
                    }
                }
                // Through the vtable: the drop entry (0 when none), then
                // the allocation by the size and align words.
                CTy::BoxDyn => {
                    body.push_str("  if (p->vt[0]) ((void (*)(void *))p->vt[0])(p->data);\n");
                    body.push_str(UNW_DSTEP);
                    body.push_str("  lust_dealloc(p->data, (uint64_t)(uintptr_t)p->vt[1], (uint64_t)(uintptr_t)p->vt[2]);\n");
                }
                CTy::RcDyn => {
                    // The two counts start the allocation (`RcI_T`).
                    let _ = writeln!(body, "  uint64_t *h = {};", own::counts(&CTy::Dyn, "(*p)"));
                    // The strong refs hold one implicit weak ref, as for `Rc<T>`.
                    let _ = writeln!(
                        body,
                        "  if (--h[0] == 0) {{ if (p->vt[0]) ((void (*)(void *))p->vt[0])(p->data); UNW_DSTEP if (--h[1] == 0) lust_dealloc((void *)h, {} + (uint64_t)(uintptr_t)p->vt[1], (uint64_t)(uintptr_t)p->vt[2]); }}",
                        own::counts_off(&CTy::Dyn, "(*p)")
                    );
                }
                CTy::Boxed(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  drop_{}(*p);", mangle(e));
                    }
                    let et = ctype(e);
                    let _ = writeln!(body, "  lust_dealloc((void*)*p, sizeof({et}), _Alignof({et}));");
                }
                CTy::BoxSlice(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < p->len; i++) drop_{}(&p->ptr[i]);", mangle(e));
                    }
                    // An empty boxed slice holds a dangling pointer.
                    let et = ctype(e);
                    let _ = writeln!(body, "  lust_dealloc((void*)p->ptr, p->len * sizeof({et}), _Alignof({et}));");
                }
                CTy::VecIter(e) => {
                    // What `next` has not moved out yet: `front..len`,
                    // in order, then the buffer (as `vec::IntoIter`).
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = p->front; i < p->len; i++) drop_{}(&(({}*)p->ptr)[i]);", mangle(e), ctype(e));
                    }
                    if c_layout(p, e).is_none_or(|l| l.size > 0) {
                        body.push_str("  if (p->cap) free(p->ptr);\n");
                    }
                }
                CTy::VecDrain(e) => {
                    // What `next` has not moved out yet drops in
                    // order, then the tail moves down to the drain
                    // start and the Vec takes its new length (as
                    // `vec::Drain`'s drop).
                    body.push_str("  lust_Vec *dv = (lust_Vec *)p->vec;\n");
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = p->front; i < p->back; i++) drop_{}(&(({}*)dv->ptr)[i]);", mangle(e), ctype(e));
                    }
                    if c_layout(p, e).is_none_or(|l| l.size > 0) {
                        let et = ctype(e);
                        let _ = writeln!(body, "  lust_memmove((({et}*)dv->ptr) + p->start, (({et}*)dv->ptr) + p->tail_start, p->tail_len * sizeof({et}));");
                    }
                    body.push_str("  dv->len = p->start + p->tail_len;\n");
                }
                CTy::StrDrain => {
                    // The bytes not yielded are removed: the tail
                    // moves down to the drain start.
                    body.push_str("  lust_String *dv = (lust_String *)p->vec;\n");
                    body.push_str("  lust_memmove(dv->ptr + p->start, dv->ptr + p->tail_start, p->tail_len);\n");
                    body.push_str("  dv->len = p->start + p->tail_len;\n");
                }
                CTy::Rc(e) => {
                    let it = format!("RcI_{}", mangle(e));
                    let inner = if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        format!("drop_{}(&(*p)->v); ", mangle(e))
                    } else {
                        String::new()
                    };
                    // The strong refs together hold one implicit weak ref
                    // (Rust's RcInner): the header outlives the value
                    // drop while any Weak remains.
                    let _ = writeln!(body, "  if (--(*p)->strong == 0) {{ {inner}if (--(*p)->weak == 0) lust_dealloc((void*)*p, sizeof({it}), _Alignof({it})); }}");
                }
                CTy::Weak(e) => {
                    let it = format!("RcI_{}", mangle(e));
                    let _ = writeln!(body, "  if (*p != ({it}*)~(uint64_t)0 && --(*p)->weak == 0) lust_dealloc((void*)*p, sizeof({it}), _Alignof({it}));");
                }
                CTy::RefCell(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  drop_{}(&p->f1);", mangle(e));
                    }
                }
                CTy::Cell(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  drop_{}(p);", mangle(e));
                    }
                }
                // A guard gives its borrow back: `Ref` counts down, a
                // `RefMut` (flag -1) counts back up to 0.
                CTy::Guard(_, m) => {
                    let _ = writeln!(body, "  (*p)->f0 {}= 1;", if *m { "+" } else { "-" });
                }
                CTy::Option(e) => {
                    need(Glue::Drop, e);
                    let _ = writeln!(body, "  if ({disc_p}) drop_{}(&{pf});", mangle(e));
                }
                CTy::Result(a, b) => {
                    if needs_drop_c(p, a) {
                        need(Glue::Drop, a);
                        let f0 = variant_field(p, t, "(*p)", 0, 0);
                        let _ = writeln!(body, "  if (!{disc_p}) drop_{}(&{f0});", mangle(a));
                    }
                    if needs_drop_c(p, b) {
                        need(Glue::Drop, b);
                        let f1 = variant_field(p, t, "(*p)", 1, 0);
                        let _ = writeln!(body, "  if ({disc_p}) drop_{}(&{f1});", mangle(b));
                    }
                }
                CTy::Tuple(es) => {
                    for (fi, ft) in es.iter().enumerate() {
                        if needs_drop_c(p, ft) {
                            need(Glue::Drop, ft);
                            let _ = writeln!(body, "  drop_{}(&p->f{fi});", mangle(ft));
                        }
                    }
                }
                CTy::Array(e, n) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < {n}; i++) drop_{}(&p->v[i]);", mangle(e));
                    }
                }
                // `array::IntoIter` (fx-array-iter): what `next` and
                // `next_back` have not moved out yet, `front..back` in
                // order, as core's drop runs `for _ in self {}`.
                CTy::ArrayIter(e, _) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = p->f1; i < p->f2; i++) drop_{}(&p->f0.v[i]);", mangle(e));
                    }
                }
                CTy::Adt(a) => {
                    // A user `Drop` impl runs before the fields drop
                    // (W-TRAITS-CORE through W-CGEN: the glue reads
                    // the instance from `Program::gx.drop_methods`).
                    if let Some(&drop_fn) = p.gx.drop_methods.get(a) {
                        // Glue has no error channel: a drop fn with an
                        // empty slot fails the C build instead.
                        if !has_generated_body(p, drop_fn) {
                            let _ = writeln!(body, "#error \"internal: drop glue calls a fn with no generated body\"");
                        }
                        let _ = writeln!(body, "  {}(p);", glue_callee(p, slots, drop_fn, types));
                        body.push_str(UNW_DSTEP);
                    }
                    let adt = p.adt(*a);
                    if adt.is_enum {
                        let _ = writeln!(body, "  switch ({disc_p}) {{");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            for (fi, f) in v.fields.iter().enumerate() {
                                let ft = cty(&p.tys, f.ty);
                                if needs_drop_c(p, &ft) {
                                    need(Glue::Drop, &ft);
                                    let _ = write!(body, " drop_{}(&p->u.v{vi}.f{fi});", mangle(&ft));
                                }
                            }
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n");
                    } else {
                        for (fi, f) in adt.variants[0].fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            if needs_drop_c(p, &ft) {
                                need(Glue::Drop, &ft);
                                let _ = writeln!(body, "  drop_{}(&p->f{fi});", mangle(&ft));
                            }
                        }
                    }
                }
                _ => {}
            }
            // panic=unwind: a panicking drop leaves the rest to drop as
            // cleanup, and the glue passes the exception on at its end.
            if p.unwind && body.contains('(') {
                let dstep = UNW_DSTEP.trim();
                body = unwind::wrap_calls(&body.replace("UNW_DSTEP ", UNW_DSTEP.trim_start()), dstep);
                body = format!("  lust_exc ex; int32_t u = 0;\n{body}  if (u) lust_unw_resume(&ex);\n");
            } else {
                body = body.replace(UNW_DSTEP, "").replace("UNW_DSTEP ", "");
            }
            let _ = writeln!(defs, "void drop_{m}({ct} *p) {{\n{body}}}\n");
        }
        Glue::Clone => {
            let _ = writeln!(protos, "{ct} clone_{m}({ct} *p);");
            // A field type with a written `Clone` impl clones through
            // that impl even when it is `Copy` (rustc's derived bodies
            // call `Clone::clone` on each field).
            let written = |t: &CTy| matches!(t, CTy::Adt(a) if p.gx.glue_methods.contains_key(&(*a, p.gx.lang.clone)));
            let clone_of = |t: &CTy, e: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                if is_copy_c(p, t) && !written(t) {
                    e.to_string()
                } else {
                    need(Glue::Clone, t);
                    format!("clone_{}(&{e})", mangle(t))
                }
            };
            if let CTy::Adt(a) = t
                && let Some(&f) = p.gx.glue_methods.get(&(*a, p.gx.lang.clone))
            {
                let call = written_glue_call(p, slots, f, "p", types);
                let _ = writeln!(defs, "{ct} clone_{m}({ct} *p) {{\n{call}}}\n");
                return;
            }
            match t {
                CTy::String => body.push_str("  return lust_string_clone(p);\n"),
                CTy::Hash(k, _) if hash::is_table(*k) => body.push_str(&hash::clone_body(p, t, &mut need)),
                CTy::Boxed(e) => {
                    let et = ctype(e);
                    let c = clone_of(e, "(**p)", &mut need);
                    let _ = writeln!(body, "  {et} *r = ({et}*)lust_alloc(sizeof({et}), _Alignof({et})); *r = {c}; return r;");
                }
                CTy::RcDyn => {
                    let _ = writeln!(body, "  {}[0]++; return *p;", own::counts(&CTy::Dyn, "(*p)"));
                }
                CTy::BoxSlice(e) => {
                    let et = ctype(e);
                    let c = clone_of(e, "p->ptr[i]", &mut need);
                    let _ = writeln!(
                        body,
                        "  {ct} r; r.len = p->len; r.ptr = ({et}*)lust_alloc(p->len * sizeof({et}), _Alignof({et}));\n  for (uint64_t i = 0; i < p->len; i++) r.ptr[i] = {c};\n  return r;"
                    );
                }
                CTy::Rc(_) => {
                    body.push_str("  (*p)->strong++; return *p;\n");
                }
                CTy::Weak(e) => {
                    let it = format!("RcI_{}", mangle(e));
                    let _ = writeln!(body, "  if (*p != ({it}*)~(uint64_t)0) (*p)->weak++; return *p;");
                }
                // `Cell<T>: Clone` needs `T: Copy`: a copy of the value.
                CTy::Cell(_) => body.push_str("  return *p;\n"),
                // `RefCell::clone` borrows (and panics as `borrow` does).
                CTy::RefCell(e) => {
                    let c = clone_of(e, "p->f1", &mut need);
                    let _ = writeln!(
                        body,
                        "  if (p->f0 < 0) lust_panic_cstr_dyn(\"RefCell already mutably borrowed\", 0);\n  {ct} r; r.f0 = 0; r.f1 = {c}; return r;"
                    );
                }
                CTy::Option(e) => {
                    let c = clone_of(e, &pf, &mut need);
                    let rf = variant_field(p, t, "r", 1, 0);
                    let _ = writeln!(body, "  {ct} r = *p;\n  if ({disc_p}) {rf} = {c};\n  return r;");
                }
                CTy::Result(a, b) => {
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if !is_copy_c(p, a) {
                        let c = clone_of(a, &variant_field(p, t, "(*p)", 0, 0), &mut need);
                        let rf = variant_field(p, t, "r", 0, 0);
                        let _ = writeln!(body, "  if (!{disc_p}) {rf} = {c};");
                    }
                    if !is_copy_c(p, b) {
                        let c = clone_of(b, &variant_field(p, t, "(*p)", 1, 0), &mut need);
                        let rf = variant_field(p, t, "r", 1, 0);
                        let _ = writeln!(body, "  if ({disc_p}) {rf} = {c};");
                    }
                    body.push_str("  return r;\n");
                }
                CTy::Tuple(es) => {
                    let _ = writeln!(body, "  {ct} r = *p;");
                    for (fi, ft) in es.iter().enumerate() {
                        if !is_copy_c(p, ft) {
                            let c = clone_of(ft, &format!("p->f{fi}"), &mut need);
                            let _ = writeln!(body, "  r.f{fi} = {c};");
                        }
                    }
                    body.push_str("  return r;\n");
                }
                CTy::Array(e, n) => {
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if !is_copy_c(p, e) {
                        let c = clone_of(e, "p->v[i]", &mut need);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < {n}; i++) r.v[i] = {c};");
                    }
                    body.push_str("  return r;\n");
                }
                // `array::IntoIter`'s Clone clones only the elements
                // it still owns; the moved-out slots keep stale bytes
                // the clone's own range never drops.
                CTy::ArrayIter(e, _) => {
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if !is_copy_c(p, e) || written(e) {
                        let c = clone_of(e, "p->f0.v[i]", &mut need);
                        let _ = writeln!(body, "  for (uint64_t i = p->f1; i < p->f2; i++) r.f0.v[i] = {c};");
                    }
                    body.push_str("  return r;\n");
                }
                CTy::Vec(e) => {
                    let et = ctype(e);
                    let _ = writeln!(body, "  lust_Vec r = lust_vec_with_capacity(p->len, sizeof({et}), _Alignof({et}));");
                    let c = clone_of(e, &format!("(({et}*)p->ptr)[i]"), &mut need);
                    let _ =
                        writeln!(body, "  for (uint64_t i = 0; i < p->len; i++) (({et}*)r.ptr)[i] = {c};\n  r.len = p->len;\n  return r;");
                }
                CTy::Adt(a) => {
                    let adt = p.adt(*a);
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if adt.is_enum {
                        let _ = writeln!(body, "  switch ({disc_p}) {{");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            for (fi, f) in v.fields.iter().enumerate() {
                                let ft = cty(&p.tys, f.ty);
                                if !is_copy_c(p, &ft) {
                                    let c = clone_of(&ft, &format!("p->u.v{vi}.f{fi}"), &mut need);
                                    let _ = write!(body, " r.u.v{vi}.f{fi} = {c};");
                                }
                            }
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n");
                    } else {
                        for (fi, f) in adt.variants[0].fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            if !is_copy_c(p, &ft) {
                                let c = clone_of(&ft, &format!("p->f{fi}"), &mut need);
                                let _ = writeln!(body, "  r.f{fi} = {c};");
                            }
                        }
                    }
                    body.push_str("  return r;\n");
                }
                _ => body.push_str("  return *p;\n"),
            }
            let _ = writeln!(defs, "{ct} clone_{m}({ct} *p) {{\n{body}}}\n");
        }
        Glue::Eq => {
            let _ = writeln!(protos, "uint8_t eq_{m}({ct} *a, {ct} *b);");
            if let CTy::Adt(adt_id) = t
                && let Some(&f) = p.gx.glue_methods.get(&(*adt_id, p.gx.lang.partial_eq))
            {
                let call = written_glue_call(p, slots, f, "a, b", types);
                let _ = writeln!(defs, "uint8_t eq_{m}({ct} *a, {ct} *b) {{\n{call}}}\n");
                return;
            }
            // An unsized newtype's `&self` is its fat value (W-SHIM).
            if let CTy::Unsized(adt_id, _) = t {
                let f = p.gx.glue_methods.get(&(*adt_id, p.gx.lang.partial_eq)).copied().expect("an unsized newtype compared by == has a written PartialEq");
                let call = written_glue_call(p, slots, f, "*a, *b", types);
                let _ = writeln!(defs, "uint8_t eq_{m}({ct} *a, {ct} *b) {{\n{call}}}\n");
                return;
            }
            let eq_of = |t: &CTy, x: &str, y: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                match t {
                    CTy::Unit | CTy::AccessError => "1".into(),
                    CTy::Int(i) if is128(*i) => format!("(({x}).lo == ({y}).lo && ({x}).hi == ({y}).hi)"),
                    CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) | CTy::FnPtr(..) | CTy::ExitCode | CTy::Ptr(_) => format!("({x} == {y})"),
                    _ => {
                        need(Glue::Eq, t);
                        format!("eq_{}(&{x}, &{y})", mangle(t))
                    }
                }
            };
            let cow = (fmt::cow_view(p, t, "a", "va"), fmt::cow_view(p, t, "b", "vb"));
            match t {
                CTy::ExitCode => body.push_str("  return *a == *b;\n"),
                CTy::AccessError => body.push_str("  return 1;\n"),
                // HashMap and HashSet (W-STD-B, cgen/hash.rs).
                CTy::Hash(k, _) if hash::is_table(*k) => body.push_str(&hash::table_eq_body(p, t, &mut need)),
                // `Cow<B>` compares the `B` views (W-STD-B).
                _ if cow.0.is_some() => {
                    let ((rb, da), (_, db)) = (cow.0.clone().unwrap(), cow.1.clone().unwrap());
                    let c = eq_of(&rb, "va", "vb", &mut need);
                    let _ = writeln!(body, "  {da}\n  {db}\n  return {c};");
                }
                CTy::String => body.push_str("  return lust_str_eq(lust_string_as_str(a), lust_string_as_str(b));\n"),
                CTy::Ref(inner) if **inner == CTy::Str => body.push_str("  return lust_str_eq(*a, *b);\n"),
                CTy::Option(e) => {
                    let (af, bf) = (variant_field(p, t, "(*a)", 1, 0), variant_field(p, t, "(*b)", 1, 0));
                    let c = eq_of(e, &af, &bf, &mut need);
                    let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                    let _ = writeln!(body, "  return {da} == {db} && (!{da} || {c});");
                }
                CTy::Result(x, y) => {
                    let ca = eq_of(x, &variant_field(p, t, "(*a)", 0, 0), &variant_field(p, t, "(*b)", 0, 0), &mut need);
                    let cb = eq_of(y, &variant_field(p, t, "(*a)", 1, 0), &variant_field(p, t, "(*b)", 1, 0), &mut need);
                    let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                    let _ = writeln!(body, "  return {da} == {db} && ({da} ? {cb} : {ca});");
                }
                CTy::Tuple(es) => {
                    for (fi, ft) in es.iter().enumerate() {
                        let c = eq_of(ft, &format!("a->f{fi}"), &format!("b->f{fi}"), &mut need);
                        let _ = writeln!(body, "  if (!{c}) return 0;");
                    }
                    body.push_str("  return 1;\n");
                }
                CTy::Array(e, n) => {
                    let c = eq_of(e, "a->v[i]", "b->v[i]", &mut need);
                    let _ = writeln!(body, "  for (uint64_t i = 0; i < {n}; i++) if (!{c}) return 0;\n  return 1;");
                }
                CTy::Slice(e) | CTy::BoxSlice(e) => {
                    let c = eq_of(e, "a->ptr[i]", "b->ptr[i]", &mut need);
                    let _ = writeln!(
                        body,
                        "  if (a->len != b->len) return 0;\n  for (uint64_t i = 0; i < a->len; i++) if (!{c}) return 0;\n  return 1;"
                    );
                }
                CTy::Ref(inner) | CTy::Boxed(inner) => {
                    let e = eq_of(inner, "(**a)", "(**b)", &mut need);
                    let _ = writeln!(body, "  return {e};");
                }
                CTy::Rc(inner) => {
                    let e = eq_of(inner, "(*a)->v", "(*b)->v", &mut need);
                    let _ = writeln!(body, "  return {e};");
                }
                CTy::Vec(e) => {
                    let et = ctype(e);
                    let c = eq_of(e, &format!("(({et}*)a->ptr)[i]"), &format!("(({et}*)b->ptr)[i]"), &mut need);
                    let _ = writeln!(
                        body,
                        "  if (a->len != b->len) return 0;\n  for (uint64_t i = 0; i < a->len; i++) if (!{c}) return 0;\n  return 1;"
                    );
                }
                CTy::Adt(a) => {
                    let adt = p.adt(*a);
                    if adt.is_enum {
                        let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                        let _ = writeln!(body, "  if ({da} != {db}) return 0;\n  switch ({da}) {{");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            for (fi, f) in v.fields.iter().enumerate() {
                                let ft = cty(&p.tys, f.ty);
                                let c = eq_of(&ft, &format!("a->u.v{vi}.f{fi}"), &format!("b->u.v{vi}.f{fi}"), &mut need);
                                let _ = write!(body, " if (!{c}) return 0;");
                            }
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n  return 1;\n");
                    } else {
                        for (fi, f) in adt.variants[0].fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            let c = eq_of(&ft, &format!("a->f{fi}"), &format!("b->f{fi}"), &mut need);
                            let _ = writeln!(body, "  if (!{c}) return 0;");
                        }
                        body.push_str("  return 1;\n");
                    }
                }
                _ => body.push_str("  return *a == *b;\n"),
            }
            let _ = writeln!(defs, "uint8_t eq_{m}({ct} *a, {ct} *b) {{\n{body}}}\n");
        }
        Glue::Cmp | Glue::PCmp => {
            // `PCmp` is this same body with `PartialOrd` order:
            // a written `partial_cmp` from `pcmp_methods` (an `Ord`
            // impl may also exist) and `PCmp` field compares, except
            // where a derive rule below sends fields to `Ord`.
            let partial = *g == Glue::PCmp;
            let pre = if partial { "pcmp" } else { "cmp" };
            let _ = writeln!(protos, "int8_t {pre}_{m}({ct} *a, {ct} *b);");
            // A written `partial_cmp` (see `glue_methods`): its
            // `Option<Ordering>` becomes the glue's code.
            let written = if partial { &p.gx.pcmp_methods } else { &p.gx.glue_methods };
            if let CTy::Adt(adt_id) | CTy::Unsized(adt_id, _) = t
                && let Some(&f) = written.get(&(*adt_id, p.gx.lang.partial_ord))
                && let Some(ord) = p.tys.local_adt_of(crate::check::generics::ordering_def())
            {
                // An unsized newtype's `&self` is its fat value (W-SHIM).
                let (a, b) = if matches!(t, CTy::Unsized(..)) { ("*a", "*b") } else { ("a", "b") };
                let opt = CTy::Option(Box::new(CTy::Adt(ord)));
                let callee = glue_callee(p, slots, f, types);
                let ot = ctype(&opt);
                if ret_is_large(p, f) {
                    let _ = writeln!(body, "  {ot} r; {callee}(&r, {a}, {b});");
                } else {
                    let _ = writeln!(body, "  {ot} r = {callee}({a}, {b});");
                }
                let some = disc_call(p, &opt, "(&r)");
                let pay = variant_field(p, &opt, "r", 1, 0);
                let ord_ct = ctype(&CTy::Adt(ord));
                let idx = disc_call(p, &CTy::Adt(ord), "(&o)");
                let _ = writeln!(body, "  if (!{some}) return 2;\n  {ord_ct} o = {pay};\n  return (int8_t)((int)({idx}) - 1);");
                let _ = writeln!(defs, "int8_t {pre}_{m}({ct} *a, {ct} *b) {{\n{body}}}\n");
                return;
            }
            // rustc's derived `partial_cmp` on a non-generic type
            // that also derives `Ord` is `Some(self.cmp(other))`
            // (collect.rs `glue_cmp_mode`): the `PCmp` glue of such
            // a type is its `Cmp` glue, field `Ord` compares included.
            if partial
                && let CTy::Adt(adt_id) = t
                && p.adt(*adt_id).derives.partial_ord
                && p.adt(*adt_id).derives.ord
                && !p.gx.adt_instance_of.get(adt_id.0 as usize).is_some_and(|o| o.is_some())
                && !p.gx.adt_generics.get(adt_id.0 as usize).is_some_and(|g| !g.params.is_empty())
            {
                need(Glue::Cmp, t);
                let _ = writeln!(defs, "int8_t pcmp_{m}({ct} *a, {ct} *b) {{\n  return cmp_{m}(a, b);\n}}\n");
                return;
            }
            // One field pair `x`, `y` (C lvalues): scalars inline, the
            // rest through their own glue.
            let cmp_of = |t: &CTy, x: &str, y: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                match t {
                    CTy::Unit => "0".into(),
                    CTy::Int(i) if is128(*i) => {
                        let f = int_fn(*i);
                        format!("((int8_t)((lust_{f}_cmp({x}, {y}) > 0) - (lust_{f}_cmp({x}, {y}) < 0)))")
                    }
                    CTy::Bool | CTy::Char | CTy::Int(_) => format!("((int8_t)(({x}) < ({y}) ? -1 : ({x}) > ({y})))"),
                    // Raw pointers order by address (w-cinterop).
                    CTy::Ptr(_) => format!("((int8_t)(((uintptr_t)({x})) < ((uintptr_t)({y})) ? -1 : ((uintptr_t)({x})) > ((uintptr_t)({y}))))"),
                    CTy::Float(_) => format!("((int8_t)(({x}) < ({y}) ? -1 : ({x}) > ({y}) ? 1 : ({x}) == ({y}) ? 0 : 2))"),
                    _ => {
                        need(if partial { Glue::PCmp } else { Glue::Cmp }, t);
                        format!("{pre}_{}(&{x}, &{y})", mangle(t))
                    }
                }
            };
            // Elements in order; the first one that is not equal (or
            // is unordered) decides. `len` compares last, as slices do.
            let seq = |e: &CTy, x: &str, y: &str, n: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                let c = cmp_of(e, x, y, need);
                format!("  for (uint64_t i = 0; i < {n}; i++) {{ int8_t c = {c}; if (c) return c; }}\n")
            };
            let cow = (fmt::cow_view(p, t, "a", "va"), fmt::cow_view(p, t, "b", "vb"));
            match t {
                // `Cow<B>` orders the `B` views (W-STD-B).
                _ if cow.0.is_some() => {
                    let ((rb, da), (_, db)) = (cow.0.clone().unwrap(), cow.1.clone().unwrap());
                    let c = cmp_of(&rb, "va", "vb", &mut need);
                    let _ = writeln!(body, "  {da}\n  {db}\n  return {c};");
                }
                CTy::String => body.push_str("  int c = lust_str_cmp(lust_string_as_str(a), lust_string_as_str(b));\n  return c < 0 ? -1 : c > 0;\n"),
                CTy::Ref(inner) if **inner == CTy::Str => body.push_str("  int c = lust_str_cmp(*a, *b);\n  return c < 0 ? -1 : c > 0;\n"),
                CTy::Option(e) => {
                    let (af, bf) = (variant_field(p, t, "(*a)", 1, 0), variant_field(p, t, "(*b)", 1, 0));
                    let c = cmp_of(e, &af, &bf, &mut need);
                    let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                    let _ = writeln!(body, "  if ({da} != {db}) return {da} < {db} ? -1 : 1;\n  if (!{da}) return 0;\n  return {c};");
                }
                CTy::Result(x, y) => {
                    let ca = cmp_of(x, &variant_field(p, t, "(*a)", 0, 0), &variant_field(p, t, "(*b)", 0, 0), &mut need);
                    let cb = cmp_of(y, &variant_field(p, t, "(*a)", 1, 0), &variant_field(p, t, "(*b)", 1, 0), &mut need);
                    let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                    let _ = writeln!(body, "  if ({da} != {db}) return {da} < {db} ? -1 : 1;\n  return {da} ? {cb} : {ca};");
                }
                CTy::Tuple(es) => {
                    body.push_str("  int8_t c;\n");
                    for (fi, ft) in es.iter().enumerate() {
                        let c = cmp_of(ft, &format!("a->f{fi}"), &format!("b->f{fi}"), &mut need);
                        let _ = writeln!(body, "  c = {c}; if (c) return c;");
                    }
                    body.push_str("  return 0;\n");
                }
                CTy::Array(e, n) => {
                    body.push_str(&seq(e, "a->v[i]", "b->v[i]", &n.to_string(), &mut need));
                    body.push_str("  return 0;\n");
                }
                CTy::Slice(e) => {
                    body.push_str("  uint64_t n = a->len < b->len ? a->len : b->len;\n");
                    body.push_str(&seq(e, "a->ptr[i]", "b->ptr[i]", "n", &mut need));
                    body.push_str("  return a->len < b->len ? -1 : a->len > b->len;\n");
                }
                CTy::Vec(e) => {
                    let et = ctype(e);
                    body.push_str("  uint64_t n = a->len < b->len ? a->len : b->len;\n");
                    body.push_str(&seq(e, &format!("(({et}*)a->ptr)[i]"), &format!("(({et}*)b->ptr)[i]"), "n", &mut need));
                    body.push_str("  return a->len < b->len ? -1 : a->len > b->len;\n");
                }
                CTy::Ref(inner) | CTy::Boxed(inner) => {
                    let c = cmp_of(inner, "(**a)", "(**b)", &mut need);
                    let _ = writeln!(body, "  return {c};");
                }
                CTy::Rc(inner) => {
                    let c = cmp_of(inner, "(*a)->v", "(*b)->v", &mut need);
                    let _ = writeln!(body, "  return {c};");
                }
                CTy::Adt(adt_id) => {
                    let adt = p.adt(*adt_id);
                    let fields_cmp = |body: &mut String, v: &Variant, pre: &str, need: &mut dyn FnMut(Glue, &CTy)| {
                        for (fi, f) in v.fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            let c = cmp_of(&ft, &format!("a->{pre}f{fi}"), &format!("b->{pre}f{fi}"), need);
                            let _ = write!(body, " c = {c}; if (c) return c;");
                        }
                    };
                    body.push_str("  int8_t c;\n");
                    if adt.is_enum {
                        // Variants order by discriminant value, then
                        // fields (derived `PartialOrd`). `rk` maps a
                        // variant index to its rank when the values
                        // are not increasing in variant order.
                        let discs: Vec<i128> = adt.variants.iter().map(|v| v.disc).collect();
                        let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                        if discs.windows(2).all(|w| w[0] < w[1]) {
                            let _ = writeln!(body, "  if ({da} != {db}) return {da} < {db} ? -1 : 1;");
                        } else {
                            let mut order: Vec<usize> = (0..discs.len()).collect();
                            order.sort_by_key(|&i| discs[i]);
                            let mut rank = vec![0usize; discs.len()];
                            for (r, &i) in order.iter().enumerate() {
                                rank[i] = r;
                            }
                            let list: Vec<String> = rank.iter().map(|r| r.to_string()).collect();
                            let _ = writeln!(body, "  static const uint32_t rk[] = {{ {} }};", list.join(", "));
                            let _ = writeln!(body, "  if ({da} != {db}) return rk[{da}] < rk[{db}] ? -1 : 1;");
                        }
                        let _ = writeln!(body, "  switch ({da}) {{");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            fields_cmp(&mut body, v, &format!("u.v{vi}."), &mut need);
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n  return 0;\n");
                    } else {
                        fields_cmp(&mut body, &adt.variants[0], "", &mut need);
                        body.push_str("\n  return 0;\n");
                    }
                }
                _ => {
                    let c = cmp_of(t, "(*a)", "(*b)", &mut need);
                    let _ = writeln!(body, "  return {c};");
                }
            }
            let _ = writeln!(defs, "int8_t {pre}_{m}({ct} *a, {ct} *b) {{\n{body}}}\n");
        }
        Glue::Default => {
            let _ = writeln!(protos, "{ct} default_{m}(void);");
            if let CTy::Adt(a) = t
                && let Some(&f) = p.gx.glue_methods.get(&(*a, p.gx.lang.default))
            {
                let call = written_glue_call(p, slots, f, "", types);
                let _ = writeln!(defs, "{ct} default_{m}(void) {{\n{call}}}\n");
                return;
            }
            let def_of = |t: &CTy, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                match t {
                    CTy::Unit | CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Float(_) => zero_lit(p, t),
                    _ => {
                        need(Glue::Default, t);
                        format!("default_{}()", mangle(t))
                    }
                }
            };
            match t {
                CTy::Hash(..) => body.push_str(&hash::default_body(p, t, &mut need)),
                CTy::String => body.push_str("  return lust_string_new();\n"),
                CTy::Vec(e) => {
                    let et = ctype(e);
                    let _ = writeln!(body, "  return lust_vec_with_capacity(0, sizeof({et}), _Alignof({et}));");
                }
                CTy::Option(_) => {
                    let _ = writeln!(body, "  return {};", variant_lit(p, t, 0, &[]));
                }
                CTy::Ref(inner) if **inner == CTy::Str => body.push_str("  return ((lust_str){(uint8_t*)\"\", 0});\n"),
                // An empty slice view, or alloc's empty `Box<[T]>`:
                // a dangling aligned pointer at length 0 (the drop
                // glue frees nothing at size 0).
                CTy::Slice(e) | CTy::BoxSlice(e) => {
                    let et = ctype(e);
                    let _ = writeln!(body, "  {ct} r; r.ptr = ({et}*)(uintptr_t)_Alignof({et}); r.len = 0;\n  return r;");
                }
                CTy::Tuple(es) => {
                    let vals: Vec<String> = es.iter().enumerate().map(|(i, e)| format!(".f{i} = {}", def_of(e, &mut need))).collect();
                    let _ = writeln!(body, "  return (({ct}){{ {} }});", vals.join(", "));
                }
                CTy::Array(e, n) => {
                    if *n == 0 {
                        let _ = writeln!(body, "  return {};", zero_lit(p, t));
                    } else {
                        let d = def_of(e, &mut need);
                        let _ = writeln!(body, "  {ct} r;\n  for (uint64_t i = 0; i < {n}; i++) r.v[i] = {d};\n  return r;");
                    }
                }
                CTy::Boxed(e) => {
                    let et = ctype(e);
                    let d = def_of(e, &mut need);
                    let _ = writeln!(body, "  {et} *r = ({et}*)lust_alloc(sizeof({et}), _Alignof({et})); *r = {d};\n  return r;");
                }
                // An unborrowed RefCell around `T::default()`; a Cell is
                // its value in C (W-STD-B).
                CTy::RefCell(e) => {
                    let d = def_of(e, &mut need);
                    let _ = writeln!(body, "  {ct} r; r.f0 = 0; r.f1 = {d};\n  return r;");
                }
                CTy::Cell(e) => {
                    let _ = writeln!(body, "  return {};", def_of(e, &mut need));
                }
                CTy::Rc(e) => {
                    // The header as `Rc::new` builds it: one implicit weak ref.
                    let it = format!("RcI_{}", mangle(e));
                    let d = def_of(e, &mut need);
                    let _ = writeln!(body, "  {it} *r = ({it}*)lust_alloc(sizeof({it}), _Alignof({it})); r->strong = 1; r->weak = 1; r->v = {d};\n  return r;");
                }
                // `Cow<B>` defaults to `Owned(Owned::default())`.
                CTy::Adt(adt_id) if p.gx.adt_instance_of.get(adt_id.0 as usize).copied().flatten().is_some_and(|(d, _)| d == crate::check::generics::cow_def()) => {
                    let owned = cty(&p.tys, p.adt(*adt_id).variants[1].fields[0].ty);
                    let d = def_of(&owned, &mut need);
                    let _ = writeln!(body, "  return {};", variant_lit(p, t, 1, &[d]));
                }
                CTy::Adt(adt_id) => {
                    let adt = p.adt(*adt_id);
                    if adt.is_enum {
                        let vi = adt.derives.default_variant.unwrap_or(0) as usize;
                        let _ = writeln!(body, "  return {};", variant_lit(p, t, vi, &[]));
                    } else if adt.variants[0].fields.is_empty() {
                        let _ = writeln!(body, "  return {};", zero_lit(p, t));
                    } else {
                        let vals: Vec<String> = adt.variants[0]
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, f)| format!(".f{i} = {}", def_of(&cty(&p.tys, f.ty), &mut need)))
                            .collect();
                        let _ = writeln!(body, "  return (({ct}){{ {} }});", vals.join(", "));
                    }
                }
                _ => {
                    let _ = writeln!(body, "  return {};", def_of(t, &mut need));
                }
            }
            let _ = writeln!(defs, "{ct} default_{m}(void) {{\n{body}}}\n");
        }
        Glue::TlsInit | Glue::TlsDtor => tls_glue(p, g, t, protos, defs, &mut need),
        Glue::Debug => {
            let _ = writeln!(protos, "int dbg_{m}(lust_Formatter *f, {ct} *p);");
            let body = fmt::debug_glue_body(p, t, slots, &mut need, types);
            let _ = writeln!(defs, "int dbg_{m}(lust_Formatter *f, {ct} *p) {{\n{body}}}\n");
        }
        Glue::Display => {
            let _ = writeln!(protos, "int disp_{m}(lust_Formatter *f, {ct} *p);");
            let body = fmt::display_glue_body(p, t, slots, &mut need, types);
            let _ = writeln!(defs, "int disp_{m}(lust_Formatter *f, {ct} *p) {{\n{body}}}\n");
        }
        Glue::HashValue
        | Glue::HashKey
        | Glue::HashOf
        | Glue::HashEq
        | Glue::HashClone
        | Glue::HashKeyQ
        | Glue::HashEqQ
        | Glue::HashEqEntry
        | Glue::HashDrop
        | Glue::HashOne => {
            types.extend(hash::glue_hasher(p, g, t));
            // A glue body that hashes through `Hasher::write` (a
            // `str` or byte key) declares a `&[u8]` local; its slice
            // type is in no signature the unit otherwise needs.
            types.extend([CTy::Slice(Box::new(CTy::Int(crate::ty::IntTy::U8)))]);
            let (sig, body) = hash::glue(p, slots, g, t, &mut need);
            let _ = writeln!(protos, "{sig};");
            let _ = writeln!(defs, "{sig} {{\n{body}}}\n");
        }
    }
}

fn place_mentions(p: &Place, l: Local) -> bool {
    p.local == l || p.proj.iter().any(|x| matches!(x, Proj::Index(i) if *i == l))
}

/// Collects the place of `o` when it is a move.
fn operand_moves<'r>(o: &'r Operand, out: &mut Vec<&'r Place>) {
    if let Operand::Move(pl) = o {
        out.push(pl);
    }
}

fn parts_moves<'r>(parts: &'r [FmtPart], out: &mut Vec<&'r Place>) {
    for part in parts {
        if let FmtPart::Arg { value, .. } = part {
            operand_moves(value, out);
        }
    }
}

/// Calls `op` for every operand one rvalue reads and `pl` for
/// every place it reads without an operand (a borrow, a
/// discriminant, a slice or length base). The one exhaustive
/// rvalue scan in this file: the move scan and the mentions scan
/// both go through it, so a new `Rvalue` variant updates both.
fn visit_rvalue_reads<'r>(rv: &'r Rvalue, op: &mut impl FnMut(&'r Operand), pl: &mut impl FnMut(&'r Place)) {
    match rv {
        Rvalue::Use(o)
        | Rvalue::Un(_, o)
        | Rvalue::Cast(o, _)
        | Rvalue::ArrayRepeat(_, o, _)
        | Rvalue::Res(_, _, o)
        | Rvalue::MakeDyn { ptr: o, .. }
        | Rvalue::DynUpcast { ptr: o, .. }
        | Rvalue::DynMeta { ptr: o, .. }
        | Rvalue::DynData { ptr: o, .. } => op(o),
        Rvalue::Bin(_, a, b)
        | Rvalue::StrCmp(_, a, b)
        | Rvalue::StringAdd(a, b)
        | Rvalue::VecRepeat(_, a, b)
        | Rvalue::Eq { a, b, .. }
        | Rvalue::Cmp { a, b, .. } => {
            op(a);
            op(b);
        }
        Rvalue::Aggregate(_, _, ops) | Rvalue::VecLit(_, ops) | Rvalue::TupleAgg(_, ops) | Rvalue::ArrayAgg(_, ops) => {
            ops.iter().for_each(|o| op(o))
        }
        Rvalue::Opt(_, o) => {
            if let Some(o) = o {
                op(o);
            }
        }
        Rvalue::Format(parts) => parts.iter().for_each(|p| {
            if let FmtPart::Arg { value, .. } = p {
                op(value);
            }
        }),
        Rvalue::WriteFmt(dst, parts, _) => {
            op(dst);
            parts.iter().for_each(|p| {
                if let FmtPart::Arg { value, .. } = p {
                    op(value);
                }
            })
        }
        Rvalue::Ref(_, p) | Rvalue::Discriminant(p) | Rvalue::SliceOf(p) | Rvalue::LenOf(p) => pl(p),
        Rvalue::Subslice { base, lo, hi, .. } => {
            pl(base);
            op(lo);
            if let Some(h) = hi {
                op(h);
            }
        }
        Rvalue::StaticLoad(_) | Rvalue::StaticRef(_) | Rvalue::FnValue(..) => {}
    }
}

/// Collects the moved places among the operands of one rvalue.
fn rvalue_moves<'r>(rv: &'r Rvalue, out: &mut Vec<&'r Place>) {
    visit_rvalue_reads(rv, &mut |o| operand_moves(o, out), &mut |_| {});
}

fn operand_mentions(o: &Operand, l: Local) -> bool {
    matches!(o, Operand::Copy(p) | Operand::Move(p) if place_mentions(p, l))
}

fn rvalue_mentions(rv: &Rvalue, l: Local) -> bool {
    let (mut op_hit, mut pl_hit) = (false, false);
    visit_rvalue_reads(rv, &mut |o| op_hit |= operand_mentions(o, l), &mut |p| pl_hit |= place_mentions(p, l));
    op_hit || pl_hit
}

fn succ(t: &Terminator) -> Vec<Bb> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::If(_, a, b) => vec![*a, *b],
        Terminator::Switch(_, cases, other) => cases.iter().map(|c| c.1).chain(std::iter::once(*other)).collect(),
        Terminator::Call { next, unwind, .. } => std::iter::once(*next).chain(*unwind).collect(),
        Terminator::Return | Terminator::Unreachable | Terminator::Panic(_) => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Byte grouping: groups fill to the target, an over-target slot
    /// stands alone, empty input gives no groups, and every slot is
    /// in exactly one group, in order.
    #[test]
    fn group_fns_by_bytes_fills_to_target() {
        assert_eq!(group_fns_by_bytes(&[], 100), Vec::<std::ops::Range<usize>>::new());
        assert_eq!(group_fns_by_bytes(&[10, 20, 30, 40], 60), vec![0..3, 3..4]);
        assert_eq!(group_fns_by_bytes(&[10, 500, 10], 100), vec![0..1, 1..2, 2..3]);
        assert_eq!(group_fns_by_bytes(&[0, 0, 5], 4), vec![0..2, 2..3]);
        let sizes = [7usize; 5000];
        let groups = group_fns_by_bytes(&sizes, 1_000_000);
        assert_eq!(groups.len(), 2, "the 4096-slot cap splits a run of small slots");
        assert_eq!(groups[0], 0..4096);
    }

    /// `LUST_IMPL` groups leave the declaration header; `#else`
    /// branches, nested other conditionals, and undecidable groups
    /// stay. The runtime's own tables and bodies are impl-only, so
    /// the built header names none of them but keeps prototypes.
    #[test]
    fn strip_impl_blocks_keeps_decl_branches() {
        let src = "a\n#ifdef LUST_IMPL\nimpl\n#ifdef __APPLE__\nimpl2\n#else\nimpl3\n#endif\n#else\ndecl\n#endif\nb\n\
                   #ifndef LUST_IMPL\nnodef\n#endif\n#ifdef __x86_64__\narch\n#endif\n\
                   #if defined(LUST_IMPL) && defined(__linux__)\nguard\n#elif defined(LUST_IMPL)\nempty\n#endif\nc\n";
        assert_eq!(strip_impl_blocks(src), "a\ndecl\nb\nnodef\n#ifdef __x86_64__\narch\n#endif\nc\n");
        let decls = runtime_decls();
        assert!(decls.contains("void lust_rt_init(void)"), "prototypes stay");
        assert!(!decls.contains("lust_uni_alphabetic_ranges"), "impl-only Unicode tables go");
        assert!(!decls.contains("lust_alt_stack"), "impl-only bodies go");
        assert!(decls.len() < runtime_source(false).len() / 2, "the header shrinks: {} bytes", decls.len());
    }

    use crate::check::check_fn;
    use crate::check::collect;
    use crate::diag::{FileId, SourceMap, Span};
    use crate::intern::{Interner, Known};
    use crate::{lexer, parser};

    /// End to end over hand-built IR for the forms the front end does
    /// not produce yet (float values, fn pointer values and indirect
    /// calls, 128-bit literals): collect and lower a plain program,
    /// rewrite `main` by hand to use the new IR, generate all units,
    /// compile them with the system C compiler, run, and compare
    /// output. This is the verification for the float and fn pointer
    /// codegen until W-CORELANG wires the front end (L0602, L0641).
    #[test]
    fn float_and_fnptr_ir_runs() {
        let src = "fn add1(x: i64) -> i64 { x + 1 }\nfn main() { println!(\"{}\", add1(41)); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let main = program.main.unwrap();
        let add1 = program.fn_names[&interner.intern("add1")];
        let n = program.fns.len();
        let slots: Vec<u32> = (0..n as u32).collect();

        let mut outs: Vec<FnOut> = Vec::new();
        for i in 0..n {
            let fid = LocalDefId(i as u32);
            let (ck, errs) = check_fn(&program, fid);
            assert!(errs.is_empty(), "{errs:?}");
            let mut body = crate::lower::lower(&program, fid, ck);
            if fid == main {
                rewrite_main(&mut body, add1);
            }
            outs.push(gen_fn(&program, &body, &map, 1, &slots));
        }
        let mut glue = GlueSet::default();
        glue.add(&program, &slots, outs.iter().flat_map(|o| o.glue.iter()));
        let units = [
            main_unit(slots[main.0 as usize], &[], None),
            glue_unit(&program, &glue),
            runtime_unit(),
            table_unit(n, &[5]),
            loc_unit(&SlotFiles { paths: &["test.rs"], of_slot: &[] }, &vec![1; n]),
            fn_unit(&program, &outs, 0..n, &glue, "lust_register_u5", Some(slots[main.0 as usize])),
        ];
        let dir = std::env::temp_dir().join(format!("lust-cgen-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let mut files = Vec::new();
        for (i, u) in units.iter().enumerate() {
            let f = dir.join(format!("u{i}.c"));
            std::fs::write(&f, u).unwrap();
            files.push(f);
        }
        let exe = dir.join("prog");
        let cc = std::process::Command::new("cc").arg("-O0").arg("-w").arg("-o").arg(&exe).args(&files).output().unwrap();
        assert!(cc.status.success(), "cc failed: {}", String::from_utf8_lossy(&cc.stderr));
        let run = std::process::Command::new(&exe).output().unwrap();
        assert!(run.status.success(), "run failed: {}", String::from_utf8_lossy(&run.stderr));
        assert_eq!(String::from_utf8(run.stdout).unwrap(), "42\n3\n1.75\n1267650600228229401496703205381\n");
    }

    /// A move out of part of a drop-needing local through a deref
    /// has no move path drop elaboration can track. The borrow
    /// checker rejects such a move before code generation, so no
    /// lowered body from source reaches this: hand-build one and
    /// check `gen_fn` reports it in `FnOut::error` instead of
    /// panicking or silently dropping the rest twice.
    #[test]
    fn bad_move_path_is_an_error_not_a_panic() {
        let src = "fn main() { println!(\"hi\"); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let main = program.main.unwrap();
        let slots: Vec<u32> = (0..program.fns.len() as u32).collect();
        let (ck, errs) = check_fn(&program, main);
        assert!(errs.is_empty(), "{errs:?}");
        let mut body = crate::lower::lower(&program, main, ck);
        assert!(gen_fn(&program, &body, &map, 1, &slots).error.is_none(), "the lowered body is fine");
        let span = Span::new(FileId(0), 0, 0);
        let elems = body.tys.intern_tys(&[STRING, int(IntTy::U8)]);
        let tuple_ty = body.tys.intern(TyKind::Tuple(elems));
        let local = |ty: Ty| LocalDecl { ty, mutable: false, name: None };
        body.locals = vec![local(UNIT), local(tuple_ty), local(STRING)];
        body.blocks = vec![BlockData {
            stmts: vec![Stmt {
                kind: StmtKind::Assign(
                    Place::local(2),
                    Rvalue::Use(Operand::Move(Place { local: 1, proj: vec![Proj::Deref, Proj::Field(0)] })),
                ),
                span,
            }],
            term: Terminator::Return,
            term_span: span,
        }];
        let out = gen_fn(&program, &body, &map, 1, &slots);
        let err = out.error.expect("a deref part move is a code generation error");
        assert!(err.contains("drop elaboration cannot track"), "{err}");
        assert!(out.code.is_empty(), "no code is emitted for a bad move body");
    }

    /// A trait method stub and a template are never generated, so
    /// their fn slots stay empty. A call into one (here hand-built:
    /// check routes no call there) is an internal error in
    /// `FnOut::error`, never C that calls an empty slot. Generating
    /// the stub itself is the same error.
    #[test]
    fn call_to_fn_without_body_is_an_error() {
        let src = "trait Tr { fn go(&self) -> i32; fn dflt(&self) -> i32 { 100 } }\nstruct A;\n\
                   impl Tr for A { fn go(&self) -> i32 { 1 } }\nfn main() { println!(\"{}\", A.go()); }\n";
        let interner = std::sync::Arc::new(Interner::default());
        let known = std::sync::Arc::new(Known::new(&interner));
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
        let mut map = SourceMap::default();
        map.add_file("test.rs", src);
        let main = program.main.unwrap();
        let slots: Vec<u32> = (0..program.fns.len() as u32).collect();
        let named = |class: crate::check::generics::FnClass, name: &str| {
            (0..program.fns.len() as u32)
                .map(LocalDefId)
                .find(|&f| program.gx.fn_class[f.0 as usize] == class && interner.get(program.fn_info(f).name) == name)
                .unwrap()
        };
        let stub = named(crate::check::generics::FnClass::Stub, "go");
        let template = named(crate::check::generics::FnClass::Template, "dflt");
        let lowered = || {
            let (ck, errs) = check_fn(&program, main);
            assert!(errs.is_empty(), "{errs:?}");
            crate::lower::lower(&program, main, ck)
        };
        assert!(gen_fn(&program, &lowered(), &map, 1, &slots).error.is_none(), "the lowered body is fine");
        for callee in [stub, template] {
            let mut bad = lowered();
            let mut calls = 0;
            for b in &mut bad.blocks {
                if let Terminator::Call { target: CallTarget::Fn(f), .. } = &mut b.term {
                    *f = callee;
                    calls += 1;
                }
            }
            assert_eq!(calls, 1, "main calls `go` once");
            let out = gen_fn(&program, &bad, &map, 1, &slots);
            let err = out.error.expect("a call to a fn without a body is a code generation error");
            assert!(err.starts_with("internal:") && err.contains("has no generated body"), "{err}");
            assert!(out.code.is_empty(), "no code is emitted for the caller");
        }
        let mut own = lowered();
        own.fn_id = stub;
        let err = gen_fn(&program, &own, &map, 1, &slots).error.expect("a stub is never generated");
        assert!(err.contains("has no generated body"), "{err}");
    }

    /// Derived glue regenerates when a field type changes under the
    /// same Adt id: `refresh` on the edited program reports the
    /// regeneration and the glue text moves; on the same program it
    /// is a no-op. (Review B3/C3: `add` alone kept the old Debug body.)
    #[test]
    fn glue_refresh_regenerates_on_field_type_edit() {
        fn with_program<R>(src: &str, f: impl FnOnce(&Interner, &crate::check::collect::Program) -> R) -> R {
            let interner = std::sync::Arc::new(Interner::default());
            let known = std::sync::Arc::new(Known::new(&interner));
            let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let ids = crate::def::CrateIds { local: crate::def::LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
            let program = collect::collect(std::sync::Arc::new(ast), interner.clone(), known.clone(), ids).unwrap();
            f(&interner, &program)
        }
        let v1 = "#[derive(Debug)]\nstruct S { b: u8 }\nfn main() { let s = S { b: 0 }; println!(\"{:?}\", s); }\n";
        let v2 = "#[derive(Debug)]\nstruct S { b: bool }\nfn main() { let s = S { b: false }; println!(\"{:?}\", s); }\n";
        let mut glue = GlueSet::default();
        // The Adt id is collect order; both programs declare S first,
        // so one key names it in both, as in one daemon session.
        let (key, text1) = with_program(v1, |interner, p| {
            let a = p.type_names[&interner.intern("S")];
            let key = (Glue::Debug, CTy::Adt(a));
            let slots: Vec<u32> = (0..p.fns.len() as u32).collect();
            glue.add(p, &slots, [&key].into_iter());
            (key, glue_unit(p, &glue))
        });
        let regen_same = with_program(v1, |_interner, p| {
            let slots: Vec<u32> = (0..p.fns.len() as u32).collect();
            glue.refresh(p, &slots, [&key].into_iter()).1
        });
        assert!(!regen_same, "same program: nothing regenerates");
        let text1_again = with_program(v1, |_interner, p| glue_unit(p, &glue));
        assert_eq!(text1_again, text1, "same program: same glue text");
        let (regen, text2) = with_program(v2, |_interner, p| {
            let slots: Vec<u32> = (0..p.fns.len() as u32).collect();
            let regen = glue.refresh(p, &slots, [&key].into_iter()).1;
            (regen, glue_unit(p, &glue))
        });
        assert!(regen, "field type edit regenerates the Debug glue");
        assert_ne!(text2, text1, "regenerated glue text differs");
    }

    /// Replaces `main` with a hand-built body: an indirect call
    /// through a fn pointer value, float add, remainder and a
    /// saturating float-to-int cast, and a 128-bit literal print.
    fn rewrite_main(body: &mut Body, add1: LocalDefId) {
        let span = Span::new(FileId(0), 0, 0);
        let i64_ty = int(IntTy::I64);
        let f64_ty = body.tys.intern(TyKind::Float(FloatTy::F64));
        let u128_ty = int(IntTy::U128);
        let inputs = body.tys.intern_tys(&[i64_ty]);
        let sig = body.tys.intern_sig(Binder::plain(FnSig::plain(inputs, i64_ty)));
        let fnptr_ty = body.tys.intern(TyKind::FnPtr(sig));
        let local = |ty: Ty| LocalDecl { ty, mutable: false, name: None };
        // Print args hold a reference to the value, as lower emits them:
        // locals 8.. hold &l2, &l5, &l6, &l7 for the four prints.
        let ref_i64 = body.tys.mk_ref(false, i64_ty);
        let ref_f64 = body.tys.mk_ref(false, f64_ty);
        let ref_u128 = body.tys.mk_ref(false, u128_ty);
        body.locals = vec![
            local(UNIT),
            local(fnptr_ty),
            local(i64_ty),
            local(f64_ty),
            local(f64_ty),
            local(i64_ty),
            local(f64_ty),
            local(u128_ty),
            local(ref_i64),
            local(ref_i64),
            local(ref_f64),
            local(ref_u128),
        ];
        let assign = |l: Local, rv: Rvalue| Stmt { kind: StmtKind::Assign(Place::local(l), rv), span };
        let print = |l: Local, ty: Ty| Stmt {
            kind: StmtKind::Print {
                stderr: false,
                newline: true,
                parts: vec![FmtPart::Arg { value: Operand::Copy(Place::local(l)), ty, debug: false, spec: FmtSpec::default(), width: None, prec: None }],
            },
            span,
        };
        let fconst = |v: f64| Operand::Const(Const::Float(v.to_bits(), FloatTy::F64));
        body.blocks = vec![
            BlockData {
                stmts: vec![assign(1, Rvalue::FnValue(add1, fnptr_ty))],
                term: Terminator::Call {
                    target: CallTarget::Indirect(1),
                    args: vec![Operand::Const(Const::Int(41, IntTy::I64))],
                    dest: Place::local(2),
                    next: Bb(1),
                    unwind: None,
                },
                term_span: span,
            },
            BlockData {
                stmts: vec![
                    assign(3, Rvalue::Use(fconst(1.5))),
                    assign(4, Rvalue::Bin(BinOp::Add, Operand::Copy(Place::local(3)), fconst(2.25))),
                    assign(5, Rvalue::Cast(Operand::Copy(Place::local(4)), i64_ty)),
                    assign(6, Rvalue::Bin(BinOp::Rem, Operand::Copy(Place::local(4)), fconst(2.0))),
                    assign(7, Rvalue::Use(Operand::Const(Const::Int((1u128 << 100) + 5, IntTy::U128)))),
                    assign(8, Rvalue::Ref(false, Place::local(2))),
                    print(8, i64_ty),
                    assign(9, Rvalue::Ref(false, Place::local(5))),
                    print(9, i64_ty),
                    assign(10, Rvalue::Ref(false, Place::local(6))),
                    print(10, f64_ty),
                    assign(11, Rvalue::Ref(false, Place::local(7))),
                    print(11, u128_ty),
                ],
                term: Terminator::Return,
                term_span: span,
            },
        ];
    }
}

/// The `(u8, T)` cell of a `thread_local!` value of C type `t`: the
/// state byte (0 initial, 1 alive, 2 destroyed) and the value.
fn tls_cell(t: &CTy) -> CTy {
    CTy::Tuple(vec![CTy::Int(IntTy::U8), t.clone()])
}

/// The `TlsInit` and `TlsDtor` glue of the cell type `c` (see `Glue`).
/// Rust's `LazyStorage` order: a value made while the init fn ran (a
/// recursive access) is replaced and dropped; else the cell turns alive
/// and a value that needs drop registers its destructor.
fn tls_glue(p: &Program, g: &Glue, c: &CTy, protos: &mut String, defs: &mut String, need: &mut dyn FnMut(Glue, &CTy)) {
    let CTy::Tuple(parts) = c else { unreachable!("tls glue keys on the cell tuple") };
    let t = &parts[1];
    let (m, ct, vt) = (mangle(c), ctype(c), ctype(t));
    let drops = needs_drop_c(p, t);
    if drops {
        need(Glue::Drop, t);
    }
    if *g == Glue::TlsDtor {
        let _ = writeln!(protos, "void tlsdtor_{m}(void *p);");
        let drop = if drops { format!("drop_{}(&c->f1); ", mangle(t)) } else { String::new() };
        let _ = writeln!(defs, "void tlsdtor_{m}(void *p) {{
  {ct} *c = ({ct} *)p;
  if (c->f0 == 1) {{ c->f0 = 2; {drop}}}
}}
");
        return;
    }
    let _ = writeln!(protos, "{ct} *tlsinit_{m}({ct} *c, void *init);");
    let make = if ret_by_out(p, t) { format!("((void (*)({vt} *))init)(&v);") } else { format!("v = (({vt} (*)(void))init)();") };
    let (replace, register) = if drops {
        need(Glue::TlsDtor, c);
        (format!(" {vt} old = c->f1; c->f1 = v; drop_{}(&old); ", mangle(t)), format!(" lust_tls_register(c, tlsdtor_{m});"))
    } else {
        (" c->f1 = v; ".to_string(), String::new())
    };
    let _ = writeln!(
        defs,
        "{ct} *tlsinit_{m}({ct} *c, void *init) {{\n  if (c->f0 == 2) return 0;\n  {vt} v; {make}\n  if (c->f0 == 1) {{{replace}}}\n  else {{ c->f1 = v; c->f0 = 1;{register} }}\n  return c;\n}}\n"
    );
}

impl FnGen<'_, '_> {
    /// `TlsAccess(key, init) -> &T`, `TlsTryAccess(key, init) ->
    /// Option<&T>`, and `TlsInitWith(key, value) -> Option<T>`
    /// (lower/tls.rs), over the runtime's per-thread cells. The common
    /// access builds no `Option`: tcc zero-fills each compound literal
    /// with a memset call.
    fn tls_builtin(&mut self, b: Builtin, vals: &[String], tys: &[CTy], loc: &str) -> String {
        let t = match b {
            Builtin::TlsAccess | Builtin::TlsTryAccess => match &tys[1] {
                CTy::FnPtr(_, r) => (**r).clone(),
                _ => unreachable!("TlsAccess takes the init fn pointer"),
            },
            _ => tys[1].clone(),
        };
        let cell = tls_cell(&t);
        collect_types(&cell, &mut self.sig_types);
        let (m, ct) = (mangle(&cell), ctype(&cell));
        let c = self.tmp();
        let _ = writeln!(self.out, "    {ct} *{c} = ({ct} *)lust_tls_cell((uint64_t *){}, sizeof({ct}), _Alignof({ct}));", vals[0]);
        if b != Builtin::TlsInitWith {
            self.want(Glue::TlsInit, &cell);
            let _ = writeln!(self.out, "    if ({c}->f0 != 1) {c} = tlsinit_{m}({c}, (void *){});", vals[1]);
        }
        if b == Builtin::TlsAccess {
            let _ = writeln!(self.out, "    if (!{c}) lust_panic_cstr_owned({}, {loc});", c_string_lit(crate::lower::tls::ACCESS_PANIC.as_bytes()));
            return format!("(&{c}->f1)");
        }
        if b == Builtin::TlsTryAccess {
            let opt = CTy::Option(Box::new(CTy::Ref(Box::new(t))));
            collect_types(&opt, &mut self.sig_types);
            let (some, none) = (self.make_variant(&opt, 1, &[format!("&{c}->f1")]), self.make_variant(&opt, 0, &[]));
            return format!("({c} ? {some} : {none})");
        }
        let opt = CTy::Option(Box::new(t.clone()));
        collect_types(&opt, &mut self.sig_types);
        let (r, v) = (self.tmp(), self.tmp());
        let register = if needs_drop_c(self.p, &t) {
            self.want(Glue::TlsDtor, &cell);
            format!(" lust_tls_register({c}, tlsdtor_{m});")
        } else {
            String::new()
        };
        let none = self.make_variant(&opt, 0, &[]);
        let some = self.make_variant(&opt, 1, std::slice::from_ref(&v));
        let _ = writeln!(
            self.out,
            "    {} {v} = {}; {} {r}; if ({c}->f0 == 0) {{ {c}->f1 = {v}; {c}->f0 = 1;{register} {r} = {none}; }} else {r} = {some};",
            ctype(&t),
            vals[1],
            ctype(&opt)
        );
        r
    }
}
