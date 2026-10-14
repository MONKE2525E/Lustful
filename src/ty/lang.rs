// Lang items, shipped crates, and the intrinsic registry (docs/ARCH.md
// sections 3.1, 3.2, and 3.6, serial refactor S5).
//
// Three closed tables live here, in one place, so no other file hardcodes a
// std path or an intrinsic name:
//
// - `LANG_ITEMS`: the items the compiler must know by def (section 3.1).
//   The std loader (`src/stdload.rs`) fills a `LangItems` once per session:
//   builtin-backed items come from `BuiltinDefs`, source items from
//   `#[lust_lang = "..."]` marks in `library/` source. A missing item that
//   is marked `required` is a compiler installation error, never a user
//   diagnostic. An item that is not required yet has no source def today;
//   the ledger in `library/README.md` tracks it.
// - `INTRINSICS`: every compiler-known callable (section 3.2), each with a
//   normal fn signature, a C symbol, and the shipped crates that may call
//   it. Check and cgen both run the privilege test (section 3.1 item 1):
//   only a shipped crate named in the row may name the intrinsic, matched
//   by the crate the call site's source belongs to, never by name matching
//   in user source. A user call is `L0642`. A privileged call to an
//   intrinsic whose body does not exist yet is `L0640`. Only `implemented`
//   rows reach codegen.
// - `STD_FNS`: the non-generic source std fns the loader splices into a
//   compile (section 9.2 S5: the source path covers non-generic fns only
//   until the minimal generic pipeline). A row with `implemented: false`
//   is a declared std item with no body yet: a call rejects with `L0640`
//   naming the item, per the surface-parity rule in section 3.1.
use super::{BOOL, BuiltinDefs, FloatTy, I32, Mut, NEVER, Ty, TyIntern, TyKind, UNIT, USIZE};
use crate::def::{DefId, StableCrateHash, stable_crate_hash};

/// A crate the compiler ships in `library/` (section 3.1) or `library/deps/`
/// (section 3.6). Privilege is matched by this identity (through its stable
/// crate hash at load, and through source ranges in a spliced compile),
/// never by a name a user crate can write.
#[allow(dead_code)] // Adapter variants are first constructed by W-DEPS source; registry rows name them now.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShippedCrate {
    Core,
    Alloc,
    Std,
    RustcHash,
    Indexmap,
    Smallvec,
    Memchr,
    Bumpalo,
    XxhashRust,
    RyuJs,
    NumBigInt,
}

impl ShippedCrate {
    /// Every shipped crate, in `library/` layout order.
    #[allow(dead_code)] // Iterated by registry tests now; the driver iterates it when adapter loading lands.
    pub const ALL: &[ShippedCrate] = &[
        ShippedCrate::Core,
        ShippedCrate::Alloc,
        ShippedCrate::Std,
        ShippedCrate::RustcHash,
        ShippedCrate::Indexmap,
        ShippedCrate::Smallvec,
        ShippedCrate::Memchr,
        ShippedCrate::Bumpalo,
        ShippedCrate::XxhashRust,
        ShippedCrate::RyuJs,
        ShippedCrate::NumBigInt,
    ];

    /// The crate name as user code writes it in a path (`std::...`).
    pub fn name(self) -> &'static str {
        match self {
            ShippedCrate::Core => "core",
            ShippedCrate::Alloc => "alloc",
            ShippedCrate::Std => "std",
            ShippedCrate::RustcHash => "rustc_hash",
            ShippedCrate::Indexmap => "indexmap",
            ShippedCrate::Smallvec => "smallvec",
            ShippedCrate::Memchr => "memchr",
            ShippedCrate::Bumpalo => "bumpalo",
            ShippedCrate::XxhashRust => "xxhash_rust",
            ShippedCrate::RyuJs => "ryu_js",
            ShippedCrate::NumBigInt => "num_bigint",
        }
    }

    /// The crate's stable disambiguator (section 1.7). The shipped library
    /// is fixed inside one lust version, so the package id is a constant.
    /// This is the identity intrinsic privilege is matched by at std load.
    pub fn stable_hash(self) -> StableCrateHash {
        stable_crate_hash(&format!("lust-library-v1/{}", self.name()), "lib", self.name(), false)
    }
}

/// One lang item the compiler must know by def (section 3.1). New items go
/// at the end only; the discriminant indexes `LangItems`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LangItem {
    Option,
    Result,
    String,
    Vec,
    Box,
    Rc,
    Arc,
    UnsafeCell,
    PhantomData,
    Range,
    RangeFrom,
    RangeTo,
    RangeFull,
    RangeInclusive,
    RangeToInclusive,
    Iterator,
    IntoIterator,
    Drop,
    Deref,
    DerefMut,
    Fn,
    FnMut,
    FnOnce,
    Sized,
    Send,
    Sync,
    Panic,
    PanicBounds,
    Formatter,
    ExchangeMalloc,
    ExchangeFree,
}

/// The static row for one lang item: its `#[lust_lang]` name, the shipped
/// crate that must define it, and whether std load must fail without it
/// today. Only items with a def source today (a builtin def, or shipped
/// source) are `required`; the rest join as W-STD writes them.
pub struct LangItemDef {
    pub item: LangItem,
    pub name: &'static str,
    pub krate: ShippedCrate,
    pub required: bool,
}

use LangItem as L;
use ShippedCrate as C;

/// The lang item table (section 3.1). Keep rows in `LangItem` order: the
/// row index is the item's discriminant (a test pins this).
pub const LANG_ITEMS: &[LangItemDef] = &[
    LangItemDef { item: L::Option, name: "option", krate: C::Core, required: true },
    LangItemDef { item: L::Result, name: "result", krate: C::Core, required: true },
    LangItemDef { item: L::String, name: "string", krate: C::Alloc, required: true },
    LangItemDef { item: L::Vec, name: "vec", krate: C::Alloc, required: true },
    LangItemDef { item: L::Box, name: "box", krate: C::Alloc, required: true },
    LangItemDef { item: L::Rc, name: "rc", krate: C::Alloc, required: true },
    LangItemDef { item: L::Arc, name: "arc", krate: C::Alloc, required: false },
    LangItemDef { item: L::UnsafeCell, name: "unsafe_cell", krate: C::Core, required: false },
    LangItemDef { item: L::PhantomData, name: "phantom_data", krate: C::Core, required: false },
    LangItemDef { item: L::Range, name: "range", krate: C::Core, required: false },
    LangItemDef { item: L::RangeFrom, name: "range_from", krate: C::Core, required: false },
    LangItemDef { item: L::RangeTo, name: "range_to", krate: C::Core, required: false },
    LangItemDef { item: L::RangeFull, name: "range_full", krate: C::Core, required: false },
    LangItemDef { item: L::RangeInclusive, name: "range_inclusive", krate: C::Core, required: false },
    LangItemDef { item: L::RangeToInclusive, name: "range_to_inclusive", krate: C::Core, required: false },
    LangItemDef { item: L::Iterator, name: "iterator", krate: C::Core, required: false },
    LangItemDef { item: L::IntoIterator, name: "into_iterator", krate: C::Core, required: false },
    LangItemDef { item: L::Drop, name: "drop", krate: C::Core, required: false },
    LangItemDef { item: L::Deref, name: "deref", krate: C::Core, required: false },
    LangItemDef { item: L::DerefMut, name: "deref_mut", krate: C::Core, required: false },
    LangItemDef { item: L::Fn, name: "fn", krate: C::Core, required: false },
    LangItemDef { item: L::FnMut, name: "fn_mut", krate: C::Core, required: false },
    LangItemDef { item: L::FnOnce, name: "fn_once", krate: C::Core, required: false },
    LangItemDef { item: L::Sized, name: "sized", krate: C::Core, required: false },
    LangItemDef { item: L::Send, name: "send", krate: C::Core, required: false },
    LangItemDef { item: L::Sync, name: "sync", krate: C::Core, required: false },
    LangItemDef { item: L::Panic, name: "panic", krate: C::Core, required: false },
    LangItemDef { item: L::PanicBounds, name: "panic_bounds", krate: C::Core, required: false },
    LangItemDef { item: L::Formatter, name: "formatter", krate: C::Core, required: false },
    LangItemDef { item: L::ExchangeMalloc, name: "exchange_malloc", krate: C::Alloc, required: false },
    LangItemDef { item: L::ExchangeFree, name: "exchange_free", krate: C::Alloc, required: false },
];

/// The lang item with this `#[lust_lang]` name, if the table has it.
pub fn lang_item_by_name(name: &str) -> Option<LangItem> {
    LANG_ITEMS.iter().find(|d| d.name == name).map(|d| d.item)
}

/// The resolved lang items of one std load: one def per item, or none while
/// the item has no def source. Built by the std loader, read by later waves
/// (mono, traits) through `get`.
#[derive(Clone, Debug)]
pub struct LangItems {
    defs: [Option<DefId>; LANG_ITEMS.len()],
}

impl LangItems {
    /// A table with the builtin-backed items filled from `BuiltinDefs`.
    /// These types are builtin Adts until source std replaces them
    /// (section 3.1); their defs are already stable path hashes.
    pub fn from_builtins(b: BuiltinDefs) -> LangItems {
        let mut items = LangItems { defs: [None; LANG_ITEMS.len()] };
        items.set(LangItem::Option, b.option);
        items.set(LangItem::Result, b.result);
        items.set(LangItem::String, b.string);
        items.set(LangItem::Vec, b.vec);
        items.set(LangItem::Box, b.boxed);
        items.set(LangItem::Rc, b.rc);
        items
    }

    /// Records the def of one item. A second record replaces the first;
    /// the loader reports duplicates before it calls this.
    pub fn set(&mut self, item: LangItem, def: DefId) {
        self.defs[item as usize] = Some(def);
    }

    /// The def of one item, if this load resolved it.
    pub fn get(&self, item: LangItem) -> Option<DefId> {
        self.defs[item as usize]
    }

    /// Required items with no def. Empty on a good load; the loader turns
    /// a non-empty list into an installation error (section 3.1).
    pub fn required_missing(&self) -> Vec<LangItem> {
        LANG_ITEMS.iter().filter(|d| d.required && self.get(d.item).is_none()).map(|d| d.item).collect()
    }
}

/// One type in an intrinsic signature, before interning. The registry is a
/// static table, so it cannot hold a `Ty`; check resolves these through
/// the body's type store. `Ptr` is an erased raw pointer (`*mut ()`):
/// sized intrinsics take explicit size and align (section 3.2), and the
/// typed pointer API is source in std wrappers. `Bytes` is `&[u8]`,
/// passed to C as two arguments (`const uint8_t *ptr, uint64_t len`), so
/// adapter cores can take a slice before source std has raw pointers.
/// `U128` is `u128` (C `lust_u128`). `StringMut` is `&mut String` (C
/// `lust_String *`), for a core that appends text. New variants go at
/// the end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SigTy {
    Unit,
    Never,
    Bool,
    I32,
    U32,
    U64,
    Usize,
    F32,
    F64,
    Ptr,
    Bytes,
    U128,
    StringMut,
}

impl SigTy {
    /// The interned form of this signature type in `tys`.
    pub fn resolve(self, tys: &mut impl TyIntern) -> Ty {
        match self {
            SigTy::Unit => UNIT,
            SigTy::Never => NEVER,
            SigTy::Bool => BOOL,
            SigTy::I32 => I32,
            SigTy::U32 => super::int(super::IntTy::U32),
            SigTy::U64 => super::int(super::IntTy::U64),
            SigTy::Usize => USIZE,
            SigTy::F32 => tys.intern(TyKind::Float(FloatTy::F32)),
            SigTy::F64 => tys.intern(TyKind::Float(FloatTy::F64)),
            SigTy::Ptr => tys.intern(TyKind::RawPtr(Mut::Mut, UNIT)),
            SigTy::Bytes => {
                let bytes = tys.intern(TyKind::Slice(super::int(super::IntTy::U8)));
                tys.intern(TyKind::Ref(super::Region::Erased, Mut::Shared, bytes))
            }
            SigTy::U128 => super::int(super::IntTy::U128),
            SigTy::StringMut => tys.intern(TyKind::Ref(super::Region::Erased, Mut::Mut, super::STRING)),
        }
    }
}

/// One intrinsic (section 3.2): a normal fn signature in
/// `core::intrinsics`, a C symbol, the shipped crates that may call it,
/// and whether codegen can emit it today. The id of an intrinsic in
/// check side tables and IR is its index in `INTRINSICS`; add new rows
/// at the end of their group only in a wave that owns this file, and
/// never remove or reorder a row inside one lust version.
pub struct IntrinsicDef {
    pub name: &'static str,
    pub c_symbol: &'static str,
    pub params: &'static [SigTy],
    pub ret: SigTy,
    pub allowed: &'static [ShippedCrate],
    pub implemented: bool,
}

impl IntrinsicDef {
    /// True if source that belongs to `krate` may call this intrinsic.
    /// `None` is user source: never allowed (section 3.1 item 1).
    pub fn allows(&self, krate: Option<ShippedCrate>) -> bool {
        krate.is_some_and(|k| self.allowed.contains(&k))
    }
}

use SigTy as S;

const LIB: &[ShippedCrate] = &[C::Core, C::Alloc, C::Std];
const ALLOC_STD: &[ShippedCrate] = &[C::Alloc, C::Std];
const CORE_ALLOC: &[ShippedCrate] = &[C::Core, C::Alloc];
const CORE_STD: &[ShippedCrate] = &[C::Core, C::Std];
const ONLY_STD: &[ShippedCrate] = &[C::Std];

/// The intrinsic registry (section 3.2 table, plus the section 3.4
/// predicates and the section 3.6 adapter cores). Width-specific atomic
/// and sync variants are one row per operation today; W-STD widens a row
/// into per-width rows when its wrappers land, with a difftest each.
pub const INTRINSICS: &[IntrinsicDef] = &[
    // Memory: the process allocator (section 3.7).
    IntrinsicDef {
        name: "alloc",
        c_symbol: "lust_alloc",
        params: &[S::Usize, S::Usize],
        ret: S::Ptr,
        allowed: ALLOC_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "dealloc",
        c_symbol: "lust_dealloc",
        params: &[S::Ptr, S::Usize, S::Usize],
        ret: S::Unit,
        allowed: ALLOC_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "realloc",
        c_symbol: "lust_realloc",
        params: &[S::Ptr, S::Usize, S::Usize, S::Usize],
        ret: S::Ptr,
        allowed: ALLOC_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "alloc_zeroed",
        c_symbol: "lust_alloc_zeroed",
        params: &[S::Usize, S::Usize],
        ret: S::Ptr,
        allowed: ALLOC_STD,
        implemented: false,
    },
    // Bytes.
    IntrinsicDef {
        name: "memcpy",
        c_symbol: "lust_memcpy",
        params: &[S::Ptr, S::Ptr, S::Usize],
        ret: S::Unit,
        allowed: LIB,
        implemented: false,
    },
    IntrinsicDef {
        name: "memmove",
        c_symbol: "lust_memmove",
        params: &[S::Ptr, S::Ptr, S::Usize],
        ret: S::Unit,
        allowed: LIB,
        implemented: false,
    },
    IntrinsicDef {
        name: "memset",
        c_symbol: "lust_memset",
        params: &[S::Ptr, S::U32, S::Usize],
        ret: S::Unit,
        allowed: LIB,
        implemented: false,
    },
    IntrinsicDef {
        name: "memcmp",
        c_symbol: "lust_memcmp",
        params: &[S::Ptr, S::Ptr, S::Usize],
        ret: S::I32,
        allowed: LIB,
        implemented: false,
    },
    // Raw pointer load/store/offset: one unsafe boundary for borrowck.
    IntrinsicDef {
        name: "ptr_read",
        c_symbol: "lust_ptr_read",
        params: &[S::Ptr, S::Ptr, S::Usize],
        ret: S::Unit,
        allowed: LIB,
        implemented: false,
    },
    IntrinsicDef {
        name: "ptr_write",
        c_symbol: "lust_ptr_write",
        params: &[S::Ptr, S::Ptr, S::Usize],
        ret: S::Unit,
        allowed: LIB,
        implemented: false,
    },
    IntrinsicDef {
        name: "ptr_offset",
        c_symbol: "lust_ptr_offset",
        params: &[S::Ptr, S::Usize],
        ret: S::Ptr,
        allowed: LIB,
        implemented: false,
    },
    // Float text: shortest round-trip print, correctly rounded parse.
    // The C entry takes (out, value, spec); SigTy cannot name the spec
    // struct yet, so these rows name the plain Display entries, whose
    // C signatures are exactly (out, value). A formatted row joins
    // when SigTy can name the spec (W-STD).
    IntrinsicDef {
        name: "fmt_f64",
        c_symbol: "lust_fmt_f64_display",
        params: &[S::Ptr, S::F64],
        ret: S::Unit,
        allowed: CORE_ALLOC,
        implemented: false,
    },
    IntrinsicDef {
        name: "fmt_f32",
        c_symbol: "lust_fmt_f32_display",
        params: &[S::Ptr, S::F32],
        ret: S::Unit,
        allowed: CORE_ALLOC,
        implemented: false,
    },
    IntrinsicDef {
        name: "parse_f64",
        c_symbol: "lust_parse_f64",
        params: &[S::Ptr, S::Usize],
        ret: S::F64,
        allowed: CORE_ALLOC,
        implemented: false,
    },
    IntrinsicDef {
        name: "parse_f32",
        c_symbol: "lust_parse_f32",
        params: &[S::Ptr, S::Usize],
        ret: S::F32,
        allowed: CORE_ALLOC,
        implemented: false,
    },
    // Panic entry points (section 7).
    IntrinsicDef {
        name: "panic",
        c_symbol: "lust_panic_payload",
        params: &[S::Ptr, S::Ptr, S::U64],
        ret: S::Never,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "panic_bounds",
        c_symbol: "lust_panic_bounds",
        params: &[S::Usize, S::Usize, S::U64],
        ret: S::Never,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "panic_str",
        c_symbol: "lust_panic_str",
        params: &[S::Ptr, S::Usize, S::U64],
        ret: S::Never,
        allowed: CORE_STD,
        implemented: false,
    },
    // Threads and TLS (section 7.3).
    IntrinsicDef {
        name: "thread_spawn",
        c_symbol: "lust_thread_spawn",
        params: &[S::Ptr, S::Ptr],
        ret: S::U64,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "thread_join_raw",
        c_symbol: "lust_thread_join_raw",
        params: &[S::U64],
        ret: S::Ptr,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "tls_key_create",
        c_symbol: "lust_tls_key_create",
        params: &[S::Ptr],
        ret: S::U64,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef { name: "tls_get", c_symbol: "lust_tls_get", params: &[S::U64], ret: S::Ptr, allowed: ONLY_STD, implemented: false },
    IntrinsicDef {
        name: "tls_set",
        c_symbol: "lust_tls_set",
        params: &[S::U64, S::Ptr],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef { name: "park", c_symbol: "lust_park", params: &[], ret: S::Unit, allowed: ONLY_STD, implemented: false },
    IntrinsicDef { name: "unpark", c_symbol: "lust_unpark", params: &[S::U64], ret: S::Unit, allowed: ONLY_STD, implemented: false },
    // Sync cores on opaque handles.
    IntrinsicDef {
        name: "mutex_lock",
        c_symbol: "lust_mutex_lock",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "mutex_unlock",
        c_symbol: "lust_mutex_unlock",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "rwlock_read",
        c_symbol: "lust_rwlock_read",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "rwlock_write",
        c_symbol: "lust_rwlock_write",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "rwlock_unlock",
        c_symbol: "lust_rwlock_unlock",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "condvar_wait",
        c_symbol: "lust_condvar_wait",
        params: &[S::U64, S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "condvar_notify_one",
        c_symbol: "lust_condvar_notify_one",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "condvar_notify_all",
        c_symbol: "lust_condvar_notify_all",
        params: &[S::U64],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    // Atomics (per width and ordering when the wrappers land).
    IntrinsicDef {
        name: "atomic_load",
        c_symbol: "lust_atomic_load",
        params: &[S::Ptr, S::Usize, S::U32],
        ret: S::U64,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "atomic_store",
        c_symbol: "lust_atomic_store",
        params: &[S::Ptr, S::U64, S::Usize, S::U32],
        ret: S::Unit,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "atomic_xchg",
        c_symbol: "lust_atomic_xchg",
        params: &[S::Ptr, S::U64, S::Usize, S::U32],
        ret: S::U64,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "atomic_cas",
        c_symbol: "lust_atomic_cas",
        params: &[S::Ptr, S::U64, S::U64, S::Usize, S::U32],
        ret: S::U64,
        allowed: CORE_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "atomic_fetch_add",
        c_symbol: "lust_atomic_fetch_add",
        params: &[S::Ptr, S::U64, S::Usize, S::U32],
        ret: S::U64,
        allowed: CORE_STD,
        implemented: false,
    },
    // Time.
    IntrinsicDef {
        name: "clock_now_raw",
        c_symbol: "lust_clock_now_raw",
        params: &[S::Ptr],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "system_time_raw",
        c_symbol: "lust_system_time_raw",
        params: &[S::Ptr],
        ret: S::Unit,
        allowed: ONLY_STD,
        implemented: false,
    },
    // Raw fd IO plus errno.
    IntrinsicDef {
        name: "fd_read",
        c_symbol: "lust_fd_read",
        params: &[S::I32, S::Ptr, S::Usize],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "fd_write",
        c_symbol: "lust_fd_write",
        params: &[S::I32, S::Ptr, S::Usize],
        ret: S::I32,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef { name: "fd_close", c_symbol: "lust_fd_close", params: &[S::I32], ret: S::I32, allowed: ONLY_STD, implemented: false },
    IntrinsicDef { name: "errno", c_symbol: "lust_errno", params: &[], ret: S::I32, allowed: ONLY_STD, implemented: false },
    // Process: raw args/env tables, and exit.
    IntrinsicDef {
        name: "args_raw",
        c_symbol: "lust_args_raw",
        params: &[S::Usize, S::Ptr],
        ret: S::Bool,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef {
        name: "env_get",
        c_symbol: "lust_env_get",
        params: &[S::Ptr, S::Usize, S::Ptr],
        ret: S::Bool,
        allowed: ONLY_STD,
        implemented: false,
    },
    IntrinsicDef { name: "exit", c_symbol: "lust_exit", params: &[S::I32], ret: S::Never, allowed: ONLY_STD, implemented: true },
    // Specialization predicates (section 3.4). Mono evaluates them as
    // constants after substitution; the signature here is the erased form.
    IntrinsicDef { name: "is_trusted_random_access", c_symbol: "", params: &[], ret: S::Bool, allowed: CORE_ALLOC, implemented: false },
    IntrinsicDef { name: "is_trusted_len", c_symbol: "", params: &[], ret: S::Bool, allowed: CORE_ALLOC, implemented: false },
    IntrinsicDef { name: "in_place_collect", c_symbol: "", params: &[], ret: S::Bool, allowed: CORE_ALLOC, implemented: false },
    // Adapter cores (section 3.6): each adapter only its own rows.
    IntrinsicDef {
        name: "arena_alloc",
        c_symbol: "lust_arena_alloc",
        params: &[S::U64, S::Usize, S::Usize],
        ret: S::Ptr,
        allowed: &[C::Bumpalo],
        implemented: false,
    },
    // Byte and substring search: the index of the first (memchr, memmem)
    // or last (memrchr) match, or usize::MAX for none (no slice is that
    // long).
    IntrinsicDef {
        name: "memchr",
        c_symbol: "lust_memchr",
        params: &[S::U32, S::Bytes],
        ret: S::Usize,
        allowed: &[C::Memchr],
        implemented: true,
    },
    IntrinsicDef {
        name: "memrchr",
        c_symbol: "lust_memrchr",
        params: &[S::U32, S::Bytes],
        ret: S::Usize,
        allowed: &[C::Memchr],
        implemented: true,
    },
    IntrinsicDef {
        name: "memmem",
        c_symbol: "lust_memmem",
        params: &[S::Bytes, S::Bytes],
        ret: S::Usize,
        allowed: &[C::Memchr],
        implemented: true,
    },
    // XXH3 of the bytes with a seed (0 is the unseeded hash).
    IntrinsicDef {
        name: "xxh3_64",
        c_symbol: "lust_xxh3_64",
        params: &[S::Bytes, S::U64],
        ret: S::U64,
        allowed: &[C::XxhashRust],
        implemented: true,
    },
    IntrinsicDef {
        name: "xxh3_128",
        c_symbol: "lust_xxh3_128",
        params: &[S::Bytes, S::U64],
        ret: S::U128,
        allowed: &[C::XxhashRust],
        implemented: true,
    },
    // Appends the ECMAScript Number::toString text of the f64 (ryu-js
    // 1.0.2 Buffer::format) to the String; the core is in float.c.
    IntrinsicDef {
        name: "ryu_js_fmt_f64",
        c_symbol: "lust_fmt_js_f64",
        params: &[S::StringMut, S::F64],
        ret: S::Unit,
        allowed: &[C::RyuJs],
        implemented: true,
    },
];

/// The intrinsic with this `core::intrinsics` name: its registry id.
pub fn intrinsic_by_name(name: &str) -> Option<u32> {
    INTRINSICS.iter().position(|d| d.name == name).map(|i| i as u32)
}

/// The registry row for an intrinsic id from check or IR.
pub fn intrinsic(id: u32) -> &'static IntrinsicDef {
    &INTRINSICS[id as usize]
}

/// One non-generic std fn the loader can route (section 9.2 S5). `path`
/// is the full Rust path a user writes. `mangled` is the name the fn
/// carries inside a spliced one-crate compile, so it can never collide
/// with a user fn of the same short name. `trigger` is the byte string
/// the driver scans for before it pays for a std load; a miss only costs
/// the old `L0505` module-path reject, never a wrong accept.
pub struct StdFnDef {
    pub path: &'static [&'static str],
    pub mangled: &'static str,
    pub trigger: &'static str,
    pub krate: ShippedCrate,
    pub implemented: bool,
}

/// The source std fns known to the loader. The loader checks that every
/// `implemented` row has a matching fn in `library/` source at load;
/// a mismatch is an installation error, like a missing lang item.
pub const STD_FNS: &[StdFnDef] = &[
    StdFnDef {
        path: &["std", "process", "exit"],
        mangled: "__lust_std_process_exit",
        trigger: "process::exit",
        krate: C::Std,
        implemented: true,
    },
    // Declared surface only (section 3.1): real std has this fn, lust std
    // has no body yet, so a call rejects with L0640 instead of "no such
    // path". The body lands with W-STD (it needs the abort runtime hook).
    StdFnDef {
        path: &["std", "process", "abort"],
        mangled: "__lust_std_process_abort",
        trigger: "process::abort",
        krate: C::Std,
        implemented: false,
    },
];

/// The std types lust knows by name that are not in the prelude
/// (W-STD-A): a module names one only after a `use` of its std path
/// or a glob of its std module, as in Rust. (crates, module, name).
pub const STD_IMPORTED_TYPES: &[(&[&str], &str, &str)] = &[
    (&["std", "alloc"], "rc", "Rc"),
    (&["std", "alloc"], "rc", "Weak"),
    (&["std", "core"], "cell", "RefCell"),
    (&["std", "core"], "cell", "Cell"),
    (&["std", "core"], "cmp", "Ordering"),
    (&["std"], "process", "ExitCode"),
    (&["std", "core"], "str", "Utf8Error"),
    (&["std", "alloc"], "string", "FromUtf8Error"),
];

/// The std types under `std::sync::mpsc` lust knows by name besides the
/// sync types (ty/sync.rs): the synthetic error Adts (W-THREADS).
pub const STD_MPSC_ADTS: &[&str] = &["RecvError", "TryRecvError"];

/// True when the glob `use` of `path` (`std::rc` in `use std::rc::*;`)
/// brings the std type `name` into scope. The sync types and
/// `atomic::Ordering` live in deeper modules (W-THREADS).
pub fn std_glob_imports(path: &[&str], name: &str) -> bool {
    let mut full = path.to_vec();
    full.push(name);
    STD_IMPORTED_TYPES
        .iter()
        .any(|&(crates, module, n)| n == name && path.len() == 2 && crates.contains(&path[0]) && path[1] == module)
        || crate::ty::sync::SyncTy::by_path(&full).is_some()
        || (name == "Ordering" && matches!(full.as_slice(), ["std" | "core", "sync", "atomic", "Ordering"]))
        || (STD_MPSC_ADTS.contains(&name) && path == ["std", "sync", "mpsc"])
}

/// True when a glob of the std module `path` imports `name` and the
/// module is one of the sync or thread modules (W-THREADS): a sync
/// type, `atomic::Ordering`, or a std free fn of that module.
pub fn std_sync_glob_imports(path: &[&str], name: &str) -> bool {
    let sync_module = matches!(path, ["std" | "core", "sync", ..] | ["std" | "core", "hint"]);
    sync_module && (std_glob_imports(path, name) || std_glob_fns(path).contains(&name))
}

/// The std free fns a glob `use` of `path` brings (`use std::sync::
/// atomic::*;` brings `fence`).
pub fn std_glob_fns(path: &[&str]) -> Vec<&'static str> {
    STD_FN_PATHS
        .iter()
        .filter_map(|row| {
            let parts: Vec<&str> = row.split('/').collect();
            (parts.len() == path.len() + 1 && parts.iter().zip(path).all(|(a, b)| a == b)).then(|| *parts.last().unwrap())
        })
        .collect()
}

/// Every std type name a glob `use` can bring (`std_glob_imports`).
pub fn std_glob_names() -> impl Iterator<Item = &'static str> {
    STD_IMPORTED_TYPES.iter().map(|t| t.2).chain(crate::ty::sync::SyncTy::ALL.iter().map(|k| k.name())).chain(STD_MPSC_ADTS.iter().copied())
}

/// The `use` path to suggest for a non-prelude std type lust knows by
/// name (`needs_std_use`), as `std::module::Name`.
pub fn std_use_hint(name: &str) -> String {
    if let Some(t) = STD_IMPORTED_TYPES.iter().find(|t| t.2 == name) {
        return format!("std::{}::{name}", t.1);
    }
    if STD_MPSC_ADTS.contains(&name) {
        return format!("std::sync::mpsc::{name}");
    }
    match crate::ty::sync::SyncTy::ALL.iter().find(|k| k.name() == name) {
        Some(k) => format!("std::{}::{name}", k.module().join("::")),
        None => format!("std::rc::{name}"),
    }
}

/// The variant names of the std enum at `path` (`std::cmp::Ordering`
/// gives Less, Equal, Greater), for a glob import of its variants.
pub fn std_enum_variants(path: &[&str]) -> Vec<&'static str> {
    STD_VARIANT_PATHS
        .iter()
        .filter_map(|row| {
            let parts: Vec<&str> = row.split('/').collect();
            (parts.len() == path.len() + 1 && parts.iter().zip(path).all(|(a, b)| a == b)).then(|| *parts.last().unwrap())
        })
        .collect()
}

/// True when `name` is one of `STD_IMPORTED_TYPES`.
pub fn needs_std_use(name: &str) -> bool {
    STD_IMPORTED_TYPES.iter().any(|&(_, _, n)| n == name) || crate::ty::sync::SyncTy::ALL.iter().any(|k| k.name() == name) || STD_MPSC_ADTS.contains(&name)
}

/// True if `src` can mention an implemented source std fn, so the driver
/// must load std before it compiles. A plain byte scan: it runs on every
/// compile, so it stays a few memmem passes with no allocation.
pub fn needs_std_load(src: &str) -> bool {
    STD_FNS.iter().any(|d| d.implemented && src.contains(d.trigger))
}

/// What namespace a canonical std path names its item in. A path
/// outside the tables below is not a std item lust knows by full
/// path: check rejects it instead of trusting its last segment
/// (rule zero: `std::option::Vec` must not mean `Vec`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StdPathKind {
    Type,
    Trait,
    Fn,
    Macro,
    Variant,
}

/// Canonical std paths lust can mean by full path, as
/// `crate/module/Name`. `std` re-exports the `core` and `alloc`
/// rows. Only rows whose item lust supports (or rejects by name,
/// like `HashMap`) belong here; a `use` rename of a row binds the
/// new name to the row's path (resolve), and check trusts a
/// written `std::...` path only when it is a row.
const STD_TYPE_PATHS: &[&str] = &[
    "core/option/Option",
    "std/option/Option",
    "core/result/Result",
    "std/result/Result",
    "alloc/string/String",
    "std/string/String",
    "alloc/vec/Vec",
    "std/vec/Vec",
    "alloc/boxed/Box",
    "std/boxed/Box",
    "alloc/rc/Rc",
    "std/rc/Rc",
    "alloc/rc/Weak",
    "std/rc/Weak",
    "alloc/sync/Arc",
    "std/sync/Arc",
    "core/cell/Cell",
    "std/cell/Cell",
    "core/cell/RefCell",
    "std/cell/RefCell",
    "core/cmp/Ordering",
    "std/cmp/Ordering",
    "std/process/ExitCode",
    "core/str/Utf8Error",
    "std/str/Utf8Error",
    "std/sync/mpsc/RecvError",
    "std/sync/mpsc/TryRecvError",
    "alloc/string/FromUtf8Error",
    "std/string/FromUtf8Error",
    "core/any/TypeId",
    "std/any/TypeId",
    "std/collections/HashMap",
    "std/collections/HashSet",
    "alloc/collections/BTreeMap",
    "std/collections/BTreeMap",
    "core/fmt/Formatter",
    "std/fmt/Formatter",
    "core/fmt/Arguments",
    "std/fmt/Arguments",
    "core/fmt/Result",
    "std/fmt/Result",
    "core/fmt/Error",
    "std/fmt/Error",
    "core/fmt/DebugStruct",
    "std/fmt/DebugStruct",
    "core/fmt/DebugTuple",
    "std/fmt/DebugTuple",
    "core/fmt/DebugList",
    "std/fmt/DebugList",
    "core/fmt/DebugSet",
    "std/fmt/DebugSet",
    "core/fmt/DebugMap",
    "std/fmt/DebugMap",
    "core/sync/atomic/Ordering",
    "std/sync/atomic/Ordering",
];

const STD_TRAIT_PATHS: &[&str] = &[
    "core/any/Any",
    "std/any/Any",
    "core/clone/Clone",
    "std/clone/Clone",
    "core/cmp/PartialEq",
    "std/cmp/PartialEq",
    "core/cmp/Eq",
    "std/cmp/Eq",
    "core/cmp/PartialOrd",
    "std/cmp/PartialOrd",
    "core/cmp/Ord",
    "std/cmp/Ord",
    "core/convert/From",
    "std/convert/From",
    "core/convert/Into",
    "std/convert/Into",
    "core/convert/AsRef",
    "std/convert/AsRef",
    "core/convert/AsMut",
    "std/convert/AsMut",
    "core/default/Default",
    "std/default/Default",
    "core/fmt/Debug",
    "std/fmt/Debug",
    "core/fmt/Display",
    "std/fmt/Display",
    "core/fmt/Write",
    "std/fmt/Write",
    "core/hash/Hash",
    "std/hash/Hash",
    "core/iter/Iterator",
    "std/iter/Iterator",
    "core/iter/IntoIterator",
    "std/iter/IntoIterator",
    "core/iter/FromIterator",
    "std/iter/FromIterator",
    "core/iter/ExactSizeIterator",
    "std/iter/ExactSizeIterator",
    "core/marker/Sized",
    "std/marker/Sized",
    "core/marker/Copy",
    "std/marker/Copy",
    "core/marker/Send",
    "std/marker/Send",
    "core/marker/Sync",
    "std/marker/Sync",
    "core/marker/Unpin",
    "std/marker/Unpin",
    "core/ops/Add",
    "std/ops/Add",
    "core/ops/Sub",
    "std/ops/Sub",
    "core/ops/Mul",
    "std/ops/Mul",
    "core/ops/Div",
    "std/ops/Div",
    "core/ops/Rem",
    "std/ops/Rem",
    "core/ops/Neg",
    "std/ops/Neg",
    "core/ops/Not",
    "std/ops/Not",
    "core/ops/BitAnd",
    "std/ops/BitAnd",
    "core/ops/BitOr",
    "std/ops/BitOr",
    "core/ops/BitXor",
    "std/ops/BitXor",
    "core/ops/Shl",
    "std/ops/Shl",
    "core/ops/Shr",
    "std/ops/Shr",
    "core/ops/AddAssign",
    "std/ops/AddAssign",
    "core/ops/SubAssign",
    "std/ops/SubAssign",
    "core/ops/MulAssign",
    "std/ops/MulAssign",
    "core/ops/DivAssign",
    "std/ops/DivAssign",
    "core/ops/RemAssign",
    "std/ops/RemAssign",
    "core/ops/BitAndAssign",
    "std/ops/BitAndAssign",
    "core/ops/BitOrAssign",
    "std/ops/BitOrAssign",
    "core/ops/BitXorAssign",
    "std/ops/BitXorAssign",
    "core/ops/ShlAssign",
    "std/ops/ShlAssign",
    "core/ops/ShrAssign",
    "std/ops/ShrAssign",
    "core/ops/Index",
    "std/ops/Index",
    "core/ops/IndexMut",
    "std/ops/IndexMut",
    "core/ops/Drop",
    "std/ops/Drop",
    "core/ops/Deref",
    "std/ops/Deref",
    "core/ops/DerefMut",
    "std/ops/DerefMut",
    "core/ops/Fn",
    "std/ops/Fn",
    "core/ops/FnMut",
    "std/ops/FnMut",
    "core/ops/FnOnce",
    "std/ops/FnOnce",
    "alloc/string/ToString",
    "std/string/ToString",
    "alloc/borrow/ToOwned",
    "std/borrow/ToOwned",
    "core/borrow/Borrow",
    "std/borrow/Borrow",
    "core/borrow/BorrowMut",
    "std/borrow/BorrowMut",
];

const STD_FN_PATHS: &[&str] = &[
    "core/mem/drop",
    "std/mem/drop",
    "core/mem/swap",
    "std/mem/swap",
    "core/mem/replace",
    "std/mem/replace",
    "core/mem/take",
    "std/mem/take",
    "core/mem/size_of",
    "std/mem/size_of",
    "core/mem/align_of",
    "std/mem/align_of",
    "core/mem/size_of_val",
    "std/mem/size_of_val",
    "core/cmp/max",
    "std/cmp/max",
    "core/cmp/min",
    "std/cmp/min",
    "core/str/from_utf8",
    "std/str/from_utf8",
    "std/env/args",
    "std/process/exit",
    "std/process/abort",
    "core/sync/atomic/fence",
    "std/sync/atomic/fence",
    "core/sync/atomic/compiler_fence",
    "std/sync/atomic/compiler_fence",
    "core/hint/spin_loop",
    "std/hint/spin_loop",
    "std/thread/spawn",
    "std/thread/current",
    "std/thread/yield_now",
    "std/thread/panicking",
    "std/thread/scope",
    "std/sync/mpsc/channel",
    "std/sync/mpsc/sync_channel",
    "std/thread/sleep",
];

const STD_MACRO_PATHS: &[&str] = &[
    "alloc/vec",
    "std/vec",
    "alloc/format",
    "std/format",
    "core/panic",
    "std/panic",
    "core/assert",
    "std/assert",
    "core/assert_eq",
    "std/assert_eq",
    "core/assert_ne",
    "std/assert_ne",
    "core/todo",
    "std/todo",
    "core/unreachable",
    "std/unreachable",
    "core/matches",
    "std/matches",
    "core/write",
    "std/write",
    "core/writeln",
    "std/writeln",
    "std/print",
    "std/println",
    "std/eprint",
    "std/eprintln",
];

const STD_VARIANT_PATHS: &[&str] = &[
    "core/option/Option/Some",
    "std/option/Option/Some",
    "core/option/Option/None",
    "std/option/Option/None",
    "core/result/Result/Ok",
    "std/result/Result/Ok",
    "core/result/Result/Err",
    "std/result/Result/Err",
    "core/cmp/Ordering/Less",
    "std/cmp/Ordering/Less",
    "core/cmp/Ordering/Equal",
    "std/cmp/Ordering/Equal",
    "core/cmp/Ordering/Greater",
    "std/cmp/Ordering/Greater",
    "core/sync/atomic/Ordering/Relaxed",
    "std/sync/atomic/Ordering/Relaxed",
    "core/sync/atomic/Ordering/Release",
    "std/sync/atomic/Ordering/Release",
    "core/sync/atomic/Ordering/Acquire",
    "std/sync/atomic/Ordering/Acquire",
    "core/sync/atomic/Ordering/AcqRel",
    "std/sync/atomic/Ordering/AcqRel",
    "core/sync/atomic/Ordering/SeqCst",
    "std/sync/atomic/Ordering/SeqCst",
    "std/sync/mpsc/TryRecvError/Empty",
    "std/sync/mpsc/TryRecvError/Disconnected",
];

/// True for a trait of the Rust 2024 prelude (and the prelude's
/// marker traits), which a bare name reaches with no `use`.
pub fn is_prelude_trait(name: &str) -> bool {
    matches!(
        name,
        "Copy"
            | "Send"
            | "Sized"
            | "Sync"
            | "Unpin"
            | "Drop"
            | "Fn"
            | "FnMut"
            | "FnOnce"
            | "AsMut"
            | "AsRef"
            | "From"
            | "Into"
            | "DoubleEndedIterator"
            | "ExactSizeIterator"
            | "Extend"
            | "IntoIterator"
            | "Iterator"
            | "Clone"
            | "Default"
            | "Eq"
            | "Ord"
            | "PartialEq"
            | "PartialOrd"
            | "ToOwned"
            | "ToString"
            | "TryFrom"
            | "TryInto"
            | "FromIterator"
            | "Future"
            | "IntoFuture"
    )
}

/// The std module of a non-prelude trait lust knows by name, for the
/// import hint of a bare name.
pub fn std_trait_module(name: &str) -> Option<&'static str> {
    STD_TRAIT_PATHS.iter().find_map(|row| {
        let mut parts = row.split('/');
        let (krate, module, n) = (parts.next()?, parts.next()?, parts.next()?);
        (krate == "std" && n == name && parts.next().is_none()).then_some(module)
    })
}

fn std_row_eq(row: &str, path: &[&str]) -> bool {
    row.split('/').eq(path.iter().copied())
}

/// The kind a full written path (`core/mem/drop`) names, if the
/// path is a canonical std path in the tables above.
pub fn std_path_kind(path: &[&str]) -> Option<StdPathKind> {
    let mut find = |rows: &[&str], kind| rows.iter().any(|r| std_row_eq(r, path)).then_some(kind);
    find(STD_TYPE_PATHS, StdPathKind::Type)
        .or_else(|| crate::ty::sync::SyncTy::by_path(path).map(|_| StdPathKind::Type))
        .or_else(|| find(STD_TRAIT_PATHS, StdPathKind::Trait))
        .or_else(|| find(STD_FN_PATHS, StdPathKind::Fn))
        .or_else(|| find(STD_MACRO_PATHS, StdPathKind::Macro))
        .or_else(|| find(STD_VARIANT_PATHS, StdPathKind::Variant))
}

/// True when `path` names a std module: a shipped crate root, or a
/// proper prefix of a canonical std path. A `use` rename of a
/// module binds the new name to this path.
pub fn std_is_module_path(path: &[&str]) -> bool {
    if path.is_empty() {
        return false;
    }
    if path.len() == 1 {
        return matches!(path[0], "std" | "core" | "alloc");
    }
    let prefix_of = |row: &str| {
        let mut parts = row.split('/');
        path.iter().all(|p| parts.next() == Some(p)) && parts.next().is_some()
    };
    [STD_TYPE_PATHS, STD_TRAIT_PATHS, STD_FN_PATHS, STD_MACRO_PATHS, STD_VARIANT_PATHS].iter().any(|rows| rows.iter().any(|r| prefix_of(r)))
        || crate::ty::sync::type_rows().iter().any(|r| prefix_of(r))
}

/// True for `std::primitive::u8` style paths: a primitive type
/// name under the `primitive` module of `std` or `core`.
pub fn std_is_primitive_path(path: &[&str]) -> bool {
    path.len() == 3
        && matches!(path[0], "std" | "core")
        && path[1] == "primitive"
        && matches!(
            path[2],
            "bool"
                | "char"
                | "str"
                | "i8"
                | "i16"
                | "i32"
                | "i64"
                | "i128"
                | "isize"
                | "u8"
                | "u16"
                | "u32"
                | "u64"
                | "u128"
                | "usize"
                | "f16"
                | "f32"
                | "f64"
                | "f128"
                | "never"
                | "unit"
                | "tuple"
                | "array"
                | "slice"
                | "pointer"
                | "reference"
                | "fn"
        )
}

/// True for the names of the primitive types a type path can name.
pub fn is_primitive_type_name(name: &str) -> bool {
    matches!(
        name,
        "bool" | "char" | "str" | "i8" | "i16" | "i32" | "i64" | "i128" | "isize" | "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "f16" | "f32" | "f64" | "f128"
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ty::GlobalTys;

    /// The table covers every lang item section 3.1 names, in enum order,
    /// with unique `#[lust_lang]` names.
    #[test]
    fn lang_table_covers_arch_list() {
        for (i, d) in LANG_ITEMS.iter().enumerate() {
            assert_eq!(d.item as usize, i, "row {} out of LangItem order", d.name);
            assert_eq!(lang_item_by_name(d.name), Some(d.item), "name {} must resolve once", d.name);
        }
        for name in [
            "option",
            "result",
            "string",
            "vec",
            "box",
            "rc",
            "arc",
            "unsafe_cell",
            "phantom_data",
            "iterator",
            "into_iterator",
            "drop",
            "deref",
            "fn",
            "sized",
            "send",
            "sync",
            "panic",
            "formatter",
            "exchange_malloc",
        ] {
            assert!(lang_item_by_name(name).is_some(), "missing lang item {name}");
        }
        // The Range family and the Fn family are one ARCH phrase each.
        assert_eq!(LANG_ITEMS.iter().filter(|d| d.name.starts_with("range")).count(), 6);
        assert_eq!(LANG_ITEMS.iter().filter(|d| d.name.starts_with("fn")).count(), 3);
    }

    /// Builtin-backed items resolve from `BuiltinDefs`, and every item
    /// marked required has a source today, so a load cannot fail on them.
    #[test]
    fn lang_items_resolve_builtins() {
        let g = GlobalTys::new();
        let b = g.builtins();
        let items = LangItems::from_builtins(b);
        assert_eq!(items.get(LangItem::Option), Some(b.option));
        assert_eq!(items.get(LangItem::Result), Some(b.result));
        assert_eq!(items.get(LangItem::String), Some(b.string));
        assert_eq!(items.get(LangItem::Vec), Some(b.vec));
        assert_eq!(items.get(LangItem::Box), Some(b.boxed));
        assert_eq!(items.get(LangItem::Rc), Some(b.rc));
        assert!(items.required_missing().is_empty(), "required items must resolve: {:?}", items.required_missing());
    }

    /// The canonical std path rows are unique across kinds, and the
    /// lookup answers only for exact rows (never a wrong module).
    #[test]
    fn std_path_rows_are_unique_and_exact() {
        let all: Vec<&str> = [STD_TYPE_PATHS, STD_TRAIT_PATHS, STD_FN_PATHS, STD_MACRO_PATHS, STD_VARIANT_PATHS]
            .iter()
            .flat_map(|rows| rows.iter().copied())
            .collect();
        for (i, a) in all.iter().enumerate() {
            assert!(!a.is_empty());
            assert!(all.iter().skip(i + 1).all(|b| b != a), "duplicate std path row {a}");
        }
        assert_eq!(std_path_kind(&["std", "option", "Option"]), Some(StdPathKind::Type));
        assert_eq!(std_path_kind(&["core", "mem", "drop"]), Some(StdPathKind::Fn));
        assert_eq!(std_path_kind(&["std", "option", "Vec"]), None);
        assert_eq!(std_path_kind(&["core", "vec", "Vec"]), None);
        assert!(std_is_module_path(&["std", "mem"]));
        assert!(std_is_module_path(&["std"]));
        assert!(!std_is_module_path(&["std", "mem", "drop"]));
        assert!(!std_is_module_path(&["std", "nope"]));
    }

    /// Registry rows are well formed: unique names, no empty allow list,
    /// and only implemented rows carry a C symbol.
    #[test]
    fn intrinsic_registry_is_well_formed() {
        for (i, d) in INTRINSICS.iter().enumerate() {
            assert_eq!(intrinsic_by_name(d.name), Some(i as u32), "duplicate intrinsic {}", d.name);
            assert!(!d.allowed.is_empty(), "intrinsic {} allows no crate", d.name);
            if d.implemented {
                assert!(!d.c_symbol.is_empty(), "implemented intrinsic {} needs a C symbol", d.name);
            }
        }
        // Every group in the section 3.2 table has at least one row.
        for name in [
            "alloc",
            "memcpy",
            "ptr_read",
            "fmt_f64",
            "panic",
            "thread_spawn",
            "mutex_lock",
            "atomic_load",
            "clock_now_raw",
            "fd_read",
            "exit",
            "arena_alloc",
        ] {
            assert!(intrinsic_by_name(name).is_some(), "missing intrinsic {name}");
        }
    }

    /// Privilege follows the row: user source (None) gets nothing, each
    /// adapter only its own cores, and `exit` is std-only.
    #[test]
    fn intrinsic_privilege_follows_the_row() {
        let exit = intrinsic(intrinsic_by_name("exit").unwrap());
        assert!(exit.allows(Some(ShippedCrate::Std)));
        assert!(!exit.allows(None));
        assert!(!exit.allows(Some(ShippedCrate::Core)));
        let arena = intrinsic(intrinsic_by_name("arena_alloc").unwrap());
        assert!(arena.allows(Some(ShippedCrate::Bumpalo)));
        assert!(!arena.allows(Some(ShippedCrate::Std)));
        assert!(!arena.allows(Some(ShippedCrate::Memchr)));
    }

    /// Shipped crate hashes are distinct, so privilege by disambiguator
    /// cannot alias two crates.
    #[test]
    fn shipped_crate_hashes_are_distinct() {
        let mut hashes: Vec<u64> = ShippedCrate::ALL.iter().map(|k| k.stable_hash().0).collect();
        hashes.sort_unstable();
        hashes.dedup();
        assert_eq!(hashes.len(), ShippedCrate::ALL.len());
    }

    /// The load trigger fires only for implemented source std fns.
    #[test]
    fn std_load_trigger() {
        assert!(needs_std_load("fn main() { std::process::exit(0); }"));
        assert!(!needs_std_load("fn main() { std::process::abort(); }"));
        assert!(!needs_std_load("fn main() { println!(\"hi\"); }"));
    }
}
