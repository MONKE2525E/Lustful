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
    LangItemDef { item: L::Box, name: "box", krate: C::Alloc, required: false },
    LangItemDef { item: L::Rc, name: "rc", krate: C::Alloc, required: false },
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
/// typed pointer API is source in std wrappers.
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
    IntrinsicDef {
        name: "memchr",
        c_symbol: "lust_memchr",
        params: &[S::U32, S::Ptr, S::Usize],
        ret: S::Ptr,
        allowed: &[C::Memchr],
        implemented: false,
    },
    IntrinsicDef {
        name: "memrchr",
        c_symbol: "lust_memrchr",
        params: &[S::U32, S::Ptr, S::Usize],
        ret: S::Ptr,
        allowed: &[C::Memchr],
        implemented: false,
    },
    IntrinsicDef {
        name: "memmem",
        c_symbol: "lust_memmem",
        params: &[S::Ptr, S::Usize, S::Ptr, S::Usize],
        ret: S::Ptr,
        allowed: &[C::Memchr],
        implemented: false,
    },
    IntrinsicDef {
        name: "xxh3_64",
        c_symbol: "lust_xxh3_64",
        params: &[S::Ptr, S::Usize],
        ret: S::U64,
        allowed: &[C::XxhashRust],
        implemented: false,
    },
    IntrinsicDef {
        name: "xxh3_128",
        c_symbol: "lust_xxh3_128",
        params: &[S::Ptr, S::Usize, S::Ptr],
        ret: S::Unit,
        allowed: &[C::XxhashRust],
        implemented: false,
    },
    IntrinsicDef {
        name: "ryu_js_fmt_f64",
        c_symbol: "lust_ryu_js_fmt_f64",
        params: &[S::F64, S::Ptr],
        ret: S::Unit,
        allowed: &[C::RyuJs],
        implemented: false,
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

/// True if `src` can mention an implemented source std fn, so the driver
/// must load std before it compiles. A plain byte scan: it runs on every
/// compile, so it stays a few memmem passes with no allocation.
pub fn needs_std_load(src: &str) -> bool {
    STD_FNS.iter().any(|d| d.implemented && src.contains(d.trigger))
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
        assert_eq!(items.get(LangItem::Box), None);
        assert!(items.required_missing().is_empty(), "required items must resolve: {:?}", items.required_missing());
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
