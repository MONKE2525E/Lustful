// `core::mem` overlay (docs/ARCH.md section 3.1; TRIAGE T5, R2):
// `MaybeUninit`'s Debug and `ManuallyDrop`. `MaybeUninit` itself is
// a synthetic std Adt (check/collect.rs registers it; `uninit`,
// `new`, `write`, and the pointer accessors are compiler builtins in
// check/iter.rs), so only its impl lives here. `core::mem::X` and `std::mem::X`
// walk into this module only for the names it defines
// (`STD_MODULES` in src/stdmods.rs).
//
// Lust std source, adapted from rust-lang/rust 1.99
// `core/src/mem/maybe_uninit.rs`: Debug prints the type name and
// never the (possibly uninitialized) value.

impl<T> core::fmt::Debug for core::mem::MaybeUninit<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "MaybeUninit<{}>", core::any::type_name::<T>())
    }
}

// Lust std source, adapted from rust-lang/rust 1.99
// `core/src/mem/manually_drop.rs` and `maybe_dangling.rs`. The
// compiler knows `ManuallyDrop` by its path
// (`Program::is_manually_drop_adt`): it has no drop glue, so the
// value inside is never dropped, and layout queries see it as
// repr(transparent) over `T` with `T`'s niche. The unsafe fns
// (`drop`, `take`) are not here: lust has no `unsafe`. No
// `T: ?Sized` yet.

/// A wrapper that stops the compiler from dropping its value. Core writes
/// `PartialEq`, `Eq`, `PartialOrd`, `Ord`, and `Hash` by hand over the one
/// field (and `StructuralPartialEq`); derives over the one field are the
/// same impls, and lust's sort, map keys, and const patterns take them.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ManuallyDrop<T> {
    value: MaybeDangling<T>,
}

/// Core's (unstable) field type of `ManuallyDrop`. Private here, so
/// user code cannot name it; it shows in `ManuallyDrop`'s Debug text
/// as in core (`ManuallyDrop { value: MaybeDangling(5) }`).
#[derive(Debug, Copy, Clone, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
struct MaybeDangling<T>(T);

impl<T> ManuallyDrop<T> {
    /// Wraps `value`, so it is not dropped.
    pub const fn new(value: T) -> ManuallyDrop<T> {
        ManuallyDrop { value: MaybeDangling(value) }
    }

    /// Takes the value out, so it is dropped again as usual.
    pub const fn into_inner(slot: ManuallyDrop<T>) -> T {
        slot.value.0
    }
}

impl<T> core::ops::Deref for ManuallyDrop<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.value.0
    }
}

impl<T> core::ops::DerefMut for ManuallyDrop<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.value.0
    }
}
