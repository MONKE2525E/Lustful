// `core::mem` overlay (docs/ARCH.md section 3.1; TRIAGE T5):
// `MaybeUninit`'s Debug. The type itself is a synthetic std Adt
// (check/collect.rs registers it; `uninit`, `new`, `write`, and
// the pointer accessors are compiler builtins in check/iter.rs),
// so only the impl lives here. `core::mem::X` and `std::mem::X`
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
