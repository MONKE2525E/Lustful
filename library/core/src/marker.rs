// `core::marker` overlay (docs/ARCH.md section 3.1; W-STD-C):
// `PhantomData`. The other `core::marker` items (Send, Sync, Copy,
// Sized, Unpin) stay compiler-known; `std::marker::X` and
// `core::marker::X` walk into this module only for the names it
// defines (`STD_MODULES` in src/stdmods.rs).
//
// The compiler treats `PhantomData<T>` as holding a `T` for auto
// traits, unused-parameter checks, and regions, while its value is
// zero-sized (`Program::is_phantom_adt`). Not here yet: `T: ?Sized`.

/// A zero-sized type that acts as if it owns a `T`. Std's impls have no
/// bounds on `T`; the derives here give the same answers, because the
/// struct has no fields (lust derives on a generic Adt ask only the
/// fields).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct PhantomData<T>;

// Lust std source, adapted from rust-lang/rust 1.99 `core/src/marker.rs`
// (`impl Hash`) and `core/src/fmt/mod.rs` (`impl Debug`): no bounds on
// `T`; Hash writes nothing, Debug prints the type name.

impl<T> core::hash::Hash for PhantomData<T> {
    fn hash<H: core::hash::Hasher>(&self, _: &mut H) {}
}

impl<T> core::fmt::Debug for PhantomData<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "PhantomData<{}>", core::any::type_name::<T>())
    }
}
