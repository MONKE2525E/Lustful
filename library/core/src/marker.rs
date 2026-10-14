// `core::marker` overlay (docs/ARCH.md section 3.1; W-STD-C):
// `PhantomData`. The other `core::marker` items (Send, Sync, Copy,
// Sized, Unpin) stay compiler-known; `std::marker::X` and
// `core::marker::X` walk into this module only for the names it
// defines (`STD_MODULES` in src/stdmods.rs).
//
// The compiler treats `PhantomData<T>` as holding a `T` for auto
// traits, unused-parameter checks, and regions, while its value is
// zero-sized (`Program::is_phantom_adt`). Not here yet: `Debug` (it
// prints `type_name::<T>()`, which lust lacks), `Hash` (no `Hasher`
// trait on next yet), and `T: ?Sized`.

/// A zero-sized type that acts as if it owns a `T`. Std's impls have no
/// bounds on `T`; the derives here give the same answers, because the
/// struct has no fields (lust derives on a generic Adt ask only the
/// fields).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct PhantomData<T>;
