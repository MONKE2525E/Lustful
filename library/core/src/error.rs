// `core::error` (docs/ARCH.md section 3.1; W-STD-C phase 2): the
// `Error` trait. `std::error::Error` is this trait, as in std;
// `core::error::X` and `std::error::X` walk into this module
// (`STD_MODULES` in src/stdmods.rs).
//
// Adapted from rust-lang/rust 1.99 `core/src/error.rs`. Not here:
// `source` and `cause`, whose signatures name `dyn Error` (a dyn
// object with the std supertraits `Debug` and `Display` is
// L0702 today; that is the dyn.std work); the unstable generic
// member access items (`Request`, `provide`); and the
// `Box<dyn Error>` conversions of `alloc`.

/// The trait of error values: `Debug` and `Display`.
pub trait Error: core::fmt::Debug + core::fmt::Display {
    /// A short text form. Deprecated in std; `Display` is the
    /// current one. The default text is std's.
    fn description(&self) -> &str {
        "description() is deprecated; use Display"
    }
}

// core's conversion errors (fx-tryfrom): `Error` with the default
// `description`, as in core.
impl Error for core::num::TryFromIntError {}
impl Error for core::char::CharTryFromError {}
impl Error for core::char::TryFromCharError {}
impl Error for core::convert::Infallible {}
