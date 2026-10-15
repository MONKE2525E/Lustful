// Lust adapter for nix 0.31.3 (docs/ARCH.md section 3.6): only
// the prctl THP forms ts-rust's thp_guard.rs uses, plus the
// Errno type they return. Everything else in nix is absent and
// rejects in lust (README).

pub mod errno;
pub mod sys;

pub use errno::Errno;

/// The nix error type (an alias of `Errno`, as upstream).
pub type Error = Errno;

/// A specialized `Result` type for nix APIs.
pub type Result<T> = core::result::Result<T, Errno>;
