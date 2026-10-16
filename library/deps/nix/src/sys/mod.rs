// `nix::sys`: only the fanotify, prctl and signal modules are here.

#[cfg(feature = "fanotify")]
pub mod fanotify;
#[cfg(feature = "process")]
pub mod prctl;
pub mod signal;
