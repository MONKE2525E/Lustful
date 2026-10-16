// `nix::sys`: only the fanotify and prctl modules are here.

#[cfg(feature = "fanotify")]
pub mod fanotify;
#[cfg(feature = "process")]
pub mod prctl;
