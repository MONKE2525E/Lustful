// `std::process` (W-SHIM): the process id, exit, and abort. The file is
// `process_os.rs` because `process.rs` is the compiler's own std source
// for `exit` (src/stdload.rs); `platform.rs` names this one with
// `#[path]`. Both exit paths call the same runtime intrinsic.

/// The OS process id.
pub fn id() -> u32 {
    core::intrinsics::sys_getpid()
}

/// Terminates the process with the given exit code. Destructors do not
/// run; buffered stdout is flushed first (the intrinsic does this).
pub fn exit(code: i32) -> ! {
    core::intrinsics::exit(code)
}
