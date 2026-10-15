// Lust adapter for rustix 1.1.5 (docs/ARCH.md section 3.6): the
// subset ts-rust's core files use, over the sys_x intrinsics
// (src/runtime/sysx.c) and the shared sys_fd intrinsics. Here:
// `io` (Errno with std's error texts, read, write), `fd`
// (BorrowedFd, OwnedFd, AsFd, AsRawFd, IntoRawFd), `fs` (the
// flag types, CWD, open, openat, fstat, statat, statx, accessat,
// utimensat, mknodat, fcntl_getfl and fcntl_setfl, FileType,
// Stat, Statx, Timespec and Timestamps), `process` (Pid, Signal,
// kill and rlimit forms), `termios` (tcgetwinsize), and `path`
// (the Arg trait of the path-taking calls).
//
// Not here (see README.md): RawDir (lust std has no CStr yet),
// the event, pipe, stdio, net, mount, thread, time, and other
// modules, the `fs` items beyond the list above, and every
// `unsafe` form. Such code rejects in lust. The fd types are
// this crate's own, not std's: code that stores a rustix
// `OwnedFd` in a `std::os::fd::OwnedFd` (one osvfs form) still
// rejects, as README.md lists.
//
// Linux x86_64 values throughout, as the lust target is.

pub mod event;
pub mod fd;
pub mod fs;
pub mod io;
pub mod path;
pub mod pipe;
pub mod process;
pub mod stdio;
pub mod termios;

/// Little-endian u64 field `i` of a sysx record.
fn rec_u64(rec: &[u8], i: usize) -> u64 {
    let mut v = 0u64;
    let base = i * 8;
    for k in 0..8 {
        v |= (rec[base + k] as u64) << (8 * k);
    }
    v
}

/// Little-endian i64 field `i` of a sysx record.
fn rec_i64(rec: &[u8], i: usize) -> i64 {
    rec_u64(rec, i) as i64
}
