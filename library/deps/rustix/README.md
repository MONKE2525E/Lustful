# Adapter: rustix 1.1.5

Lust adapter crate (docs/ARCH.md section 3.6) for the subset
ts-rust uses, over the sysx runtime shims (src/runtime/sysx.c).
Gate: `scripts/test-adapters.sh rustix`.

## Implemented, same results as upstream

- `io`: `Errno` (Linux numbers and upstream's names, e.g.
  `ACCESS`; Debug and Display are std's `io::Error` forms, as
  upstream), `Result`, `read` (over `buffer::Buffer`: `&mut [u8]`,
  `&mut [u8; N]`, `&mut Vec<u8>`), `write`.
- `fd`: std's `BorrowedFd`, `OwnedFd`, `AsFd`, `AsRawFd`,
  `IntoRawFd`, `FromRawFd`, `RawFd`, re-exported as upstream
  does with the `std` feature (lust std has `std::os::fd`).
- `fs`: `OFlags`, `Mode`, `AtFlags`, `Access`, `StatxFlags`,
  `StatVfsMountFlags`, `CWD`, `FileType`, `Stat`, `Statx`,
  `StatxTimestamp`, `StatVfs`, `Timespec`, `Timestamps`,
  `UTIME_NOW`, `UTIME_OMIT`, `open`, `openat`, `fstat`,
  `statat`, `statx`, `statvfs`, `fstatvfs`, `accessat`,
  `utimensat`, `mknodat`, `fcntl_getfl`, `fcntl_setfl`.
- `fs::inotify`: `CreateFlags`, `WatchFlags`, `ReadFlags`,
  `init`, `add_watch`, `remove_watch`. Events are read with
  `io::read` on the fd, as ts-rust does.
- `process`: `Pid`, `RawPid`, `Signal` (named consts,
  `from_named_raw`, upstream's quoted Debug forms), `getpid`,
  `getppid`, `kill_process`, `test_kill_process`,
  `set_parent_process_death_signal`, `Resource`, `Rlimit`,
  `getrlimit`, `setrlimit`.
- Modules and std-only items follow upstream's feature gates
  (`fs`, `path`, `event`, `pipe`, `process`, `stdio`,
  `termios`; `std` for the `io::Error` forms, `stdio::stdin`
  and kin, `Pid::from_child`, and the std path `Arg` forms).
- `pipe`: `PipeFlags`, `pipe`, `pipe_with`. `event`: `PollFd`,
  `PollFlags`, `poll`. `stdio`: `stdin`, `stdout`, `stderr`,
  `dup2_stdin`, `dup2_stdout`, `dup2_stderr`. `termios`:
  `Winsize`, `tcgetwinsize`. `path`: the `Arg` forms for
  `&str`, `String`, `&OsStr`, `&OsString`, `&Path`, `&PathBuf`,
  and `PathBuf`.
- Features `default`, `std`, `alloc`, `fs`, `process`,
  `termios`, `pipe`, `event`, `stdio`: the set ts-rust enables.

## Known differences

- `Pid` and `Signal` store a plain `i32`, not a `NonZeroI32`
  (no `as_raw_nonzero`).
- `poll` runs through poll(2) with the timeout rounded up to
  whole milliseconds; upstream uses ppoll. A timed-out wait
  can run up to a millisecond long.
- No `impl std::error::Error for Errno` (the core::error
  overlay is spliced only when user code names it). The
  `From<Errno> for io::Error` conversion ts-rust uses is here.

## Rejected (lust error, never a different answer)

- `RawDir`, its entry type, and `fs::inotify::Reader`: their
  buffer type is `core::mem::MaybeUninit`, which lust does
  not have yet (the layout engine knows its size only). The
  `sys_x_getdents` intrinsic RawDir needs is in place.
  Every other module (`net`, `mount`, `thread`, `time`,
  `io_uring`, `pty`, `rand`, `shm`, `system`, and the rest),
  the `fs` and `process` items
  beyond the lists above (wait and exec forms included), and
  layout queries on every adapter type.
- Debug of the flag types (upstream prints flag-name lists),
  upstream's `Arg` methods (`as_str`, `into_with_c_str`, ...;
  a user `Arg` impl rejects), `Statx::stx_attributes` (its
  `StatxAttributes` type is not here), and the `MaybeUninit`
  and `SpareCapacity` buffer forms.
