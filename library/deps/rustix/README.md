# Adapter: rustix 1.1.5

Lust adapter crate (docs/ARCH.md section 3.6) for the subset
ts-rust uses, over the sysx runtime shims (src/runtime/sysx.c).
Gate: `scripts/test-adapters.sh rustix`.

## Implemented, same results as upstream

- `io`: `Errno` (Linux numbers; Debug and Display are std's
  `io::Error` forms, as upstream), `Result`, `read`, `write`.
- `fd`: std's `BorrowedFd`, `OwnedFd`, `AsFd`, `AsRawFd`,
  `IntoRawFd`, `FromRawFd`, `RawFd`, re-exported as upstream
  does with the `std` feature (lust std has `std::os::fd`).
- `fs`: `OFlags`, `Mode`, `AtFlags`, `Access`, `StatxFlags`,
  `CWD`, `FileType`, `Stat`, `Statx`, `StatxTimestamp`,
  `Timespec`, `Timestamps`, `UTIME_NOW`, `UTIME_OMIT`, `open`,
  `openat`, `fstat`, `statat`, `statx`, `accessat`, `utimensat`,
  `mknodat`, `fcntl_getfl`, `fcntl_setfl`.
- `process`: `Pid`, `RawPid`, `Signal` (named consts,
  `from_named_raw`, upstream's quoted Debug forms), `getpid`,
  `getppid`, `kill_process`, `test_kill_process`,
  `set_parent_process_death_signal`, `Resource`, `Rlimit`,
  `getrlimit`, `setrlimit`.
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
- `BorrowedFd::borrow_raw` and `FromRawFd::from_raw_fd` are
  safe fns in lust std (it cannot spell `unsafe fn`);
  upstream's are `unsafe`. Calling them in safe code is a
  false accept with the same result.
- `poll` runs through poll(2) with the timeout rounded up to
  whole milliseconds; upstream uses ppoll. A timed-out wait
  can run up to a millisecond long.
- The flag types' Debug forms are the derived tuple forms,
  not upstream's flag-name lists. A program that prints an
  `OFlags` with `{:?}` prints a different text.
- No `impl std::error::Error for Errno` (the core::error
  overlay is spliced only when user code names it). The
  `From<Errno> for io::Error` conversion ts-rust uses is here.

## Rejected (lust error, never a different answer)

- `RawDir` and its entry type,
  every other module (`net`, `mount`, `thread`, `time`,
  `io_uring`, `pty`, `rand`, `shm`, `system`, `fs::inotify`
  and fanotify, and the rest), the `fs` and `process` items
  beyond the lists above (wait and exec forms included), and
  layout queries on every adapter type.
