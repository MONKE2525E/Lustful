# Adapter: nix 0.31.3

Lust adapter crate (docs/ARCH.md section 3.6) for the two prctl
forms ts-rust's thp_guard.rs uses and the fanotify forms
fswatch/unix.rs uses. Gate: `scripts/test-adapters.sh nix`.

## Implemented, same results as upstream

- `sys::prctl::set_thp_disable` and `get_thp_disable` over
  prctl (the sysx shim), with nix's `Result` form.
- `sys::fanotify` (feature `fanotify`): `Fanotify::init` and
  `Fanotify::mark` over fanotify_init(2) and fanotify_mark(2),
  the `MaskFlags`, `InitFlags`, `EventFFlags`, and `MarkFlags`
  flag types, `FANOTIFY_METADATA_VERSION`, and the `AsFd`,
  `AsRawFd`, `FromRawFd`, and `From<Fanotify> for OwnedFd`
  impls. Events are read by callers as raw bytes on the fd,
  as ts-rust does.
- `NixPath` for `[u8]`, `str`, `OsStr`, `CStr`, `Path`, and
  `PathBuf` (interior NUL is EINVAL, as upstream).
- `sys::prctl` needs feature `process` and `sys::fanotify`
  feature `fanotify`, as upstream.
- `errno::Errno` (also `nix::Error`): upstream's Linux
  `#[repr(i32)]` enum with every variant, so `err as i32`
  works; variant-name Debug, `EPERM: Operation not permitted`
  Display from nix's `desc` table, `from_raw` (unknown codes
  are `UnknownErrno`, as upstream), and the `io::Error`
  conversions.

## Rejected (lust error, never a different answer)

- Everything else in nix, including fanotify `read_events`,
  `FanotifyEvent`, `write_response`, and the Errno forms that
  read or write the C errno (`last`, `set`, `clear`,
  `result`). Layout queries on adapter types reject.
