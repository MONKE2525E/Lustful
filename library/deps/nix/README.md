# Adapter: nix 0.31.3

Lust adapter crate (docs/ARCH.md section 3.6) for the two prctl
forms ts-rust's thp_guard.rs uses. Gate:
`scripts/test-adapters.sh nix`.

## Implemented, same results as upstream

- `sys::prctl::set_thp_disable` and `get_thp_disable` over
  prctl (the sysx shim), with nix's `Result` form.
- `Errno` (also `nix::Error`): the common Linux codes as
  constants, upstream's `EPERM: Operation not permitted`
  Display form and variant-name Debug for the listed codes,
  and the `io::Error` conversion.

## Rejected (lust error, never a different answer)

- Everything else in nix. An Errno code outside the adapter's
  table Debug-prints as `UnknownErrno` where upstream has a
  variant name; layout queries on `Errno` reject.
