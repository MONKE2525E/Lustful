# Adapter: tikv-jemalloc-ctl 0.7.0

Lust adapter crate (docs/ARCH.md section 3.6) for the by-name
mallctl form ts-rust uses. Gate:
`scripts/test-adapters.sh tikv-jemalloc-ctl`.

## Implemented, same results as upstream

- `Name`, `AsName` (for `[u8]` and `str`, with upstream's
  empty and non-null-terminated panics), `Name::value_type_str`,
  `Name::as_bytes`, Debug and Display of `Name`.
- `Access<T> for Name` for `u32`, `u64`, `usize`, `isize`,
  `bool`, `&'static [u8]`, and `&'static str`, with upstream's
  size rules: a key read or written at the wrong size is
  `EINVAL`, an unknown key is `ENOENT`, a write to a read-only
  key is `EPERM`, and an arena index that does not exist is
  `EFAULT`. `Error` Debug and Display texts are upstream's.
- Keys: `version` (the exact jemalloc 5.3.1 string of
  tikv-jemalloc-sys 0.7.1, trailing null included), `epoch`
  (starts at 1, each write or update advances it and update
  returns the new value), `thread.tcache.enabled` (a per-thread
  bool, initially true), `thread.arena`, and `opt.narenas`.
- The `epoch` and `version` modules (`read`, `write`, `update`,
  `epoch::advance`). Features `default`, `use_std`, and
  `disable_initial_exec_tls`.

## Known differences (output that cannot match)

Real jemalloc answers depend on its build, `MALLOC_CONF`, and
the machine, so no adapter over a different allocator can match
them in general. The lust runtime has one allocator arena:

- `opt.narenas` reads 1 (jemalloc defaults to 4 per CPU;
  ts-rust's bins set 4). A program that prints it prints a
  different number under lust.
- Every thread's `thread.arena` reads 0 and only the write of
  0 succeeds. Jemalloc gives new threads later arenas in turn.
  Programs that read an arena and write it back on another
  thread (the ts-rust use) behave the same; a program that
  prints the arena of a spawned thread can differ.

## Adapter-only form

- `AsName` is also implemented for `[u8; N]`, because lust's
  method probe does not yet unsized-autoderef a byte array to
  `[u8]` for trait methods. Upstream has only the `[u8]` impl;
  the array impl forwards to it, so every call upstream accepts
  behaves the same. A UFCS call that names the array impl
  directly (`<[u8; 3] as AsName>::name(..)`) is accepted here
  and rejected upstream. That is a known false accept in this
  adapter until the checker learns the autoderef step.

## Rejected or in error (never a fake count)

- Accounting keys (`stats.*`, `arenas.*`, and kin) answer
  `ENOENT` by name. With no `stats` feature, upstream's
  jemalloc build also has no `stats.allocated`; other stats
  keys exist upstream and do not here.
- The typed key modules other than `epoch` and `version`
  (`opt`, `thread`, `stats`, `arenas`, `config`, `raw`,
  `stats_print`, `profiling`), `Mib` and `MibStr`, and layout
  queries on `Error` and `Name` reject in lust.
- The `stats` and `profiling` features reject at resolve
  (L0508).
