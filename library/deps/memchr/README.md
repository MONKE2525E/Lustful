# Adapter: memchr 2.8.2

Lust adapter crate (docs/ARCH.md section 3.6). Dev builds compile it in
place of the registry package memchr 2.8.2; release builds use the real
crate through Cargo. Gate: `scripts/test-adapters.sh memchr` (the real
crate is the oracle).

## Implemented, same results as upstream

- `memchr`, `memchr2`, `memchr3`, `memrchr`, `memrchr2`, `memrchr3`.
- `memchr_iter`, `memchr2_iter`, `memchr3_iter` and `Memchr`, `Memchr2`,
  `Memchr3` (`new`, `next`, `Clone`).
- `memmem::{find, rfind, find_iter, rfind_iter}`, `Finder` and
  `FinderRev` (`new`, `find`/`rfind`, `find_iter`/`rfind_iter`,
  `into_owned` with feature `alloc`, `as_ref`, `needle`, `Clone`),
  `FindIter` and `FindRevIter` (`next`, `into_owned`).
- Features: `alloc`, `default`, `libc`, `std`, `use_std`.

One-needle searches and forward substring search go through one
intrinsic each (`memchr`, `memrchr`, `memmem`; libc memchr and memcmp in
src/runtime/deps.c). Two- and three-needle searches and reverse
substring search are loops in source. Upstream's SIMD paths change
speed, not answers.

## Rejected (lust error, never a different answer)

- `size_hint`, `next_back`, `count`, `rev`, and other `Iterator` extras
  on the iterators: lust's `Iterator` has only `next` and `for` today
  (L0104). Upstream overrides `size_hint` and implements
  `DoubleEndedIterator`; add both here when std gains them
  (tests/adapters/crates/memchr/iter_hint.rs catches the gap).
- `memrchr_iter`, `memrchr2_iter`, `memrchr3_iter` (`iter::Rev`), `arch`,
  `FinderBuilder`, `Prefilter`: not in the adapter (L0506 at the use).
- `Debug` on every type (upstream prints raw pointers).
- `size_of` and other layout queries on every type here (L0652): the
  layouts differ from upstream's.
- Feature `logging` (L0508).
