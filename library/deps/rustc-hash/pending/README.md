# Adapter: rustc-hash 2.1.2

Lust adapter crate (docs/ARCH.md section 3.6). Upstream is already only
aliases plus the hasher, so this is upstream's stable code with the byte
reads written out. Gate: `scripts/test-adapters.sh rustc-hash`.

## Implemented, same results as upstream

- `FxHasher` (`with_seed`, `default`, every `write_*`, `finish`),
  `FxBuildHasher`, `FxSeededState`, and the `FxHashMap`, `FxHashSet`,
  `FxHashMapSeed`, `FxHashSetSeed` aliases over std's maps (feature
  `std`). Checked with rustc against the real crate on 20,000 random
  hasher cases; hash values are upstream's test vectors.
- `FxHasher`, `FxBuildHasher`, and `FxSeededState` are exact-layout.
- On W-STD-B's HashMap (branch b/w-std-b, fb05355b), maps with String,
  tuple (seeded), and Vec<u8> keys print the same order and capacity as
  the real crate (the aliases were left out there: that tree has no
  generic aliases).
- One spelling differs from upstream with the same meaning: `write`
  calls the 64-bit body of `write_u64` directly.

## Rejected (lust error, never a different answer)

- Features `nightly` and `rand` (`FxRandomState`, `FxHashMapRand`).
