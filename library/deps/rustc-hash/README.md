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
- Maps and sets with these hashers print the same iteration order and
  capacity as the real crate (tests/adapters/crates/rustc-hash,
  maps_typed).
- Two spellings differ from upstream with the same meaning: `write`
  calls the 64-bit body of `write_u64` directly, and the multiplier is
  named `MULTIPLIER`, not `K` (private; with `K`, lust resolves the
  type parameter `K` of the re-exported `FxHashMapSeed<K, V>` to the
  const).

## Not usable through lust yet (lust rejects)

- An associated fn called through an alias, such as
  `FxHashMap::default()` (L0101; W-CHECK-G). `HashMap::default()` with
  the alias as the type works.
- Hashing a value whose `Hash` impl is written by hand (L0640; W-STD-B).

## Rejected (lust error, never a different answer)

- Features `nightly` and `rand` (`FxRandomState`, `FxHashMapRand`).
