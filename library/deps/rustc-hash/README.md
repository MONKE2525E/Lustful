# Adapter: rustc-hash 2.1.2 (pending)

The adapter is written and checked against the real crate with rustc
(pending/README.md), but lust cannot compile it yet. Until then it waits
in `pending/`, and a dependency on rustc-hash is L0508 ("no lust adapter
yet"). The corpus is tests/adapters/crates/rustc-hash (UNSUPPORTED today).

Blocked on: the std `Hasher` and `BuildHasher` traits and `HashMap` /
`HashSet` with a custom `S` (W-STD-B), and generic type aliases with
associated fn paths such as `FxHashMap::default()` (W-CHECK-G).

To activate: move `pending/Cargo.toml` and `pending/src` here, then run
`LUST=target/release/lust scripts/test-adapters.sh rustc-hash`.
