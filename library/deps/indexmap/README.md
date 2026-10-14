# Adapter: indexmap 2.14.0 (pending)

The adapter is written and checked against the real crate with rustc
(pending/README.md), but lust cannot compile it yet. Until then it waits
in `pending/`, and a dependency on indexmap is L0508 ("no lust adapter
yet"). The corpus is tests/adapters/crates/indexmap (UNSUPPORTED today).

Blocked on: `Iterator::size_hint` overrides, `DoubleEndedIterator`,
`ExactSizeIterator`, `Extend`, the `std::vec::IntoIter` type name,
`BuildHasher::hash_one` in generic code, and `RandomState` (W-STD-A,
W-STD-B); generic parameter defaults (`S = RandomState`, W-CHECK-G).

To activate: move `pending/Cargo.toml` and `pending/src` here, update
tests/crates/adapter-missing and docs/errors/L0508.md (both use indexmap
as the crate with no adapter), then run
`LUST=target/release/lust scripts/test-adapters.sh indexmap`.
