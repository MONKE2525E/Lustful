# Adapter: indexmap 2.14.0 (pending)

The adapter is written and checked against the real crate with rustc
(pending/README.md), but lust cannot compile it yet. Until then it waits
in `pending/`, and a dependency on indexmap is L0508 ("no lust adapter
yet"). The corpus is tests/adapters/crates/indexmap (UNSUPPORTED today).

Blocked on: `Iterator::size_hint` overrides, `DoubleEndedIterator`,
`ExactSizeIterator`, `Extend`, `BuildHasher::hash_one` in generic
code, and `RandomState` (W-STD-B, in its queue); `into_iter()` on a
generic `I: IntoIterator` parameter, which `Extend` and `FromIterator`
need (W-STD-B or W-TRAITS).

On next plus W-STD-B's queue (a scratch merge) with `extend` and
`from_iter` cut, the adapter compiles. The corpus cases then also need
std adapters over a user iterator whose `Iterator` impl is generic
(L0640) and one inference fix (L0111).

To activate: move `pending/Cargo.toml` and `pending/src` here, update
tests/crates/adapter-missing and docs/errors/L0508.md (both use indexmap
as the crate with no adapter), then run
`LUST=target/release/lust scripts/test-adapters.sh indexmap`.
