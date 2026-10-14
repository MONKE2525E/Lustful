# Adapter: indexmap 2.14.0 (pending)

The adapter is written and checked against the real crate with rustc
(pending/README.md), but lust cannot compile it yet. Until then it waits
in `pending/`, and a dependency on indexmap is L0508 ("no lust adapter
yet"). The corpus is tests/adapters/crates/indexmap (UNSUPPORTED today).

Blocked on: `Iterator::size_hint` overrides, `DoubleEndedIterator`,
`ExactSizeIterator`, `Extend`, `BuildHasher::hash_one` in generic
code, and `RandomState` (W-STD-B, in its queue); a user `Index` impl
as the `map[&key]` operator (L0113 on next 8028b54b).

Working on next: generic parameter defaults, the std iterator type
names, and `into_iter()` on a generic `I: IntoIterator` (W-TRAITS2
d8d322eb). On next, `lust check` of this crate stops only at the
W-STD-B items above. The corpus cases then also need std adapters
over a user iterator with a generic `Iterator` impl (L0640) and one
inference fix (L0111).

To activate: move `pending/Cargo.toml` and `pending/src` here, update
tests/crates/adapter-missing and docs/errors/L0508.md (both use indexmap
as the crate with no adapter), then run
`LUST=target/release/lust scripts/test-adapters.sh indexmap`.
