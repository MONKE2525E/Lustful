# Adapter: smallvec 1.15.1 (pending)

The adapter is written and checked against the real crate with rustc
(pending/README.md), but lust cannot compile it yet. Until then it waits
in `pending/`, and a dependency on smallvec is L0508 ("no lust adapter
yet"). The corpus is tests/adapters/crates/smallvec (UNSUPPORTED today).

Blocked on: `Iterator::size_hint` overrides, `DoubleEndedIterator`,
`ExactSizeIterator`, `Extend`, and the `Hasher` trait (W-STD-B, in its
queue). `drain` (ts-rust calls `drain(..)`) also needs `Vec::drain`,
`RangeBounds`, and `..` as a value (L9001 today), which no package has
queued yet (W-STD-A owns Vec).

Working on next: method arguments typed `A::Item` (W-TRAITS2
225c970b), method calls and indexing through the user `Deref`
(W-CHECK-G2 4f30cf3f, 8028b54b), and generic `IntoIterator` (W-TRAITS2
d8d322eb). `lust check` of this crate stops only at the std pieces
above.

To activate: move `pending/Cargo.toml` and `pending/src` here, then run
`LUST=target/release/lust scripts/test-adapters.sh smallvec`.
