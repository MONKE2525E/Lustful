# Adapter: smallvec 1.15.1 (pending)

The adapter is written and checked against the real crate with rustc
(pending/README.md), but lust cannot compile it yet. Until then it waits
in `pending/`, and a dependency on smallvec is L0508 ("no lust adapter
yet"). The corpus is tests/adapters/crates/smallvec (UNSUPPORTED today).

Blocked on: indexing through a user `Deref<Target = [T]>`, `v[i]` and
`&v[a..b]` (L0113 on next; W-CHECK-G; method calls, `*v`, and `&v` to
`&[T]` work since 4f30cf3f); `Iterator::size_hint` overrides,
`DoubleEndedIterator`, `ExactSizeIterator`, `Extend`, and the `Hasher`
trait (W-STD-B, in its queue); `into_iter()` on a generic
`I: IntoIterator` parameter (in W-TRAITS2's next landing). `drain` (ts-rust
calls `drain(..)`) also needs `Vec::drain`, `RangeBounds`, and `..` as
a value (L9001 today), which no package has queued yet (W-STD-A owns
Vec).

Method arguments typed `A::Item` work on next since W-TRAITS2
(225c970b). On next, `lust check` of this crate now stops only at the
std pieces above: DoubleEndedIterator, Extend, size_hint overrides,
RangeBounds, and vec::Drain.

To activate: move `pending/Cargo.toml` and `pending/src` here, then run
`LUST=target/release/lust scripts/test-adapters.sh smallvec`.
