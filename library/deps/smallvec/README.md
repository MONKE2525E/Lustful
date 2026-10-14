# Adapter: smallvec 1.15.1 (pending)

The adapter is written and checked against the real crate with rustc
(pending/README.md), but lust cannot compile it yet. Until then it waits
in `pending/`, and a dependency on smallvec is L0508 ("no lust adapter
yet"). The corpus is tests/adapters/crates/smallvec (UNSUPPORTED today).

Blocked on: method calls that autoderef from a user type to builtin
slice methods (`Deref<Target = [T]>`, W-CHECK-G); `Iterator::size_hint` overrides,
`DoubleEndedIterator`, `ExactSizeIterator`, `Extend`, and the `Hasher`
trait (W-STD-B, in its queue); `into_iter()` on a generic
`I: IntoIterator` parameter (W-STD-B or W-TRAITS). `drain` (ts-rust
calls `drain(..)`) also needs `Vec::drain`, `RangeBounds`, and `..` as
a value (L9001 today), which no package has queued yet (W-STD-A owns
Vec).

Method arguments typed `A::Item` work on next since W-TRAITS2
(225c970b). On next, `lust check` of this crate now stops only at the
std pieces above: DoubleEndedIterator, Extend, size_hint overrides,
RangeBounds, and vec::Drain.

To activate: move `pending/Cargo.toml` and `pending/src` here, then run
`LUST=target/release/lust scripts/test-adapters.sh smallvec`.
