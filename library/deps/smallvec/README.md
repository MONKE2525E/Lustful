# Adapter: smallvec 1.15.1 (pending)

The adapter is written and checked against the real crate with rustc
(pending/README.md), but lust cannot compile it yet. Until then it waits
in `pending/`, and a dependency on smallvec is L0508 ("no lust adapter
yet"). The corpus is tests/adapters/crates/smallvec (UNSUPPORTED today).

Blocked on: method arguments typed by an associated type of the Adt's
parameter (`push(value: A::Item)`, fixed on b/w-traits2); method calls
that autoderef from a user type to builtin slice methods (`Deref<Target
= [T]>`, W-CHECK-G); `Iterator::size_hint` overrides,
`DoubleEndedIterator`, `ExactSizeIterator`, `Extend`, the
`std::vec::IntoIter` type name, and `usize::checked_mul` checks
(W-STD-A, W-STD-B).

On b/w-traits2 (projections normalized), the core (new, push, spill,
capacity, clone, into_vec) compiles and prints the same as the real
crate once the impls that need missing std pieces are cut: Extend,
FromIterator, IntoIterator (slice::Iter, IterMut, vec::IntoIter names,
DoubleEndedIterator, size_hint) and Hash (the Hasher trait).

To activate: move `pending/Cargo.toml` and `pending/src` here, then run
`LUST=target/release/lust scripts/test-adapters.sh smallvec`.
