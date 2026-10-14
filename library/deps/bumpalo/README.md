# Adapter: bumpalo 3.20.3 (pending)

The adapter is written and checked against the real crate with rustc
(pending/README.md), but lust cannot compile it yet. Until then it waits
in `pending/`, and a dependency on bumpalo is L0508 ("no lust adapter
yet"). The corpus is tests/adapters/crates/bumpalo (UNSUPPORTED today).

Blocked on: `std::cell::Cell` (W-STD-A). ts-rust's only user,
leak_arena.rs, also needs `MaybeUninit` in its own code (no owner yet).

To activate: move `pending/Cargo.toml` and `pending/src` here, then run
`LUST=target/release/lust scripts/test-adapters.sh bumpalo`.
