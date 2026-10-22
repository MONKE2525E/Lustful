<img src="assets/icon.svg" width="64" height="64" alt="Lustful logo: a pink crab with a smiling face">

# Lustful

This is the Verenu compatibility fork of Lustful. See [Verenu support](docs/VERENU.md) for the compiler additions, verification commands, and remaining desktop blockers.

Lustful is an experiment. It asks one question: how fast can `check` and `build` of real Rust code get if the compiler supports only a subset of Rust, keeps a warm daemon, and gives up LLVM in dev builds?

To test this, Lustful compiles a subset of Rust. Every program Lustful accepts must be valid Rust (rustc 1.99, edition 2024), and it must give the same output as the `rustc` build. When Lustful cannot match rustc, it rejects the program with a precise diagnostic.

## Status

Lustful is early-stage, but it already compiles real projects and includes a working daemon, type checker, trait solver, and borrow checker.

## Quick start

```sh
# build from source
scripts/build-tcc.sh
cargo build --release

# check a Rust file
lust check main.rs

# build a dev binary
lust build main.rs -o out
```

## Why Lustful

- Warm daemon-based incremental checking
- Restricted Rust subset with strong verification guarantees
- Fast edit loops for real-world compiler workloads
- Native C backend with `tcc` in dev builds

## Docs

- [DESIGN.md](DESIGN.md)
- [docs/ARCH.md](docs/ARCH.md)
- [docs/PLAN.md](docs/PLAN.md)
- [docs/VERENU.md](docs/VERENU.md)

## Supported subset

Lustful supports a substantial subset of Rust, including many common language features, standard library patterns, Cargo workspace workflows, and diagnostic-driven development. The full list is available via `lust capabilities`.

## Testing

```sh
scripts/difftest.sh
SANITIZE=1 scripts/difftest.sh
PANIC=unwind scripts/difftest.sh
```

## License

See the repository license for usage terms.
