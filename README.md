<img src="assets/icon.svg" width="64" height="64" alt="">

# lust

lust is a compiler for a subset of Rust. It checks and builds Rust code much faster than rustc, so the edit, check, run loop stays short. It emits C and compiles it with [tcc](https://bellard.org/tcc/).

Rule zero: every program lust accepts is valid Rust (rustc 1.99, edition 2024), and it gives the same output. When lust cannot match rustc, it rejects the program with an error code. It never guesses.

Use lust for dev checks and dev builds. Use Cargo for release builds.

## Status

lust is new. The main target today is fast `lust check` on [ts-rust](https://github.com/pingdotgg/ts-rust), a Rust port of the TypeScript compiler (about 786k lines).

On a fork of ts-rust (upstream commit `b11b618ae`, 2026-10-09) with small changes for lust, 2026-10-16 census:

- `lust check`: 17 of 17 targets pass (every lib, bin, and cdylib).
- `lust build`: 11 of 11 bins build.
- Parity with the Cargo builds: 350 of 350 fixture runs give the same stdout, stderr, exit code, and written files. 7 of 7 integration test bins and 12 of 12 tool runs are the same. 479 of 479 unit tests give the same result.

## Speed

Warm `lust check` through the daemon, compared with `cargo check` (rustc 1.99, incremental, the faster of the default and `-Z threads=8` setups). 16 vCPU Linux box. All numbers come from [docs/speed.md](docs/speed.md) and the latest runs on the full ts_goport crate.

| Edit | Code | lust median | lust p95 | cargo check median | Ratio median | Ratio p95 |
|---|---|---:|---:|---:|---:|---:|
| Change one function body | ts-rust slices, 150k to 165k lines | 3 to 4 ms | 7 to 15 ms | 2.0 to 2.4 s | 519x to 644x | 187x to 346x |
| Change a signature, a type, or a derive | full ts_goport crate, 348k lines | 43 to 94 ms | 110 ms to 7.0 s | about 5.6 to 6.6 s | 64x to 131x | not measured |

The fine print:

- Body edits are the fast path. The worst body edit in 120 was 102 to 143 ms.
- Edits outside bodies are slower and less even. Some signature edits still fall back to a full check, which costs about as much as a cold check. That is where the 7.0 s p95 comes from.
- A cold check (no daemon) is only about 2x faster than cargo check on ts-rust. The first check of a new daemon session costs the same as a cold check.
- `lust build` after a body edit is about 17x faster than a cargo build at the median (9x at p95). A cold `lust build` of a large ts-rust bin takes about 2 minutes.
- Built programs run slower than rustc debug builds, because tcc does not optimize.
- The daemon holds the whole program in memory: about 3.3 GB peak on a 165k-line slice.

## Install

Linux x86_64 only. Download `lust-0.1.0-x86_64-linux.tar.gz` from the [releases](../../releases) page, then:

```sh
tar xzf lust-0.1.0-x86_64-linux.tar.gz
export PATH="$PWD/lust-0.1.0-x86_64-linux/bin:$PATH"
lust --version
```

The package holds `lust`, `lust-core`, the pinned tcc, and the std and adapter sources. lust finds them relative to its own executable, so you can move the folder or link `bin/lust` into your `PATH`.

You also need:

- glibc 2.38 or later (Ubuntu 24.04, Debian 13, Fedora 39, or newer).
- The C library development files (`libc6-dev` on Debian and Ubuntu, `glibc-devel` on Fedora). tcc links your program against them.
- Cargo, to check a Cargo crate: lust reads `cargo metadata` and the registry sources. Cargo also does release builds.

To build from source, see [Build from source](#build-from-source).

## Use

```sh
lust check main.rs                  # type check and borrow check
lust run main.rs [-- args]          # build with tcc and run
lust build main.rs [-o out]         # build a dev binary
lust test main.rs [filter]          # run #[test] functions
lust check main.rs --rustc          # ask the real rustc for a second opinion
lust build main.rs --release        # release build with Cargo (or rustc -O for a single file)
lust explain L0301                  # long help for one error code
lust capabilities --json            # what the subset supports and rejects
```

A crate target in a Cargo workspace:

```sh
lust check crates/ts_goport/src/lib.rs --manifest-path crates/ts_goport/Cargo.toml --lib
lust build crates/tsgo/src/main.rs --manifest-path crates/tsgo/Cargo.toml --bin tsgo -o tsgo
```

Crate flags work as in Cargo: `--features`, `--no-default-features`, `--all-features`, `--package`, `--target`, `--offline`, `--locked`. A project can drop features from lust dev builds (for example a native allocator such as jemalloc) with `dev-exclude-features`. See [docs/dev-features.md](docs/dev-features.md).

### The daemon

You do not need to start it. When `check`, `build`, or `run` finds no daemon for the directory, lust answers that command cold and starts a daemon in the background. The next command is warm.

- The daemon exits after 30 idle minutes (`LUST_DAEMON_IDLE`, for example `10m`; `0` means never).
- `LUST_NO_DAEMON=1` turns it off.
- Its log is `.lust-cache/daemon.log` next to the source file.
- Cold runs also use a disk cache in `.lust-cache/`. Do not commit or share it: a cached build can run, so treat it like a ccache directory.

### What happens with code lust does not support

lust does not fall back to rustc for checks. If your code uses a feature outside the subset, lust stops with an error that has a stable code, such as `L9001` (not supported yet) or `L0508` (a dependency with no lust adapter). `lust explain <code>` says what to change.

Release builds always go to Cargo (`cargo build --release` for a crate, `rustc -O` for a single file). lust prints which tool ran.

## Platform and limits

- Linux x86_64 only. The release package is built and tested there. Other platforms are not supported yet.
- The backend is tcc. Dev binaries are not optimized.
- Dependencies: lust compiles a crates.io package only through an adapter in `library/deps` (18 today, for example `indexmap`, `memchr`, `smallvec`, `num-bigint`), or through a small set of shims. Other dependencies give `L0508`.
- Not supported (each gives an error code): `async`, `unsafe` code, unions, `extern` blocks and functions, and proc macros other than the built-in derives.
- Release builds should use Cargo. lust makes dev binaries only.

## Build from source

```sh
scripts/build-tcc.sh                 # builds the pinned tinycc into third_party/tcc
cargo build --release                # builds lust (client) and lust-core (compiler)
scripts/release.sh                   # builds dist/lust-<version>-x86_64-linux.tar.gz
```

`scripts/build.sh` builds a faster-to-compile profile for test runs. Tests: `scripts/difftest.sh` compares lust with rustc on `tests/pass`, `tests/fail`, and `tests/reject`.

`third_party/ts-rust` is a git submodule. It points to a private fork of ts-rust that only the ts-rust census scripts (`scripts/tsrust-full.sh`) use. You do not need it to build or use lust. This stays so until the lust changes land in upstream ts-rust.

## More

- [DESIGN.md](DESIGN.md): the original design and plan. Some parts are older than the code.
- [docs/speed.md](docs/speed.md): the speed method and full tables.
- [docs/errors](docs/errors): one page per error code.

## License

MIT, see [LICENSE](LICENSE). tcc (`third_party/tcc`, and the copy in the release package) keeps its own LGPL 2.1 license. The adapter crates in `library/deps` stand in for crates.io packages; those packages keep their own licenses.
