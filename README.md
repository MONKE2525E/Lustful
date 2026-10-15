<img src="assets/icon.svg" width="64" height="64" alt="">

# lust-lang

A Rust subset that compiles much faster than Rust. Every valid lust program is a valid Rust program with the same output. The plan is in [DESIGN.md](DESIGN.md).

Status: **prototype.** It compiles a real subset of Rust end to end, with a real type checker and borrow checker. No generics, traits, or closures yet.

## Demo: an agent's edit loop, 130x faster than rustc

`bench/realish/agent_loop.py` plays the loop a coding agent runs all day: edit a function, check, build, run. It does this on a 31k-line crate (40 modules of a 784-line warehouse service: inventory, orders, a pricing-rule language with a tokenizer, parser, and evaluator, shortest-path routing, and reports). The 12 edits include behavior changes, a new function, and two mistakes (a type error and a borrow error) that both compilers must reject.

- **rustc 1.99** runs in its fastest incremental setup on this machine: `-Z threads=8`, `-C incremental`, `-C debuginfo=0`.
- **lust** runs through a warm `lust daemon`. The `lust` command is a thin client.
- After every edit, both compilers must agree on pass or fail, and the two programs must print exactly the same output.

24-core x86_64 Linux:

| # | Edit | rustc check | lust check | rustc build | lust build |
|---|---|---|---|---|---|
| 1 | tweak the bulk discount | 1351 ms | 13.5 ms | 2463 ms | 13.9 ms |
| 2 | restock more often | 1212 ms | 7.5 ms | 2143 ms | 13.7 ms |
| 3 | add a currency suffix | 1082 ms | 6.7 ms | 2134 ms | 14.3 ms |
| 4 | lower the max quantity | 837 ms | 6.3 ms | 1884 ms | 19.0 ms |
| 5 | allow cancelling paid orders | 1344 ms | 6.4 ms | 2435 ms | 13.7 ms |
| 6 | mistake: wrong integer type (both reject) | 847 ms | 8.3 ms | - | - |
| 7 | fix the type error | 782 ms | 8.0 ms | 1171 ms | 16.9 ms |
| 8 | restock a bit more | 1281 ms | 7.6 ms | 2432 ms | 13.7 ms |
| 9 | rewrite a heap check | 1232 ms | 6.5 ms | 2425 ms | 15.8 ms |
| 10 | add a new helper function | 1169 ms | 13.8 ms | 2254 ms | 15.7 ms |
| 11 | mistake: borrow conflict (both reject) | 819 ms | 9.1 ms | - | - |
| 12 | fix the borrow conflict | 845 ms | 7.0 ms | 1106 ms | 18.0 ms |
| | **total** | **12.80 s** | **0.101 s** | **20.45 s** | **0.155 s** |

**Check: 127x. Build: 132x. Whole edit loop: 130x.**

The fine print:

- Running the built program is not faster. tcc does not optimize, so lust's binary runs about 1.7x slower than rustc's debug build (22 ms versus 13 ms per run here). If you count that run as part of every iteration, the loop is about 70x faster. This benchmark measures the compiler.
- The crate is one module cloned 40 times, with renamed items. That gives realistic code at a realistic size, but not the variety of a real project.
- One big crate is a worst case for rustc. Real projects split code into crates, which makes rustc's incremental builds faster.
- Cold compiles are about 20x to 55x faster, not 100x. The 100x comes from incremental work (see below).

Reproduce with `python3 bench/realish/agent_loop.py`.

## Cold compiles

Same generated file, same output. rustc gets its best configuration for each number (the fastest of incremental, non-incremental, and `-Z threads=8`). Reproduce with `bench/compare.sh plain 640 3200`.

| Lines | Operation | rustc | lust | Speedup |
|---|---|---|---|---|
| 9.6k | check | 1.33 s | 42 ms | 32x |
| 9.6k | debug build | 2.49 s | 115 ms | 22x |
| 48k | check | 5.86 s | 109 ms | 54x |
| 48k | debug build | 11.1 s | 279 ms | 40x |

## How incremental compiles work

The daemon keeps one session per crate selection: the crate (package and target) plus the resolver inputs that select its build (features, target triple, profile flags). A single file is a synthetic one-crate package, so `lust check file.rs` needs no setup. Two feature selections of one file get two sessions. An edit costs time that grows with the size of the edit, not of the program:

1. **Find what changed.** It compares the new source with the last one (two `memcmp`s), and lexes again only the chunks of whole items that the edit touched. Chunk boundaries are content-defined, so an inserted function does not move the others.
2. **Classify the edit.** A token-level scan hashes each function body, and everything outside bodies, without positions. If only bodies changed, only those bodies are parsed, checked, and borrow-checked again. If only top-level functions were added, removed, or changed signature, it parses only the changed chunks, and re-checks only those functions and the bodies that mention their names. Anything else (a type, an impl) is a full rebuild.
3. **Swap in new code without relinking.** Every call goes through a function table (`lust_fns[slot]`). A slot is a function's stable identity, so adding a function does not renumber the others. The first build links everything into `libbase.so`. After an edit, only the changed functions' unit is compiled, as an "overlay" object. The small executable links main plus the overlays against `libbase.so`, and at startup the overlays replace their entries in the table. After 32 overlays, the base is rebuilt.
4. **Stay valid when code moves.** Panic locations in generated C are relative to the function's first line, so moving a function does not change its code.

## Build

```sh
scripts/build-tcc.sh      # builds the pinned tinycc into third_party/tcc
cargo build --release     # builds `lust` (client) and `lust-core` (compiler)
scripts/build.sh          # same binaries, fast-to-build profile [profile.gate], for test runs (28 s vs 126 s)
```

## Use

```sh
lust check main.rs [--json] [--max-errors N] [--timings]
lust build main.rs [-o out] [-g] [--emit-c prefix] [--timings]
lust build src/main.rs --manifest-path Cargo.toml [--bin name] [--features a,b] [--target triple]  # name a Cargo crate target; the file stays the crate root
lust run main.rs [-- args]
lust build main.rs --release            # release build: Cargo if a Cargo.toml is above the file, else rustc -O
lust build main.rs --profile fast       # same, with a named Cargo profile
lust check main.rs --rustc              # second opinion: the real rustc checks the file
lust test main.rs [filter] [--json] [--timeout SECONDS]
lust explain L0301
lust capabilities [--json]
lust daemon                             # serve this directory yourself (not needed: see below)
```

A project can pin the feature set for lust dev builds (for example, dev
builds without a `jemalloc` feature, while Cargo release builds keep it):
set `dev-exclude-features` or `dev-features` under
`[package.metadata.lust]`, `[workspace.metadata.lust]`, or in a
`.lust.toml` file. A plain `lust check` or `lust build` then uses that
selection with no flags; command line feature flags override it. See
`docs/dev-features.md`.

No setup is needed for warm speed. When `check`, `build`, or `run` finds no daemon for the directory, it answers that one command cold and starts a daemon in the background (its own session, log at `.lust-cache/daemon.log`). The next command is warm. The daemon exits after 30 idle minutes (`LUST_DAEMON_IDLE`, in seconds or with an `s`/`m`/`h` suffix; `0` means never). `LUST_NO_DAEMON=1` turns autostart off. Without a daemon, `lust` compiles cold in a fresh process and links a standalone executable. With a daemon, the executable loads `libbase.so` from the daemon's cache directory.

Cold runs also use a whole-request disk cache in `.lust-cache/` next to the source file (`LUST_CACHE_DIR` overrides it, `LUST_NO_CACHE=1` turns it off, `LUST_CACHE_MAX_BYTES` sets the size cap; default 512 MiB, oldest entries deleted first). An unchanged file with the same flags replays in about 4 ms (check) or 8 ms (build). The key covers the compiler build, the tcc binary and runtime files, the source bytes and path, the flags, and the target.

Trust rule for the cache: it is trusted like ccache's local cache. A cached build result is copied out and can run, so a poisoned cache is code execution. Never commit `.lust-cache/` (it is in `.gitignore`), never share it, and delete it if a checkout brings one along.

Release builds go through the real Rust toolchain on the same source, and lust prints which tool ran. With a `Cargo.toml` above the file, lust runs `cargo build --release` (or `--profile <name>`) with the file's package and bin selection; `-o` copies the artifact out of `target/`. Without one, it runs `rustc -O --edition 2024` with the release oracle flags from [DESIGN.md](DESIGN.md).

`--json` prints one diagnostic per line (schema 1), each with `code`, `severity`, `message`, `file`, `source_hash`, `span` (bytes plus line and column), labeled secondary `labels`, `fix`, and `edits`. Output is capped at 20 diagnostics by default; a final `truncated` record says how many were omitted. `lust test` runs each `#[test]` function in its own child process. `lust explain` prints the long-form page for one code (see `docs/errors/`). `lust capabilities --json` lists what the subset supports and rejects. The three agent-kit commands never use the daemon.

## Supported subset

- Items: `fn`, `struct` (named fields or unit), `enum` (unit, tuple, and struct variants), inherent `impl` blocks, `use`.
- Derives: `Debug`, `Clone`, `Copy`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Default` (with `#[default]` enum variants). The derived bodies are structural glue; a field type with a written non-generic `Clone`, `Default`, `PartialEq` (with no `ne` of its own), or `PartialOrd` (with no `Ord` and no `lt`/`le`/`gt`/`ge` of its own) impl is called through that impl, and other written field impls are rejected where the derived method is used. `Hash` answers bounds only; nothing hashes yet.
- Comparison operators and core's default methods (`ne`, `lt`/`le`/`gt`/`ge`, `Ord::max`/`min`/`clamp`) work through written `PartialEq`/`PartialOrd`/`Ord` impls; `Ordering` has `is_*`, `reverse`, `then`, and `then_with` (with a closure).
- Types: integers (no 128-bit), `bool`, `char`, `String`, `&str`, `Vec<T>`, `Option<T>`, `&T`, `&mut T`.
- Control flow: `if`, `if let`, `match` (guards, `|`, ranges, nested patterns, default binding modes), `loop`, `while`, `while let`, `for` over ranges, `&vec`, `&mut vec`, and `s.chars()`, `break` with a value, early `return`.
- Macros: `macro_rules!` definitions and calls (matching, hygiene, textual and `#[macro_export]` scope, in one file), plus built-ins: `println!`, `print!`, `eprintln!`, `eprint!`, `format!` (`{}`, `{:?}`, positional, and captured names), `vec!`, `panic!`, `assert!`/`assert_eq!`/`assert_ne!`, `debug_assert!` family, `matches!`, `concat!`, `stringify!`, `cfg!`, `env!`, `option_env!`, `line!`, `column!`, `file!`, `module_path!`, `include!`, `include_str!`, `compile_error!`, `dbg!`, `write!`/`writeln!`, `todo!`, `unreachable!`, `unimplemented!`.
- Std: common methods on `String`, `str`, `Vec`, `Option`, `char`, and integers, plus `std::env::args().count()`.
- Borrow checking: moves, initialization, mutability, NLL-style conflicting borrows with two-phase borrows, dangling references, temporaries dropped while borrowed, and returned references (elision only).

Not yet: generics, traits, closures, iterators beyond `chars()`, `Result` and `?`, `HashMap`, floats, tuples, arrays, slices, modules, `const`, `let`-else, and moving one field out of a struct while keeping the rest. Each one gives error `L9001`.

Lust rejects on purpose: lifetime syntax (`L0203`) and references in struct fields (`L0201`).

## Tests

```sh
scripts/difftest.sh             # compare with rustc
SANITIZE=1 scripts/difftest.sh  # also run the generated C under ASan and UBSan
scripts/test-client.sh          # daemon autostart, disk cache, release handoff
scripts/test-crates.sh          # Cargo package fixtures built by Cargo and by lust
scripts/testtest.sh             # compare `lust test` with `rustc --test`
scripts/check-explain.sh        # check every `lust explain` example against lust and rustc
scripts/agentkit-test.sh        # JSON diagnostics, explain, capabilities, test edges
```

- `tests/pass`: lust and rustc must give the same stdout and exit status.
- `tests/fail`: rustc and lust must both reject. lust must give the expected error code.
- `tests/reject`: valid Rust that lust rejects on purpose.
- `tests/testrun`: files with `#[test]` functions; `lust test` and `rustc --test` must agree per test.

The agent-loop benchmark also tests incremental mode: every edit's result is compared with rustc.

## Code map

| File | Role |
|---|---|
| `src/client.rs`, `src/protocol.rs` | The thin `lust` client (daemon autostart, release handoff) and the daemon wire format. |
| `src/driver/cache.rs` | The whole-request disk cache for cold runs. |
| `src/main.rs`, `src/daemon.rs`, `src/driver/` | `lust-core`: cold compiles, the daemon, and the incremental pipeline. |
| `src/diag.rs`, `docs/errors/` | Diagnostics with stable codes. `--json` uses schema 1 records with spans, labels, and a source hash. One explain page per code. |
| `src/testrun.rs`, `src/explain.rs`, `src/capabilities.rs` | The agent kit: `lust test`, `lust explain`, and `lust capabilities`. |
| `src/lexer.rs`, `src/scan.rs`, `src/parser.rs`, `src/ast.rs` | Syntax in flat arenas; the token scan that finds what changed. |
| `src/check/collect.rs` | Item tables and signatures. |
| `src/check/mod.rs`, `src/ty/mod.rs` | Local type inference, method resolution, exhaustiveness; interned semantic types. |
| `src/lower.rs`, `src/ir.rs` | Lowering to a MIR-like CFG with explicit temporaries and drops. |
| `src/borrowck/mod.rs` | Init, move, and loan dataflow, plus liveness. |
| `src/cgen.rs`, `src/runtime/` | C backend and runtime. Checked math is done in 64-bit unsigned, so C never sees signed overflow. |
| `src/tcc.rs` | libtcc in process, parallel `tcc -c` for large programs, and shared-library linking. |
