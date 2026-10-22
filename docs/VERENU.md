# Verenu compatibility

This fork develops Lust support for Verenu's Rust backend. The complete Tauri
application does not compile with Lust yet. Cargo/rustc release compilation
requires an explicit `--host-tools` opt-in in this fork.

## Supported additions

`std::str::Chars::as_str(&self) -> &'a str` returns the unconsumed part of the
iterator's original string. Advancing either end of the iterator changes later
views, while earlier views remain valid. The returned view borrows the original
string, so dropping the iterator is allowed and dropping or mutating the string
while the view is live is rejected.

This supports Verenu's capitalization function in `src-tauri/src/system/text.rs`
without changing application source. Tests compare Unicode, empty strings,
front and back iteration, saved views, and lifetime errors against rustc.

```sh
bash scripts/build-tcc.sh
bash scripts/build.sh --locked -j 4
DIFFTEST_JOBS=2 SANITIZE=1 bash scripts/difftest.sh chars_as_str
bash scripts/runtest.sh chars_as_str
```

Verenu's `tools/lust/` workflow pins the fork and checks the original production
files and tests. Its `full-check` command records the complete dependency graph's
first failures without replacing implementations or falling back to rustc.

The [log 0.4.34 source adapter](../library/deps/log/README.md) implements logger
registration, filtering, lazy formatting, record builders, and source metadata.
Its corpus compares registered logger behavior with the upstream registry crate,
including concurrent registration and suppressed argument evaluation. Unsupported
features and layout queries remain explicit errors.

```sh
LUST_HOST_TOOLS=1 LUST=./target/release/lust LUST_STRICT=1 SANITIZE=1 bash scripts/test-adapters.sh log
LUST_HOST_TOOLS=1 LUST=./target/release/lust LUST_STRICT=1 LUST_USE_DAEMON=1 bash scripts/test-adapters.sh log
```

These adapter comparisons use Cargo host tools and a rustc oracle. They are
not rustc-free build audits.

The selected Cargo target supplies the crate name for `module_path!()`. A binary
whose target name differs from its package name therefore records the same
default log target as rustc.

### Primitive C imports

On `x86_64-unknown-linux-gnu`, the TinyCC backend accepts module-level
`unsafe extern "C"` function declarations. Parameters and returns may use
`i32`, `u32`, `i64`, `u64`, `isize`, and `usize`; a function may also return
unit. Thin raw pointers to `i8`, `u8`, `i32`, `u32`, `i64`, `u64`, `isize`,
and `usize` are accepted as parameters and returns, preserving mutability.
Narrow integers remain unsupported by value. Calls require a lexical `unsafe`
block and use the system C ABI.

```rust
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() { assert_eq!(unsafe { abs(-17) }, 17); }
```

Nested pointers, other pointees, callbacks, variadics, foreign statics, native exports, and `#[link]`
remain unsupported. Symbols must be ASCII C identifiers outside the compiler's
reserved namespace. General unsafe operations remain rejected. Crates that
deny or forbid `unsafe_code` are rejected until Lust can enforce that lint by
scope. Other targets and the system C compiler backend reject native imports.

The tests compare calls with rustc, exercise guarded buffer writes, pointer
returns, eight mixed arguments and void side effects against C peers, and
rebuild declaration edits through the daemon. The C peers are test fixtures;
this does not add library configuration or Rust crate linking. Raw-pointer
dereferencing and ownership transfer remain unsupported.

Shared daemon bases are validated with an executable link before publication.
Missing native symbols fail with code 3, including after warm edits or daemon
restart. Restoring a deleted base validates against its saved main object so
existing overlays can still be linked without duplicate globals.

```sh
bash scripts/difftest.sh native_
bash scripts/test-native.sh
LUST_NATIVE_ABI_SANITIZE=1 cargo test --profile gate native_abi_calls_c_peers
cargo test --profile gate native
```

The Cargo command bootstraps tests and uses rustc as an independent oracle.
It is separate from a rustc-free Lust target build.

## Compiler boundary

The selected approach adds language and library support to Lust, with differential
tests against rustc for each addition. It preserves the target of compiling the
existing native application. It also leaves unsupported programs rejected while
their required features are incomplete.

A second approach would keep Tauri and Tokio in a rustc host and move pure logic
across a C ABI into a Lust library. That would require foreign-function exports,
library output, and explicit ownership and panic boundaries. It could execute
part of Verenu with Lust, but it would keep the desktop shell on rustc and change
application architecture. This fork does not introduce that split.

Lust cannot consume rustc crate metadata or link arbitrary Rust ABI calls.
Loading rustc-built dependencies as if they were Lust crates would require
compatible layouts, generics, unwinding, and metadata support.

## Remaining full-application requirements

`lust metadata --manifest-path Cargo.toml --offline --locked` resolves a full
Cargo graph without calling rustc. It uses a query-only Lust compiler entry:
the identity says `lust`, target facts come from Lust's own cfg table, and
unsupported Cargo library artifact types are reported as unsupported. This
currently accepts the native `x86_64-unknown-linux-gnu` target without extra
compiler flags. Other queries and all attempts to compile host artifacts fail.
The returned graph can describe build scripts and procedural macros; neither
is executed. Resolving a graph does not make its packages compilable by Lust,
and this command does not relax the strict build policy.

```sh
bash scripts/test-cargo-query.sh
```

The test traces query executions with a refusing rustc sentinel and separately
compares Cargo's graph, including feature activation, against a rustc-query
oracle. The oracle is outside the rustc-free execution traces.

Verenu requires edition 2021, async functions and Tokio, unsafe native FFI,
custom procedural macros, and dependencies outside Lust's shipped adapters.
With host preparation explicitly permitted, the edition-2024 compatibility overlay expands `log::warn!` and reaches
unsupported `serde_json::json!` expansion. The production edition-2021 manifest
still fails L0530. Async remains rejected as L0405. Primitive C imports cover
buffer calls such as `gethostname` on the target above; broader native APIs,
callbacks, and foreign library configuration remain unsupported. No full
desktop build has succeeded.

Strict compilation starts with `cargo metadata --no-deps`. It admits one package
without dependencies, build scripts, or proc-macro targets, resolving its local
feature closure without rustc. It also admits featureless workspaces with only
unconditional normal path dependencies between members, without version
requirements, build scripts, or proc macros. These edges resolve by canonical
manifest path; no feature probe runs. A single-member workspace may also use
normal unconditional dependencies, including optional dependencies, renamed
crates, and Cargo features. Lust resolves that graph through its read-only Cargo
query interface and uses Cargo's feature sets. Every resolved edge must be a
normal unconditional edge, with no build scripts or proc-macro targets. Root
dev dependencies, build dependencies, and target-conditional dependencies are
rejected: their per-unit feature sets are not implemented on this path.
Dependency source, adapter versions, and supported adapter features still
have to satisfy Lust's existing checks. A directly qualified unsupported
dependency macro reports L0508 with the dependency classifier's reason.
Imported macros and crate aliases still report the generic unknown-macro error.

Other graphs, including Verenu, stop at L0532 before host preparation. This gate also
rejects warm host outputs and is part of each daemon session's identity.
`--host-tools` or `LUST_HOST_TOOLS=1` opts into existing host-tool behavior and
is not a rustc-free run. The gate prevents hidden compiler use; it does not
add the missing desktop compiler capabilities.

`bash scripts/test-local-graphs.sh` audits the local-workspace path and compares
its output with a separately built Cargo oracle. The oracle is outside the
strict build trace and does use rustc.

`bash scripts/test-normal-graphs.sh` audits actual builds with the renamed `log`
adapter and a path dependency, compares feature-selected output against separate
Cargo builds, and checks cache/daemon invalidation and host-tool rejection. Those
Cargo oracle builds use rustc outside the strict traces.

The compiler must preserve native behavior and reject unsupported constructs
throughout this work. A successful core test run does not establish a working
desktop application or native integration on any operating system.
