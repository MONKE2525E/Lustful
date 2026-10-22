# Verenu compatibility

This fork develops Lust support for Verenu's Rust backend. The complete Tauri
application does not compile with Lust yet. Release compilation still uses
Cargo and rustc through upstream's release path.

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
LUST=./target/release/lust LUST_STRICT=1 SANITIZE=1 bash scripts/test-adapters.sh log
LUST=./target/release/lust LUST_STRICT=1 LUST_USE_DAEMON=1 bash scripts/test-adapters.sh log
```

The selected Cargo target supplies the crate name for `module_path!()`. A binary
whose target name differs from its package name therefore records the same
default log target as rustc.

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

Verenu requires edition 2021, async functions and Tokio, unsafe native FFI,
custom procedural macros, and dependencies outside Lust's shipped adapters.
The edition-2024 compatibility overlay now expands `log::warn!` and reaches
unsupported `serde_json::json!` expansion. The production edition-2021 manifest
still fails L0530. The standalone async and native-FFI probes still fail L0405
and L0810. No full desktop build has succeeded.

Cargo graph discovery still uses rustc for host build scripts and procedural
macro crates. Removing those invocations is also required for a complete build
that uses rustc only to bootstrap Lust and compile test oracles.

The compiler must preserve native behavior and reject unsupported constructs
throughout this work. A successful core test run does not establish a working
desktop application or native integration on any operating system.
