# lust compiler architecture: milestones 4 to 9

Status: decision document. It is ready for review. It is not implemented.
Scope: milestones 4 to 9 in `docs/PLAN.md`. The north star is ts-rust.
Rule zero does not change. Every program lust accepts is valid Rust
(rustc 1.99, edition 2024) with the same output. Release builds go
through Cargo. Lust owns only the dev loop.

This document makes one choice per open question. Each choice is
concrete enough to implement without a new design round. Where a
choice can fail, the document names a spike, a gate, and a fallback.
Section 9 splits the work so 4 to 8 agents can build in parallel.

Readers: the orchestrator and the agents who get work packages.
Conventions: `file:line` means a line in the lust worktree, or in
ts-rust at `/home/theo/.t3/projects/ts-rust` when the path says so.
"Must" is a requirement. "Reject" means a stable `L####` error, not a
panic in the compiler.

Evidence base:

- Current compiler: 10,286 lines in `src/*.rs`, 402 lines in
  `src/runtime.c`.
- `/tmp/lust-ts/inventory/INVENTORY.md`: 571k handwritten prod lines,
  19,492 prod functions, feature counts from a real parser.
- `/tmp/lust-ts/design/DESIGN-TS.md`: the port design. Section 2 is
  the restricted lifetime model. Section 3 is the trait solver shape.
- `/tmp/lust-verify/g/VERIFY.md`: the generics verdict. Lock
  monomorphization plus iterator fusion, with layout-erased std
  container cores. No dictionary passing.
- `docs/PLAN.md` and `DESIGN.md`: targets, gates, and the exact
  rule-zero contract.

## 0. Where we start

The prototype pipeline is in `src/main.rs:5-21`: flat modules
`ast, borrowck, cgen, check, collect, daemon, diag, driver, intern,
ir, lexer, lower, parser, protocol, scan, tcc, types`. One file is
one crate. The important limits, by file:

| Area today | Where | Limit to remove |
|---|---|---|
| Closed types | `src/types.rs:82-104` `TyKind` | No generic args, tuples, arrays, slices, fn ptrs, `dyn`, closures, floats, u128. `Vec(Ty)` and `Option(Ty)` are built in. |
| Std as an enum | `src/check.rs:17-79` `Builtin`, about 55 cases | Every std method is hand-written in `check.rs`, `ir.rs`, `cgen.rs`, and `runtime.c`. It cannot scale to the std ts-rust uses. |
| One flat namespace | `src/collect.rs:59-71` `Program` | `type_names: HashMap<Sym, AdtId>`, `methods: HashMap<(AdtId, Sym), FnId>`. No modules, no crates, no traits, no generics. Module paths in types are rejected at `src/collect.rs:124-131` unless they start with `std`. |
| Items | `src/ast.rs:55-61` `ItemKind` | Only `Fn, Struct, Enum, Impl, Use`. `Use` carries no data. No `mod`, `trait`, `type`, `const`, `static`, `macro_rules`. |
| Types in syntax | `src/ast.rs:138-143` `TyExpr` | Only `Path`, `Ref`, `Unit`. `PathSeg.generics` exists at `src/ast.rs:133-136` but collect rejects generics for all types except `Vec` and `Option`. |
| Lifetimes rejected | `src/parser.rs:65-72`, `src/collect.rs` ref-field check | Any `'a` token is error `L0203`. DESIGN-TS section 2 requires the opposite. |
| Trait queries are functions | `src/collect.rs:480-539` | `is_copy`, `has_clone`, `has_eq`, `has_debug`, `has_display`, `needs_drop` are fixed rules plus derives. There is no impl index and no obligation queue. |
| Inference | `src/check.rs:1-2` | Local unification plus integer vars. Output is side tables in `Checked` at `src/check.rs:155-170`. Keep this shape. Extend it, do not replace it. |
| IR | `src/ir.rs:76-99` `Rvalue` | `Call(FnId)`, `Builtin(Builtin)`, `Aggregate`, `Opt`, `VecLit`. No method-call target for traits, no closure, no vtable, no unwind edge. |
| Borrow checker | `src/borrowck.rs:1-103` | NLL loans, liveness, two-phase support. One synthetic loan for ref params. No regions, no field-carried borrows through ADTs. Keep the loan engine. Add regions above it. |
| Incremental | `src/driver.rs:1-14`, `src/scan.rs:1-45` | Three cases only. A type, impl, or `use` edit is a full rebuild. Slots are keyed by `(Sym, Sym)` at `src/driver.rs:43`. |
| Daemon | `src/daemon.rs:16-25`, `src/protocol.rs:19-47` | One `Session` per file. A request names one file. No crate, no features, no target. |
| Spans | `src/diag.rs:5-19` | `Span { start, end }` in one file. No file id, no expansion site. Macros and multi-file crates both break this. |
| Codegen | `src/cgen.rs:604-612`, `src/runtime.c:19-22` | Every call goes through `lust_fns[slot]`. `lust_Vec` is already erased: `lust_vec_push_slot(v, sizeof(T))` at `src/runtime.c:213-216`. This is the seed of the std design in section 3. |
| Panics | `src/runtime.c:111-127` | `lust_panic` prints and aborts. No payload, no recovery, no cleanup on unwind. |

Design rules for all sections:

1. Prefer the simplest design that ports ts-rust. Ts-rust is
   Go-shaped: 591 generic functions (3%), 6 blanket impls, no GATs,
   no proc macros, no unions (INVENTORY summary 1). Do not build
   general Rust where a stated subset covers the evidence.
2. Reject outside the subset with a clear error. Never guess. A
   wrong accept breaks rule zero. A reject only costs a codemod.
3. Keep flat arenas and indices. No pointer trees in hot data.
4. Check cost must grow with the edit. Every new global table needs
   an index and an invalidation rule in section 8.
5. No trait search with backtracking. No global type inference.
   These are perf contracts, not preferences.

## 1. Crate graph and modules

### 1.1 Packages, crates, targets

Lust does not write a Cargo resolver. The driver runs
`cargo metadata --format-version 1` once per workspace session and
caches the result by the hash of all `Cargo.toml` files plus
`Cargo.lock`. Cargo owns version solving. Lust reads: packages
(name, version, manifest path, features, dependencies with rename
and target cfg), targets (kind, name, `src_path`, edition,
`crate_types`), and the resolve graph (which features are on).

Terms:

- A *package* is a Cargo package.
- A *crate* is one target of one package: a lib, a bin, a test, an
  example, or a bench. Each crate has one root file. A crate is the
  unit of name resolution, type checking roots, and daemon
  sessions.
- `build.rs` is not compiled by lust in milestones 4 to 7. The
  driver runs it through Cargo during `lust port prepare`, or
  reads a recorded build-script output. Its `OUT_DIR`,
  `cargo::rustc-cfg`, and env outputs enter cache keys. Ts-rust
  needs this: `goport_util/build.rs` returns early on native
  builds but packs wasm data (DESIGN-TS section 4).
- Test crates: `lust test` builds the lib or bin crate again with
  `cfg(test)` on and `#[test]` fns as extra roots. Integration
  tests in `tests/` are normal bin-like crates that depend on the
  lib crate. Ts-rust's baseline runner is such a target with
  `test = false` in `crates/ts_goport/Cargo.toml`, so target
  handling must not assume `cargo test` semantics.

Ts-rust workspace shape, from `/home/theo/.t3/projects/ts-rust/Cargo.toml:1-9`:
members are `ts_goport`, `parts/goport_lsproto`,
`parts/goport_util`, `ts_wasm`, and two codegen tools. The first
port scope in PLAN.md is the core CLI: package `ts_goport`, bin
`tsgo`, plus its two path dependencies. All other workspace
members stay visible in the graph but unchecked until selected.

Dependency crates split into three classes. The class is a
property of the resolved package id, version, and feature set.
It is never chosen by a source spelling.

| Class | Meaning | Ts-rust examples |
|---|---|---|
| Lust source | Lust compiles the crate from Rust source like user code. | `goport_util`, `goport_lsproto` |
| Adapter | Lust compiles a lust-owned crate with the same public API in place of the dependency. Section 3.6. | `indexmap`, `smallvec`, `rustc-hash` aliases over std maps |
| Shim | A rustc-built static or shared library exports C functions. Lust links it. Section 3.7. | `rustix`, `nix`, `flate2`, `jiff` |

Release always uses the original crates through Cargo. Adapters
and shims exist only in dev builds.

### 1.2 Module tree

A crate starts at its root file. `mod foo;` loads, in edition 2024
order: `foo.rs`, then `foo/mod.rs`, relative to the current
file's directory (or the current inline module's directory).
`#[path = "..."]` overrides the file. Ts-rust has 6 `#[path]`
modules in 3 files (INVENTORY items table), so support it in
milestone 4, not later. Inline `mod foo { ... }` needs no file.
A file belongs to exactly one (crate, module) pair, with one
exception below.

Shared files across crates exist in ts-rust. The two part crates
keep their files under `ts_goport/src/` and enter through
`src/goport_util_root.rs` and `src/goport_lsproto_root.rs`
(`crates/ts_goport/src/lib.rs:1-7` and
`crates/ts_goport/Cargo.toml` comments). The same file can thus be
a module in two crates with different module paths and different
`crate::` meaning. Rule: file text and tokens are cached per
file. AST, defs, and checks are per (crate, module). Never share
a `DefId` across crates for the same file.

Module discovery is a scan, not a full parse. Extend `src/scan.rs`:
at brace depth 0, record `mod` declarations (name, visibility,
`#[path]`, `#[cfg]`), `use` headers, `macro_rules!` names, and
item header hashes. Bodies are hashed, as today at
`src/scan.rs:10-16`. The driver walks `mod` edges from the root
to build the file set. A `mod` edit can add or remove a file;
section 8 makes that a module-tree invalidation, not a full
rebuild.

Each file gets a `FileId` (u32) per workspace session, assigned
in sorted canonical path order at crate load, then append-only.
`FileId` is session-local. It must never enter a disk cache key.
Disk keys use the canonical path string hash instead.

### 1.3 Namespaces and resolution

Rust has three item namespaces: type, value, and macro. Modules
live in the type namespace. Lifetimes have their own per-item
scope (section 5) and do not enter module resolution. Lust keeps
exactly this split. One name can hold a struct (type) and a fn
(value) at once. A tuple struct fills both: the type and its
constructor in value space. A unit struct does the same.

Resolution runs after macro expansion (section 6) and `cfg`
stripping (section 1.6), per crate, in four steps:

1. Build the module tree. Create one `ModuleId` per module.
   Record parent, file, visibility, and the inline/file kind.
2. Collect defined names per module: items, impl blocks (no name),
   trait items, enum variants (namespaced by the enum, plus
   prelude-style value access through the enum path), fields (not
   module names), and macro defs visible by textual scope.
3. Resolve imports to a fixpoint. See below.
4. Resolve every path in signatures, then in bodies, to a `Res`:
   a `DefId`, a local, a primitive, a self type, or an error.
   Bodies resolve in parallel after signatures, as collect and
   check split today (`src/collect.rs:1-2`).

Import fixpoint. Imports form a graph. Globs and re-exports make
it cyclic (`prelude` modules re-export whole subtrees). Algorithm:

- State per module: for each namespace, a map `name -> Binding`.
  A binding is `Def(DefId, Vis)`, `Glob(ModuleId)`, or
  `Ambiguous` marked on use.
- Pass 1: insert all local definitions and all explicit imports
  whose target path resolves without a glob. Explicit imports
  include groups `use a::{b, c as d}`, `self`, and `super`.
- Pass 2, repeat until no change, at most `modules + 2` rounds:
  for each glob `use m::*`, copy each public-enough binding of
  `m` that the local module does not already have from a local
  def or explicit import. If two globs bring the same name with
  different defs, store `Ambiguous`. It is an error only if code
  uses the name (Rust rule; ts-rust's `prelude.rs` relies on
  explicit disambiguation, see section 1.4).
- `pub use` re-exports: the binding in the re-exporting module
  carries the re-export's visibility. The target `DefId` does not
  change. There is no alias def. Effective visibility of a name
  through a path is the minimum visibility along the chain.
- A failed import records a failed-lookup node (section 8):
  `(module, namespace, name, scope_fingerprint)`. Adding a def
  or an import later must re-run the bodies that recorded it.

Determinism: iterate modules in `ModuleId` order and names in
`Sym` order inside each round. The fixpoint result must not
depend on hash map order. Cap: if the round cap hits, emit
`L0130 import cycle does not settle` and stop the crate. Rust
accepts all such graphs; the cap is a compiler bug guard, not a
language limit. Log any hit as a bug.

Path forms to support in milestone 4: `crate::`, `self::`,
`super::` (repeated), `::dep::` absolute extern, bare extern
crate names in 2024 style, `Self`, qualified paths
`<T as Trait>::Item` (needed once traits land; parse in 4,
resolve fully in 5), and paths in type, value, pattern, and
macro positions. `use` inside fn bodies and blocks: support.
Ts-rust has function-local imports. They resolve against the
module tables plus the local scope chain.

Preludes:

- *Std prelude*: the names in `library/std/src/prelude.rs`
  (section 3). Imported into every module as the lowest-priority
  glob. A local def or explicit import with the same name wins.
  `#[no_implicit_prelude]` on a module or crate turns it off.
- *Extern prelude*: each direct dependency's lib crate root is a
  name in the type namespace of every module's first path
  segment, with rename from `Cargo.toml` (`name = "x"` in the
  dependency, and `-` to `_`). Plus `std`, `core`, `alloc`.
  Adapter and shim crates appear here with their real crate
  name, so user source does not change.
- There is no language-level crate prelude. `crate::prelude::*`
  is a normal glob import. It must work well because ts-rust
  uses it in 698 files (INVENTORY: prelude globs 700 in 698
  files).

### 1.4 Why globs must be exact: ts-rust evidence

`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/prelude.rs:1-30`
glob re-exports `ast::*`, `binder::*`, `checker::*`, `core::*`,
and more, then pins collisions by explicit re-export:
`pub use crate::ast::NodeFactory` at line 5 with the comment
that `printer::NodeFactory` must not shadow it, and lines 27-30
pin `factory`, `TypeMapperKind`, `EmitHost`, and others. So:
explicit beats glob, glob-vs-glob ambiguity errors only on use,
and a `pub use` inside a globbed module propagates. Counts from
INVENTORY: glob imports `crate::` 822, prelude 700, `super::`
230; `pub use` 753 in 73 files; use groups 813, renames 45.
Every file uses globs or tuples. This is not an edge case. It
is milestone 4's core.

Macro namespace resolution has two layers (section 6): textual
`#[macro_use]` order inside a crate, and path-based
`crate::mac!` / `dep::mac!` for `#[macro_export]` macros.
Ts-rust needs both: `go_flags!` is `#[macro_export]` in
`goport_util` and re-imported through an inline module at
`crates/ts_goport/src/lib.rs:44-47`.

### 1.5 Visibility

Forms: private (default), `pub`, `pub(crate)`, `pub(super)`,
`pub(in path)`. Private means the defining module and its
descendants. Fields, variants, trait items, and impl methods
follow Rust rules: a trait item is as visible as its trait; an
inherent impl item carries its own visibility; enum variants
take the enum's visibility. `pub` on a non-`pub` re-export chain
does not widen access. Check visibility at path resolution time
for each segment, and again for field and method access in
check. Errors: one code family `L014x`, with a fix hint that
names the smallest widening (`pub(crate)`) that would work.
Do not auto-apply the fix. PLAN.md milestone 3 limits `--fix`
to narrow safe edits; visibility widening changes API surface.

Dead-code and unused-import warnings: out of scope for check
correctness. Unused names must not change ambiguity behavior.

### 1.6 cfg

Evaluate `#[cfg(...)]` and `#[cfg_attr(...)]` during collect,
before resolution, per item, per field, per variant, per match
arm where Rust allows it, and on `mod` declarations before file
loading. `cfg!` expands to a `bool` literal in the expander.

The cfg environment is a fixed set per crate session:
`target_arch`, `target_os`, `target_family`, `target_endian`,
`target_pointer_width`, `target_env`, `target_abi`, `unix`,
`windows`, `debug_assertions` (dev on), `test` (only in test
crates), `feature = "..."` from the resolve graph, and
build-script cfgs recorded by `lust port prepare`. The target
values come from a small built-in table for tier 1 targets
(`x86_64-unknown-linux-gnu`, `aarch64-apple-darwin`) plus
`wasm32-wasip1` for classification only. Do not shell out to
rustc per request.

Rules for unknown cfgs: an unknown *name* (say `cfg(frobnicate)`)
is error `L0150` in lust, listing the known names. Rust treats
it as false with a warning (or an error under `check-cfg`).
Rejecting is safer: silently dropping a module changes the
program. The fix hint says to declare it via build script
output or remove it. Ts-rust cfg counts: 341 `#[cfg]` plus 35
`cfg!`, mostly `wasm` (101), `linux` (51), `windows` (31),
`unix` (26) target families. All are in the known set. One
lust-only cfg name exists: `lust_dev`. It is true in lust dev
builds and false in Cargo release. Adapters may use it.
Application code may use it only for implementation swaps with
equal behavior; `lust port scan` flags other uses. Never fake a
target cfg (say, pretend wasm) to delete threads.

Stripped items leave no def. Diagnostics in stripped code do
not fire. The scan stage still hashes stripped text so edits
there invalidate nothing but the file node.

Attributes other than cfg: parse all. Honor: `derive`, `repr`,
`path`, `macro_use`, `macro_export`, `no_implicit_prelude`,
`inline` (ignored in dev codegen), `cold` (ignored),
`must_use` (ignored in v1, no warning infra), `track_caller`
(real semantics, section 3.5), `allow`/`warn`/`deny` (parsed,
only `dead_code` family ignored), `non_exhaustive` (real check
across crates), `deprecated` (ignored), `doc` (ignored),
`test`, `bench`, `global_allocator` (recorded; dev link picks
the allocator, section 3.7). Unknown attributes: `L0151`
error with the supported list. Ts-rust uses `must_use` 1,215,
`inline` 713, `cold` 93, `track_caller` 16, `allow` 106.

### 1.7 Stable DefIds

Today a fn's stable identity is a slot keyed by `(name, owner)`
at `src/driver.rs:43`, and `FnId` shifts on edits
(`src/driver.rs:40-42`). The disk cache, the daemon overlay
table, the fuzzer, and panic line tables all depend on this
identity. Multi-crate code needs the general form now, before
parallel work starts. This is serial refactor S2 (section 9.2).

Definitions:

```rust
pub struct CrateId(pub u32);      // session-local, dense
pub struct DefPathHash(pub u64);  // stable across sessions
pub struct DefId { pub krate: CrateId, pub hash: DefPathHash }
pub struct LocalDefId(pub u32);   // dense index inside one crate, per session
```

A `DefId` answers "which item is this" across edits and across
daemon restarts. A `LocalDefId` is the fast array index inside
one crate session. The crate session keeps
`FxMap<DefPathHash, LocalDefId>` and `Vec<DefId>` side tables.
Only `DefId` (never `LocalDefId`, `FileId`, or `Sym`) may enter
disk keys, slot keys, or fuzzer transcripts.

`DefPathHash` inputs, hashed with the existing FxHash
(`src/intern.rs:9-41`):

1. Crate disambiguator: hash of the package id string from
   Cargo metadata (name, version, source). For path packages,
   the workspace-relative manifest path replaces the source,
   so two checkouts of one workspace share hashes on one
   machine. Two path deps with the same name and version in
   one workspace are a Cargo error already.
2. The target kind and target name (`lib`, `bin:"tsgo"`, ...).
   The same lib compiled as a test crate gets a distinct
   disambiguator suffix `:test`. Test and non-test defs must
   never collide in the instance cache.
3. The module path: each segment's name string (not `Sym`,
   which is session-local), from the crate root.
4. The item kind tag and item name string.
5. A disambiguator for name-less or same-name items, below.

Name-less and synthetic items:

| Item | Disambiguator |
|---|---|
| Impl block | Hash of the normalized impl header tokens (generics, trait path, self type, where bounds), plus an ordinal among impls in the same module with equal header hash, in file order. Body edits keep the id. A header edit makes a new id. That is correct: the old impl is gone. |
| Method, assoc type/const/fn | Parent impl or trait hash plus item name. |
| Closure | Parent fn hash plus the closure's ordinal in that body, in token order. An inserted closure above shifts later ordinals. Only cache reuse is lost. Correctness never depends on it because instance keys add the body fingerprint. |
| `impl Trait` opaque | Parent fn hash plus return-position ordinal. |
| Derived impl | Adt hash plus the trait name (`derive:Debug`). |
| Static inside `thread_local!`, `const` in a body | Parent hash plus item name plus ordinal among same-name items in the parent. |
| Macro-generated item | The item's own module path and name, as if hand-written. The expansion site does not enter the hash. Two expansions that generate the same item name in one module are a duplicate-def error, as in Rust. |

Collisions: a 64-bit hash collision inside one crate is
detected when two distinct def paths map to one hash; emit an
internal error and stop. Do not add a collision-resolution
scheme. At 786k lines the birthday risk is negligible, and the
check makes it safe.

Slots generalize directly: `slot_of: FxMap<DefPathHash, u32>`
per crate for fn-like defs, and per instance in section 4. The
panic line table keys by slot as today. The fuzzer compares
diagnostics by (crate, module path, name), never by `FnId`.

What a `DefId` is not: it carries no generic arguments, no
types, and no span. Renaming an item changes its `DefId`. That
is intended: a rename is a delete plus an insert for caches,
and section 8 handles dependents through signature nodes.

### 1.8 Daemon sessions per crate

Replace per-file sessions (`src/daemon.rs:22-25`) with:

```text
Daemon
  WorkspaceSession per (workspace root, lust version)
    Interner (one, shared by all crates)
    Cargo graph (cached metadata)
    CrateSession per SessionKey
      Front: files, tokens, ASTs, module tree, defs
      Checks: per-DefId generic checked bodies
      Mono: instance table and slots
      Caches: C text, objects, libbase overlays
    File index: canonical path -> set of (CrateId, ModuleId)
```

`SessionKey` = (crate disambiguator, feature set hash, cfg
environment hash, profile, lust version, adapter/shim versions
for its deps). One shared `Interner` per workspace matters:
`Sym` values must mean the same string in every crate, or
cross-crate signature exchange needs translation tables. The
interner is already sharded and thread-safe
(`src/intern.rs:56-68`).

Request routing: the protocol gains a crate selector. New wire
form (keep tab-separated lines, add fields): manifest path,
package, target, features, then the file the user named. If the
user names a file, the daemon finds its crate through the file
index; if the file is in two crates (shared part files), the
request must name the target or the daemon checks the
"primary" crate (the one whose root owns the file by `mod`
reachability from a lib target first, then bins, in metadata
order) and says which crate it picked in the response. Silent
guessing is not allowed.

Cross-crate flow: a crate session reads dependency crates only
through their *signature surface*: defs, generic signatures,
layouts of `pub` types, impl headers, macro defs, and const
values. Dependency bodies are needed only at monomorphization
for generic fns and `#[inline]`-style cross-crate generics,
which in dev means all generic fns (mono is per final bin).
So each crate keeps checked generic bodies in memory for its
dependents. No rlib or metadata file format in milestones 4
to 9. Cold builds compile crates in dependency order in one
process. The disk cache (section 8) stores per-instance C and
objects, keyed across crates, so a cold daemon restart does
not redo codegen.

Session eviction: keep at most the crates of the last two
workspaces in memory. Ts-rust's full graph at 786k lines will
not fit a naive per-crate clone of today's `Front`. ASTs of
dependency crates can drop after collect if the crate has no
generic fns used downstream; keep defs and signatures. Measure
at milestone 8 and tune. Do not build an eviction policy
before there is a memory number.

## 2. Types and the trait system

### 2.1 Type representation

Replace the closed `TyKind` (`src/types.rs:82-104`) with an
open, interned form. Keep `Ty(pub u32)` and the two-level
global-plus-local interning (`src/types.rs:130-197`). The
global table holds signature types and is frozen after
collect. Body-local overlays hold inference state. One change
is forced: `TyKind` can no longer be `Copy` with inline
payloads only, because generic args are slices. Store arg
lists in an interned slice arena next to the kind arena.

```rust
pub enum TyKind {
    Error, Unit, Bool, Char, Never,
    Int(IntTy),          // add I128, U128
    Float(FloatTy),      // F32, F64
    Str,                 // unsized str
    Ref(Region, Mut, Ty),
    RawPtr(Mut, Ty),     // std and shim code only at first
    Slice(Ty),
    Array(Ty, ConstId),
    Tuple(ArgsId),       // ArgsId indexes interned &[Ty]
    Adt(DefId, ArgsId),  // user and std structs/enums/unions(none)
    FnPtr(SigId),        // SigId: interned (inputs, output, safety, abi)
    FnDef(DefId, ArgsId),// fn item used as a value, before coercion
    Closure(DefId, ArgsId),
    Dyn(BoundsId, Region),
    Opaque(DefId, ArgsId),        // impl Trait return
    Param(ParamId),               // index into the current Generics
    Projection(AssocId, ArgsId),  // <Self as Trait>::Assoc, unnormalized
    Infer(InferId),               // body-local only, never in global tys
}
```

Supporting interned data, all in `src/ty/`:

- `GenericArg = Ty(Ty) | Lifetime(Region) | Const(ConstId)`.
  `ArgsId` interns `&[GenericArg]` in declared parameter
  order: lifetimes, types, consts interleaved as written.
  Store the slice once; hashing a `Ty` stays O(1).
- `Region = Static | Param(u32) | Infer(u32) | Erased`.
  `Param` indexes the lifetime params of the item whose
  signature the type sits in. `Erased` appears only after
  borrow checking, at mono and codegen. Section 5 owns the
  rules. In milestone 4, all regions are `Erased` except the
  std-internal handling that exists today through
  `ret_borrows_from` (`src/collect.rs:52-53`), which the
  region work replaces in milestone 6.
- `ConstId` interns const generic values and const item
  values: ints, bools, chars, and const param references.
  A tiny const evaluator handles literals, arithmetic on
  literals, `size_of`/`align_of` of sized types (section
  4.4), and assoc const lookup. Anything else in const
  position is `L0240` reject. Ts-rust needs const generics
  in only 3 functions (INVENTORY), so keep the evaluator
  small and reject the rest.
- `BoundsId` interns a `dyn` bound list: one principal trait
  ref, plus auto traits (`Send`, `Sync`, `Unpin`) as bits.
- `SigId` interns fn pointer signatures, including
  higher-ranked binders: `for<'a> fn(&'a T) -> U` stores a
  binder count; regions inside use de Bruijn indices in a
  `BoundRegion` form. Only rank-1 binders. See 2.9.

`String`, `Vec<T>`, `Option<T>`, `Chars`, `Args` stop being
`TyKind` cases. They become `Adt` defs in the std crates
(section 3). This is the single biggest representation
change. It deletes special paths in `collect.rs`,
`check.rs`, `ir.rs`, and `cgen.rs` and replaces them with
the general Adt path. Do it in serial refactor S3 with the
std skeleton (S5) so the general path has real users from
day one.

Every def that can be generic owns a `Generics`:

```rust
pub struct Generics {
    pub parent: Option<DefId>,       // impl or trait for a method
    pub params: Vec<ParamDef>,       // lifetime, type, or const; name, span
    pub predicates: Vec<Predicate>,  // bounds, in source order
}
pub enum Predicate {
    Trait(TraitRef),                 // T: Clone, T: Iterator<Item = u8>
    Outlives(Region, Region),
    TypeOutlives(Ty, Region),
}
pub struct TraitRef { pub def: DefId, pub args: ArgsId } // Self is args[0]
```

Bounds written as `T: A + B`, in `where` clauses, and on
assoc types all become predicates in source order. Source
order is observable in error messages only. Keep it anyway;
it costs nothing.

Substitution is one function: `subst(ty, args, tys) -> Ty`.
It replaces `Param` by args, normalizes projections when
the impl is known (2.5), and erases nothing. Mono calls it
on every type in a generic body. It must be allocation-light:
return the input `Ty` unchanged when the type contains no
params. Track "contains param/projection/infer" as flag bits
cached per `Ty` in the interner, computed at intern time.

### 2.2 Definitions and signatures

Collect grows from `AdtDef` and `FnInfo`
(`src/collect.rs:35-55`) into a `Defs` table per crate:

```rust
pub enum DefKind {
    Module, Struct, Enum, Union, Variant, Field,
    Trait, TraitAlias(no: reject), AssocTy, AssocConst, AssocFn,
    Fn, Method, Const, Static, TypeAlias, Macro,
    Impl, Closure, Opaque, ForeignFn, ForeignStatic,
}
pub struct DefData {
    pub kind: DefKind, pub parent: Option<DefId>,
    pub name: Sym, pub module: ModuleId, pub vis: Vis,
    pub generics: Generics, pub span: Span,
    pub sig: SigData, // per-kind payload, resolved types only
}
```

Signatures resolve fully in collect, as today: fields,
variant payloads, fn params and returns, trait items with
defaults, assoc type defaults, const types, alias targets.
A signature may contain `Param`, `Projection`, and
`Opaque`. It may never contain `Infer`. Bodies check after
all signatures in the crate (and its deps' signature
surface) are frozen. This preserves the parallel body check
that makes lust fast (`src/collect.rs:1-2`).

Type aliases: transparent. `resolve_ty` expands an alias to
its target with args substituted, and records the alias def
in a side table for error messages ("type `Foo` is
`Bar<T>`"). Associated-type aliases in traits are defs, not
expansions. Generic aliases: 44 in ts-rust. Alias cycles
through non-Adt positions (`type A = B; type B = A;`) are
`L0210`. Recursive types through `Box`, `Vec`, `Rc`, refs,
and fn ptrs are fine. The infinite-size check at
`src/collect.rs:332` generalizes: a cycle in the
by-value field graph of Adts is an error.

Derives become synthetic impls at collect, one `DefId` each
(1.7). Supported: `Clone, Copy, Debug, Default, PartialEq,
Eq, PartialOrd, Ord, Hash`. Ts-rust counts: Clone 1,262,
Debug 1,137, PartialEq 573, Copy 427, Eq 379, Hash 151,
Default 936, PartialOrd 60, Ord 59. A derive expands to the
same impl shape rustc generates: field-wise, with bounds on
the Adt's type params as rustc adds them. The bodies are
synthetic IR built by collect, not source. Keep today's
derive validation idea (`src/collect.rs:306-330`) but emit
real impls so traits, mono, and drops all see one path.

### 2.3 The impl index

All trait selection goes through one index. Build it at
collect, per crate, then merge visible deps' indexes by
reference (never copy impl bodies).

```rust
pub enum SelfHead {
    Adt(DefId), Ref, RefMut, RawPtr, Slice, Array,
    Tuple(u16), Str, FnPtr, Dyn(DefId), // DefId = principal trait
    Int(IntTy), Float(FloatTy), Bool, Char, Never, Unit,
    Param,    // blanket: impl<T> Trait for T (optionally wrapped, see below)
    Infer,    // transient, never stored
}
// Index key: (trait DefId, SelfHead) -> SmallVec<ImplId, 2>
```

`head_of(ty)`: `Adt(d, _)` to `Adt(d)`; `Ref` to `Ref` or
`RefMut` by mutability? No: Rust treats `impl Trait for &T`
and `for &mut T` as distinct Self types that can overlap in
lookup only through the exact Self type, so the head must
distinguish them. Keep `Ref`, `RefMut`. `Param` self types
in an impl header (`impl<T> Tr for Vec<T>`) head to
`Adt(Vec)`; the param is inside the args. Only a bare param
Self, or a bare param under one reference or one known
smart-pointer Adt (`Box`, `Rc`, `Arc`), heads to `Param`
with a wrapper tag stored on the impl. These are the
blanket forms lust accepts (2.6).

Each impl stores: trait ref pattern (Self type pattern plus
trait args, with `Param`s for the impl's generics),
predicates, assoc bindings, item `DefId`s, a coherence
fingerprint, and its crate. Orphan rules: enforce Rust's
rule as written (the trait or a covering type must be
local). Ts-rust obeys it. Enforcing it keeps the index
merge sound: two crates cannot both add the impl that wins
a lookup in a third crate.

Method index, separate from the impl index:
`(SelfHead, method name) -> candidates`, split into inherent
and trait candidates. Trait candidates carry the trait
`DefId` so check can require the trait to be in scope.
Build it from the same collect pass. Method resolution is
in 2.10.

### 2.4 Obligations without search

Per body, check keeps a work queue, extending the current
unification context (`src/check.rs:196-215`). An obligation
is `TraitRef` plus the span that needs it plus an optional
assoc binding to prove. Selection algorithm:

1. If Self or any trait input arg contains an unresolved
   `Infer`, defer the obligation. (Assoc outputs may stay
   unknown; they are outputs, not inputs. This is DESIGN's
   one-candidate rule, kept.)
2. If the obligation matches a predicate in the current
   *param env* (the bounds of the enclosing generic item,
   after substitution), select `ParamEvidence`. No impl
   lookup runs. Mono re-solves with concrete types.
3. Else look up `(trait, head_of(Self))` in the impl index.
   For each impl in the bucket (coherence, 2.6, proves at
   most one can match a concrete Self), try first-order
   *matching*: unify the impl's Self pattern against the
   known Self type. Pattern params bind once. There is no
   backtracking across impls and no guessing of impl
   params from predicates. If matching leaves an impl
   type param unbound, defer; if still unbound at body
   end, error `L0220 type annotations needed` with the
   fix naming the param.
4. On a match, push the impl's predicates (substituted) as
   new obligations. Memoize by `(TraitRef)` in the body.
   Depth cap 64 and a cycle set: re-entering the same
   `TraitRef` on the stack is `L0221` (overflow), matching
   rustc's overflow class.
5. If the bucket is empty or no pattern matches, record a
   failed lookup (section 8) and error `L0222 no impl of
   Trait for Type`, listing the bucket's impls when the
   bucket is non-empty.

Queue processing: run after each expr that binds an
`Infer`. At body end, run to fixpoint. Anything left is an
annotation error, never a silent default, except integer
and float literal fallback (`i32`, `f64`, as today).

What this rejects that rustc accepts: obligations where an
impl param is determined only by the impl's predicates or
by an assoc output used as an input elsewhere. The fix
hint tells the agent to add a turbofish or annotation.
`lust port scan` reports sites; a checked codemod adds the
annotation (it does not change machine code). This is the
price for no search. Ts-rust is Go-shaped and mostly
concrete (3% generic fns), so the count should be small.
Measure in the milestone 5 spike. If it is large, widen
step 3 to bind impl params from assoc bindings on the
obligation itself. Do not add backtracking.

Auto traits and `Sized` do not use the queue. They compute
structurally (2.7). `Drop` is not an obligation; drop glue
asks "does this type have a `Drop` impl or droppable
fields" directly.

### 2.5 Associated types and consts

A trait def lists assoc items. An assoc type use
`<S as Tr>::A` becomes `Projection(assoc_def, args)`
where args are the trait ref (Self first). Normalization:

- If the trait ref selects a concrete impl (2.4 step 3),
  the projection rewrites to the impl's binding, then
  normalization recurses.
- If it selects `ParamEvidence` and the param-env predicate
  carries an assoc binding (`T: Iterator<Item = u8>`),
  rewrite to that binding.
- Else it stays a `Projection` type inside the generic
  body. It unifies only with the identical projection or
  through a binding that appears later. Mono normalizes
  it after substitution. A projection that survives mono
  is a compiler bug, not an error path.

Assoc consts: same shape, values are `ConstId`s evaluated
by the const evaluator. Ts-rust declares 2 user assoc
types and uses std assoc types (`Item`, `IntoIter`,
`Target`, `Output`) in 66 impls. Example: `IntoIterator`
for `&SharedList<T>` at
`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/checker/types.rs:289-296`
binds `Item = &'a T` and `IntoIter = slice::Iter<'a, T>`.
Assoc const example: `ExpectedJsonKind::JSON_TYPE`
(DESIGN-TS section 3). GATs (assoc types with their own
params): reject `L0230`. Ts-rust has none.

`?` desugars through `Try` in Rust, but lust implements
`?` as a direct match on `Result` and `Option` plus
`From::from` error conversion, checked as a normal
obligation. User `Try` impls: reject. Ts-rust uses `?`
2,422 times (plus 5,516 generated) on `Result` and
`Option`. The direct form covers it and skips a
not-yet-stable-in-spirit trait.

Operator traits (`Add`, `BitOr`, `Index`, `Deref`, and
kin) are normal traits. Binary operator syntax checks the
builtin scalar path first, then the trait path with one
obligation. `go_flags!` generates `BitOr::Output`
impls at
`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/flags_macros.rs:53-58`,
so assoc `Output` must normalize in operator result types.

### 2.6 Coherence and blanket impls

At collect, for each `(trait, head)` bucket, check every
pair of impls for possible overlap: unify their Self
patterns and trait input args. If unification can succeed,
the pair is an overlap. Then:

- Two concrete impls overlap: `L0225`, as in Rust.
- A blanket impl and any impl whose Self pattern can unify
  with the blanket's Self form: `L0225`. So a blanket
  `impl<T: A> Tr for T` forbids every other `Tr` impl
  whose Self is not disjoint by head wrapper. In
  practice: one bare-param blanket per trait, or blankets
  partitioned by wrapper head.

This is stricter than rustc in one way: rustc also rejects
overlaps it cannot disprove, so the practical difference
is small. It is looser in no way. Do not try to prove
disjointness from predicates (`impl<T: A> Tr for T` vs
`impl<T: B> Tr for T`): reject. Rust rejects these too.

Accepted blanket Self forms, stored with a wrapper tag:
`T`, `&T`, `&mut T`, `Box<T>`, `Rc<T>`, `Arc<T>`. The head
is `Param` plus the wrapper; at lookup, after the concrete
bucket misses, check checks the blanket bucket for the
trait whose wrapper matches the Self type's outer shape,
binds `T`, and pushes the blanket's predicates. Order is
deterministic: concrete bucket first, then exactly one
applicable blanket bucket by wrapper shape. Coherence
above guarantees the two never both apply to one Self.

Ts-rust's 6 blanket impls fit this subset:

- `impl<T: Any + MarshalerTo + Debug + Send> AnyValue for T`
  at `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/frontend/json_ext.rs:43-47`.
  Bare param. `AnyValue` has no other impls.
- `impl<T: MarshalerTo + ?Sized> MarshalerTo for &T` at
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/frontend/json.rs:1660-1664`.
  `&T` wrapper. Concrete `MarshalerTo` impls are on Adt
  heads, disjoint from `Ref`. This is why the head split
  by wrapper is the key point: bucket it under `Ref`, not
  under a global blanket bucket, and both this rule and
  the solver stay simple. Refine the index: a blanket
  with wrapper `&T` sits in the `Ref` bucket as a param
  pattern. Bare `T` sits in a per-trait `Param` bucket
  checked after all head buckets.

Generic impls on named containers (178 in ts-rust), impls
for `&T` (6), and impls for `dyn Trait` (6) are normal
index entries. Negative impls, specialization, and
overlapping marker traits: reject. None exist in ts-rust.

### 2.7 Auto traits: Send, Sync, Unpin, and Sized

`Send`, `Sync`, `Unpin` compute structurally per type:

- Scalars, `&T`, fn ptrs: by fixed table (`&T: Send` iff
  `T: Sync`; `&mut T: Send` iff `T: Send`; `*const T`:
  neither, as in Rust).
- `Adt`: all field types (with args substituted) must
  hold the trait, combined with the Adt's own marker
  fields. `PhantomData<T>` contributes `T`'s auto traits,
  including the raw-pointer marker idiom ts-rust uses
  (DESIGN-TS section 6 cites `core.rs:4467`).
- Std overrides live in the std source as explicit
  negative facts through private marker fields
  (`Rc` holds a `*mut` plus a non-atomic count cell, so
  the structural rule already yields neither `Send` nor
  `Sync`; `RefCell` is `Send` if `T: Send`, never `Sync`,
  via its borrow flag cell). Where structure alone gives
  the wrong answer (`Mutex<T>: Sync` if `T: Send`), std
  uses the privileged `unsafe impl` form. User code may
  write `unsafe impl Send/Sync` only under the opt-in
  `unsafe` support (PLAN.md decision 3). Ts-rust has no
  `unsafe impl` in its own code.
- Closures: from capture types. `dyn`: from its bound
  bits. Params: from the param env. Cycles through Adts:
  compute by fixpoint with a three-state lattice
  (yes/no/in-progress-as-yes-then-verify), memoized per
  `(Ty, trait)`. Store results in the crate session;
  invalidate by the Adt's signature fingerprint.

`Sized`: every type param has an implicit `Sized` bound
unless written `?Sized`. Unsized types: `str`, `[T]`,
`dyn Trait`, and structs whose last field is unsized (the
struct is then unsized; only `FileRef`-style uses in
ts-rust need this, DESIGN-TS section 2). Unsized values
may only sit behind a pointer-like (`&`, `&mut`, `Box`,
`Rc`, `Arc`, raw ptr) or as the last field. Check this at
collect for fields and at check for locals and params.
`?Sized` bounds appear 203 times in 14 ts-rust files, so
this is core, not polish.

Where checks fire: `thread::spawn` and `scope` (7.3),
shared statics (`Sync`), `Arc`/`Mutex` bounds in std
signatures (they are normal predicates that the
structural solver answers), and `dyn` bounds that name
auto traits.

### 2.8 dyn Trait and vtables

`Dyn(BoundsId, Region)`. Object safety, checked at the
`dyn` type's span: no `Self: Sized` methods callable, no
generic methods, no assoc consts, assoc types must be
bound (`dyn Iterator<Item = u8>`) or the method using
them must be excluded by `where Self: Sized`. Non-object
-safe use is `L0250` with the method named. Supertraits
are allowed if object-safe. `dyn` with two non-auto
principal traits: reject (Rust rejects too).

Dev representation: a fat pointer `{ data: *mut (), vtable:
*const VTable }` (section 4.4 for the C form).

```c
struct lust_vtable {
    void (*drop_in_place)(void *);
    uint64_t size, align;
    uint64_t type_id;              // for Any, else 0
    const struct lust_vtable *super_0; // one slot per supertrait, in trait-decl order
    // then one fn ptr per object-safe method, in trait declaration order
};
```

Rules:

- One vtable instance per `(concrete type, dyn bounds)`,
  emitted as a static in the glue unit, deduplicated by
  mono like an instance (section 4). Method entries point
  at slot trampolines (4.5), never at a body address, so
  a daemon overlay edit cannot leave a stale callback.
  DESIGN-TS section 3 states this requirement.
- Upcasting `dyn Sub` to `dyn Super` uses the `super_N`
  slots. Multi-level upcasts chain at check time to a
  fixed slot path; no runtime search.
- `Any`: `type_id` is the low 64 bits of the concrete
  type's fingerprint: `DefPathHash` of the Adt plus a
  hash of its args with regions erased. `TypeId::of::<T>`
  in lust std computes the same value at mono time.
  `downcast_ref`/`downcast` compare ids, then reinterpret
  data. A hash collision here is the same accepted risk
  as 1.7, and dev-only: release uses real Rust `Any`.
- Unsizing coercions supported: `T -> dyn`, and inside
  `&`, `&mut`, `Box`, `Rc`, `Arc`, plus `Rc<RefCell<dyn>>`
  style nesting through one smart pointer whose pointee
  unsizes. Array-to-slice unsizing in the same positions.
  Coercion sites are recorded in `Checked` like today's
  `Coerce` (`src/check.rs:117-128`); extend that enum.

Ts-rust scale: 1,917 `dyn` types, 94 user traits, `dyn Fn`
285, `dyn FnMut` 233, containers `Rc` 667, `&` 498, `Box`
316, `Arc` 109. `dyn Any` with downcasts: 127 uses. The
visitor aliases at
`/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/ast/visitor.rs:26-33`
(`Rc<dyn Fn(Node, &mut NodeVisitor) -> Node + 'a>`) are
the design center: regional `dyn Fn`, inside `Rc`, held
in struct fields, called recursively.

### 2.9 Closures and Fn traits

Each closure expression gets a `Closure` def (1.7). Its
type is `Closure(def, args)` where args are the capture
types in capture order. At codegen it is an anonymous
struct of its captures (4.4).

Capture analysis (edition 2024 precise captures): walk
the closure body, record each used place as (local,
projection path). Capture the smallest prefix place that
covers all uses of one local, per Rust's disjoint capture
rules. Capture kind: by ref, by mut ref, or by move,
upgraded by use (move out forces move; mutation forces
mut ref; `move` keyword forces move for `Copy`-eligible
places a copy, as in Rust). The capture list is fixed at
check time and stored on the def. Borrow checking treats
the closure value as holding those loans (section 5).

Trait implementation, decided by body use of captures:

- Moves a capture out, or drops a by-move capture and the
  closure can run again: `FnOnce` only.
- Else mutates a capture: `FnMut` and `FnOnce`.
- Else: `Fn`, `FnMut`, `FnOnce`.

These are synthetic impls in the index, keyed by the
closure def. The `Fn` traits use sugar: `Fn(A, B) -> C`
is a `TraitRef` with args `(Self, (A, B))` plus assoc
`Output = C`. Higher-ranked `Fn(&T)`: the principal use
(545 implicit cases in ts-rust) is a rank-1 binder over
the ref regions in the args. Represent `for<'a> Fn(&'a
T)` by a binder on the `TraitRef` in predicates and
`dyn` bounds. At call sites, instantiate the binder with
fresh region vars. No other higher-ranked forms:
binders on fn *items* are just their lifetime params;
binders nested under another binder are `L0260`.

Closure signature inference: from the expected type when
it is an `Fn` bound, a `dyn Fn`, or a fn ptr; else from
annotations on params; else params get fresh `Infer`s
resolved by body use. If a param `Infer` survives, error
`L0220` asking for an annotation on that param. Stored
closures with no expected type are the common failure;
ts-rust stores 349 in `let`s. Most get types from use
sites in the same body through unification. The rest
need one annotation each. That is an accepted codemod
class (it does not change machine code).

`FnOnce` call consumes the closure value (or the box
pointee). Through `dyn FnOnce`, the vtable method takes
`Box<Self>`-style ownership of data and drops the env
after the call. Calling a `dyn FnMut` needs `&mut` to the
fat pointer's data. Check enforces these receiver rules.

Function items as values: type `FnDef(def, args)`,
zero-sized, implements the `Fn` traits its signature
matches, coerces to the fn ptr `FnPtr(sig)`. Typed
receivers (`self: &Rc<Self>`, 168 uses in ts-rust):
support receiver types `Self`, `&Self`, `&mut Self`,
`Box<Self>`, `Rc<Self>`, `Arc<Self>`, `Pin<&mut Self>`
(std only at first). Method resolution handles them by
receiver type matching, not by autoderef alone (2.10).

### 2.10 Method resolution

Input: receiver type `R`, method name, arg types,
expected result. Algorithm (Rust's, restricted):

1. Build the autoderef chain: `R`, then `*R` via `Deref`
   (or `DerefMut` when a `&mut` receiver or a unique
   place is needed), repeatedly. Cap 32 steps. Builtin
   derefs: `&T -> T`, `&mut T -> T`, `Box/Rc/Arc<T> -> T`
   (through their `Deref` impls, not special-cased, once
   std is source), `[T; N] -> [T]`, `String -> str` via
   `Deref`. Record each step's type.
2. For each step type `S`, in order, probe receiver forms
   in Rust's order: by value `S`, then `&S`, then `&mut
   S`. For each form, look up inherent methods first
   (exact receiver type match up to the form), then
   trait methods whose trait is in scope (imported or
   prelude) and whose Self pattern matches. First hit
   wins. Two trait hits in the same probe with different
   traits: `L0270 ambiguous method`, fix hint gives the
   fully qualified form. Inherent and trait in the same
   probe: inherent wins, as in Rust.
3. Typed receivers (`self: Rc<Self>`) match when any
   chain step equals the pointee and the actual receiver
   place has the smart-pointer type. No autoderef runs
   for that candidate.
4. On a hit, create obligations for the method's bounds
   and unify args. Generic method params come from args
   and the expected type. `?Sized` Self types (`str`
   methods on `&String`) work through the deref chain.
5. No hit: record a failed method lookup keyed by
   `(head_of(R), name)` for invalidation, then error
   `L0271` listing same-name methods on other types.

Field access: autoderef to the first Adt or tuple with
the field, checking field visibility. `dyn` has no
fields. Index syntax goes through `Index`/`IndexMut`
obligations after the builtin slice/array/Vec paths,
which are std impls once std is source, so there is one
path: obligations. Keep a fast path only if profiles
demand it.

Current code hardcodes all of this per `Builtin`
(`src/check.rs:1002-1227`). The method index plus this
algorithm replaces it. Autoref/autoderef bookkeeping
already exists in `Res::Method { derefs, autoref }` at
`src/check.rs:91-100`; extend the recorded form to a
small `MethodRes { def, args, derefs, autoref,
receiver_coerce }`.

### 2.11 impl Trait

- Argument position (`fn f(x: impl Clone)`): sugar for a
  fresh type param, exactly as in Rust. 371 uses.
- Return position: an `Opaque` def per (fn, position).
  Check records the hidden concrete type from the body.
  All return paths must give the same hidden type.
  Captures follow edition 2024 rules: the opaque captures
  all in-scope type and lifetime params unless `use<>`
  restricts. Support `use<>` syntax; ts-rust uses it once
  (DESIGN-TS section 3, `impl Send + use<>`). Callers see
  only the bounds. Mono substitutes the hidden type.
  Returning different closure types per branch: reject
  unless they unify, as in Rust.
- `impl Trait` in assoc type position and in `let` type
  ascriptions: reject. Not used in ts-rust.

40 return-position uses in ts-rust, mostly `impl
Iterator`. Iterator fusion (4.3) sees through the opaque
inside the defining crate only at mono time, never at
check time across the boundary. That keeps fusion sound
without making the opaque transparent to callers.

### 2.12 Inference boundary

Inference stays body-local, as today (`src/check.rs:1-2`),
plus these stated inputs: expected types flow down from
signatures, `let` ascriptions, return position, struct
field types, and `Fn` bounds for closures. Generic args
at a call come from: explicit turbofish, arg types,
the receiver, assoc bindings written at the use, and the
expected result type. `collect` gets its target from the
expected type or turbofish; ts-rust writes the target
explicitly in only part of its 804 collects, the rest
come from ascriptions and field types, which the expected
type flow covers.

Not inferred, by design: types across fn boundaries
(signatures stay explicit in source, as in Rust), impl
params from predicates alone (2.4), closure param types
with no expected `Fn` and no body constraint, and numeric
types beyond literal fallback. Each gap errors with the
specific missing annotation. This is the "how far beyond
local" answer: no further. The deterministic solver is
what keeps check near-linear and independently
re-runnable per body, which the daemon depends on.

## 3. Std strategy

### 3.1 The decision

Write std in lust source. Ship it with the compiler as
three crates under `library/` in the lust repo:

```text
library/core/    no OS, no alloc: traits, Option, Result, iter adapters,
                 fmt traits, slice/str methods, mem, cmp, hash, num
library/alloc/   heap types: String, Vec, Box, Rc, Arc, collections,
                 format!, Cow, BTreeMap
library/std/     OS: fs, io, env, process, path, time, thread, sync,
                 panic runtime hooks, prelude
library/deps/    adapter crates (3.6): indexmap, smallvec, rustc-hash
```

Lust compiles these crates with lust itself, once per
(lust version, target, profile) tuple, and caches the
result on disk like Go's build cache (PLAN.md decision
1). A user crate's `std` dependency is implicit, rooted
at `library/std`. The prelude (1.3) is
`library/std/src/prelude.rs`.

Why source, not more `Builtin` cases: today each std
method costs edits in four places (`check.rs` typing,
`ir.rs`, `cgen.rs`, `runtime.c`). The `Builtin` enum has
about 55 cases for a tiny surface. Ts-rust touches 24,879
`Vec`/`String`/`Option` paths alone (INVENTORY std
table), plus `Result`, iterators with 3,516 chains,
`Rc`/`RefCell` in 2,608 functions, and the `io`/`fs`/
`time` surface. As source, a new std method is one lust
fn: check, borrowck, mono, and codegen already handle
it. Std bugs become difftest programs, not compiler
hacks. And generic std code monomorphizes with the same
machinery as user generics, which VERIFY G requires:
almost all real instances come from std, not user
generics (VERIFY G section P1).

Std source is privileged in exactly two ways:

1. It may use the intrinsic functions in 3.2, through a
   private module `core::intrinsics`. The checker allows
   `intrinsics` calls only in crates whose manifest the
   compiler ships (matched by crate disambiguator of the
   shipped library), never by name matching in user
   source.
2. It may use `unsafe` blocks, raw pointers, and
   `UnsafeCell`. This is the opt-in `unsafe` from
   PLAN.md decision 3, scoped to shipped crates first.
   User crates get `unsafe` only for shim-facing code
   in milestone 7, behind the same checker support.

Std source must be valid Rust, like all lust programs.
Where real Rust std uses compiler internals lust lacks
(`#[rustc...]`, lang items), lust std writes the plain
equivalent. It does not need to compile under rustc as a
replacement std. It needs to behave the same through
its public API in programs lust accepts. Rule zero
compares program output, not std internals.

Lang items the compiler must know by def, looked up once
when the std crates load, by a `#[lust_lang = "..."]`
attribute in std source (unknown to rustc; std source is
never fed to rustc): `Option`, `Result`, `String`,
`Vec`, `Box`, `Rc`, `Arc`, `UnsafeCell`, `PhantomData`,
`Range` family, `Iterator`, `IntoIterator`, `Drop`,
`Deref`, `Fn` traits, `Sized`, `Send`, `Sync`, panic
entry points, `Formatter`, exchange malloc hooks. Keep
the list in one table in `src/ty/lang.rs`. A missing
lang item at std load is a compiler installation error,
not a user diagnostic.

### 3.2 What stays intrinsic

Intrinsics are the only compiler-known callables left.
They replace the `Builtin` enum with a small, stable set.
Target: about 40. Each intrinsic has a normal fn
signature in `core::intrinsics`, a C symbol, and a
difftest. Codegen emits the C call directly; there is
no IR node per intrinsic family beyond "call this
runtime symbol with this signature". Sized operations
take explicit size and align (the erased-core rule).

| Group | Intrinsics (C symbol) | Why not source |
|---|---|---|
| Memory | `alloc(size, align)`, `dealloc(ptr, size, align)`, `realloc(...)`, `alloc_zeroed` | Must call the process allocator (3.7). Align up to 4 MiB must work (`jemalloc_layout.rs:66` in ts-rust). |
| Bytes | `memcpy`, `memmove`, `memset`, `memcmp` (ptr, len forms) | One call each in C; source loops are slower and touch raw ptr rules everywhere. |
| Ptr | `ptr_read`, `ptr_write` (typed in std wrappers), `ptr_offset` | The typed API is source. The raw load/store is one intrinsic so borrowck has one unsafe boundary. |
| Float text | `fmt_f64`, `fmt_f32`, `parse_f64`, `parse_f32` | Shortest round-trip printing and correctly rounded parsing, byte-exact with Rust (3.5). C code, fuzz-verified. |
| Int text | none | Write in source over `String` push bytes. |
| Panic | `panic(payload_ptr, payload_vtable, loc)`, `panic_bounds`, `panic_str` helpers | Section 7. Location stays (slot, line, col) as today. |
| Thread | `thread_spawn`, `thread_join_raw`, `tls_key_create/get/set`, `park`, `unpark` | pthreads wrappers (7.3). Policy (poisoning, results) is source. |
| Sync cores | `mutex_lock/unlock`, `rwlock_*`, `condvar_*`, on opaque handles | pthread objects have no lust layout. Handles are boxed C structs. |
| Atomics | `atomic_load/store/xchg/cas/fetch_add/...` per width and ordering | C11 `stdatomic.h` through tcc mob (DESIGN evidence). Typed `AtomicU64` etc. are source wrappers. |
| Time | `clock_now_raw`, `system_time_raw` | `clock_gettime` values out. `Duration` math is source. |
| IO raw | `fd_read`, `fd_write`, `fd_close` plus errno fetch | Everything above byte IO on fds is source or shim (3.7). |
| Process | `args` raw table, `env_get` raw, `exit` | Set once at startup in the runtime unit. |
| Hash core | none | FxHash and SipHash are source. The table core is C (3.3), the hasher is not. |
| Arena | `arena_alloc(bytes, align) -> ptr` per arena handle | The leak arena bump core (3.6). Typed `alloc_with` is source in the adapter. |

Everything not in this table is source. In particular:
`Option` and `Result` methods (hundreds), iterator
adapters and consumers, `Vec` and `String` methods above
the erased cores, sort, `Rc`, `Weak`, `RefCell`, `Cell`,
`OnceCell`, `OnceLock`, `LazyLock`, `Cow`, `VecDeque`,
`BTreeMap`, `HashMap` typed layer, `fmt` machinery,
`Display`/`Debug` for all std types, `str` methods,
`char` methods, `Path`/`PathBuf`, `io::Read`/`Write`
adapters, `mpsc`, guards. If a proposed intrinsic is
not on the list, the default answer is source. Add to
the list only with a profile.

### 3.3 Erased container cores in C

Per VERIFY G section 4: containers are typed thin
wrappers in lust source over one erased C core per data
structure, keyed by element size and align plus a small
per-type glue table (hash, eq, drop, clone fn ptrs).
Measured cost is 0.8x to 1.4x of mono under tcc, and it
removes the largest instance class after iterators.
Today's `lust_Vec` is the prototype
(`src/runtime.c:19-22`, `lust_vec_push_slot` at
`src/runtime.c:213-216`). Generalize it:

```c
typedef struct { void *ptr; uint64_t len, cap; } lust_vec;
void  lust_vec_reserve(lust_vec *, uint64_t extra, uint64_t size, uint64_t align);
void *lust_vec_push_slot(lust_vec *, uint64_t size, uint64_t align);
// plus insert/remove/splice byte moves, drain, truncate-with-drop-callback

typedef struct lust_str { uint8_t *ptr; uint64_t len; } lust_str;      // exists
typedef struct { uint8_t *ptr; uint64_t len, cap; } lust_string_core;  // exists as lust_String

typedef struct lust_hashmap lust_hashmap;  // SwissTable-compatible, see 3.5
// ops take (map, hash, key_ptr, key_size, glue) and return slot ptrs

typedef struct lust_deque lust_deque;      // ring buffer over a lust_vec
```

Rules:

- The C core never knows Rust types. All typed access
  (indexing, iteration, entry API) is in the source
  wrapper, which computes byte offsets from `size`.
  Callers stay monomorphic and typed. The compiler
  needs no erased ABI for user types (VERIFY G).
- Drop and clone of elements go through glue fn ptrs
  from the per-type glue table mono emits (4.2). The
  Vec drop loop exists today as glue in
  `src/cgen.rs:1226-1269`; it moves behind the glue
  table.
- Growth must match Rust so `capacity()` matches
  (3.5). Fix `lust_vec_reserve`
  (`src/runtime.c:199-205`): today it starts at 4 for
  every element size. Rust's rule: minimum capacity is
  8 for 1-byte elements, 4 for up to 8-byte... in
  general `max(8 / size, 1)` rounded as `RawVec` does,
  then double. Copy the exact `RawVec` growth function
  (amortized and exact paths) into the C core, driven
  by size, and difftest `capacity()` hard.
- `String` is `Vec<u8>` with UTF-8 checks in source.
  Keep the C string core for push bytes and case ops
  where they exist (`src/runtime.c:54-99`) but route
  new methods through the source wrapper. Do not grow
  the C string API method by method.
- Sorting: one erased C sort (introsort with a
  comparator fn ptr) is the fallback. Rust sort is
  stable driftsort with observable comparison order
  only through the comparator's side effects and panic
  behavior. `sort` (stable) and `sort_unstable` in
  source call the erased core with glue compare. If a
  comparator panics mid-sort, Rust leaves the slice in
  a valid but unspecified state; the erased core must
  do the same (never duplicate or lose elements).
  Difftest with panicking comparators.

### 3.4 Iterators in source, fusion in the compiler

Iterator adapters are ordinary generic structs in
`library/core` (`Map`, `Filter`, `Take`, `Zip`, and the
rest), with real `next` methods. Any crate can consume
them unfused through mono. Fusion (4.3) is an
optimization that pattern-matches known adapter defs.
This split matters: correctness never depends on the
fusion pattern list, and user iterators (ts-rust has 5
custom `Iterator`, 2 `DoubleEnded`, 4 `ExactSize`, 6
`IntoIterator` impls) work through the unfused path.

`size_hint`, `ExactSizeIterator`, and collect capacity
behavior live in the source impls and must match Rust
(VERIFY G section P4 gives the failure cases). The
fusion spec in 4.3 consumes these exact semantics.

`for` loops desugar in check to `IntoIterator::into_iter`
plus a `next` loop, or to a fused chain when 4.3
applies. Range types are std structs with `Iterator`
impls, with a fused fast path for integer ranges (307
ts-rust uses).

### 3.5 Byte-exact behavior

Rule zero compares stdout and exit status. DESIGN
excludes panic text, `HashMap` order, thread
interleaving, and `{:p}`. Ts-rust narrows those
exclusions: its baseline tests compare bytes, panic
text can become an IPC response (DESIGN-TS section 1),
and ordered-map output reaches JSON bytes. So be exact
where output can observe it:

- **Float printing and parsing.** Rust `Display` and
  `Debug` for `f64`/`f32` use shortest round-trip
  decimal. Implement one C implementation (Ryu for
  print, Eisel-Lemire with exact fallback for parse),
  then wrap with Rust's formatting rules (when to use
  exponent form in `Debug` vs `Display`, trailing
  `.0`, `inf`, `NaN` signs). Gate: a fuzz difftest over
  at least 10 million random bit patterns plus directed
  edges (subnormals, powers of 10, halfway cases),
  lust vs rustc output, both `Display` and `Debug`.
  Ts-rust JS numbers need a *different* printer
  (ECMAScript `Number::toString`, the `ryu-js` crate,
  1 call site): that is a separate C port in the deps
  layer (3.6), not a reuse of the Rust printer.
- **Formatting.** `format!` compiles to `fmt::Arguments`
  built from pieces, as in Rust. Today `FmtPart`
  (`src/ir.rs:66-71`) has only literal and arg with a
  debug flag. Extend to a parsed format spec: fill,
  align, sign, `#`, zero, width (literal, arg, `.*`),
  precision, radix (`x X e E o b p`), `?`. Parsing
  happens in the expander (builtin macro), specs become
  const data, rendering is std source (`Formatter`,
  `write!` to any `fmt::Write`). Ts-rust uses width or
  precision 40 times and radix 37. Implement the full
  spec grammar once; partial specs cause repeat work.
  `{:p}` prints a dev address; output that depends on
  it stays excluded by rule zero.
- **HashMap order.** Rust `HashMap` (SipHash, random
  seed) has no stable order; lust keeps a fixed seed
  and the corpus rule that map order must not reach
  output. `FxHashMap` is different: deterministic
  hash, and hashbrown's table gives a deterministic
  iteration order for a fixed insertion sequence.
  Where ts-rust output depends on it, lust must match.
  The only safe way is a hashbrown-compatible table:
  same bucket count growth (power of two, 87.5% load
  via growth-left), same quadratic probe sequence,
  same iteration scan order (bucket index order), same
  tombstone behavior on remove. Group width (16) does
  not change order if probing matches. Implement it in
  the C core (`lust_hashmap`), with the hasher in
  source: FxHash as `rustc-hash 2.1.2` computes it,
  SipHash-1-3 for std maps with a fixed seed. Gate:
  difftest that inserts, removes, rehashes thousands of
  keys and compares full iteration order against a
  rustc binary using `rustc-hash =2.1.2` and
  `hashbrown` as in ts-rust's `Cargo.lock`. Pin those
  versions in the test. If the gate fails on a case,
  the fallback is a reviewed list of ts-rust sites that
  sort before output, not silent divergence.
- **IndexMap order.** Insertion order by definition;
  `shift_remove` vs `swap_remove` differ and both are
  observable. The adapter (3.6) implements entries in a
  `Vec` plus a `lust_hashmap` from key hash to entry
  index. Iteration walks the Vec. Entry order is then
  exact by construction. JSON output at
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/frontend/json.rs:1643`
  (cited in DESIGN-TS section 4) is the acceptance
  shape.
- **Vec capacity.** Copy `RawVec` growth (3.3).
  `collect` uses `size_hint` lower bounds and
  `TrustedLen`-equivalent paths only inside std source
  where the impl proves length. Difftest `capacity()`
  after map/filter/collect chains (VERIFY G P4 lists
  the traps: `Vec<u8>` through filter gives 8, 34 kept
  items give 64).
- **Panic messages from std.** Copy the Rust 1.99 texts
  verbatim for every std panic lust can raise: unwrap
  on `None`, expect messages, index out of bounds
  (today at `src/runtime.c:220-225`), slice index,
  `RefCell` double borrow, channel closed, poisoned
  lock, parse errors. Locations: `#[track_caller]` is
  real. A `track_caller` fn receives a hidden
  `&Location` param, added at mono. Codegen passes the
  caller's (slot, line, col). Nested `track_caller`
  forwards. Without it, an `unwrap` in std source
  would report a `library/` line; rustc reports the
  user line. Ts-rust has 16 `track_caller` uses and
  the `GoThread` spawn path depends on caller location
  for fatal messages
  (`crates/ts_goport/src/gopanic.rs:249`).
- **Drop order.** Already a rule-zero requirement and
  tested today with printing `Drop` impls. Std source
  must not reorder drops: `Vec` drops elements front
  to back, scope drops run in reverse declaration
  order, temporaries drop at Rust's points. Early-exit
  paths (`?`, `collect::<Result>` short-circuit) drop
  in Rust order (VERIFY G P4: closure captures drop
  before partial Vec elements).

### 3.6 Adapter crates (dependency layer)

Adapters are normal lust crates in `library/deps/`,
each with the dependency's crate name and public API.
The driver swaps them in by resolved package id (1.1).
Each adapter declares the exact upstream version it
matches in its manifest comment and a `lust-adapter`
version the driver checks. An upstream version bump in
a user's `Cargo.lock` with no matching adapter is a
clear error, not a silent mismatch.

| Adapter | Implementation | Exactness gate |
|---|---|---|
| `rustc-hash` | Type aliases over lust `HashMap` with the Fx hasher in source. The upstream crate is already only aliases plus the hasher. | Hash values vs 2.1.2 on byte slices, ints, strings. Table order gate from 3.5. |
| `indexmap` | `Vec<(K, V)>` plus `lust_hashmap` side index. `IndexSet` likewise. Entry API, `shift_*`/`swap_*`, `sort_by`, slicing. | Order and capacity difftests vs 2.14.0. |
| `smallvec` | Generic struct with inline array `[MaybeUninit<T>; N]` plus spill to the Vec core. Observable: `capacity`, spill point, `inline` size in `size_of`. | Capacity and drop difftests vs 1.15.1. |
| `memchr` | Source wrappers over libc `memchr`/`memrchr`/`memmem` via one intrinsic each. Finder types in source. | Byte-search difftests on random buffers. |
| `bumpalo` (subset) | Leak arena over `arena_alloc`. Only the API `leak_arena.rs` uses: `Bump::new`, fixed chunk limit, `try_alloc_with`, slice copy. | Alignment, failure-on-full, no-drop semantics vs the ts-rust usage at `crates/ts_goport/src/leak_arena.rs:40-80`. |
| `xxhash-rust` (xxh3) | C xxhash in the runtime, thin source API. 128-bit results as `u128`. | Digests vs upstream test vectors. |
| `ryu-js` | C port of the JS number printer. | Byte compare vs the crate on random f64 bits. |
| `num-bigint` (subset) | Small source BigInt: parse, print, the ops ts-rust calls (5 refs). | Parse/print roundtrip difftests. |

Adapter code is user-level lust. It goes through the
same check and mono as any crate. It may use
intrinsics only where the table says (memchr, arena,
xxh3, ryu-js cores).

### 3.7 Shim crates and the allocator

Shims cover coarse OS and data services: `rustix`,
`nix`, `signal-hook`, `flate2` (zlib), `jiff` (local
time), `name-to-handle-at`, jemalloc control. One Rust
crate in `shims/` in the lust repo builds all of them
into one `staticlib` (or `cdylib` for the first spike)
with `extern "C"` exports. Cargo builds it once during
`lust port prepare`, keyed by lockfile, features,
target, toolchain, and shim ABI version (DESIGN-TS
section 4). Lust-side, each shim has a lust source
crate with the public API whose bodies call the C
exports through `extern "C"` foreign fns (checker
support for foreign fns under opt-in `unsafe`).

Boundary rules (from DESIGN-TS section 4, made
concrete):

- Only scalars, byte buffers (ptr plus len), C-layout
  records (`#[repr(C)]` of scalars), and opaque handles
  (u64) cross. Never `String`, `Vec<T>`, closures, or
  trait objects by layout.
- Ownership: inputs are borrowed for the call. Outputs
  are copy-out buffers with an explicit free fn, or
  caller-provided buffers. One allocator owns each
  buffer: shim-allocated memory is freed only by the
  shim.
- Callbacks: fn ptr plus env handle plus a status
  return. A panic in a lust callback sets the thread
  panic flag and returns the status at once (7.2); the
  shim must not call back again after a panic status.
- The shim catches its own Rust panics and returns a
  status plus message. A panic must never unwind
  through lust C frames.

Allocator: dev builds link mimalloc by default, as the
compiler itself does (`src/main.rs:26-27`), through the
`alloc` intrinsic. If the crate records a
`#[global_allocator]`, dev honors it only for known
allocators: jemalloc (link the shim's jemalloc and
route `alloc` to it) or the system allocator. Ts-rust
needs jemalloc arena control
(`crates/ts_goport/src/jemalloc_layout.rs:66-99`): the
`tikv-jemalloc-ctl` surface is a shim, and thread arena
assignment must be real, not a no-op, because the
single-threaded checker allocates in the loader's
arena. 4 MiB alignment from the same file must hold in
the dev allocator or ts-rust's layout guard aborts.

### 3.8 How std gets built and cached

On first use of a (lust version, target, profile)
tuple, the driver compiles `core`, `alloc`, `std`, and
any requested `library/deps/*` adapters with the normal
pipeline, as crates with no `main`, roots being all
`pub` items. Output goes to the disk cache (section
8): per-instance C and objects, plus a serialized
signature surface (defs, generics, impl index) so a
cold session loads std defs without rechecking std
bodies. The signature surface is versioned with the
compiler; a mismatch rebuilds.

Std is immutable inside a daemon session. Editing
`library/` source requires a new lust version string
in dev (use the git hash of the lust repo) or an
explicit `LUST_STD_SRC` override that keys the cache
by the std source tree hash. That override exists for
the agents who build std (package W-STD, section 9)
so they get normal incremental behavior on std code.

## 4. Monomorphization and codegen

### 4.1 Pipeline change: generic bodies, then instances

Today: collect, then per fn check (`src/check.rs:215`)
and lower (`src/lower.rs:28`) to IR, borrowck on IR,
cgen per fn. New pipeline per crate:

```text
expand + resolve + collect      (signatures, impl index)
check generic body per fn       (parallel; Param and Projection types stay)
lower to generic IR per fn      (parallel)
borrowck on generic IR          (parallel; section 5)
mono: walk instances from roots (substitute, normalize, resolve calls)
cgen per instance               (parallel, by slot unit)
tcc per unit, link              (as today)
```

Check and borrowck run once per *template*, not per
instance. That is a deliberate difference from rustc,
which re-elaborates per instance in codegen. Soundness
argument: the generic body checks against its declared
bounds (param env). Any concrete args that satisfy the
bounds, proven at the call site, keep every call and
loan in the body valid. Two instance-dependent checks
still run at mono and can error, matching rustc's
post-mono errors: the recursion limit (VERIFY G P3)
and layout-dependent const asserts (`const _:
assert!(size_of::<T>() ...)`) after substitution.
Mono must walk all instances even where codegen could
skip one, or those errors diverge from rustc.

Generic IR keeps trait method calls as
`CallTrait { trait_def, method, self_ty, args,
evidence }` where evidence is `Param(index)` for a
param-env bound or `Impl(ImplId)` already selected.
Mono resolves `Param` evidence by running selection
(2.4 step 3) on the concrete self type. If selection
at mono fails for args that passed check, that is a
compiler bug. Keep a debug assertion and a user error,
not a panic.

### 4.2 Instance keys, sharing, and the daemon cache

Discovery key (correctness):

```rust
pub struct InstanceKey {
    pub def: DefId,          // fn, method, closure, or static initializer
    pub args: ArgsId,        // type and const args only; regions erased
}
```

Regions never enter the key. They do not affect code.
Recursion detection uses the discovery stack of
`InstanceKey`s; cap depth at 128 like rustc, error on
exceed with the instantiation chain printed (must
match rustc's error class so `tests/fail` agrees).
Also cap total instances per crate (default 2,000,000,
flag-tunable) and per-template fan-out, with an error
that names the worst template. These caps stop hangs;
they are not language limits.

Roots: `main`, `#[test]` fns in test crates, exported
`extern "C"` fns, statics' initializers (as instances
of a synthetic init fn), vtable method sets for every
`dyn` coercion site reached, and drop glue for every
concrete droppable type reached. Non-generic fns are
instances with empty args. Dead generic fns produce
no instance and no C.

Sharing key (code size), per VERIFY G section 4 item
3: after substitution, compute a codegen identity:

```text
share_key = (def,
             layout_class of each type arg,
             sorted set of instance keys the body calls trait methods on)
layout_class(ty) = (size, align, is_copy, needs_drop,
                    contains fat ptr shape)  computed recursively
```

If two discovery instances of one template have equal
share keys, emit C once; the second instance's slot
points at the first instance's function. Bodies that
only move `T`, store it, or pass it to shared callees
share. Bodies that inspect `T` (match on an enum arg,
call a method on it) differ through the callee set.
V1 simplification, if the sharing analysis slips:
share nothing, measure C size on the milestone 5
spike fixtures, and add sharing in milestone 9 only
if instance C exceeds 30% of total C after fusion
(VERIFY G's revisit threshold). Decide at the spike,
with numbers. Do not block traits on sharing.

Glue per concrete type (drop, clone, eq, hash, debug
where derived or std-known) becomes instances too,
keyed by `(GlueKind, Ty)`, replacing today's per-`CTy`
glue (`src/cgen.rs:30-36`, `GlueSet` at
`src/cgen.rs:980-1054`). The per-type glue *table*
for erased cores (3.3) is a static struct of fn ptrs
to those instances' slots, emitted once per type that
reaches a container core.

Daemon instance cache: per crate session (and across
crates in one workspace session, since instances are
per final bin but discovery repeats per crate),
`FxMap<InstanceKeyHash, Slot>` where the hash covers
def hash plus args fingerprint (type fingerprints use
DefPathHash and structure, never session-local `Ty`
ids, so the same map seeds the disk cache). An
instance is re-emitted only when its fingerprint
changes (section 8): template body fingerprint, arg
layout fingerprints, or any selected impl on its call
edges. This is the milestone 9 instance cache; design
slots for it now so milestone 5 does not paint over
it. Slot assignment is append-only per session, as
today (`src/driver.rs:317-336`). Removed instances
leave dead slots until the next base rebuild (32
overlays today; keep the policy).

### 4.3 Iterator fusion with an unfused fallback

Fusion recognizes a chain at lower time, on the typed
AST of one body, before mono:

- Source: `.iter()`, `.iter_mut()`, `.into_iter()` on
  `Vec` and slices and arrays, `str::chars` and
  `bytes`, ranges, `once`, `empty`, and std adapters
  by def: `map, filter, filter_map, copied, cloned,
  enumerate, take, skip, zip, chain, flatten (one
  level), flat_map, step_by, rev` on double-ended
  sources, `inspect`.
- Sink: `for` loop, `collect` to `Vec`/`String`/
  `HashMap`/`HashSet`/`Result<_, _>` of those,
  `for_each`, `fold`, `sum`, `count`, `any`, `all`,
  `find`, `position`, `min`, `max`, `next` chains in
  `while let`.
- The chain must be linear, single-use, not stored,
  not passed to a fn, not behind `dyn`, and every
  closure must be a local closure value (not a fn ptr
  variable that could be reassigned; fn *items* are
  fine). Else: unfused path. No diagnostic. Fusion is
  invisible.

Fused form: one loop over an index or pointer, with a
written spec. The spec is the contract; an
implementation that does not meet it is wrong even if
simple tests pass. From VERIFY G P4, the spec must
state:

- Pull order is demand-driven per `next` call. `take(n)`
  tests its count *before* pulling. `zip` pulls left,
  then right, once per output, with the known
  specialization exception: when the right side has an
  exact remaining length the left side may be pulled
  only that many times; replicate Rust's
  `TrustedRandomAccess` behavior for the fused sources
  by pulling left only up to the right length when the
  right source is a slice or range iterator. The
  side-effect count in user closures is observable.
- `collect` capacity: pre-size from the chain's
  `size_hint` exactly as the source impls compute it
  (map preserves, filter gives (0, upper) so collect
  uses the lower bound path Rust uses). Then grow by
  the Vec rule. `capacity()` after a fused collect
  must equal the unfused value.
- Early exit (`?` in a closure, `break`, `find` hit,
  `collect::<Result>` on `Err`): drop order is
  closures first (captures), then already-collected
  elements in order, then the source if owned. Build
  the fused loop's exit edges to match the unfused
  drop tree. This is the most error-prone rule;
  difftest it per adapter.
- Panic in a closure mid-chain: elements already
  produced and owned by the sink drop on unwind
  (section 7). Elements borrowed from the source do
  not.

Gate (VERIFY G section 5): 150 or more difftest cases
with side-effect counters, `Drop` impls that print,
`capacity()` prints, and early exits, run fused vs
rustc. Keep an env flag `LUST_NO_FUSION=1` that forces
the unfused path; CI runs the iterator corpus both
ways and diffs the outputs. A fusion bug then has an
instant bisect.

Estimated share: VERIFY G measures real code at 15 to
18 iterator instances per chain, 1 chain per 58 to
137 lines, fusion removing most of 23 to 35% of -O0
code bytes. Ts-rust: 3,516 chains (2,644 with one
adapter, 205 with 2 or more), top adapters map 1,087,
copied 405, cloned 350, enumerate 336, take 250,
filter 247. Single-adapter chains dominate, so v1
fusion quality on short chains matters more than
deep-chain cleverness.

### 4.4 Layout

One layout engine in `src/ty/layout.rs`:
`layout(ty) -> Layout { size, align, field_offsets,
enum_tag }` for sized types, memoized per `Ty`.
Pointer width from the target table (1.6). Rules:

- Scalars: C sizes. `bool` 1 byte (values 0 and 1
  only; codegen must never produce other bytes in a
  bool slot). `char` 4 bytes. `u128/i128` 16 bytes,
  align 16 on x86_64 through tcc's `__int128`? tcc
  support is thin: represent `u128` as a 2-word struct
  with runtime helpers for arithmetic beyond add and
  compare, unless the tcc spike (section 10) proves
  `__int128` works on both tier 1 targets. Ts-rust
  needs `u128` only for xxh3_128 values (54 uses):
  construction, compare, hash, print. Helpers cover
  that.
- `repr(Rust)` (default): fields in declaration order,
  each aligned to its align, struct align is max field
  align, size rounded up. Lust does *not* reorder
  fields like rustc may. Consequence: `size_of` for
  default-repr types can differ from rustc. Where
  ts-rust asserts sizes, the types are `repr(C)` (see
  below) or the assert is a performance guard.
  `lust port scan` lists every `size_of`/`offset_of`
  assert on non-`repr(C)` types for human review: if
  the assert guards safety, the port adds `repr(C)`
  or the assert moves to the release-only path with a
  recorded exception (DESIGN-TS section 6). Never
  silently accept a different size where code
  *depends* on it (transmute, raw reads): those need
  `unsafe` and stay rejected in safe lust.
- `repr(C)`: exact C layout. The C emitter writes
  explicit padding fields from the layout engine's
  offsets, so the C struct's layout equals lust layout
  regardless of the C compiler's choices. Enums with
  `repr(C)`: tag per C (`int`-sized unless a repr int
  is given), payload union. Ts-rust: `repr(C)` 6,
  `repr(u8)` 6, align 3, packed 1, transparent 1.
- `repr(transparent)`: layout of the one non-ZST
  field. Check the one-field rule at collect.
- `repr(align(n))`: raise align. Combined with C as
  in `#[repr(C, align(64))]` on
  `/home/theo/.t3/projects/ts-rust/crates/ts_goport/src/checker/types.rs:853-870`,
  where `size_of::<Type>() <= 128` and
  `offset_of!(Type, data) == 24` are const-asserted.
  With declaration order plus C rules, lust computes
  the same numbers; the milestone 4 fixtures must
  include this struct shape as a test.
- `repr(packed)`: align 1, no padding. Field access
  through unaligned loads in C (memcpy). One use in
  ts-rust; support it simply.
- Enums, default repr: tag is the smallest int of
  1, 2, 4, 8 bytes that holds the variant count,
  placed first, then the largest payload. Explicit
  discriminants (46 prod plus 351 generated in
  ts-rust) set tag values, not sizes.
- Niches: implement exactly one niche rule, because
  it is widely observable in `size_of` and in memory
  use: `Option<T>` where `T` is a non-null single
  pointer (`&T`, `&mut T`, `Box<T>`, `Rc<T>`,
  `Arc<T>`, `NonZero*`, fn ptr) has the size of `T`,
  with null as `None`. No other niches (no bool or
  char range niches, no enum tag packing into payload
  padding). `size_of::<Option<T>>()` for other `T`
  will differ from rustc when rustc finds a niche;
  port scan flags asserts that depend on it.
- Unsized: fat pointers are (ptr, len) for slices and
  str (today's `lust_str`, `src/runtime.c:19`), and
  (ptr, vtable) for `dyn`. A struct with an unsized
  last field stores the fat metadata in the pointer
  to the struct, not in the struct.
- ZSTs: size 0, align from fields (1 if none). Vec of
  ZST never allocates; the erased core handles
  size 0. `PhantomData` is a ZST field that still
  contributes variance and auto traits.

`size_of`, `align_of`, `offset_of!` evaluate in the
const evaluator from this engine. `mem::swap`,
`replace`, `take` lower to byte moves of `size`
through a stack temp when the type is not `Copy`.
Heap alloc always goes through the `alloc(size,
align)` intrinsic. Never zero-initialize a value Rust
leaves uninit (`MaybeUninit` in std and arena code);
codegen zero-fills *locals' storage* today for safety
(DESIGN C rules) but drop flags, not bytes, decide
whether a drop runs.

### 4.5 C ABI for the dev backend

Keep today's model and extend it:

- Every lust fn instance is a C function with a slot.
  Calls go through `lust_fns[slot]` in daemon builds
  (`src/cgen.rs:604-612`) so overlays can swap bodies.
  Direct calls are allowed only within one unit in
  cold (non-daemon) builds, where nothing is swapped.
  Decide per build mode, not per call: daemon mode is
  all-indirect, cold mode is direct within the final
  link. Vtable entries and fn ptrs and closure call
  fields always store the *slot trampoline*, a tiny
  generated forwarder with a stable address, in both
  modes. One trampoline per slot, emitted in the
  table unit.
- Aggregates pass by value as C structs, as today.
  Large aggregates (over 32 bytes) pass by hidden
  out-pointer for returns only; params stay by value
  to keep the slot cast simple. This is a dev ABI.
  Nothing here promises Rust ABI compat. Only
  `extern "C"` fns (shim and FFI surface) follow the
  platform C ABI, and only with C-ABI-safe types:
  scalars, raw ptrs, `repr(C)` structs of scalars.
  Check rejects other types at foreign signatures.
- Fat pointers are two-word C structs passed by value.
- Closures: env struct (captures in order) plus the
  trampoline ptr at offset 0 for `dyn Fn` erasure. A
  direct closure call knows the def and calls its
  slot with `&env` first. A `dyn Fn` call goes through
  the vtable (one vtable per closure def per Fn
  signature).
- Checked arithmetic, bounds, and overflow keep
  today's runtime helpers and inline checks
  (`src/runtime.c:232-300`), with panic behavior from
  section 7.
- `#line` directives map C back to the `.rs` file and
  line through the per-build line table, as today
  (`src/cgen.rs:1059-1095`). Panic locations stay
  (slot, line-in-fn, col).

Backend swap stays possible: cgen consumes mono IR
only. The milestone 9 bake-off (tcc, Cranelift,
copy-and-patch) reads the same IR. Nothing in mono or
IR may name C types. Today's `CTy` in cgen
(`src/cgen.rs:37-115`) stays inside cgen.

## 5. Lifetimes: the restricted region model

This section implements DESIGN-TS section 2 option B.
Read that section with this one. Summary of the deal:
real region checking, bounded algorithm, stated
rejects. Ts-rust needs it: 168 user types with
lifetime params, 111 with non-static ref fields, 27
with `&mut` fields, 10 with 2 or more lifetimes, one
with 3 (`transformers/destructuring.rs:93`, cited in
DESIGN-TS). Do not cap the region count.

### 5.1 Rollout in two steps

Step A (with or before `dyn`, milestone 5 end):
`'static` and `'_`. `'static` is `Region::Static`, no
inference. `'_` in a signature is a fresh region param
subject to elision; in an impl header it is required
syntax (rustc E0726) and means the elided param. This
step removes the `L0203` blanket reject
(`src/parser.rs:65-72`) for these two forms and allows
`&'static T` fields (191 in ts-rust) and std types
like `Formatter<'_>`, `Cow<'static, str>`,
`MutexGuard<'_>`. INVENTORY credits this step with
moving ts-rust from 16.6% to 32.7% of prod lines for 1k
to 2k lines. It is the cheapest big win in the plan.

Step B (milestone 6): named regions everywhere below.

### 5.2 What is checked

Syntax: lifetime params on fns, structs, enums, impls,
traits, aliases; `T: 'a` and `'a: 'b` bounds; refs and
generic args carrying regions; `dyn Trait + 'a`;
`impl Trait + 'a`; rank-1 `for<'a>` on fn ptrs, `Fn`
bounds, and trait objects. Elision copies Rust's three
rules exactly (each elided input gets its own param;
`&self` wins for outputs; else error). A signature
that elision cannot settle and that names no lifetime
is an error asking for a name, replacing today's
"return owned" advice where a named region works.

Per body, region checking reuses the loan engine in
`src/borrowck.rs`. Add one layer above it:

1. Every `Ref` and borrow-carrying `Adt` in the body
   gets region vars from its type. Loans (existing)
   record which place and which region var the borrow
   was stored under. A loan escapes into an Adt field
   or a closure capture when the IR stores it there;
   the field's type gives the region var it must fit.
2. Subtyping constraints arise at assignments, calls,
   returns, and struct literals: `actual <: expected`
   decomposes through types with variance (5.3),
   producing region outlives constraints `'x: 'y` and
   "loan L must live at least 'y". Callee signatures
   summarize: their region params are fresh vars at
   the call, constrained by arg and return types.
   This replaces `ret_borrows_from`
   (`src/collect.rs:52-53`, set at
   `src/collect.rs:372`) with the general form.
3. Solve: live range of each loan comes from the
   existing NLL liveness (a loan is live where a live
   local may hold it, `src/borrowck.rs:1-8`). A region
   var's required live range is the union of points
   where values typed with it are used, plus outlives
   closure over the constraint graph. Check: for every
   loan stored under region `'x`, the loan's place
   stays valid (not moved, not dropped, not mutably
   aliased) across `'x`'s whole required range, and if
   `'x` is a param or outlives the body scope through
   the return type or a stored field, the loan's place
   must itself come from a param with a region that
   outlives `'x` per the signature. Concretely: a
   reference to a local can never satisfy a region
   that reaches the return, a `&'static` slot, or a
   field whose Adt region outlives the body.

This is a constraint check, not region *inference* of
named signatures: signatures are as written (with
elision). Inside a body, region vars are only from
locals, temporaries, and call instantiation. The
graph is small (vars per borrow site). Solve by
reachability, no backtracking, in time linear-ish in
loans. Keep the two-phase borrow support and the
`FakeRead` device (`src/ir.rs:108-110`).

Reborrows through field projections: the loan place
set already tracks projections (`src/ir.rs:15-24`).
Storing `&x.field` in a struct field of region `'a`
constrains `x.field` to stay borrowed for `'a`, and
`x` itself cannot move while the struct is live. The
existing conflict check (access vs live loans) covers
it once loans live as long as the containing Adt
value, which is why loan liveness must flow *through*
Adt fields and closure captures, not just through
ref-typed locals. That flow is the main borrowck
change: "local holds loan" becomes "place holds loan",
through projections, with Adt field types telling
which field carries which region var.

Well-formedness at collect: a type `Foo<'a, T>` is
usable only if its declared bounds hold (`T: 'a` where
declared). Fields with refs make the Adt borrow-carrying;
drop check (5.4) applies. `contains_ref`
(`src/collect.rs:449-478`) generalizes to "regions of
this type", a set of region params reachable through
fields with variance signs.

### 5.3 Variance

Compute each Adt type and lifetime param's variance
from fields, Rust-style: covariant by default;
`&mut T`, `Cell`, `RefCell`, `UnsafeCell`, fn ptr
args, and raw ptr (by kind) flip or freeze to
invariant per Rust's table. `PhantomData<T>` gives
`T`'s variance without storage. Variance feeds step 2
above: covariant positions produce `'x: 'y`,
contravariant flip, invariant produce equality (both
directions). Variance is per (Adt def, param index),
computed once at collect by fixpoint over the field
graph. Cycles resolve to invariant on conflict.

Where it bites in ts-rust: `RuleContext<'a, 'c>` holds
`&'a mut TypeParser<'c>` (INVENTORY Q1 sample), so
`'c` is invariant through the mut ref. Skipping
variance would accept programs rustc rejects there.
With 27 `&mut`-field types, this is not optional.

### 5.4 Drop check

Structural drop check, conservative: when a value of
type `Adt<...>` with a `Drop` impl (or a field that
transitively has one) drops at point P, every region
arg of the type must still be live at P (its loans
valid). No `#[may_dangle]`. If the check cannot prove
liveness, reject with `L0285` naming the type and
region. Rust's dropck with `may_dangle` accepts some
of these; ts-rust uses no `may_dangle` (it needs
`unsafe`). Conservative is sound and sufficient.

### 5.5 What is rejected

Stable errors, each with a fix hint. Port scan counts
them before milestone 6 starts, so the list is
evidence-checked:

- GATs and any assoc type with its own lifetime
  params (`L0230`, from 2.5).
- Higher-ranked binders beyond rank 1, and binders on
  trait *defs* (`trait Tr<'a>` is fine; `for<'a> Trait`
  as a supertrait bound on a nested binder is not).
  One explicit `for<'a>` exists in ts-rust
  (`ast/synthetic.rs:1447` fn ptr, DESIGN-TS section
  2 table): rank-1 fn ptr, supported.
- Signatures where early-bound vs late-bound lifetime
  distinction is observable through turbofish region
  args at a call. Lust treats all fn lifetime params
  as late-bound (fresh at each call). A turbofish that
  names a lifetime arg (`f::<'static>(...)`) is
  accepted and only checked for well-formedness; if
  the named region would need to flow *into* the call
  as an early-bound constraint to typecheck, reject
  `L0286`. Rare by construction; port scan counts.
- Borrows held across `.await` until the async work
  in milestone 8b. The ATA futures borrow request
  data across suspension (DESIGN-TS section 6); that
  support lands with the state machine lowering, and
  the borrow checker treats suspension points as uses
  there. Before 8b, async itself is rejected.
- Self-referential structs. No support; `Pin` is a
  std type with the usual API for futures, but lust
  does not prove pinning invariants beyond Rust's own
  type rules. That matches Rust: pinning safety is on
  `unsafe` code, which ts-rust does not write.
- `impl Trait` capturing a lifetime param not named
  in the bounds under edition 2024 rules: follow
  2024 capture rules (capture all in scope), reject
  2021-style implicit capture differences by edition.
  Lust only supports edition 2024 crates (1.1); a
  2021 crate is `L0112` at session start. Ts-rust is
  edition 2024 workspace-wide
  (`/home/theo/.t3/projects/ts-rust/Cargo.toml:11-15`).

### 5.6 Negative corpus

Before step B lands, write the reject corpus (each
checked against rustc): arena reset while borrowed,
mutable alias through a struct field, nested borrowed
fields escaping, invariant cell shortening, callback
(`Rc<dyn Fn + 'a>`) escaping its scope, guard-backed
borrow outliving its guard (`FileRef` shape), scoped
thread borrowing past `scope` end, dropck case. The
corpus is the gate. Features follow it (BRIEF test
rules: `tests/fail` for both-reject, `tests/reject`
for lust-only rejects).

## 6. Macros

### 6.1 Where expansion sits

Pipeline per file:

```text
lex to token stream with token trees (delimiters nested)
  -> parse "outline": items with MacroCall nodes intact,
     fn bodies as token ranges (as scan does today)
  -> expand: resolve macro defs visible at each call,
     expand outermost-first, re-lex nothing (tokens all the way)
  -> parse expanded token stream to full AST
  -> cfg strip, resolve, collect, ...
```

The lexer grows token trees: `TokenTree = Token |
Delimited(kind, Vec<TokenTree>, span)`. Today tokens
are flat (`src/lexer.rs:20-115`). Keep a flat view for
the scan/hashing path; the parser consumes trees for
macro positions and flat tokens elsewhere. Macro calls
can appear in item, stmt, expr, pat, type, and vis
positions. The outline parser must find item boundaries
without expanding, which token trees make possible:
an item-level macro call ends at its closing delimiter
plus an optional `;`.

Expansion order: outermost-first per position, as in
rustc. A macro can expand to another macro call
(ts-rust forwards args between macros, DESIGN-TS
section 5). Expand until no calls remain or a cap
hits. Caps: expansion depth 128, output tokens per
call 1,000,000, total expanded tokens per crate
16,000,000. A cap hit is `L0301` with the macro named,
never a hang.

Macro *definitions* are items. `macro_rules!` visibility:

- Textual: a def is usable after its point of
  definition in the same module and in child modules
  declared after it, plus across modules with
  `#[macro_use]` on the `mod` (or on the crate root
  for all modules). Implement with a scope stack built
  during the outline walk, ordered by (file, position).
- Path-based: `#[macro_export]` puts the macro at the
  crate root in the macro namespace, usable as
  `crate::name!` and `dep::name!` and importable by
  `use dep::name`. `$crate` inside expands to the
  defining crate's root path.

Both layers feed the expander a `(macro DefId)` per
call site. Unresolved macro name: if it is a builtin
(6.4), use that; else `L0302`, with the failed lookup
recorded (section 8).

### 6.2 Matching and transcription

Fragment specifiers to support, from ts-rust evidence
(INVENTORY Q2: only simple fragments) plus the std
macro needs: `expr` (2024: `expr_2021` too), `ident`,
`ty`, `tt`, `literal`, `meta`, `vis`, `pat` (2024:
`pat_param` distinction: accept `pat` as Rust 2024
defines it), `block`, `item`, `stmt`, `path`, `lifetime`.
Matching: per arm, a token-tree matcher with
repetition `$( ... ) sep*`, `+`, `?`. Local
backtracking inside one arm's match is allowed and
bounded (this is token matching, not trait search);
arms try in order, first full match wins, as in Rust.
Fragment parsing reuses the real parser on the
fragment's token slice: an `expr` fragment must parse
as one expr and consume exactly its slice up to the
follow set the matcher determines. Implement the follow
sets Rust requires (for `expr`: `=>`, `,`, `;`).
Transcription substitutes `$name` and repetitions,
checks repetition depth agreement, and handles
`$crate`. Nested repetitions to depth 4 cover
ts-rust (`flags_macros.rs:10` nested repetitions with
`ident`, `ty`, `meta`, `expr`).

Metavariables keep their tokens' spans and hygiene
contexts (6.3). The transcription output is a token
tree stream fed to the parser in the syntactic
position of the call. Parse errors inside expanded
code report at the call span with a note naming the
macro and its def span.

### 6.3 Hygiene and spans

`Span` must grow. Replace `src/diag.rs:5-19`:

```rust
pub struct Span { pub file: FileId, pub lo: u32, pub hi: u32, pub ctxt: CtxtId }
pub struct CtxtId(pub u32); // 0 = root, else index into expansion table
pub struct Expansion { pub macro_def: DefId, pub call_span: Span, pub parent: CtxtId }
```

Identifiers carry `(Sym, CtxtId)` where hygiene
matters: local bindings introduced by a macro do not
capture user locals of the same name, and macro-introduced
locals with user-passed idents keep the caller's ctxt
for the passed tokens. Item names from macros resolve
in the invoking module (plus `$crate` paths are
absolute). Implement hygiene for locals and labels;
for items, Rust's `macro_rules` hygiene is mostly
"$crate and def-site paths", which the path rules
cover. Lifetimes and generic params introduced by a
macro are hygienic like locals (edition 2024 rules).

Every token from an expansion gets the expansion's
ctxt and a span that maps back: diagnostics print the
call site first, then "in expansion of `name!` at
def:line" chain. The panic line table uses the call
site's file and line. This span change touches every
stage; it is serial refactor S1 and lands before
macros (milestone 4 can carry multi-file spans before
expansion exists).

### 6.4 Builtin macros and derives

Builtin macros stay compiler forms, parsed directly,
never expanded through the token machinery:
`format!`/`format_args!`, `println!`/`print!`/
`eprintln!`/`eprint!`, `write!`/`writeln!`, `vec!`,
`panic!`, `assert!`/`assert_eq!`/`assert_ne!`,
`debug_assert!`/`debug_assert_eq!`/`debug_assert_ne!`,
`unreachable!`, `todo!`, `unimplemented!`, `matches!`,
`cfg!`, `concat!`, `stringify!`, `include_str!`,
`include_bytes!`, `include!`, `env!`, `option_env!`,
`thread_local!`, `pin!`, `offset_of!`, `compile_error!`,
`dbg!`. Ts-rust call counts are in INVENTORY Q2
(`format!` 1,299, `vec!` 975, `panic!` 533, `matches!`
249). Semantics notes:

- `include_bytes!` (49 uses) and `include_str!` read a
  file relative to the current file at expand time.
  The file's hash enters the expansion cache key and
  the dep graph. A missing file is `L0303`.
- `env!` (3) and `option_env!` (4) read from a driver
  provided env map: Cargo's build env (`CARGO_PKG_*`,
  `OUT_DIR`) plus the daemon's environment snapshot at
  session start. The read keys enter the cache key.
  Reading live env per request breaks cache soundness.
- `thread_local!` (73) desugars to a `Static` def of
  std `LocalKey<T>` plus an init fn (7.3).
- `debug_assert!` compiles to nothing when
  `debug_assertions` cfg is off. Dev default on.
- `vec![x; n]` with non-`Copy` `x` clones per element,
  as today (`src/cgen.rs:586-598` seeds the pattern).

Derives are compiler-generated impls (2.2), not
macros. Proc macros: out. A `proc-macro` dependency in
the graph is `L0304` at session start with the crate
named. Ts-rust has none.

### 6.5 Caching expansions

Cache per call site, keyed by: macro def fingerprint
(section 8 hash of the def tokens), hash of input
tokens, ctxt of the call, cfg environment hash,
edition, and hashes of any files or env vars read by
builtins during the expansion. Value: the output token
trees plus the list of items or the AST fragment it
parsed to, where position allows. An unchanged call
reuses output even when surrounding code moves. A def
edit invalidates its calls through the dep graph, not
by flushing the cache. Gate from PLAN.md milestone 4:
all 66 ts-rust macros expand to the same tokens as
rustc. Test by expanding each call fixture with
`rustc -Zunpretty=expanded` as oracle on tokens, not
on printed text (cargo-expand warns printed expansion
is lossy; token compare on our own fixtures avoids
that trap).

## 7. Panics and threads

### 7.1 The decision on panic recovery

Explicit propagation in IR, with cleanup edges. This
is DESIGN-TS section 6's spike, decided here with a
fallback gate. Rejected alternatives:

| Option | Normal-path cost | Why not |
|---|---|---|
| Abort only (today, `src/runtime.c:111-127`) | 0 | Ts-rust catches panics in 59 places. The LSP would die on a bad request. Not parity. |
| `setjmp` per fn with a cleanup registry | One `setjmp` per fn with droppable locals, plus registry push/pop per scope | `setjmp` cost lands on every fn, and "which locals are live" at jump time needs the same cleanup metadata as explicit edges, with worse C semantics (volatile rules). |
| `longjmp` from panic, skip drops | Near 0 | Wrong: skips drops, breaks rule zero wherever a drop prints or releases a lock. |
| Real unwinding tables for tcc C | 0 until panic | tcc emits no unwind info. Writing it is a backend project. Revisit only if the backend bake-off picks an unwind-capable backend. |
| Explicit propagation (chosen) | One TLS flag test after each fallible call; duplicate drop code on cleanup edges | Simple C, exact drop order, works with tcc today. |

### 7.2 Explicit propagation design

Per thread, a panic state in the runtime:

```c
typedef struct {
    int panicking;
    void *payload_data;              // Box<dyn Any + Send> parts
    const struct lust_vtable *payload_vtable;
    lust_loc loc;
    int hook_depth;
} lust_panic_state;                  // one per OS thread, TLS
```

IR change: every call terminator gets an optional
unwind successor block. Lowering builds, per scope,
cleanup blocks that run the drops for locals live at
that scope exit, in reverse order, then propagate:
in a fn, fall through to the caller-visible return
with the flag set; in a `catch_unwind` closure body,
land in the catch landing pad. Only fns that *can*
panic need the check. Compute can-panic by fixpoint
over the call graph of instances: contains a panic
op, an intrinsic that can panic (bounds, overflow in
dev, alloc failure aborts instead, matching Rust),
a call to a can-panic fn, or a `dyn`/fn-ptr call
(unknown: can panic). In practice most fns can panic.
Do not spend effort shrinking the set before profiles.

Codegen shape per fallible call:

```c
ret = ((SIG)lust_fns[slot])(args);
if (lust_tls_panic.panicking) goto cleanup_3;
```

One TLS load and a predictable branch. Cost estimate:
C size grows 30 to 60% on drop-heavy code (cleanup
blocks duplicate drop sequences per scope exit; share
cleanup blocks per distinct live set to stay near the
low end). Runtime: tcc code already pays a call per
operation group; one flag test per call is an
estimated 5 to 15% on call-dense dev code. That is
acceptable inside the dev budget because the dev
binary is already about 1.7x slower than rustc debug
(DESIGN daemon section), and compile speed is barely
affected. The spike gate (milestone 7 entry): build
the `NodeVisitor` plus panic fixtures with propagation
on, measure C bytes, tcc time, and run time vs
abort-mode. If C bytes grow over 2x or run time over
1.5x on the fixtures, stop and evaluate per-fn
`setjmp` with cleanup registry before building
threads on top. Keep `panic = "abort"` crates (wasm
profile in ts-rust's `Cargo.toml:38-47`) on the old
path: no flag tests, `catch_unwind` rejected there.

Semantics that must match Rust:

- Payload: `Box<dyn Any + Send>`. `panic!("...")`
  payloads are `&str` or `String` as in Rust
  (`panic_any` for other types). `catch_unwind`
  returns `Result<R, Box<dyn Any + Send>>`.
  `resume_unwind` re-raises the same payload object.
  Downcasts through the `type_id` in 2.8.
- Panic during unwinding (a `Drop` panics while the
  flag is set): abort the process with Rust's
  double-panic message. No second payload.
- Panic hook: `set_hook`/`take_hook` store one fn
  (`dyn Fn(&PanicHookInfo) + Send + Sync`) in a
  global. The hook runs at panic start with payload
  and location, unless a hook is already running.
  Ts-rust's bins install hooks that format Go-style
  output and use `in_go_recover` depth to stay quiet
  during recovery
  (`crates/ts_goport/src/gopanic.rs:138-166`). The
  default hook prints Rust's panic line format.
- Lock poisoning: `MutexGuard` and `RwLock` guards
  check the flag in their `Drop`: if set, mark the
  lock poisoned. `lock()` returns `Err(PoisonError)`
  after. `RefCell` borrow flags reset in guard drops
  as usual (drop runs on unwind).
- Thread panic: an uncaught panic at a thread root
  ends that thread; `JoinHandle::join` returns
  `Err(payload)`. Other threads continue. Main thread
  uncaught panic: run hook, unwind `main`, exit with
  Rust's code 101.
- Foreign boundary: a panic flag set when returning
  into a C or shim frame must not propagate through
  it. Callback trampolines (3.7) convert flag-set to a
  status code at the boundary. A panic escaping an
  `extern "C"` lust fn aborts, as in Rust. Panics in
  shim Rust code are caught inside the shim.

`AssertUnwindSafe`, `catch_unwind`, `resume_unwind`,
`panic_any` live in `library/std`. `catch_unwind`
needs one compiler assist: the closure call inside
it is marked so lowering emits a landing pad that
clears the flag and moves the payload into the
return value. Represent it as an intrinsic wrapper
`intrinsics::catch_unwind_call` known to lowering.
Everything else is source.

### 7.3 Threads, TLS, atomics, sync

- Runtime: pthreads through tcclib-linked libc.
  `thread_spawn(trampoline, env_ptr, stack_size,
  name)` returns a handle id. The trampoline is the
  closure instance's slot trampoline. Env is a boxed
  closure value. Thread result: the trampoline writes
  (value slot, panic payload) into a heap cell;
  `thread_join_raw` reads it. Stack size and names
  pass through; spawn failure returns the OS error so
  `Builder::spawn` can be fallible and ts-rust's
  EAGAIN retry in `GoThread`
  (`crates/ts_goport/src/gopanic.rs:249-296`) works.
- `thread::scope`: scoped threads are normal spawns
  plus a join-all on scope exit, with the region
  model proving borrows do not escape (5.2: the scope
  fn's region param covers them). A panic in a scoped
  thread resumes in the scope after all joins, as in
  Rust.
- `Send`/`Sync` gate at check (2.7): spawn closure
  and return `Send + 'static`; scoped: `Send + 'scope`.
  Generic spawn works (bounds in std signatures),
  removing DESIGN's old "no spawn in generic code"
  limit, which ts-rust violates
  (`GoThread::spawn<F, T>` at gopanic.rs:249).
- TLS: one pthread key per `thread_local!` static.
  Lazy init on first `with`, destructor drops the
  value at thread exit in unspecified order (Rust
  makes the same weak promise). `LocalKey::with` and
  `try_with` in source. A TLS destructor that panics
  aborts. Re-entrant init gives Rust's behavior
  (panic on recursive access during init for
  non-const init). 73 `thread_local!` uses, including
  per-thread leaked arenas (3.6).
- Atomics: types in source over C11 `stdatomic.h`
  intrinsics (3.2). Widths: bool, 8 to 64-bit ints,
  ptr, usize. Orderings map to C11 memory orders
  one-to-one. `fence`, `spin_loop` hint (emit
  `__builtin_ia32_pause` where tcc allows, else a
  compiler barrier; measure in the spike). Ts-rust:
  404 atomic uses in 46 files.
- Sync in source over C handles (3.2): `Mutex`,
  `RwLock`, `Condvar`, `Once`, `OnceLock`,
  `LazyLock`, `mpsc` (channel and `sync_channel`
  with disconnect semantics), `Arc`/`Weak` with
  atomic counts. Wait/notify timeouts use the time
  intrinsics. No serial-execution shortcut for
  workers: ts-rust's bind/check/emit pools
  (`program.rs` sites in INVENTORY Q3) deadlock
  without real threads.

## 8. Incremental invalidation

Today the daemon has three cases (`src/driver.rs:7-14`):
body edits are cheap, signature edits recheck name
users, everything else rebuilds. A type change in
ts-rust costs rustc 60.2 s and lust a full rebuild
(PLAN.md target table). Milestone 9 needs finer
invalidation, but the graph must be designed now or
every stage will need a rewrite to record its reads.

### 8.1 Nodes and fingerprints

A node is a pure function of its inputs with a 64-bit
fingerprint (FxHash over normalized content, never
over session ids). "Normalized" means token-level, no
positions, as `src/scan.rs` already hashes bodies and
item headers without positions.

| Node | Inputs | Fingerprint covers |
|---|---|---|
| `File(file)` | bytes on disk | raw bytes |
| `Tokens(file)` | File | token stream with trees, no spans |
| `ModTree(crate)` | mod decls in all files | module set, parents, file assignment |
| `MacroDef(def)` | Tokens | def token stream (arms, normalized) |
| `Expansion(call)` | MacroDef, input tokens, cfg, files/env read | output token trees |
| `Items(file)` | Tokens, Expansions | parsed item headers |
| `Sig(def)` | Items, Sigs it names | resolved signature: types with def hashes, generics, predicates, repr, vis |
| `LayoutOf(adt)` | Sig of adt and field adts (generic form) | size/align function shape: field order, offsets as functions of params; concrete layouts derive at mono |
| `ImplSet(trait, head)` | all impl headers in the bucket, across visible crates | set of impl header hashes, sorted |
| `Scope(module)` | ModTree, imports, defs visible | resolved binding map fingerprint |
| `Checked(def)` | Sig(def), body tokens, every node it reads (8.2) | typed side tables exist; key is the read set plus body hash |
| `BodyIR(def)` | Checked | generic IR fingerprint |
| `Instance(key)` | BodyIR(template), arg layout fingerprints, selected impl instances on edges | substituted IR fingerprint |
| `CUnit(slot range)` | Instances in the unit, glue set | C text hash |
| `FailedLookup(query)` | Scope or ImplSet fingerprint at fail time | query key (module path, name) or (trait, self-type fingerprint) |

Const values (`Const` nodes) fold into `Sig` for const
items and assoc consts: the evaluated value is part of
the signature fingerprint. A const body edit that
keeps the same value invalidates nothing downstream.
Same idea for enum discriminants.

### 8.2 Recording reads

Check, collect, and mono take a `Reads` sink. Every
cross-item query records the node it used:

- `sig_of(def)`, `layout_of(adt)`, `impl_set(trait,
  head)` at every obligation (success records the
  impl; failure records a `FailedLookup` plus the
  bucket fingerprint), `scope(module)` at every path
  resolution, `macro_def` at every expansion,
  `checked(def)` at every call edge in mono,
  `layout(arg)` per instance arg.

This is a discipline, not a framework. Rules:

1. A stage may only read another item through a query
   fn on `Program`/`MonoCtx` that logs to `Reads`.
   Direct field pokes into other defs from check are
   banned by module privacy where Rust allows it, and
   by review where it does not.
2. The read set of a `Checked(def)` is stored with
   the result. On the next request, recompute the
   fingerprint of each read node (cheap hashes, bottom
   up) and reuse the result if all match and the body
   hash matches.
3. Failed lookups are first-class reads. Adding an
   impl changes `ImplSet(trait, head)`. Bodies that
   failed an obligation on that bucket recheck. Adding
   a def or an import changes `Scope(module)`. Bodies
   with a failed name there recheck. This is the rule
   DESIGN-TS section 3 states; without it, "add the
   missing impl" would keep failing until a full
   rebuild.

Today's name-based approximation ("bodies that mention
the name", `src/scan.rs:35-38` body idents) stays as a
prefilter for signature edits in milestones 4 to 5.
The read-set mechanism replaces it incrementally:
queries land with each subsystem (traits first, since
impl edits are the painful case).

### 8.3 Edit processing

Per request, per crate session:

1. Stat and read changed files (mtime plus size, then
   hash; hash is the truth). Re-run scan on them.
2. If `ModTree` changed (mod decl edit, file added or
   removed), rebuild the module tree and `Scope` for
   affected modules. Files not reachable any more
   leave the session.
3. Re-expand only calls whose inputs changed (6.5).
4. Re-collect changed items. Compare `Sig`
   fingerprints: unchanged sigs stop propagation even
   if the item body or formatting changed.
5. Dirty marking: reverse-walk `Reads` edges from
   changed nodes. Re-run `Checked`, `BodyIR` for
   dirty defs, in parallel.
6. Re-run mono discovery. It is a graph walk over
   cached `BodyIR`; only instances whose fingerprint
   changed re-emit C. Instance discovery itself is
   fast (hashmap walks). Do not try to incrementalize
   the walk; incrementalize its outputs.
7. Recompile dirty C units with tcc, overlay-link as
   today. Base rebuild after 32 overlays or when the
   slot table outgrows capacity, as today.

Worst case stays a full rebuild, but only when the
graph says so. The milestones sequence the wins:
milestone 4 keeps today's three cases at crate scale;
milestone 5 adds `ImplSet` and failed-lookup reads
(type and impl edits stop forcing full rebuilds
within a crate); milestone 9 adds cross-crate edges
and the disk instance cache, and tunes against the
ts-rust edit benchmark.

### 8.4 Disk cache

Content-addressed, local, ignored by git (PLAN.md
decision 1). Key per entry: (lust version, target,
profile flags, cfg hash, node fingerprint). Stored:

- Std crates: signature surface plus per-instance C
  and objects (3.8).
- Per instance: C text and the compiled object,
  keyed by `Instance` fingerprint. A cached-cold
  build re-runs the front end (fast, and it must, to
  know the instance set) and links cached objects.
- Expansion outputs for the 20 largest macros by
  output size. The rest are cheap to redo and not
  worth disk IO.
- The slot manifest per crate: `DefPathHash` and
  `InstanceKeyHash` to slot, so a restarted daemon
  reuses `libbase.so` instead of rebuilding it.

Not stored: checked bodies. Serializing `Checked`
plus local tys costs more than rechecking at lust's
check speed, and it freezes an IR format early.
Revisit only if cached-cold check profiles say the
front end dominates after milestone 9's work.

Soundness rule: a cache hit must be indistinguishable
from recomputation. Every input that can change an
output is in the key: file bytes, cfg, features,
edition, env reads by builtins, build-script outputs,
shim and adapter versions, allocator choice, overflow
and debug flag state. The milestone 2 "fixed
whole-request disk cache" work owns the key list;
this section extends it per node. CI runs the
random-edit fuzzer with the cache on and compares
against fresh sessions (the fresh-session guard in
PLAN.md milestone 1). Any mismatch is a cache bug,
not a flake.

## 9. Work breakdown for parallel agents

### 9.1 Source layout

Split the flat modules into owned directories. The
split serves ownership. It is not a rewrite: files
move, contents mostly stay, in serial refactor S4.

```text
src/
  main.rs  client.rs  daemon.rs  protocol.rs   (driver shell)
  diag.rs                Span, Diag, rendering            [S1]
  intern.rs              Sym, FxHash                      (shared, stable)
  lexer.rs               tokens, token trees              [W-MACRO]
  scan.rs                outline scan, hashes             [W-RESOLVE]
  parser.rs              AST parse                        [W-MACRO + all]
  ast.rs                 AST nodes                        [shared, frozen by S3]
  expand/
    mod.rs  match_.rs  transcribe.rs  builtin.rs          [W-MACRO]
  resolve/
    cargo.rs             cargo metadata, crate graph      [W-RESOLVE]
    modules.rs           module tree, mod loading         [W-RESOLVE]
    imports.rs           fixpoint, globs, visibility      [W-RESOLVE]
    cfg.rs               cfg env and strip                [W-RESOLVE]
  ty/
    mod.rs               TyKind, interning, subst         [S3, then W-TY]
    defs.rs              Defs, Generics, signatures       [S3, then W-TY]
    layout.rs            layout engine, const eval        [W-TY]
    lang.rs              lang item table                  [W-TY + W-STD]
    print.rs             ty_name for diagnostics          [W-TY]
  traits/
    index.rs             impl and method index, coherence [W-TRAITS]
    solve.rs             obligation queue, selection      [W-TRAITS]
    auto.rs              Send/Sync/Unpin/Sized            [W-TRAITS]
  check/
    mod.rs               body checking (today check.rs)   [W-CHECK]
    collect.rs           signature collection (today)     [W-TY + W-CHECK]
    method.rs            method and field resolution      [W-CHECK]
    coerce.rs            coercions, unsizing              [W-CHECK]
  borrowck/
    mod.rs               loans, liveness (today)          [W-BORROW]
    regions.rs           region vars, variance feed       [W-BORROW]
  ir.rs  lower.rs        IR and lowering                  [W-LOWER]
  mono/
    mod.rs               instance walk, substitution      [W-MONO]
    fuse.rs              iterator fusion                  [W-MONO]
  cgen.rs  tcc.rs        C backend (today)                [W-CGEN]
  runtime.c              C runtime cores                  [W-RUNTIME]
  driver/
    session.rs           workspace and crate sessions     [W-DRIVER]
    graph.rs             dep nodes, fingerprints, Reads   [W-DRIVER]
    cache.rs             disk cache                       [W-DRIVER]
    compile.rs           pipeline orchestration (today)   [W-DRIVER]
library/                 lust std source (3.1)            [W-STD]
  core/  alloc/  std/  deps/
shims/                   Rust shim crate (3.7)            [W-SHIM]
tests/  bench/           as today
```


### 9.2 Serial refactors first (keep this list closed)

These land one at a time, each by one agent, each
small, each with the full test suite green. No
parallel package starts until S1 to S6 are in. Total
serial cost target: 2.5k to 4k lines of churn. If a
serial item grows past its estimate by 2x, stop and
re-split; do not let it absorb feature work.

| ID | Change | Files | Size | Done when |
|---|---|---|---|---|
| S1 | `Span { file, lo, hi, ctxt }`, `FileId`, per-file line indexes. One file per crate still. | `diag.rs`, all span users (mechanical) | 400-700 | Difftest green. Diagnostics print file paths. |
| S2 | `DefId`/`DefPathHash`/`CrateId` types; slots keyed by hash; `FnId` becomes session-local alias of `LocalDefId`. No behavior change. | `collect.rs`, `driver.rs`, `cgen.rs` | 300-500 | Fuzzer green. Slot manifest round-trips. |
| S3 | `TyKind` v2 with `Adt(DefId, ArgsId)`, arg interning, `Generics`, `Defs` skeletons. `Vec`/`Option`/`String` still special-cased through compat helpers, deleted by W-STD. AST type nodes v2 (tuple, array, slice, fn ptr, dyn, impl trait, qualified path). Parse only; collect rejects the new forms with today's codes where unsupported. | `types.rs` to `ty/`, `ast.rs`, `parser.rs`, `collect.rs` | 800-1,200 | Difftest green. Parser accepts and collect cleanly rejects new type forms. |
| S4 | Module directory split per 9.1. Moves only, no logic change. `driver.rs` splits into `driver/` with `Session` per crate keyed by a `CrateKey` of one file. | all of `src/` (git mv) | 200-400 churn | `cargo build` and tests green. `git log --follow` works. |
| S5 | Std skeleton: `library/` crates with `Option`, `Result`, `Vec`, `String`, prelude; intrinsic registry in check and cgen; lang item lookup. Compiler flag to use std-source defs for these four while `Builtin` covers the rest. | `library/`, `ty/lang.rs`, `check/`, `cgen.rs`, `runtime.c` | 600-1,000 | A test program using only those types compiles through the source path. |
| S6 | Cargo graph loader and protocol v2: request names a crate; daemon routes by `SessionKey`. Single-file programs become a synthetic one-crate package. | `resolve/cargo.rs`, `protocol.rs`, `daemon.rs`, `driver/session.rs` | 400-700 | `lust check file.rs` unchanged for users. A two-file `mod` fixture checks. |

Interface freeze at the end of the serial phase.
These types change only through their owner, with a
note to all package owners: `Span`, `DefId`, `Ty`,
`TyKind`, `Generics`, `TraitRef`, `Defs` queries, AST
node shapes, IR `Rvalue` and `Terminator`, the
`Reads` query fns, intrinsic signatures, slot and
`InstanceKey` definitions. Everyone else codes against
them. Add new variants at the end of enums only.
Never renumber.

### 9.3 Parallel work packages

Packages run in waves. Sizes are implementation lines
(compiler plus runtime plus std source in the package),
not tests. Each package lists its tests and gate.
"Difftest green" always means `scripts/difftest.sh`
plus `SANITIZE=1` where codegen changes, per the
brief. Test dirs: `tests/pass`, `tests/fail`,
`tests/reject`, plus per-package fixture dirs named
below. Focused tests only; no bulk-generated slop.

#### Wave A (milestone 4): modules, macros, core language

Run 4 packages in parallel after S1-S6.

**W-RESOLVE: crate graph, modules, imports, cfg.**
Owns: `src/resolve/*`, `src/scan.rs`, module and `use`
AST handling in `parser.rs` (coordinate with W-MACRO),
visibility checks in collect.
Interfaces out: `CrateGraph`, `ModuleTree`, `Scope`
queries (`resolve_path`, `binding`), cfg env, file set
per crate. In: AST, expanded items.
Depends on: S1, S2, S4, S6. Not on W-MACRO internals:
it consumes post-expansion AST; until W-MACRO lands, a
stub expander passes macro-free code through.
Work: 1.2-1.3 module loading and fixpoint, glob and
re-export semantics, preludes, visibility, cfg strip,
`#[path]`, function-local `use`. Non-generic core
language that needs only resolution and collect:
`const`, `static`, type aliases (non-generic first),
tuple and unit structs.
Tests: `tests/modules/` fixtures: glob collisions from
1.4, re-export chains, `pub(crate)` edges, cfg on/off
per target, shared file in two crates, `#[path]`.
Gate: the ts-rust `prelude.rs` shape resolves in a
fixture crate; an ambiguous glob name errors only on
use. Size: 2.5k-3.5k.

**W-MACRO: token trees, expansion, builtin macros.**
Owns: `src/lexer.rs` (token trees), `src/expand/*`,
macro call parsing in `parser.rs`, hygiene contexts,
builtin macro parsing (format specs with W-STD),
`thread_local!` desugar shape (runtime in wave C).
Interfaces out: expanded token stream to AST, expansion
cache, span mapping for diagnostics. In: AST outline,
macro def items from W-RESOLVE's item scan.
Depends on: S1, S3 (AST v2). W-RESOLVE depends on its
output, not on its internals; sequence the stub so
both proceed.
Work: 6.1-6.5. Fragments, repetitions, `$crate`,
textual and path macro scopes, caps, `include` and
`env` builtins with cache keys.
Tests: `tests/macros/`: every ts-rust macro *shape*
(the 4 groups in INVENTORY Q2), hygiene cases
(capture, shadowing, labels), recursion caps.
Gate: all 66 ts-rust macro defs from an owned fixture
corpus expand token-equal to rustc. Size: 2.5k-4k.

**W-CORELANG: milestone 4 language without traits.**
Owns: `src/check/*` (body check growth), `src/ir.rs`,
`src/lower.rs` (with W-LOWER in later waves; in wave A
one owner holds both to avoid a split mid-flight),
`src/ty/layout.rs` basics, const evaluator basics.
Interfaces out: checked bodies and IR for the new
forms. In: `Defs`, `Scope`, layout queries.
Depends on: S3, S5, W-RESOLVE (scopes), W-STD (below)
for `Box`/`Result` defs.
Work: tuples, arrays, slices, range indexing and slice
patterns, `Box`, `Result`/`?`/let-else, labels and
break-with-value (exists), struct update, `if let`
chains, nested fns, reference and tuple patterns, enum
discriminants, u128/f32/f64 scalar paths (float text
with W-RUNTIME), format spec checking plumbing, `Drop`
trait as a real (non-generic) impl lookup ahead of full
traits, more derives (`Default`, `PartialOrd`, `Ord`),
`mem` ops. Sized checks for unsized slice/str behind
refs only; full `?Sized` bounds wait for traits.
Tests: `tests/pass` bulk per feature, layout assert
fixture from 4.4 (`repr(C, align(64))` offsets).
Gate: ts-rust scanner and JSON *kernels* as owned
fixtures compile with byte-equal output (PLAN.md
milestone 4 gate). Size: 6k-9k. This is the biggest
wave A package; split it in two (types/data in check,
control/patterns in lower) if staffing allows 5
agents, with `ir.rs` owned by the lower half.

**W-STD-A: core and alloc source, first half.**
Owns: `library/core/*`, `library/alloc/src/{string,
vec,boxed,rc,borrow}.rs` (rc bodies can land before
traits are general by using only concrete impls that
W-CORELANG's Drop path needs; full generic impls
finish in wave B), `library/std/src/{prelude,env,
io basics,path,time}`. Runtime cores it needs go
through W-RUNTIME interface (wave A slice: Vec growth
fix, string core freeze, float text).
Interfaces out: lang item defs, prelude, intrinsic
list (frozen with S5). In: language support as it
lands; std source must not use a feature before its
package lands it. Keep a `library/README` feature
ledger per file.
Depends on: S5. Co-evolves with W-CORELANG weekly, not
daily: freeze the needed std API list for the scanner
and JSON kernels first, build exactly that.
Tests: every public method gets a `tests/pass` case;
capacity and drop-order cases from 3.5.
Gate: `Builtin` cases for String/Vec/Option deleted;
difftest green through the source path.
Size: 4k-6k of lust source.

Wave A also needs a thin W-RUNTIME slice (can be the
W-STD-A agent or a 5th agent): Vec growth fix (3.3),
float print/parse C code with the fuzz gate (3.5),
`alloc(size, align)`. Size: 1k-1.5k C.

#### Wave B (milestone 5): traits, closures, dyn, mono

Entry condition: run the compatibility spike first
(one agent, one week-box): `NodeVisitor` with stored
`Rc<dyn Fn>` callbacks, `ArenaBox` with `Deref`,
one blanket impl (`AnyValue` shape), `go_flags!`
output types. The spike is throwaway code on top of
wave A stubs where needed. It validates 2.4, 2.8,
and 4.2 before the wave commits. Then 5 packages:

**W-TRAITS: impl index, solver, auto traits.**
Owns: `src/traits/*`, coherence in collect, derive
synthetic impls (from W-CORELANG's derives),
`Sized`/`?Sized` bound handling.
Interfaces out: `select(obligation) -> Selection`,
`auto_trait(ty, trait)`, method candidates query.
In: `Defs`, `Sig` queries (logs `ImplSet` reads, 8.2).
Depends on: S3, W-RESOLVE (trait-in-scope sets).
Tests: `tests/traits/`: blanket partition cases from
2.6 (both ts-rust shapes), overlap rejects, depth cap,
assoc type and const normalization, `?` conversion,
operator traits with `Output`.
Gate: traced solver test on the DESIGN syntax sample
plus the spike's blanket case, step-visible. Size:
3k-4.5k.

**W-CHECK-G: generic bodies, closures, method calls.**
Owns: `src/check/*`, capture analysis, `Fn` bound
handling, `impl Trait` (arg sugar and opaque
recording), coercions and unsizing, typed receivers.
Interfaces out: generic `Checked` bodies with
`CallTrait` evidence for W-MONO. In: W-TRAITS
selection, layout for capture structs (sizes only).
Depends on: W-TRAITS interface (can start against its
stub: `select` returning `ParamEvidence` always).
Tests: closure capture matrix (by ref/mut/move,
disjoint fields), stored closures, higher-ranked
`Fn(&T)` bounds, method ambiguity and autoderef order
fixtures, `impl Iterator` returns.
Gate: 3,733-fn closure problem reduced to fixtures:
one fixture per INVENTORY closure class passes
(adapters, std methods, user fns, stored, `dyn Fn`).
Size: 4k-6k.

**W-MONO: instantiation, vtables, fusion.**
Owns: `src/mono/*`, `src/lower.rs` generic-to-mono
boundary, glue instances, `TypeId` values, slot
assignment with W-DRIVER.
Interfaces out: concrete IR per instance for cgen,
vtable statics list. In: generic IR, W-TRAITS
selection for concrete self types, layouts.
Depends on: W-CHECK-G output shape (frozen in S3 plus
`CallTrait`), W-TRAITS.
Work: 4.1-4.3, share keys only if the spike numbers
demand it, fusion with the 4.3 spec and
`LUST_NO_FUSION` dual-run gate.
Tests: recursion limit parity with rustc, instance
dedup counts on a std-heavy fixture, the 150-case
fusion corpus.
Gate: `Rc<dyn Fn>` callback fixture runs byte-equal;
fusion corpus passes fused and unfused. Size:
4k-6k (fusion 3k-4k of it, per VERIFY G).

**W-STD-B: traits-heavy std and containers.**
Owns: `library/alloc` collections (`HashMap` typed
layer, `BTreeMap`, `VecDeque`), `Rc`/`Weak`/`RefCell`/
`Cell` completion, `Cow`, iterator adapter source in
`library/core`, `fmt` full surface, `io::Read/Write`
traits. With W-RUNTIME: `lust_hashmap` core.
Interfaces out: iterator adapter defs (fusion pattern
list for W-MONO, by `DefId`, frozen), glue needs.
Depends on: W-TRAITS, W-CHECK-G.
Gate: FxHashMap iteration-order difftest (3.5)
passes; `Rc<RefCell<T>>` fixture set passes.
Size: 5k-8k lust source, 0.8k-1.2k C for the table.

**W-DEPS: adapter crates.**
Owns: `library/deps/*` (indexmap, smallvec,
rustc-hash, memchr, bumpalo subset, xxh3 and ryu-js
C cores with W-RUNTIME review).
Interfaces out: crates by package id; version pins.
Depends on: W-STD-B containers.
Gate: per-crate exactness difftests in 3.6 table.
Size: 3k-5k.

#### Wave C (milestones 6 and 7): regions, threads, panics

**W-BORROW: regions over the loan engine.**
Owns: `src/borrowck/*`, variance in `ty/defs.rs`
(feed), region syntax in parser and collect (step A
can land at wave B tail by the same agent).
Depends on: W-CHECK-G (place-holds-loan needs final
IR place shapes), negative corpus first (5.6).
Gate: `Parser<'a>`, `JsonDecoder<'a>`,
`RuleContext<'a, 'c>` shaped fixtures compile; the
5.6 corpus rejects in both lust and rustc. Size:
3.5k-6k. Step A alone: 1k-2k, do it in wave B.

**W-PANIC: explicit propagation.**
Owns: IR unwind edges (with W-LOWER owner), lowering
cleanup blocks, runtime panic state and hooks in
`runtime.c`, `catch_unwind` assist, `track_caller`
already in wave A/B plumbing.
Entry: the 7.2 spike gate with measurements.
Depends on: W-MONO instance graph (can-panic fixpoint).
Gate: nested catch, rethrow, poison, drop-on-unwind
print order, panic in `FnOnce` env drop, thread join
payload: all byte-equal vs rustc. Size: 2k-3.5k.

**W-THREADS: std thread and sync surface.**
Owns: `library/std/src/{thread,sync}`, thread and
sync intrinsics in `runtime.c`, TLS keys, `mpsc`,
atomics wrappers, scope.
Depends on: W-PANIC (join payloads, poisoning),
W-BORROW (scoped borrows), auto traits.
Gate: parallel bind-shaped fixture (scoped workers
over files, mpsc results, shared `Arc<Mutex>`) runs
with equal sorted output; `Rc` across spawn rejects.
Size: 3k-5k (mostly lust source).

**W-SHIM: rustc shim and platform surface.**
Owns: `shims/` crate, lust-side foreign fn crates for
rustix/nix/signal/zlib/time/jemalloc-ctl,
`lust port prepare` build of the shim, allocator
selection (3.7).
Depends on: foreign fn support (small, in W-CHECK-G
wave B tail), W-PANIC boundary rules.
Gate: one end-to-end syscall path (file watch event
or signal) works in a fixture; jemalloc arena assign
plus 4 MiB align fixture passes. Size: 2.5k-4k plus
Rust shim code.

#### Wave D (milestones 8 and 9): port and speed

**W-PORT: ts-rust core CLI port.**
Owns: no compiler files by default. Owns the port
tree, `lust port scan/apply` fixes as separate small
packages when a gap is a compiler bug (filed to the
owning package, not fixed ad hoc).
Depends on: waves A-C gates.
Gate: PLAN.md 8a, baseline tests byte-equal, release
through Cargo at equal speed. Size: 3k-6k tool and
fix lines.

**W-PERF: invalidation depth and cold speed.**
Owns: `src/driver/graph.rs`, `cache.rs`, read-set
coverage in stages it does not own (paired commits
with owners), instance disk cache, front-end profiles,
backend bake-off harness.
Depends on: everything; starts part-time in wave B
(ImplSet reads) and full-time in wave D.
Gate: PLAN.md milestone 9 measurements on the ts-rust
edit loop, cold rows separate. Size: 4k-8k.

### 9.4 Milestone map

| Milestone (PLAN.md) | Packages | Gate (short) |
|---|---|---|
| 4 Rust core (13k-20k) | S1-S6, W-RESOLVE, W-MACRO, W-CORELANG, W-STD-A, runtime slice | Scanner and JSON kernels byte-equal. 66 macros token-equal. |
| 5 Traits, closures, dyn, Rc (25k-38k) | Spike, W-TRAITS, W-CHECK-G, W-MONO, W-STD-B, W-DEPS, step A lifetimes | Compatibility spike set byte-equal. Fusion corpus dual-run. |
| 6 Lifetimes (5k-9k) | W-BORROW | Three named fixtures compile. 5.6 corpus rejects. |
| 7 Threads and panics (9k-15k) | W-PANIC, W-THREADS, W-SHIM | Parallel bind. Recovered panic byte-equal. |
| 8 Port (3k-6k) | W-PORT plus fixes | Core CLI baselines pass. |
| 9 100x (4k-8k) | W-PERF | Measured 100x edit loop; cold rows stated. |

Package sizes sum inside the PLAN.md ranges. The
async surface for ATA (8b in PLAN.md; 3k-6k in
DESIGN-TS) is a wave D package of its own when the
port reaches it: state machine lowering in
`src/lower.rs`, `Future`/`Pin`/`Waker` in std. It
depends on W-BORROW (borrows across suspension) and
W-PANIC. Do not start it in wave C.

### 9.5 Coordination rules

1. One owner per file at a time (brief rule). The
   layout in 9.1 is the ownership map. Cross-owner
   edits go through the owner or land as a paired
   commit with the owner as reviewer.
2. Frozen interfaces (9.2) change only in a dedicated
   commit that touches no logic, so rebases stay
   mechanical. Announce in the wave channel before,
   not after.
3. Std source and compiler land features in lockstep
   per the std feature ledger (W-STD). A std file
   that needs a feature lists it; the feature package
   adds a fixture from that file.
4. Every package keeps `tests/pass|fail|reject`
   green on its branch tip before asking for merge.
   The orchestrator rebases packages in dependency
   order at wave end, then runs the full gates.
5. Perf: each wave B and later package records check
   and build time on the 31k crate plus its fixtures,
   before and after. A regression over 10% needs a
   note or a fix in the same package. Cold numbers
   use interleaved runs and medians (brief rule for
   the shared box).

## 10. Spikes, risks, and rejected options

Spikes are time-boxed, throwaway, and end in a number
or a yes/no. Schedule them at wave entries, not after
trouble.

| # | Spike | When | Question | Fallback |
|---|---|---|---|---|
| K1 | Compatibility spike (DESIGN-TS): NodeVisitor, ArenaBox, blanket, go_flags, stored callback | Wave B entry | Do 2.4, 2.8, 4.2 hold on real shapes? | Widen solver only where the spike points. No backtracking. |
| K2 | Panic propagation cost | Wave C entry | C bytes and run time vs abort (7.2 thresholds) | Per-fn setjmp with cleanup registry. |
| K3 | tcc platform check: `stdatomic.h`, TLS (`_Thread_local`), `__int128`, on Linux x86_64 and macOS arm64 | Wave A | Can the C backend express 3.2 and 4.4 as written? | Helper structs for u128 (already the default), pthread keys instead of `_Thread_local`. |
| K4 | Hashbrown order fidelity | W-STD-B | Does the C table match iteration order through rehash and remove storms? | Reviewed sort-before-output list for ts-rust; keep the difftest as a known-fail register, never silent. |
| K5 | Float printer fuzz | Wave A runtime | Byte-equal on 10M random bit patterns? | Swap Ryu variant; keep fuzz in CI at lower count. |
| K6 | Staticlib linking through tcc | W-SHIM entry | Does libtcc link the Rust staticlib (relocations, TLS)? | `cdylib` plus system linker for final link in dev. |
| K7 | Annotation burden count | Wave B, on port scan | How many ts-rust sites hit `L0220`? | Widen 2.4 step 3 (assoc binding inputs) if over ~200 sites. |

Risks that can change the plan, with first evidence:
restricted lifetimes growing toward full Rust (the
5.6 corpus passing but real ts-rust modules still
needing rewrites); mono C size on real modules (watch
instance C share vs the 30% threshold in 4.2);
adapter drift on upstream version bumps (pins make it
loud, not silent); daemon memory at 786k lines (1.8
eviction note; measure at milestone 8).

Rejected, with reasons on record:

- Dictionary passing for generics (VERIFY G: saves
  about 10 ms per 31k lines at real density, costs a
  second codegen path, still needs the instance walk
  for rustc's post-mono errors).
- One-time macro expansion as source (PLAN.md decision
  7: 29k lines of boilerplate to maintain).
- Serial worker execution in place of threads
  (INVENTORY Q3: 2.8x to 3.2x slower, and watch/LSP
  block on IO threads anyway).
- Handle conversion for borrowed fields (DESIGN-TS
  option C: callback and guard shapes do not map; also
  slows the release binary).
- A metadata (rlib-like) crate format before
  milestone 9 (in-process signature surfaces cover
  the port; a format freezes too much too early).

## Appendix A: new diagnostic code ranges

Reserve ranges now so parallel packages do not
collide. Existing codes keep their meanings.

| Range | Area |
|---|---|
| L0110-L0199 | Modules, imports, visibility, cfg, attributes (L0130 import cycle, L014x visibility, L0150 cfg, L0151 attribute) |
| L0200-L0219 | Types and aliases (L0210 alias cycle) |
| L0220-L0239 | Traits (L0220 annotation, L0221 overflow, L0222 no impl, L0225 overlap, L0230 GAT) |
| L0240-L0249 | Const eval |
| L0250-L0269 | dyn and closures (L0250 object safety, L0260 binder rank) |
| L0270-L0279 | Method resolution |
| L0280-L0299 | Regions and drop check (L0285 dropck, L0286 early-bound) |
| L0300-L0309 | Macros (L0301 caps, L0302 unknown, L0303 include, L0304 proc macro) |
| L0310-L0319 | Foreign and shim boundary |
| L9001 | Unsupported prototype feature (existing). New work must not add L9001 sites for planned features; use the ranges above. |

