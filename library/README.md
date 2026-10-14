# Lust std in source: the feature ledger

Std is lust source in three shipped crates, plus adapter crates for
dependencies (docs/ARCH.md sections 3.1 and 3.6). This file is the
ledger: what exists, what is declared but has no body yet, and what
waits for a later wave. Keep it current when a row moves. The
machine-checked tables are in `src/ty/lang.rs`; the loader is
`src/stdload.rs`.

## How std loads in S5

- The driver pays for std only when user source can mention a source
  std fn (a byte scan for the triggers in `STD_FNS`). Normal compiles
  do not parse std at all.
- On a hit, the loader parses and checks the shipped module files as
  their own crates, once per daemon session (the result is cached in
  the session). A check failure in shipped source, a missing required
  lang item, or a registry row with no matching source fn is a
  compiler installation error, not a user diagnostic.
- Checked non-generic std fns are spliced into the user compile under
  mangled names, in a source range the checker knows belongs to the
  shipped crate. Intrinsic privilege keys on that provenance, never
  on names user code can write (section 3.1 item 1).
- Generic std waits for the minimal generic pipeline (section 9.3).
  No `Builtin` case is deleted by S5; String, Vec, and Option stay
  builtin until W-STD moves them.
- `LUST_STD_SRC=<dir>` makes the loader read module files from
  `<dir>/std/src/` instead of the copies built into the compiler
  (the section 3.8 override, for std authors). Std is otherwise
  immutable inside one session.

## Crates

Adapter crates in `deps/` follow `src/resolve/adapters.rs`: each has a
`Cargo.toml` that pins the exact upstream version, the adapter format,
the upstream features it implements, and its exact-layout types.

| Crate | State in S5 | Next owner |
|---|---|---|
| core | Skeleton: lib.rs, intrinsics.rs (signature mirror). No items. | W-STD |
| alloc | Skeleton: lib.rs only. String/Vec stay builtin. | W-STD |
| std | `process::exit` in source, over the `exit` intrinsic. | W-STD |
| deps/rustc-hash | README only. Upstream 2.1.2. | W-DEPS |
| deps/indexmap | README only. Upstream 2.14.0. | W-DEPS |
| deps/smallvec | README only. Upstream 1.15.1. | W-DEPS |
| deps/memchr | Adapter for 2.8.2: byte and substring search in source (deps/memchr/README.md). | W-DEPS |
| deps/xxhash-rust | Adapter for 0.8.15: `xxh3` over the C core (deps/xxhash-rust/README.md). | W-DEPS |
| deps/ryu-js | Adapter for 1.0.2: `Buffer::format` for f64 over the runtime JS printer (deps/ryu-js/README.md). | W-DEPS |
| deps/bumpalo, deps/num-bigint, deps/num-traits | No crate yet (section 3.6). | W-DEPS |

## Source std fns (`STD_FNS` in src/ty/lang.rs)

| Path | Body | Notes |
|---|---|---|
| `std::process::exit` | library/std/src/process.rs | Over intrinsic `exit` (`lust_exit`: flush, then libc exit). Test: tests/pass/std_process_exit.rs. |
| `std::process::abort` | Declared, no body | A call rejects with L0640 (declared surface, section 3.1). Body needs the abort runtime hook; W-STD. |

## Intrinsics (`INTRINSICS` in src/ty/lang.rs)

Implemented (codegen emits them): `exit`; the adapter cores
`xxh3_64`/`xxh3_128` (xxhash-rust, C in src/runtime/deps.c) and
`ryu_js_fmt_f64` (ryu-js, the JS printer in src/runtime/float.c).
Adapter crates get their privilege from the resolver's record of their
files (`Program::shipped_crate_at`).

Registered with signature and privilege list, no body yet (a
privileged call rejects with L0640): the memory, bytes, ptr, float
text, panic, thread, sync, atomic, time, fd IO, and process groups of
section 3.2; the three specialization predicates of section 3.4; the
adapter cores `arena_alloc` (bumpalo) and `memchr`/`memrchr`/`memmem`
(memchr, whose adapter searches in source for now). A user call to any
intrinsic rejects with L0642.

Specialization that changes output (section 3.4 gate): none in source
yet, so no unfused difftest rows yet. Add one row here per predicate
use when W-STD writes it.

## Lang items (`LANG_ITEMS` in src/ty/lang.rs)

Resolved at load today: `option`, `result`, `string`, `vec` (builtin
defs; required, a load fails without them).

Declared in the table, no def yet: `box`, `rc`, `arc`,
`unsafe_cell`, `phantom_data`, the Range family, `iterator`,
`into_iterator`, `drop`, `deref`, `deref_mut`, the Fn family,
`sized`, `send`, `sync`, `panic`, `panic_bounds`, `formatter`,
`exchange_malloc`, `exchange_free`. W-STD marks the source def of
each with `#[lust_lang = "..."]` (alone on the line above the item
until the parser learns the attribute) and flips its row to
required in the same change.

## Rules for new source std fns (until W-RESOLVE)

1. Add the fn in the right `library/<crate>/src/<module>.rs`, in the
   supported subset, non-generic.
2. Add its `STD_FNS` row (path, mangled name, trigger substring).
3. Register each new intrinsic first: signature, C symbol, privilege
   list, and a difftest (section 3.2). Default answer for a new
   intrinsic is source, not a new row.
4. Add a tests/pass difftest that calls it, and update this ledger.
