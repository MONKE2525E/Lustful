# lust speed on real ts-rust code

The promise: **a warm `lust check` after a one-function edit is 100x faster than
`cargo check` (rustc 1.99, incremental) on the same source.** The source is a
pinned slice of ts-rust, not generated code. Cold check, build, and restart are
reported in their own rows; they are not the promise.

## Method

- Corpus: `bench/slices/<name>`, real ts-rust source pinned at a commit, minus
  the items lust cannot take yet (see `bench/slices/README.md`). lust and rustc
  both accept it, and `lust build` builds it.
- One source tree for both compilers. Every row runs lust, then cargo, on the
  same files.
- lust runs through a warm `lust daemon` (the client is the `lust` command).
  Cold rows use a one-shot process with an empty cache.
- rustc runs through cargo in two configs, each with its own target dir:
  `default` (stable dev profile, incremental on) and `threads8`
  (`RUSTC_BOOTSTRAP=1`, `-Z threads=8`). Both use `debuginfo = 0`. The ratio
  uses the faster config's median for each row.
- For the daemon first check, no-op, and cached restart rows, the rustc column
  is a no-op `cargo check` (nothing changed since its last check).
- Body edits: 120 edits that alternate across 24 fns in 24 different files.
  Each edit inserts or changes one `let` statement in one fn body.
- Signature, type, and impl edits are in the slice's `edits.json`. Each is
  applied and reverted, 5 cycles. The error edit puts a type error in a body
  (both compilers must reject it); the fix edit removes it.
- Exactness: on every source state, lust and cargo agree on pass or fail. Every
  10th state and every non-body edit, a cold one-shot `lust check` must give
  the same stdout, stderr, and exit code as the warm daemon. A mismatch stops
  the run.
- Wall time of the whole command (client or cargo process), median, p95, and
  worst. Phase times come from `lust check --timings`. Peak RSS: the daemon's
  VmHWM; for cargo, the largest process in its tree.
- Host: one boat sandbox per run (16 vCPU, nothing else running).
- The slice's empty `main` calls `bench/slices/driver.rs` in the benchmark
  copy: it calls kept ts-rust tspath fns and prints the results. After every
  build, the lust binary and each rustc binary run, and stdout, stderr, and exit
  code must match. That gives the run and build+run rows. The run row is tiny
  work; it is there for exactness, not speed.

Reproduce:

```sh
cargo build --release
python3 scripts/scale-gate.py --slice bench/slices/goport-util --json gu.json
python3 scripts/speed_slice.py --render docs/speed.md lsp.json gu.json small.json
```

The quick gate row: `scripts/speed-row.sh` (small slice, 20 body edits).

## Where we are (2026-10-14)

The promise row is **body edit check**. Today, on the 50k-line slice
(goport-util-lsp), it is 1.6x: lust 393 ms, rustc 642 ms. 100x on this slice
means 6.4 ms per warm check.

| Slice | lines | warm body edit check, lust / rustc | ratio | 100x needs |
|---|---:|---|---:|---:|
| goport-util-lsp | 50,597 | 393 / 642 ms | 1.6x | 6.4 ms |
| goport-util | 35,038 | 278 / 242 ms | 0.9x | 2.4 ms |
| goport-util-small | 7,253 | 132 / 94 ms | 0.7x | 0.9 ms |

- lust's own edit work is small: "check changed fns" is 9 to 15 ms. The rest is
  whole-crate work that every warm request repeats, even a no-op: std
  load+splice (97 to 142 ms), collect (57 to 79 ms), and resolve (about 45 ms).
  Removing it is the first step (W-INCR2).
- rustc's warm cost grows with the crate: 242 ms at 35k lines, 642 ms at 50k
  (the lsproto part is dense generated code), 12.1 s on all of ts-rust
  (bench/tsrust/baseline.json). So the same lust speed gives a larger ratio on
  a larger slice. Do not compare a slice's lust time with the full-crate rustc
  time.
- Cold check is 1.1x to 2.5x. rustc with `-Z threads=8` is fast on these
  slices.

## Results

<!-- speed-table:start -->
### `goport-util-lsp`: 50,597 lines (34,236 code)

ts-rust `b11b618ae`, lust `3fb35fed`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 319 ms | 362 | 368 | 5 | 810 ms (threads8) | 2.5x |
| cold build | 400 ms | 418 | 422 | 5 | 861 ms (threads8) | 2.1x |
| daemon first check (new session, empty cache) | 381 ms | 381 | 381 | 1 | 10 ms (default) | 0.03x |
| no-op check (warm daemon) | 328 ms | 354 | 360 | 5 | 11 ms (threads8) | 0.03x |
| cached restart check (new daemon, disk cache) | 368 ms | 382 | 385 | 5 | 10 ms (threads8) | 0.03x |
| body edit check (one fn) | 392 ms | 465 | 523 | 120 | 642 ms (default) | **1.6x** |
| body edit build (one fn) | 489 ms | 604 | 647 | 12 | 769 ms (threads8) | 1.6x |
| signature edit check | 375 ms | 411 | 416 | 10 | 596 ms (default) | 1.6x |
| type edit check | 395 ms | 437 | 438 | 10 | 670 ms (threads8) | 1.7x |
| impl edit check | 398 ms | 489 | 536 | 10 | 620 ms (threads8) | 1.6x |
| error edit check (both reject) | 345 ms | 356 | 357 | 5 | 472 ms (threads8) | 1.4x |
| fix edit check | 393 ms | 456 | 471 | 5 | 547 ms (default) | 1.4x |

Cold build: 9.5 MB of C, 25 units, link 5 ms.
Peak RSS: lust cold check 267 MB, lust daemon 1030 MB (VmHWM over the run), cargo cold check 426 MB (default), 586 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): std load+splice 142, collect 79, resolve: expand+parse 29, check changed fns (par) 15, resolve: strip+register 12.

### `goport-util`: 35,038 lines (26,468 code)

ts-rust `b11b618ae`, lust `83c9e328`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 246 ms | 308 | 322 | 5 | 377 ms (threads8) | 1.5x |
| cold build | 299 ms | 385 | 394 | 5 | 438 ms (threads8) | 1.5x |
| daemon first check (new session, empty cache) | 285 ms | 285 | 285 | 1 | 11 ms (default) | 0.04x |
| no-op check (warm daemon) | 243 ms | 247 | 248 | 5 | 11 ms (threads8) | 0.04x |
| cached restart check (new daemon, disk cache) | 265 ms | 300 | 306 | 5 | 11 ms (threads8) | 0.04x |
| body edit check (one fn) | 278 ms | 345 | 401 | 120 | 242 ms (default) | **0.87x** |
| body edit build (one fn) | 358 ms | 407 | 435 | 12 | 296 ms (default) | 0.83x |
| signature edit check | 301 ms | 353 | 383 | 10 | 263 ms (default) | 0.87x |
| type edit check | 312 ms | 395 | 414 | 10 | 289 ms (threads8) | 0.92x |
| impl edit check | 311 ms | 399 | 417 | 10 | 282 ms (threads8) | 0.91x |
| error edit check (both reject) | 283 ms | 358 | 377 | 5 | 193 ms (threads8) | 0.68x |
| fix edit check | 321 ms | 401 | 407 | 5 | 236 ms (default) | 0.73x |

Cold build: 8.0 MB of C, 24 units, link 4 ms.
Peak RSS: lust cold check 473 MB, lust daemon 849 MB (VmHWM over the run), cargo cold check 286 MB (default), 422 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): std load+splice 97, collect 57, resolve: expand+parse 23, check changed fns (par) 9, resolve: discovery 7.

### `goport-util-small`: 7,253 lines (4,223 code)

ts-rust `b11b618ae`, lust `83c9e328`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 143 ms | 163 | 165 | 5 | 152 ms (threads8) | 1.1x |
| cold build | 182 ms | 186 | 186 | 5 | 161 ms (threads8) | 0.88x |
| daemon first check (new session, empty cache) | 133 ms | 133 | 133 | 1 | 11 ms (default) | 0.09x |
| no-op check (warm daemon) | 112 ms | 124 | 127 | 5 | 13 ms (default) | 0.11x |
| cached restart check (new daemon, disk cache) | 142 ms | 163 | 164 | 5 | 13 ms (threads8) | 0.09x |
| body edit check (one fn) | 132 ms | 171 | 177 | 120 | 94 ms (default) | **0.71x** |
| body edit build (one fn) | 168 ms | 188 | 190 | 12 | 136 ms (threads8) | 0.81x |
| signature edit check | 119 ms | 133 | 137 | 10 | 81 ms (default) | 0.68x |
| type edit check | 120 ms | 141 | 142 | 10 | 109 ms (threads8) | 0.91x |
| impl edit check | 118 ms | 132 | 141 | 10 | 94 ms (threads8) | 0.8x |
| error edit check (both reject) | 95 ms | 103 | 105 | 5 | 83 ms (threads8) | 0.87x |
| fix edit check | 106 ms | 115 | 116 | 5 | 71 ms (default) | 0.67x |

Cold build: 4.6 MB of C, 24 units, link 3 ms.
Peak RSS: lust cold check 277 MB, lust daemon 417 MB (VmHWM over the run), cargo cold check 141 MB (default), 204 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): collect 38, std load+splice 30, resolve: expand+parse 14, check changed fns (par) 6, resolve: chunk scan+concat 3.

<!-- speed-table:end -->

## Larger slices

A 200k-line row and a full-size row come when lust accepts more of ts-rust.
Two lust bugs block every larger slice today: a user module named `core`
breaks lust's std (ts-rust has `crate::core`), and a glob import does not bring
in std items that a module re-exports (ts-rust's `use crate::prelude::*`). The
pruner lists every other blocker in `bench/slices/<name>/prune.json`
(`removed_lines_by_oracle_and_code`).
