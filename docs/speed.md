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
(goport-util-lsp), it is 1.7x: lust 495 ms, rustc 851 ms. 100x on this slice
means 8.5 ms per warm check.

| Slice | lines | warm body edit check, lust / rustc | ratio | 100x needs | cold check ratio |
|---|---:|---|---:|---:|---:|
| goport-util-lsp | 50,639 | 495 / 851 ms | 1.7x | 8.5 ms | 2.5x |
| goport-util | 35,080 | 280 / 277 ms | 1.0x | 2.8 ms | 1.7x |
| goport-util-small | 7,295 | 103 / 75 ms | 0.7x | 0.8 ms | 1.3x |

Line counts include the 42-line driver. The three runs ran on three sandboxes
at the same time. An earlier run of goport-util-lsp alone gave 393 / 642 ms
(1.6x): absolute times moved by about 25% between sandboxes, the ratio by
0.1x. Compare ratios across runs, not milliseconds.

- lust's own edit work is small: "check changed fns" is 5 to 19 ms. The rest
  is whole-crate work that every warm request repeats, even a no-op: std
  load+splice (24 to 180 ms), collect (30 to 100 ms), and resolve (11 to
  50 ms).
  Removing it is the first step (W-INCR2).
- rustc's warm cost grows with the crate: 277 ms at 35k lines, 851 ms at 50k
  (the lsproto part is dense generated code), 12.1 s on all of ts-rust
  (bench/tsrust/baseline.json). So the same lust speed gives a larger ratio on
  a larger slice. Do not compare a slice's lust time with the full-crate rustc
  time.
- Cold check is 1.3x to 2.5x. rustc with `-Z threads=8` is fast on these
  slices.

## Results

<!-- speed-table:start -->
### `goport-util-lsp`: 50,639 lines (34,236 code)

ts-rust `b11b618ae`, lust `62738dad`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 406 ms | 437 | 438 | 5 | 1022 ms (threads8) | 2.5x |
| cold build | 482 ms | 517 | 525 | 5 | 1176 ms (threads8) | 2.4x |
| run (built program) | 1 ms | 2 | 2 | 17 | 1 ms (threads8) | 0.53x |
| cold build+run | 483 ms | 518 | 526 | 5 | 1177 ms (threads8) | 2.4x |
| daemon first check (new session, empty cache) | 433 ms | 433 | 433 | 1 | 12 ms (threads8) | 0.03x |
| no-op check (warm daemon) | 374 ms | 382 | 383 | 5 | 12 ms (threads8) | 0.03x |
| cached restart check (new daemon, disk cache) | 422 ms | 447 | 451 | 5 | 12 ms (threads8) | 0.03x |
| body edit check (one fn) | 495 ms | 1038 | 1185 | 120 | 851 ms (default) | **1.7x** |
| body edit build (one fn) | 570 ms | 925 | 1257 | 12 | 972 ms (threads8) | 1.7x |
| body edit build+run (one fn) | 572 ms | 926 | 1259 | 12 | 973 ms (threads8) | 1.7x |
| signature edit check | 501 ms | 572 | 573 | 10 | 861 ms (threads8) | 1.7x |
| type edit check | 514 ms | 559 | 571 | 10 | 944 ms (threads8) | 1.8x |
| impl edit check | 538 ms | 647 | 673 | 10 | 891 ms (threads8) | 1.7x |
| error edit check (both reject) | 460 ms | 494 | 499 | 5 | 664 ms (threads8) | 1.4x |
| fix edit check | 534 ms | 552 | 554 | 5 | 788 ms (threads8) | 1.5x |

Cold build: 9.5 MB of C, 25 units, link 5 ms.
Peak RSS: lust cold check 268 MB, lust daemon 1022 MB (VmHWM over the run), cargo cold check 422 MB (default), 584 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): std load+splice 180, collect 100, resolve: expand+parse 36, check changed fns (par) 19, resolve: strip+register 16.

### `goport-util`: 35,080 lines (26,468 code)

ts-rust `b11b618ae`, lust `62738dad`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 237 ms | 274 | 282 | 5 | 402 ms (threads8) | 1.7x |
| cold build | 323 ms | 428 | 451 | 5 | 487 ms (threads8) | 1.5x |
| run (built program) | 1 ms | 2 | 3 | 17 | 1 ms (threads8) | 0.52x |
| cold build+run | 324 ms | 431 | 454 | 5 | 488 ms (threads8) | 1.5x |
| daemon first check (new session, empty cache) | 339 ms | 339 | 339 | 1 | 12 ms (threads8) | 0.03x |
| no-op check (warm daemon) | 208 ms | 222 | 223 | 5 | 9 ms (threads8) | 0.04x |
| cached restart check (new daemon, disk cache) | 251 ms | 260 | 261 | 5 | 10 ms (threads8) | 0.04x |
| body edit check (one fn) | 280 ms | 334 | 368 | 120 | 277 ms (default) | **0.99x** |
| body edit build (one fn) | 330 ms | 383 | 392 | 12 | 328 ms (default) | 0.99x |
| body edit build+run (one fn) | 332 ms | 384 | 394 | 12 | 329 ms (default) | 0.99x |
| signature edit check | 285 ms | 298 | 301 | 10 | 275 ms (default) | 0.97x |
| type edit check | 294 ms | 316 | 326 | 10 | 313 ms (threads8) | 1.1x |
| impl edit check | 287 ms | 314 | 318 | 10 | 274 ms (threads8) | 0.96x |
| error edit check (both reject) | 246 ms | 255 | 256 | 5 | 205 ms (threads8) | 0.83x |
| fix edit check | 286 ms | 304 | 307 | 5 | 245 ms (default) | 0.86x |

Cold build: 8.0 MB of C, 24 units, link 5 ms.
Peak RSS: lust cold check 241 MB, lust daemon 822 MB (VmHWM over the run), cargo cold check 249 MB (default), 342 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): std load+splice 99, collect 56, resolve: expand+parse 24, check changed fns (par) 10, resolve: chunk scan+concat 6.

### `goport-util-small`: 7,295 lines (4,223 code)

ts-rust `b11b618ae`, lust `62738dad`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 95 ms | 101 | 102 | 5 | 120 ms (threads8) | 1.3x |
| cold build | 140 ms | 146 | 146 | 5 | 170 ms (threads8) | 1.2x |
| run (built program) | 1 ms | 1 | 1 | 17 | 1 ms (threads8) | 0.64x |
| cold build+run | 141 ms | 147 | 148 | 5 | 171 ms (threads8) | 1.2x |
| daemon first check (new session, empty cache) | 139 ms | 139 | 139 | 1 | 11 ms (default) | 0.08x |
| no-op check (warm daemon) | 86 ms | 88 | 88 | 5 | 11 ms (threads8) | 0.13x |
| cached restart check (new daemon, disk cache) | 111 ms | 119 | 119 | 5 | 11 ms (default) | 0.1x |
| body edit check (one fn) | 103 ms | 119 | 134 | 120 | 75 ms (default) | **0.73x** |
| body edit build (one fn) | 137 ms | 159 | 161 | 12 | 120 ms (default) | 0.87x |
| body edit build+run (one fn) | 138 ms | 160 | 162 | 12 | 120 ms (default) | 0.87x |
| signature edit check | 114 ms | 135 | 139 | 10 | 80 ms (default) | 0.7x |
| type edit check | 110 ms | 130 | 132 | 10 | 103 ms (threads8) | 0.94x |
| impl edit check | 108 ms | 131 | 134 | 10 | 98 ms (threads8) | 0.91x |
| error edit check (both reject) | 90 ms | 101 | 101 | 5 | 78 ms (default) | 0.87x |
| fix edit check | 101 ms | 110 | 112 | 5 | 66 ms (default) | 0.65x |

Cold build: 4.6 MB of C, 24 units, link 2 ms.
Peak RSS: lust cold check 86 MB, lust daemon 428 MB (VmHWM over the run), cargo cold check 141 MB (default), 205 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): collect 30, std load+splice 24, resolve: expand+parse 11, check changed fns (par) 5, resolve: chunk scan+concat 2.

<!-- speed-table:end -->

## Larger slices

A 200k-line row and a full-size row come when lust accepts more of ts-rust.
Two lust bugs block every larger slice today: a user module named `core`
breaks lust's std (ts-rust has `crate::core`), and a glob import does not bring
in std items that a module re-exports (ts-rust's `use crate::prelude::*`). The
pruner lists every other blocker in `bench/slices/<name>/prune.json`
(`removed_lines_by_oracle_and_code`).
