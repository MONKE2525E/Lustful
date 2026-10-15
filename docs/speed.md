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
python3 scripts/speed_slice.py --render docs/speed.md full.json nochecker.json lsp.json gu.json small.json
```

The quick gate row: `scripts/speed-row.sh` (small slice, 20 body edits).

## Where we are (2026-10-14, lust next 23fffb0b)

The promise row is **body edit check**. On the biggest slice, `tsrust-full`
(all of ts_goport that lust takes today, 150k lines), it is **8.9x**: lust
271 ms, rustc 2,423 ms. 100x on this slice means 24 ms per warm check.

| Slice | lines | warm body edit check, lust / rustc | ratio | p95 lust | 100x needs | no-op | cold check ratio | cold build+run ratio |
|---|---:|---|---:|---:|---:|---:|---:|---:|
| tsrust-full | 150,189 | 271 / 2423 ms | **8.9x** | 461 ms | 24.2 ms | 2.7 ms | 2.1x | 2.0x |
| tsrust-nochecker | 107,126 | 207 / 1373 ms | **6.6x** | 769 ms | 13.7 ms | 2.3 ms | 2.5x | 2.0x |
| goport-util-lsp | 53,960 | 92 / 669 ms | **7.3x** | 174 ms | 6.7 ms | 1.1 ms | 5.3x | 3.1x |
| goport-util | 37,939 | 61 / 281 ms | **4.6x** | 130 ms | 2.8 ms | 1.1 ms | 3.4x | 2.1x |
| goport-util-small | 8,379 | 20 / 61 ms | **3.1x** | 40 ms | 0.6 ms | 0.6 ms | 2.3x | 1.3x |

Line counts include the 42-line driver. Five sandboxes ran at the same time,
one slice each. Earlier runs moved absolute times by about 25% between
sandboxes and the ratio by about 0.1x to 0.3x: compare ratios, not
milliseconds. On 885e1c30 (W-BENCH2 start) the 53k ratio was 5.6x; on
67cf0640 (W-BENCH) the 50k ratio was 1.7x.

- The ratio grows with the slice, as expected: rustc's warm cost grows with
  the crate (61 ms at 8k, 2.4 s at 150k), lust's body patch does not grow as
  fast.
- lust's remaining warm cost per body edit is whole-crate work, not the
  edit: collect (15 to 190 ms) and resolve's expand+parse (11 to 32 ms on the
  three small slices). "check changed fns" is 2 to 56 ms.
- On the two big slices some edits leave the body patch and take a full
  resolve (`resolve: strip+register` 290 to 640 ms in the phase medians): an
  edit in a fn that holds an item (`static X: OnceLock<..>` in the body) or
  in cfg-disabled code (`#[cfg(test)]`, `#[cfg(not(unix))]`). 5 of the 24
  targets on tsrust-nochecker do this, so its p95 is 3.7x its median.
- Signature, type, and impl edits are 1.5x to 3.9x: they cost close to a
  cold check.
- The daemon's peak RSS on tsrust-full is 2.8 GB; cargo's largest process is
  1.0 GB.
- Cold check is 2.1x to 5.3x. rustc with `-Z threads=8` is fast on these
  slices.

## Results

<!-- speed-table:start -->
### `tsrust-full`: 150,189 lines (91,879 code)

ts-rust `b11b618ae`, lust `23fffb0bd`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 1105 ms | 1164 | 1165 | 5 | 2299 ms (threads8) | 2.1x |
| cold build | 1310 ms | 1332 | 1335 | 5 | 2668 ms (threads8) | 2.0x |
| run (built program) | 2 ms | 4 | 5 | 17 | 1 ms (threads8) | 0.4x |
| cold build+run | 1311 ms | 1334 | 1336 | 5 | 2669 ms (threads8) | 2.0x |
| daemon first check (new session, empty cache) | 1295 ms | 1295 | 1295 | 1 | 13 ms (default) | 0.01x |
| no-op check (warm daemon) | 3 ms | 3 | 3 | 5 | 13 ms (default) | 4.7x |
| cached restart check (new daemon, disk cache) | 1277 ms | 1306 | 1311 | 5 | 13 ms (threads8) | 0.01x |
| body edit check (one fn) | 271 ms | 461 | 1878 | 120 | 2423 ms (default) | **8.9x** |
| body edit build (one fn) | 460 ms | 571 | 574 | 12 | 2536 ms (threads8) | 5.5x |
| body edit build+run (one fn) | 462 ms | 574 | 576 | 12 | 2537 ms (threads8) | 5.5x |
| signature edit check | 1270 ms | 1477 | 1499 | 10 | 1990 ms (threads8) | 1.6x |
| type edit check | 1319 ms | 1405 | 1443 | 10 | 2109 ms (threads8) | 1.6x |
| impl edit check | 1330 ms | 1581 | 1641 | 10 | 1988 ms (threads8) | 1.5x |
| error edit check (both reject) | 135 ms | 177 | 179 | 5 | 1604 ms (threads8) | 11.9x |
| fix edit check | 255 ms | 294 | 298 | 5 | 1820 ms (default) | 7.2x |

Cold build: 14.8 MB of C, 39 units, link 9 ms.
Peak RSS: lust cold check 756 MB, lust daemon 2779 MB (VmHWM over the run), cargo cold check 748 MB (default), 967 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): resolve: expand+parse 276, total 260, collect 188, resolve: other 121, resolve: epoch 96.

### `tsrust-nochecker`: 107,126 lines (67,850 code)

ts-rust `b11b618ae`, lust `23fffb0bd`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 614 ms | 638 | 643 | 5 | 1508 ms (threads8) | 2.5x |
| cold build | 828 ms | 833 | 834 | 5 | 1681 ms (threads8) | 2.0x |
| run (built program) | 2 ms | 2 | 3 | 17 | 1 ms (default) | 0.46x |
| cold build+run | 829 ms | 834 | 836 | 5 | 1682 ms (threads8) | 2.0x |
| daemon first check (new session, empty cache) | 699 ms | 699 | 699 | 1 | 13 ms (threads8) | 0.02x |
| no-op check (warm daemon) | 2 ms | 3 | 4 | 5 | 13 ms (threads8) | 5.7x |
| cached restart check (new daemon, disk cache) | 653 ms | 686 | 693 | 5 | 13 ms (threads8) | 0.02x |
| body edit check (one fn) | 207 ms | 769 | 949 | 120 | 1373 ms (default) | **6.6x** |
| body edit build (one fn) | 369 ms | 401 | 405 | 12 | 1589 ms (threads8) | 4.3x |
| body edit build+run (one fn) | 371 ms | 403 | 407 | 12 | 1590 ms (threads8) | 4.3x |
| signature edit check | 832 ms | 1043 | 1082 | 10 | 1664 ms (default) | 2.0x |
| type edit check | 891 ms | 1055 | 1071 | 10 | 1902 ms (threads8) | 2.1x |
| impl edit check | 1030 ms | 1113 | 1146 | 10 | 1881 ms (threads8) | 1.8x |
| error edit check (both reject) | 130 ms | 148 | 148 | 5 | 1348 ms (threads8) | 10.3x |
| fix edit check | 260 ms | 349 | 372 | 5 | 1681 ms (default) | 6.5x |

Cold build: 11.9 MB of C, 39 units, link 8 ms.
Peak RSS: lust cold check 412 MB, lust daemon 1486 MB (VmHWM over the run), cargo cold check 538 MB (default), 693 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): total 197, collect 132, resolve: expand+parse 122, check changed fns (par) 47, resolve: other 41.

### `goport-util-lsp`: 53,960 lines (36,890 code)

ts-rust `b11b618ae`, lust `23fffb0bd`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 152 ms | 156 | 156 | 5 | 809 ms (threads8) | 5.3x |
| cold build | 289 ms | 302 | 305 | 5 | 899 ms (threads8) | 3.1x |
| run (built program) | 1 ms | 2 | 2 | 17 | 1 ms (threads8) | 0.48x |
| cold build+run | 290 ms | 304 | 308 | 5 | 900 ms (threads8) | 3.1x |
| daemon first check (new session, empty cache) | 176 ms | 176 | 176 | 1 | 10 ms (default) | 0.06x |
| no-op check (warm daemon) | 1 ms | 1 | 1 | 5 | 10 ms (default) | 9.1x |
| cached restart check (new daemon, disk cache) | 177 ms | 200 | 202 | 5 | 11 ms (default) | 0.06x |
| body edit check (one fn) | 92 ms | 174 | 199 | 120 | 669 ms (default) | **7.3x** |
| body edit build (one fn) | 204 ms | 283 | 363 | 12 | 760 ms (threads8) | 3.7x |
| body edit build+run (one fn) | 205 ms | 284 | 364 | 12 | 761 ms (threads8) | 3.7x |
| signature edit check | 175 ms | 205 | 209 | 10 | 668 ms (threads8) | 3.8x |
| type edit check | 192 ms | 256 | 273 | 10 | 745 ms (threads8) | 3.9x |
| impl edit check | 195 ms | 238 | 240 | 10 | 739 ms (threads8) | 3.8x |
| error edit check (both reject) | 50 ms | 53 | 53 | 5 | 531 ms (threads8) | 10.5x |
| fix edit check | 100 ms | 116 | 117 | 5 | 634 ms (default) | 6.3x |

Cold build: 8.6 MB of C, 40 units, link 5 ms.
Peak RSS: lust cold check 158 MB, lust daemon 623 MB (VmHWM over the run), cargo cold check 386 MB (default), 513 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): collect 65, resolve: expand+parse 32, check changed fns (par) 14, resolve: strip+register 13, resolve: discovery 8.

### `goport-util`: 37,939 lines (28,695 code)

ts-rust `b11b618ae`, lust `23fffb0bd`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 113 ms | 126 | 127 | 5 | 380 ms (threads8) | 3.4x |
| cold build | 209 ms | 213 | 213 | 5 | 444 ms (threads8) | 2.1x |
| run (built program) | 1 ms | 2 | 2 | 17 | 1 ms (threads8) | 0.47x |
| cold build+run | 211 ms | 214 | 215 | 5 | 445 ms (threads8) | 2.1x |
| daemon first check (new session, empty cache) | 131 ms | 131 | 131 | 1 | 9 ms (threads8) | 0.07x |
| no-op check (warm daemon) | 1 ms | 2 | 2 | 5 | 10 ms (threads8) | 9.5x |
| cached restart check (new daemon, disk cache) | 133 ms | 150 | 153 | 5 | 10 ms (threads8) | 0.08x |
| body edit check (one fn) | 61 ms | 130 | 167 | 120 | 281 ms (default) | **4.6x** |
| body edit build (one fn) | 137 ms | 157 | 164 | 12 | 341 ms (default) | 2.5x |
| body edit build+run (one fn) | 138 ms | 158 | 165 | 12 | 342 ms (default) | 2.5x |
| signature edit check | 116 ms | 124 | 125 | 10 | 278 ms (default) | 2.4x |
| type edit check | 134 ms | 154 | 161 | 10 | 330 ms (threads8) | 2.5x |
| impl edit check | 126 ms | 154 | 158 | 10 | 305 ms (default) | 2.4x |
| error edit check (both reject) | 35 ms | 37 | 38 | 5 | 220 ms (threads8) | 6.3x |
| fix edit check | 61 ms | 65 | 65 | 5 | 248 ms (default) | 4.1x |

Cold build: 7.2 MB of C, 38 units, link 5 ms.
Peak RSS: lust cold check 150 MB, lust daemon 552 MB (VmHWM over the run), cargo cold check 259 MB (default), 353 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): collect 43, resolve: expand+parse 28, check changed fns (par) 9, resolve: strip+register 6, resolve: epoch 6.

### `goport-util-small`: 8,379 lines (5,014 code)

ts-rust `b11b618ae`, lust `23fffb0bd`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median (config) | Ratio |
|---|---:|---:|---:|---:|---:|---:|
| cold check | 43 ms | 43 | 43 | 5 | 98 ms (threads8) | 2.3x |
| cold build | 101 ms | 104 | 105 | 5 | 137 ms (threads8) | 1.4x |
| run (built program) | 1 ms | 1 | 1 | 17 | 0 ms (threads8) | 0.53x |
| cold build+run | 102 ms | 105 | 106 | 5 | 137 ms (threads8) | 1.3x |
| daemon first check (new session, empty cache) | 54 ms | 54 | 54 | 1 | 8 ms (threads8) | 0.15x |
| no-op check (warm daemon) | 1 ms | 1 | 1 | 5 | 8 ms (threads8) | 12.6x |
| cached restart check (new daemon, disk cache) | 51 ms | 52 | 52 | 5 | 8 ms (threads8) | 0.16x |
| body edit check (one fn) | 20 ms | 40 | 43 | 120 | 61 ms (default) | **3.1x** |
| body edit build (one fn) | 63 ms | 72 | 75 | 12 | 96 ms (default) | 1.5x |
| body edit build+run (one fn) | 64 ms | 73 | 75 | 12 | 97 ms (default) | 1.5x |
| signature edit check | 37 ms | 39 | 39 | 10 | 60 ms (default) | 1.6x |
| type edit check | 40 ms | 44 | 46 | 10 | 78 ms (threads8) | 1.9x |
| impl edit check | 41 ms | 45 | 45 | 10 | 72 ms (threads8) | 1.8x |
| error edit check (both reject) | 12 ms | 13 | 14 | 5 | 58 ms (default) | 4.8x |
| fix edit check | 20 ms | 22 | 22 | 5 | 55 ms (default) | 2.8x |

Cold build: 3.1 MB of C, 22 units, link 2 ms.
Peak RSS: lust cold check 71 MB, lust daemon 362 MB (VmHWM over the run), cargo cold check 147 MB (default), 212 MB (threads8) (largest process in the tree).

lust phases, body edit check (median ms): collect 15, resolve: expand+parse 11, check changed fns (par) 2, resolve: strip+register 2, resolve: epoch 2.

<!-- speed-table:end -->

## Larger slices

`tsrust-full` is all of ts_goport (670,906 lines with both part crates)
pruned to what lust takes today: 150k lines. A 200k-line slice needs lust to
take more of ts-rust; the top blocker is L0806 on doc comments passed to a
`$(#[$meta:meta])*` macro arm (core.rs `handle!` ids, 188k lines of
cascade). docs/real-coverage.md ranks the blockers per root cause.
