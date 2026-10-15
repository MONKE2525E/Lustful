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
  (`RUSTC_BOOTSTRAP=1`, `-Z threads=8`). Both use `debuginfo = 0`. One config
  is picked per row by its median. The table gives the ratio for the median
  and for p95, both from that config. The 100x goal is tracked at the median,
  at p95, and at the worst request.
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
  worst. Phase times come from `lust check --timings`. A phase median runs
  over all requests of the row. A phase a request did not emit counts as
  zero. A separate line gives the median over only the requests that did
  emit the phase, with its count. The result JSON (`requests`) saves one
  record per lust request: edit id, target fn, wall time, every phase, and
  the `lust-visits:` counters. It also saves the body-patch and kept-program
  (`kept=`) hit or miss and the miss reason. Peak RSS: the daemon's VmHWM;
  for cargo, the largest process in its tree.
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

## Where we are (2026-10-15, lust next 4c9f1cab1 + 3dd33ca21)

The promise row is **body edit check**. On the biggest slice, `tsrust-all`
(all of ts_goport that lust takes today, 160k lines), the median is
**621.8x** (lust 3.7 ms, rustc 2,319 ms) and the p95 is **162.5x** (23 ms vs
3,737 ms): the first p95 over 100x. The worst request is 171 ms. On the
other slices the median passes 100x from 54k lines up; the p95 does not.
The tail is the patch and kept-program misses in the table.

| Slice | lines | warm body edit check, lust / rustc | ratio median | ratio p95 | p95 lust | worst lust | patch hit/miss | kept hit/miss | no-op | cold check ratio | cold build+run ratio |
|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| tsrust-all | 160,107 | 3.7 / 2,319 ms | **621.8x** | **162.5x** | 23 ms | 171 ms | 120/0 | 115/5 | 1.4 ms | 2.1x | 2.0x |
| tsrust-full | 150,189 | 3.2 / 1,786 ms | **549.7x** | **22.0x** | 96 ms | 1,267 ms | 115/5 | 110/10 | 1.2 ms | 1.9x | 1.8x |
| tsrust-nochecker | 107,126 | 5.9 / 1,346 ms | **229.2x** | **2.1x** | 874 ms | 1,024 ms | 95/25 | 90/30 | 1.2 ms | 2.3x | 1.9x |
| goport-util-lsp | 53,960 | 3.6 / 692 ms | **190.7x** | **7.3x** | 204 ms | 587 ms | 105/15 | 100/20 | 1.0 ms | 4.6x | 3.1x |
| goport-util | 37,939 | 5.0 / 250 ms | **49.7x** | **2.2x** | 131 ms | 151 ms | 85/35 | 80/40 | 0.9 ms | 3.3x | 2.0x |
| goport-util-small | 8,379 | 2.2 / 78 ms | **34.8x** | **2.1x** | 58 ms | 83 ms | 95/25 | 95/25 | 0.8 ms | 2.4x | 1.4x |

Line counts include the 42-line driver. Six sandboxes ran at the same time,
one slice each, on the same tree (next 4c9f1cab1 plus W-BENCH3's
3dd33ca21, a check-only fix). Earlier runs moved absolute times by about
25% between sandboxes: compare ratios, not milliseconds. The prior run
(W-SPEEDMETER, 53ff7e4d3) had median ratios of 206.8x, 126.4x, 124.3x,
41.3x, and 24.4x on the five older slices, and p95 ratios of 25.0x, 2.2x,
4.3x, 2.5x, and 1.8x.

- On a patch hit with a kept program, a warm body edit costs 2 to 6 ms at
  the median. Body patch is 0.3 to 1.5 ms, collect 0.4 to 0.9 ms.
- The edit targets are one fn in each of the 24 largest files of the slice.
  `tsrust-all` has more large files, so its 24 targets differ from
  `tsrust-full`'s: they leave out `frontend/parser/lib_parse_snapshot.rs`
  `mode`, the target that misses the patch every time on `tsrust-full` and
  `tsrust-nochecker` (worst 1,267 ms). Its p95 of 162.5x is real for these
  targets, but the same miss is still in lust.
- A patch miss takes a full resolve and costs hundreds of ms. Reasons over
  all six slices: `not_in_a_fn_body` 55 (a cfg-disabled fn: `osvfs.rs`
  `os_path`, `#[cfg(test)]` fns, `slices.rs` `sort_func`), `body_tokens` 45
  (a fn that holds an item or a macro: `lib_parse_snapshot.rs` `mode`,
  `file_version.rs` `free_file_versions`, `diagnostics/mod.rs` `fmt`),
  `signature_nodes` 5 (`fanotify_linux.rs` `make_fanotify_handle_key`).
  Every patch miss also misses the kept program (`gen_state`).
- A kept-program miss after a patch hit (`fn_class`, 5 per slice from 38k
  up) is one target: `gostd/unicode_tables.rs` `map_get`. It costs a full
  collect: 171 ms, the worst request on `tsrust-all`.
- Signature, type, and impl edits are 1.4x to 3.8x: they cost close to a
  cold check.
- The daemon's peak RSS on tsrust-all is 3.2 GB; cargo's largest process is
  0.9 GB.
- Cold check is 1.9x to 4.6x. rustc with `-Z threads=8` is fast on these
  slices.

## Results

<!-- speed-table:start -->
### `tsrust-all`: 160,107 lines (98,983 code)

ts-rust `b11b618ae`, lust `3dd33ca21`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 1150 ms | 1828 | 1977 | 5 | 2449 ms | 3843 ms (threads8) | 2.1x | 2.1x |
| cold build | 1434 ms | 2943 | 3296 | 5 | 2841 ms | 6557 ms (threads8) | 2.0x | 2.2x |
| run (built program) | 2 ms | 3 | 4 | 17 | 1 ms | 2 ms (threads8) | 0.36x | 0.71x |
| cold build+run | 1435 ms | 2946 | 3299 | 5 | 2842 ms | 6559 ms (threads8) | 2.0x | 2.2x |
| daemon first check (new session, empty cache) | 1708 ms | 1708 | 1708 | 1 | 11 ms | 11 ms (threads8) | 0.01x | 0.01x |
| no-op check (warm daemon) | 1 ms | 2 | 2 | 5 | 12 ms | 12 ms (default) | 8.4x | 8.1x |
| cached restart check (new daemon, disk cache) | 1410 ms | 1923 | 2050 | 5 | 13 ms | 13 ms (threads8) | 0.01x | 0.01x |
| body edit check (one fn) | 4 ms | 23 | 171 | 120 | 2319 ms | 3737 ms (threads8) | **621.8x** | **162.5x** |
| body edit build (one fn) | 129 ms | 315 | 455 | 12 | 2430 ms | 3740 ms (default) | 18.8x | 11.9x |
| body edit build+run (one fn) | 131 ms | 317 | 457 | 12 | 2430 ms | 3740 ms (default) | 18.6x | 11.8x |
| signature edit check | 1535 ms | 3544 | 4741 | 10 | 2334 ms | 3028 ms (default) | 1.5x | 0.85x |
| type edit check | 1639 ms | 1981 | 2015 | 10 | 2358 ms | 3350 ms (threads8) | 1.4x | 1.7x |
| impl edit check | 1718 ms | 2381 | 2502 | 10 | 2434 ms | 3845 ms (threads8) | 1.4x | 1.6x |
| error edit check (both reject) | 144 ms | 179 | 186 | 5 | 1995 ms | 2369 ms (threads8) | 13.8x | 13.3x |
| fix edit check | 154 ms | 206 | 210 | 5 | 2297 ms | 3284 ms (threads8) | 14.9x | 15.9x |

Cold build: 16.8 MB of C, 38 units, link 10 ms.
Peak RSS: lust cold check 885 MB, lust daemon 3134 MB (VmHWM over the run), cargo cold check 842 MB (default), 1060 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 120 hit, 0 miss. kept program: 115 hit, 5 miss (fn_class x5).

lust phases, body edit check (median ms over all requests, absent = 0): body patch 1, collect 1, check changed fns (par) 0, route 0, read 0.

### `tsrust-full`: 150,189 lines (91,879 code)

ts-rust `b11b618ae`, lust `3dd33ca21`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 1000 ms | 1002 | 1002 | 5 | 1910 ms | 2079 ms (threads8) | 1.9x | 2.1x |
| cold build | 1200 ms | 1426 | 1470 | 5 | 2105 ms | 2263 ms (threads8) | 1.8x | 1.6x |
| run (built program) | 1 ms | 2 | 2 | 17 | 0 ms | 1 ms (threads8) | 0.4x | 0.41x |
| cold build+run | 1200 ms | 1427 | 1471 | 5 | 2105 ms | 2264 ms (threads8) | 1.8x | 1.6x |
| daemon first check (new session, empty cache) | 1152 ms | 1152 | 1152 | 1 | 10 ms | 10 ms (threads8) | 0.01x | 0.01x |
| no-op check (warm daemon) | 1 ms | 2 | 2 | 5 | 10 ms | 12 ms (threads8) | 8.4x | 7.1x |
| cached restart check (new daemon, disk cache) | 1099 ms | 1139 | 1149 | 5 | 11 ms | 11 ms (threads8) | 0.01x | 0.01x |
| body edit check (one fn) | 3 ms | 96 | 1267 | 120 | 1786 ms | 2122 ms (default) | **549.7x** | **22.0x** |
| body edit build (one fn) | 113 ms | 355 | 377 | 12 | 2004 ms | 2234 ms (threads8) | 17.7x | 6.3x |
| body edit build+run (one fn) | 115 ms | 357 | 379 | 12 | 2005 ms | 2234 ms (threads8) | 17.5x | 6.3x |
| signature edit check | 1198 ms | 1296 | 1349 | 10 | 1619 ms | 1652 ms (default) | 1.4x | 1.3x |
| type edit check | 1195 ms | 1229 | 1233 | 10 | 1726 ms | 1759 ms (threads8) | 1.4x | 1.4x |
| impl edit check | 1199 ms | 1218 | 1222 | 10 | 1647 ms | 1663 ms (threads8) | 1.4x | 1.4x |
| error edit check (both reject) | 88 ms | 91 | 91 | 5 | 1320 ms | 1328 ms (threads8) | 15.1x | 14.7x |
| fix edit check | 100 ms | 103 | 104 | 5 | 1524 ms | 1670 ms (default) | 15.3x | 16.1x |

Cold build: 15.1 MB of C, 38 units, link 9 ms.
Peak RSS: lust cold check 781 MB, lust daemon 2769 MB (VmHWM over the run), cargo cold check 750 MB (default), 961 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 115 hit, 5 miss (body_tokens x5). kept program: 110 hit, 10 miss (fn_class x5, gen_state x5).

lust phases, body edit check (median ms over all requests, absent = 0): body patch 1, collect 1, check changed fns (par) 0, route 0, read 0.

lust phases when present only (fallback requests, median ms): resolve: strip+register 551 (5/120 requests), resolve: expand+parse 172 (5/120 requests), resolve: other 68 (5/120 requests), resolve: epoch 53 (5/120 requests), resolve: discovery 31 (5/120 requests).

### `tsrust-nochecker`: 107,126 lines (67,850 code)

ts-rust `b11b618ae`, lust `3dd33ca21`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 495 ms | 498 | 498 | 5 | 1122 ms | 1139 ms (threads8) | 2.3x | 2.3x |
| cold build | 650 ms | 659 | 659 | 5 | 1236 ms | 1313 ms (threads8) | 1.9x | 2.0x |
| run (built program) | 1 ms | 2 | 3 | 17 | 1 ms | 1 ms (threads8) | 0.4x | 0.46x |
| cold build+run | 650 ms | 660 | 660 | 5 | 1237 ms | 1313 ms (threads8) | 1.9x | 2.0x |
| daemon first check (new session, empty cache) | 729 ms | 729 | 729 | 1 | 11 ms | 11 ms (threads8) | 0.01x | 0.01x |
| no-op check (warm daemon) | 1 ms | 1 | 1 | 5 | 10 ms | 10 ms (default) | 8.6x | 8.3x |
| cached restart check (new daemon, disk cache) | 646 ms | 759 | 786 | 5 | 10 ms | 12 ms (threads8) | 0.02x | 0.02x |
| body edit check (one fn) | 6 ms | 874 | 1024 | 120 | 1346 ms | 1847 ms (threads8) | **229.2x** | **2.1x** |
| body edit build (one fn) | 287 ms | 374 | 395 | 12 | 1480 ms | 1897 ms (default) | 5.2x | 5.1x |
| body edit build+run (one fn) | 288 ms | 376 | 397 | 12 | 1481 ms | 1898 ms (default) | 5.1x | 5.0x |
| signature edit check | 819 ms | 974 | 996 | 10 | 1429 ms | 1861 ms (threads8) | 1.7x | 1.9x |
| type edit check | 821 ms | 1365 | 1405 | 10 | 1499 ms | 2402 ms (threads8) | 1.8x | 1.8x |
| impl edit check | 764 ms | 994 | 1032 | 10 | 1350 ms | 1890 ms (threads8) | 1.8x | 1.9x |
| error edit check (both reject) | 87 ms | 133 | 139 | 5 | 1034 ms | 1699 ms (threads8) | 11.9x | 12.7x |
| fix edit check | 83 ms | 116 | 121 | 5 | 1148 ms | 1712 ms (default) | 13.8x | 14.7x |

Cold build: 12.4 MB of C, 38 units, link 7 ms.
Peak RSS: lust cold check 423 MB, lust daemon 1514 MB (VmHWM over the run), cargo cold check 538 MB (default), 684 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 95 hit, 25 miss (body_tokens x10, not_in_a_fn_body x15). kept program: 90 hit, 30 miss (fn_class x5, gen_state x25).

lust phases, body edit check (median ms over all requests, absent = 0): body patch 1, collect 1, check changed fns (par) 0, route 0, read 0.

lust phases when present only (fallback requests, median ms): resolve: strip+register 291 (25/120 requests), resolve: expand+parse 120 (25/120 requests), resolve: other 48 (25/120 requests), resolve: epoch 37 (25/120 requests), resolve: chunk scan+concat 20 (25/120 requests).

### `goport-util-lsp`: 53,960 lines (36,890 code)

ts-rust `b11b618ae`, lust `3dd33ca21`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 168 ms | 246 | 260 | 5 | 780 ms | 848 ms (threads8) | 4.6x | 3.5x |
| cold build | 298 ms | 323 | 325 | 5 | 932 ms | 1085 ms (threads8) | 3.1x | 3.4x |
| run (built program) | 1 ms | 2 | 4 | 17 | 1 ms | 2 ms (threads8) | 0.46x | 0.83x |
| cold build+run | 299 ms | 324 | 326 | 5 | 933 ms | 1086 ms (threads8) | 3.1x | 3.4x |
| daemon first check (new session, empty cache) | 333 ms | 333 | 333 | 1 | 11 ms | 11 ms (threads8) | 0.03x | 0.03x |
| no-op check (warm daemon) | 1 ms | 1 | 1 | 5 | 11 ms | 11 ms (threads8) | 10.4x | 10.1x |
| cached restart check (new daemon, disk cache) | 201 ms | 209 | 211 | 5 | 10 ms | 11 ms (threads8) | 0.05x | 0.05x |
| body edit check (one fn) | 4 ms | 204 | 587 | 120 | 692 ms | 1488 ms (default) | **190.7x** | **7.3x** |
| body edit build (one fn) | 191 ms | 397 | 468 | 12 | 756 ms | 1887 ms (threads8) | 4.0x | 4.8x |
| body edit build+run (one fn) | 193 ms | 398 | 469 | 12 | 757 ms | 1889 ms (threads8) | 3.9x | 4.7x |
| signature edit check | 265 ms | 404 | 430 | 10 | 1016 ms | 1439 ms (default) | 3.8x | 3.6x |
| type edit check | 338 ms | 471 | 479 | 10 | 1283 ms | 1708 ms (threads8) | 3.8x | 3.6x |
| impl edit check | 369 ms | 510 | 541 | 10 | 1114 ms | 1510 ms (threads8) | 3.0x | 3.0x |
| error edit check (both reject) | 95 ms | 98 | 98 | 5 | 796 ms | 1051 ms (default) | 8.3x | 10.7x |
| fix edit check | 97 ms | 112 | 115 | 5 | 1008 ms | 1262 ms (default) | 10.4x | 11.3x |

Cold build: 9.0 MB of C, 39 units, link 6 ms.
Peak RSS: lust cold check 174 MB, lust daemon 699 MB (VmHWM over the run), cargo cold check 387 MB (default), 516 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 105 hit, 15 miss (body_tokens x5, not_in_a_fn_body x10). kept program: 100 hit, 20 miss (fn_class x5, gen_state x15).

lust phases, body edit check (median ms over all requests, absent = 0): body patch 1, collect 1, check changed fns (par) 0, route 0, read 0.

lust phases when present only (fallback requests, median ms): resolve: expand+parse 39 (15/120 requests), resolve: strip+register 13 (15/120 requests), resolve: discovery 8 (15/120 requests), resolve: epoch 7 (15/120 requests), resolve: other 6 (15/120 requests).

### `goport-util`: 37,939 lines (28,695 code)

ts-rust `b11b618ae`, lust `3dd33ca21`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 115 ms | 126 | 129 | 5 | 380 ms | 447 ms (threads8) | 3.3x | 3.5x |
| cold build | 223 ms | 235 | 236 | 5 | 442 ms | 475 ms (threads8) | 2.0x | 2.0x |
| run (built program) | 1 ms | 1 | 2 | 17 | 1 ms | 1 ms (threads8) | 0.52x | 0.5x |
| cold build+run | 223 ms | 236 | 238 | 5 | 443 ms | 476 ms (threads8) | 2.0x | 2.0x |
| daemon first check (new session, empty cache) | 185 ms | 185 | 185 | 1 | 10 ms | 10 ms (threads8) | 0.06x | 0.06x |
| no-op check (warm daemon) | 1 ms | 1 | 1 | 5 | 9 ms | 10 ms (default) | 10.2x | 9.0x |
| cached restart check (new daemon, disk cache) | 141 ms | 157 | 159 | 5 | 10 ms | 12 ms (threads8) | 0.07x | 0.08x |
| body edit check (one fn) | 5 ms | 131 | 151 | 120 | 250 ms | 293 ms (default) | **49.7x** | **2.2x** |
| body edit build (one fn) | 134 ms | 156 | 161 | 12 | 326 ms | 378 ms (threads8) | 2.4x | 2.4x |
| body edit build+run (one fn) | 135 ms | 158 | 163 | 12 | 327 ms | 379 ms (threads8) | 2.4x | 2.4x |
| signature edit check | 127 ms | 150 | 157 | 10 | 260 ms | 297 ms (default) | 2.1x | 2.0x |
| type edit check | 135 ms | 201 | 237 | 10 | 311 ms | 345 ms (threads8) | 2.3x | 1.7x |
| impl edit check | 136 ms | 171 | 181 | 10 | 281 ms | 332 ms (threads8) | 2.1x | 1.9x |
| error edit check (both reject) | 34 ms | 36 | 36 | 5 | 223 ms | 229 ms (default) | 6.5x | 6.4x |
| fix edit check | 33 ms | 36 | 37 | 5 | 260 ms | 323 ms (default) | 7.9x | 8.9x |

Cold build: 7.6 MB of C, 39 units, link 5 ms.
Peak RSS: lust cold check 151 MB, lust daemon 616 MB (VmHWM over the run), cargo cold check 259 MB (default), 356 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 85 hit, 35 miss (body_tokens x10, not_in_a_fn_body x20, signature_nodes x5). kept program: 80 hit, 40 miss (fn_class x5, gen_state x35).

lust phases, body edit check (median ms over all requests, absent = 0): body patch 1, collect 0, check changed fns (par) 0, route 0, read 0.

lust phases when present only (fallback requests, median ms): resolve: expand+parse 28 (35/120 requests), resolve: strip+register 6 (35/120 requests), resolve: discovery 5 (35/120 requests), resolve: epoch 5 (35/120 requests), resolve: other 4 (35/120 requests).

### `goport-util-small`: 8,379 lines (5,014 code)

ts-rust `b11b618ae`, lust `3dd33ca21`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 50 ms | 52 | 52 | 5 | 118 ms | 138 ms (threads8) | 2.4x | 2.7x |
| cold build | 116 ms | 128 | 130 | 5 | 165 ms | 177 ms (threads8) | 1.4x | 1.4x |
| run (built program) | 1 ms | 1 | 2 | 17 | 1 ms | 1 ms (threads8) | 0.48x | 0.62x |
| cold build+run | 118 ms | 129 | 131 | 5 | 166 ms | 178 ms (threads8) | 1.4x | 1.4x |
| daemon first check (new session, empty cache) | 63 ms | 63 | 63 | 1 | 9 ms | 9 ms (threads8) | 0.14x | 0.14x |
| no-op check (warm daemon) | 1 ms | 1 | 1 | 5 | 8 ms | 9 ms (threads8) | 11.0x | 10.2x |
| cached restart check (new daemon, disk cache) | 56 ms | 58 | 59 | 5 | 9 ms | 10 ms (threads8) | 0.16x | 0.16x |
| body edit check (one fn) | 2 ms | 58 | 83 | 120 | 78 ms | 122 ms (default) | **34.8x** | **2.1x** |
| body edit build (one fn) | 82 ms | 113 | 126 | 12 | 128 ms | 149 ms (threads8) | 1.6x | 1.3x |
| body edit build+run (one fn) | 83 ms | 114 | 127 | 12 | 128 ms | 150 ms (threads8) | 1.5x | 1.3x |
| signature edit check | 62 ms | 91 | 101 | 10 | 102 ms | 124 ms (default) | 1.6x | 1.4x |
| type edit check | 72 ms | 133 | 155 | 10 | 121 ms | 150 ms (threads8) | 1.7x | 1.1x |
| impl edit check | 64 ms | 91 | 95 | 10 | 127 ms | 145 ms (threads8) | 2.0x | 1.6x |
| error edit check (both reject) | 5 ms | 6 | 6 | 5 | 92 ms | 157 ms (default) | 19.4x | 25.4x |
| fix edit check | 2 ms | 3 | 3 | 5 | 85 ms | 129 ms (default) | 44.1x | 40.5x |

Cold build: 3.2 MB of C, 23 units, link 2 ms.
Peak RSS: lust cold check 72 MB, lust daemon 366 MB (VmHWM over the run), cargo cold check 147 MB (default), 212 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 95 hit, 25 miss (body_tokens x15, not_in_a_fn_body x10). kept program: 95 hit, 25 miss (gen_state x25).

lust phases, body edit check (median ms over all requests, absent = 0): collect 0, body patch 0, check changed fns (par) 0, read 0, route 0.

lust phases when present only (fallback requests, median ms): resolve: expand+parse 14 (25/120 requests), resolve: strip+register 2 (25/120 requests), resolve: discovery 2 (25/120 requests), resolve: epoch 2 (25/120 requests), resolve: other 1 (25/120 requests).

<!-- speed-table:end -->

## Larger slices

`tsrust-all` is all of ts_goport (671,746 lines with both part crates and
the smallvec and xxhash_rust stand-ins) pruned to what lust takes today:
160k lines. A 200k-line slice needs lust to take more of ts-rust; the top
blocker is `Default` for `Box<[T]>` (derive(Default) over a `Box<[T]>`
field in core.rs `FileNodeBind` and `Table`, checker `FlatMap`: 131k lines
of cascade). docs/real-coverage.md ranks the blockers per root cause.
