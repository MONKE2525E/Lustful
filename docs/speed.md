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

## Where we are (2026-10-15, lust next 53ff7e4d3, with W-INCR3)

The promise row is **body edit check**. On the biggest slice, `tsrust-full`
(all of ts_goport that lust takes today, 150k lines), the median is
**206.8x**: lust 14 ms, rustc 2,978 ms. The p95 ratio is **25.0x** and the
worst request is 2,269 ms. The median passes 100x on the three big slices.
The tail does not. The tail is the patch and kept-program misses in the
table.

| Slice | lines | warm body edit check, lust / rustc | ratio median | ratio p95 | p95 lust | worst lust | patch hit/miss | kept hit/miss | no-op | cold check ratio | cold build+run ratio |
|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| tsrust-full | 150,189 | 14 / 2978 ms | **206.8x** | **25.0x** | 159 ms | 2269 ms | 115/5 | 110/10 | 5.4 ms | 2.5x | 2.3x |
| tsrust-nochecker | 107,126 | 9 / 1174 ms | **126.4x** | **2.2x** | 677 ms | 1035 ms | 95/25 | 90/30 | 1.7 ms | 2.5x | 2.1x |
| goport-util-lsp | 53,960 | 5 / 675 ms | **124.3x** | **4.3x** | 190 ms | 344 ms | 105/15 | 100/20 | 2.0 ms | 5.2x | 3.2x |
| goport-util | 37,939 | 8 / 317 ms | **41.3x** | **2.5x** | 156 ms | 334 ms | 85/35 | 80/40 | 1.4 ms | 3.2x | 2.2x |
| goport-util-small | 8,379 | 4 / 92 ms | **24.4x** | **1.8x** | 62 ms | 84 ms | 95/25 | 95/25 | 2.0 ms | 2.9x | 1.6x |

Line counts include the 42-line driver. Five sandboxes ran at the same time,
one slice each. Earlier runs moved absolute times by about 25% between
sandboxes: compare ratios, not milliseconds. The prior run (2026-10-14,
23fffb0b, before W-INCR3) had median ratios of 8.9x, 6.6x, 7.3x, 4.6x, and
3.1x on the same slices.

- On a patch hit with a kept program, a warm body edit costs 4 to 14 ms at
  the median. The largest phase is now the body patch itself (10 ms median
  on tsrust-full). Collect is 1 ms at the median. It was 188 ms before
  W-INCR3.
- A patch miss takes a full resolve and costs hundreds of ms. The miss
  reasons are in each slice section. `not_in_a_fn_body` and `body_tokens`
  lead. On tsrust-full one target of 24 misses every time
  (`frontend/parser/lib_parse_snapshot.rs`, `mode`): 5 misses, worst
  2,269 ms.
- A kept-program miss after a patch hit costs a full collect. The reasons
  are `fn_class` (a template that cannot recheck in place) and `gen_state`
  (generic reuse is off for this request). In these runs, every patch miss
  also missed the kept program with `gen_state` on the same request: 105 of
  125 kept misses. The other 20 are `fn_class` after a patch hit.
- Signature, type, and impl edits are 1.6x to 3.7x: they cost close to a
  cold check.
- The daemon's peak RSS on tsrust-full is 2.8 GB; cargo's largest process is
  1.0 GB.
- Cold check is 2.5x to 5.2x. rustc with `-Z threads=8` is fast on these
  slices.

## Results

<!-- speed-table:start -->
### `tsrust-full`: 150,189 lines (91,879 code)

ts-rust `b11b618ae`, lust `53ff7e4d3`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 1466 ms | 1616 | 1626 | 5 | 3706 ms | 3943 ms (threads8) | 2.5x | 2.4x |
| cold build | 1694 ms | 1997 | 2000 | 5 | 3915 ms | 4976 ms (threads8) | 2.3x | 2.5x |
| run (built program) | 2 ms | 3 | 3 | 17 | 1 ms | 1 ms (threads8) | 0.43x | 0.39x |
| cold build+run | 1696 ms | 1999 | 2002 | 5 | 3916 ms | 4977 ms (threads8) | 2.3x | 2.5x |
| daemon first check (new session, empty cache) | 1675 ms | 1675 | 1675 | 1 | 20 ms | 20 ms (threads8) | 0.01x | 0.01x |
| no-op check (warm daemon) | 5 ms | 8 | 9 | 5 | 20 ms | 27 ms (threads8) | 3.8x | 3.2x |
| cached restart check (new daemon, disk cache) | 1617 ms | 1690 | 1703 | 5 | 18 ms | 20 ms (threads8) | 0.01x | 0.01x |
| body edit check (one fn) | 14 ms | 159 | 2269 | 120 | 2978 ms | 3984 ms (default) | **206.8x** | **25.0x** |
| body edit build (one fn) | 172 ms | 452 | 454 | 12 | 3011 ms | 3931 ms (threads8) | 17.5x | 8.7x |
| body edit build+run (one fn) | 174 ms | 454 | 456 | 12 | 3012 ms | 3933 ms (threads8) | 17.3x | 8.7x |
| signature edit check | 2336 ms | 3369 | 3408 | 10 | 3872 ms | 5820 ms (default) | 1.7x | 1.7x |
| type edit check | 2833 ms | 3209 | 3220 | 10 | 4704 ms | 6349 ms (threads8) | 1.7x | 2.0x |
| impl edit check | 2791 ms | 3653 | 3706 | 10 | 4767 ms | 6749 ms (default) | 1.7x | 1.8x |
| error edit check (both reject) | 274 ms | 344 | 361 | 5 | 3340 ms | 5226 ms (threads8) | 12.2x | 15.2x |
| fix edit check | 291 ms | 383 | 406 | 5 | 4465 ms | 5278 ms (threads8) | 15.3x | 13.8x |

Cold build: 14.8 MB of C, 39 units, link 11 ms.
Peak RSS: lust cold check 771 MB, lust daemon 2764 MB (VmHWM over the run), cargo cold check 748 MB (default), 959 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 115 hit, 5 miss (body_tokens x5). kept program: 110 hit, 10 miss (fn_class x5, gen_state x5).

lust phases, body edit check (median ms over all requests, absent = 0): body patch 10, collect 1, check changed fns (par) 0, route 0, read 0.

lust phases when present only (fallback requests, median ms): resolve: strip+register 750 (5/120 requests), resolve: expand+parse 330 (5/120 requests), resolve: other 149 (5/120 requests), resolve: epoch 100 (5/120 requests), resolve: chunk scan+concat 75 (5/120 requests).

### `tsrust-nochecker`: 107,126 lines (67,850 code)

ts-rust `b11b618ae`, lust `53ff7e4d3`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 564 ms | 566 | 566 | 5 | 1400 ms | 1450 ms (threads8) | 2.5x | 2.6x |
| cold build | 726 ms | 776 | 787 | 5 | 1521 ms | 1670 ms (threads8) | 2.1x | 2.2x |
| run (built program) | 1 ms | 2 | 2 | 17 | 1 ms | 1 ms (threads8) | 0.41x | 0.45x |
| cold build+run | 727 ms | 777 | 788 | 5 | 1521 ms | 1670 ms (threads8) | 2.1x | 2.1x |
| daemon first check (new session, empty cache) | 648 ms | 648 | 648 | 1 | 10 ms | 10 ms (threads8) | 0.02x | 0.02x |
| no-op check (warm daemon) | 2 ms | 2 | 2 | 5 | 11 ms | 11 ms (default) | 6.3x | 5.9x |
| cached restart check (new daemon, disk cache) | 607 ms | 649 | 655 | 5 | 11 ms | 13 ms (threads8) | 0.02x | 0.02x |
| body edit check (one fn) | 9 ms | 677 | 1035 | 120 | 1174 ms | 1472 ms (default) | **126.4x** | **2.2x** |
| body edit build (one fn) | 252 ms | 301 | 311 | 12 | 1241 ms | 1572 ms (threads8) | 4.9x | 5.2x |
| body edit build+run (one fn) | 253 ms | 302 | 312 | 12 | 1242 ms | 1572 ms (threads8) | 4.9x | 5.2x |
| signature edit check | 694 ms | 1204 | 1322 | 10 | 1456 ms | 2446 ms (default) | 2.1x | 2.0x |
| type edit check | 756 ms | 1028 | 1122 | 10 | 1401 ms | 2096 ms (threads8) | 1.9x | 2.0x |
| impl edit check | 718 ms | 1102 | 1249 | 10 | 1381 ms | 2281 ms (threads8) | 1.9x | 2.1x |
| error edit check (both reject) | 81 ms | 127 | 137 | 5 | 1031 ms | 1702 ms (threads8) | 12.7x | 13.4x |
| fix edit check | 82 ms | 144 | 158 | 5 | 1193 ms | 2100 ms (default) | 14.6x | 14.6x |

Cold build: 11.9 MB of C, 39 units, link 7 ms.
Peak RSS: lust cold check 422 MB, lust daemon 1499 MB (VmHWM over the run), cargo cold check 540 MB (default), 691 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 95 hit, 25 miss (body_tokens x10, not_in_a_fn_body x15). kept program: 90 hit, 30 miss (fn_class x5, gen_state x25).

lust phases, body edit check (median ms over all requests, absent = 0): body patch 5, collect 1, check changed fns (par) 0, route 0, read 0.

lust phases when present only (fallback requests, median ms): resolve: strip+register 247 (25/120 requests), resolve: expand+parse 96 (25/120 requests), resolve: other 38 (25/120 requests), resolve: epoch 29 (25/120 requests), resolve: discovery 16 (25/120 requests).

### `goport-util-lsp`: 53,960 lines (36,890 code)

ts-rust `b11b618ae`, lust `53ff7e4d3`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 183 ms | 340 | 373 | 5 | 946 ms | 1067 ms (threads8) | 5.2x | 3.1x |
| cold build | 321 ms | 329 | 329 | 5 | 1033 ms | 1116 ms (threads8) | 3.2x | 3.4x |
| run (built program) | 1 ms | 2 | 2 | 17 | 1 ms | 1 ms (threads8) | 0.49x | 0.63x |
| cold build+run | 322 ms | 330 | 330 | 5 | 1033 ms | 1117 ms (threads8) | 3.2x | 3.4x |
| daemon first check (new session, empty cache) | 263 ms | 263 | 263 | 1 | 13 ms | 13 ms (default) | 0.05x | 0.05x |
| no-op check (warm daemon) | 2 ms | 2 | 2 | 5 | 13 ms | 14 ms (threads8) | 6.6x | 6.2x |
| cached restart check (new daemon, disk cache) | 212 ms | 241 | 247 | 5 | 12 ms | 13 ms (threads8) | 0.06x | 0.05x |
| body edit check (one fn) | 5 ms | 190 | 344 | 120 | 675 ms | 819 ms (default) | **124.3x** | **4.3x** |
| body edit build (one fn) | 166 ms | 232 | 247 | 12 | 788 ms | 964 ms (threads8) | 4.7x | 4.2x |
| body edit build+run (one fn) | 168 ms | 233 | 248 | 12 | 789 ms | 965 ms (threads8) | 4.7x | 4.1x |
| signature edit check | 175 ms | 197 | 203 | 10 | 640 ms | 695 ms (default) | 3.7x | 3.5x |
| type edit check | 195 ms | 208 | 211 | 10 | 718 ms | 755 ms (threads8) | 3.7x | 3.6x |
| impl edit check | 191 ms | 207 | 208 | 10 | 700 ms | 739 ms (default) | 3.7x | 3.6x |
| error edit check (both reject) | 51 ms | 55 | 56 | 5 | 500 ms | 509 ms (threads8) | 9.7x | 9.3x |
| fix edit check | 50 ms | 56 | 57 | 5 | 599 ms | 655 ms (default) | 11.9x | 11.6x |

Cold build: 8.6 MB of C, 40 units, link 7 ms.
Peak RSS: lust cold check 166 MB, lust daemon 664 MB (VmHWM over the run), cargo cold check 386 MB (default), 519 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 105 hit, 15 miss (body_tokens x5, not_in_a_fn_body x10). kept program: 100 hit, 20 miss (fn_class x5, gen_state x15).

lust phases, body edit check (median ms over all requests, absent = 0): body patch 3, collect 1, check changed fns (par) 0, route 0, read 0.

lust phases when present only (fallback requests, median ms): resolve: expand+parse 37 (15/120 requests), resolve: strip+register 14 (15/120 requests), resolve: discovery 7 (15/120 requests), resolve: epoch 6 (15/120 requests), resolve: other 6 (15/120 requests).

### `goport-util`: 37,939 lines (28,695 code)

ts-rust `b11b618ae`, lust `53ff7e4d3`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 141 ms | 149 | 151 | 5 | 457 ms | 534 ms (threads8) | 3.2x | 3.6x |
| cold build | 254 ms | 266 | 266 | 5 | 560 ms | 584 ms (threads8) | 2.2x | 2.2x |
| run (built program) | 1 ms | 2 | 2 | 17 | 1 ms | 1 ms (threads8) | 0.6x | 0.42x |
| cold build+run | 255 ms | 267 | 267 | 5 | 561 ms | 585 ms (threads8) | 2.2x | 2.2x |
| daemon first check (new session, empty cache) | 326 ms | 326 | 326 | 1 | 12 ms | 12 ms (default) | 0.04x | 0.04x |
| no-op check (warm daemon) | 1 ms | 2 | 2 | 5 | 11 ms | 13 ms (default) | 7.8x | 8.1x |
| cached restart check (new daemon, disk cache) | 145 ms | 157 | 160 | 5 | 10 ms | 10 ms (threads8) | 0.07x | 0.07x |
| body edit check (one fn) | 8 ms | 156 | 334 | 120 | 317 ms | 386 ms (default) | **41.3x** | **2.5x** |
| body edit build (one fn) | 145 ms | 195 | 196 | 12 | 386 ms | 590 ms (default) | 2.7x | 3.0x |
| body edit build+run (one fn) | 146 ms | 197 | 197 | 12 | 387 ms | 591 ms (default) | 2.6x | 3.0x |
| signature edit check | 159 ms | 216 | 246 | 10 | 362 ms | 454 ms (default) | 2.3x | 2.1x |
| type edit check | 173 ms | 217 | 224 | 10 | 403 ms | 456 ms (threads8) | 2.3x | 2.1x |
| impl edit check | 183 ms | 247 | 253 | 10 | 390 ms | 443 ms (threads8) | 2.1x | 1.8x |
| error edit check (both reject) | 48 ms | 64 | 66 | 5 | 297 ms | 366 ms (threads8) | 6.2x | 5.7x |
| fix edit check | 41 ms | 46 | 47 | 5 | 377 ms | 472 ms (threads8) | 9.2x | 10.3x |

Cold build: 7.2 MB of C, 38 units, link 5 ms.
Peak RSS: lust cold check 145 MB, lust daemon 563 MB (VmHWM over the run), cargo cold check 260 MB (default), 356 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 85 hit, 35 miss (body_tokens x10, not_in_a_fn_body x20, signature_nodes x5). kept program: 80 hit, 40 miss (fn_class x5, gen_state x35).

lust phases, body edit check (median ms over all requests, absent = 0): body patch 3, collect 1, check changed fns (par) 0, route 0, read 0.

lust phases when present only (fallback requests, median ms): resolve: expand+parse 33 (35/120 requests), resolve: strip+register 7 (35/120 requests), resolve: discovery 7 (35/120 requests), resolve: epoch 6 (35/120 requests), resolve: other 5 (35/120 requests).

### `goport-util-small`: 8,379 lines (5,014 code)

ts-rust `b11b618ae`, lust `53ff7e4d3`, rustc 1.99.0 (b940084d7 2026-09-28), 16 vCPU. 171 source states; lust and cargo agree on pass or fail on every one.

| Row | lust median | p95 | worst | n | rustc median | rustc p95 (config) | Ratio median | Ratio p95 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| cold check | 75 ms | 86 | 86 | 5 | 219 ms | 304 ms (threads8) | 2.9x | 3.5x |
| cold build | 163 ms | 193 | 199 | 5 | 266 ms | 336 ms (threads8) | 1.6x | 1.7x |
| run (built program) | 1 ms | 2 | 2 | 17 | 1 ms | 1 ms (default) | 0.63x | 0.71x |
| cold build+run | 165 ms | 195 | 201 | 5 | 267 ms | 337 ms (threads8) | 1.6x | 1.7x |
| daemon first check (new session, empty cache) | 146 ms | 146 | 146 | 1 | 13 ms | 13 ms (threads8) | 0.09x | 0.09x |
| no-op check (warm daemon) | 2 ms | 2 | 2 | 5 | 14 ms | 17 ms (default) | 7.2x | 7.7x |
| cached restart check (new daemon, disk cache) | 100 ms | 110 | 112 | 5 | 13 ms | 18 ms (default) | 0.13x | 0.16x |
| body edit check (one fn) | 4 ms | 62 | 84 | 120 | 92 ms | 112 ms (default) | **24.4x** | **1.8x** |
| body edit build (one fn) | 85 ms | 104 | 104 | 12 | 140 ms | 166 ms (default) | 1.7x | 1.6x |
| body edit build+run (one fn) | 86 ms | 105 | 105 | 12 | 141 ms | 167 ms (default) | 1.6x | 1.6x |
| signature edit check | 55 ms | 63 | 67 | 10 | 86 ms | 93 ms (default) | 1.6x | 1.5x |
| type edit check | 65 ms | 72 | 75 | 10 | 108 ms | 124 ms (threads8) | 1.7x | 1.7x |
| impl edit check | 62 ms | 69 | 70 | 10 | 102 ms | 109 ms (threads8) | 1.6x | 1.6x |
| error edit check (both reject) | 4 ms | 4 | 4 | 5 | 81 ms | 85 ms (default) | 21.1x | 19.5x |
| fix edit check | 3 ms | 4 | 4 | 5 | 78 ms | 81 ms (default) | 25.5x | 23.2x |

Cold build: 3.1 MB of C, 22 units, link 3 ms.
Peak RSS: lust cold check 68 MB, lust daemon 401 MB (VmHWM over the run), cargo cold check 147 MB (default), 212 MB (threads8) (largest process in the tree).

Body edit check paths: body patch: 95 hit, 25 miss (body_tokens x15, not_in_a_fn_body x10). kept program: 95 hit, 25 miss (gen_state x25).

lust phases, body edit check (median ms over all requests, absent = 0): body patch 1, collect 0, check changed fns (par) 0, route 0, read 0.

lust phases when present only (fallback requests, median ms): resolve: expand+parse 18 (25/120 requests), resolve: strip+register 3 (25/120 requests), resolve: discovery 2 (25/120 requests), resolve: epoch 2 (25/120 requests), body patch 2 (95/120 requests).

<!-- speed-table:end -->

## Larger slices

`tsrust-full` is all of ts_goport (670,906 lines with both part crates)
pruned to what lust takes today: 150k lines. A 200k-line slice needs lust to
take more of ts-rust; the top blocker is L0806 on doc comments passed to a
`$(#[$meta:meta])*` macro arm (core.rs `handle!` ids, 188k lines of
cascade). docs/real-coverage.md ranks the blockers per root cause.
