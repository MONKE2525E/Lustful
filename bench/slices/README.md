# bench/slices: pinned ts-rust slices for the speed benchmark

The 100x promise is measured here: warm `lust check` after a one-function edit,
against `cargo check` (rustc 1.99, incremental) on the same source.

A slice is real ts-rust source (commit in `prune.json`), copied verbatim, minus
whole items that lust cannot take yet. Both lust and rustc accept every slice,
and `lust build` builds it.

| Slice | Lines (code) | From |
|---|---|---|
| `goport-util` | 35,038 (26,468) | ts-rust `goport_util` (87,779 lines on this target) |
| `goport-util-small` | 7,253 (4,223) | the same crate without gostd, locale, fswatch, astdata |

## How a slice is made

`prune.py <spec.json> <out-dir>` copies the crate's module tree from ts-rust
(read only), then repeats: `lust check`, remove the innermost item that holds
each error; `rustc`, the same; `lust build`, the same. It stops when all three
accept. A removed item makes its users fail to resolve, so they go too: the
slice is closed over its own dependencies. When lust gives an error with no
usable location (a std span under the root file, line 1, a panic), the fn is
found by stubbing fn bodies in halves (bisect). `prune.json` lists every
removed item with the oracle and error code that removed it. That list is a
ranked to-do list for lust coverage.

`items/` is a small syn tool that lists items, fn bodies, and the module tree.

Bench-owned text, not ts-rust code:

- the root file (`slice_main.rs`): ts-rust's `goport_util_root.rs` with a
  `fn main() {}`, the stand-in mods, and the `root_replace` edits of the spec;
- `support.rs`: stand-ins for `rustc_hash`, `indexmap`, `memchr` (from
  tests/kernels, with two lust-friendly changes; see its header). Paths to
  those crates are rewritten to `crate::<name>::` (spec `rewrite`).

`core` (`gopanic.rs`) is not mounted: a user module named `core` makes lust's
std fail to resolve its own `core::` paths (lust bug, see REPORT). When that
is fixed, drop that `root_replace` entry and rerun prune.py.

## Grow a slice

```sh
cargo build --release
python3 bench/slices/prune.py bench/slices/goport-util/spec.json /tmp/gu
rm -rf bench/slices/goport-util/src && cp -r /tmp/gu/src /tmp/gu/prune.json bench/slices/goport-util/
```

Then check that the anchors in `edits.json` still occur once (the benchmark
fails with a clear message if not), and rerun the benchmark.

## Measure

```sh
python3 scripts/scale-gate.py --slice bench/slices/goport-util --json out.json
scripts/speed-row.sh            # the quick gate row (small slice)
```

Run timing on a quiet host (boat), never on a loaded shared box. Results and
the method are in docs/speed.md.
