# lust-port

`lust-port scan` is the gap scanner from PLAN.md milestone 3. It reads a
Rust crate with a full parser and reports every feature lust does not
support yet, grouped by root cause. Run it as `lust port scan` (the
`lust` client execs this binary) or directly.

This crate is standalone. It is not part of the root crate, and the root
crate gains no dependencies from it.

## Use

```sh
cargo build --release --manifest-path tools/lust-port/Cargo.toml
tools/lust-port/target/release/lust-port scan --manifest-path /path/to/Cargo.toml [-p pkg] [--target x86_64-unknown-linux-gnu]
tools/lust-port/target/release/lust-port scan --manifest-path /path/to/Cargo.toml -p pkg --json > report.json
tools/lust-port/target/release/lust-port scan --manifest-path /path/to/Cargo.toml -p pkg --markdown > report.md
```

- With `-p`, only that package is scanned. With a package manifest and
  no `-p`, that package is scanned. With a virtual workspace manifest
  and no `-p`, every workspace member is scanned.
- `--json` writes the full machine report. Add `--summary` to keep at
  most 5 findings per feature (counts and samples stay). The full
  ts-rust report is well over 2 MB, so `docs/ts-rust-gaps.json` is a
  summary.
- The scan is read-only. It runs `cargo metadata --no-deps`, with
  `--locked` when a `Cargo.lock` exists, and only reads `.rs` files.
- A completed scan exits 0 even when gaps are found. Gaps are output.

## What it reports

- One finding per primary-key hit: feature id, file, byte range, line,
  snippet, scope (active, test-only, or target-specific), fix class
  (compiler work, adapter, mechanical rewrite, manual), and whether a
  release-safe rewrite exists.
- Human output groups findings by root cause, then by feature, with at
  most 2 samples per feature.
- Coverage: the missing features per file, and how many prod files and
  lines would compile after each PLAN milestone and after each
  INVENTORY.md step.
- Dependencies: each direct dependency of the scanned packages with
  the dev-path decision from `dependencies.json` (built-in adapter,
  C shim, or compile from source). Release always uses Cargo.
- Parse errors, missing modules, and cfg predicates that cannot be
  decided from the target triple (for example `feature = "..."`).

## Tables the orchestrator updates

- `features.json` maps raw scanner keys to a feature id, lust status,
  PLAN milestone, inventory step, root cause, and fix class. First
  match wins. `primary_keys` create findings; `keys` block a file in
  the coverage curve. When lust learns a feature, set its status to
  `supported` and milestone to 0.
- A later `lust capabilities --json` can feed the same ids:
  `lust-port scan --capabilities caps.json` accepts
  `{"features": [{"id": "...", "status": "...", "milestone": 0}]}` and
  overrides the table by id.
- `--features <file>` and `--dependencies <file>` replace the tables.

## Limits

The scanner has no type information. Method names are not tied to
receivers, paths resolve through `use` items and crate preludes,
`macro_rules!` bodies are not expanded, and user macro arguments count
only when they parse as expressions. A construct with no rule in
`features.json` is treated as supported, so a new std or crate path
needs a rule. The code starts from the ts-rust inventory analyzer
(`/tmp/lust-ts/inventory/analyzer`), so its raw keys and counts match
that study by construction; see `docs/ts-rust-gaps.md` for the
comparison.
