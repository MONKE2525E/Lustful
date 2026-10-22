#!/usr/bin/env bash
# Query-only resolution: no build scripts or proc macros may execute.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
lust="$root/target/release/lust"
core="$root/target/release/lust-core"
export CARGO_TARGET_DIR="$work/target" LUST_NO_DAEMON=1 LUST_HOST_TOOLS=0
mkdir -p "$work/ws/app/src" "$work/ws/leaf/src" "$work/deny"
cat > "$work/deny/rustc" <<'SH'
#!/bin/sh
echo 'unexpected rustc invocation' >&2
exit 97
SH
chmod +x "$work/deny/rustc"
cat > "$work/ws/Cargo.toml" <<'TOML'
[workspace]
members = ["app", "leaf"]
resolver = "2"
TOML
cat > "$work/ws/app/Cargo.toml" <<'TOML'
[package]
name = "app"
version = "0.1.0"
edition = "2024"
[dependencies]
renamed = { package = "leaf", path = "../leaf", optional = true, features = ["selected"] }
[features]
default = ["dep:renamed"]
TOML
echo 'fn main() {}' > "$work/ws/app/src/main.rs"
cat > "$work/ws/app/build.rs" <<'RS'
fn main() { std::fs::write("BUILD_SCRIPT_RAN", "bad").unwrap(); }
RS
cat > "$work/ws/leaf/Cargo.toml" <<'TOML'
[package]
name = "leaf"
version = "0.1.0"
edition = "2024"
[features]
selected = []
[lib]
proc-macro = true
TOML
echo 'extern crate proc_macro;' > "$work/ws/leaf/src/lib.rs"
strict() {
  local label=$1 expected=$2 rc=0
  shift 2
  PATH="$work/deny:$PATH" RUSTC="$work/deny/rustc" RUSTC_WRAPPER="$work/deny/rustc" \
    RUSTC_WORKSPACE_WRAPPER="$work/deny/rustc" \
    strace --kill-on-exit -f -qq -s 4096 -e trace=execve,execveat -o "$work/$label.trace" \
    "$@" > "$work/$label.out" 2> "$work/$label.err" || rc=$?
  [[ "$rc" == "$expected" ]] || { cat "$work/$label.err"; echo "FAIL $label: exit $rc"; exit 1; }
  if grep -Eq 'execve(at)?\(([^,]*, )?"([^"]*/)?rustc(-real)?",|execve(at)?\([^[]*\["([^"]*/)?rustc(-real)?"' "$work/$label.trace"; then
    cat "$work/$label.trace"; echo "FAIL $label: compiler invocation"; exit 1
  fi
  [[ ! -e "$work/ws/app/BUILD_SCRIPT_RAN" ]]
  echo "PASS Cargo query $label"
}
cd "$work/ws"
strict graph 0 "$lust" metadata --offline --manifest-path Cargo.toml --filter-platform x86_64-unknown-linux-gnu
strict warm 0 "$lust" metadata --offline --locked --manifest-path Cargo.toml --format-version 1 --filter-platform x86_64-unknown-linux-gnu
grep -q -- '"-vV"' "$work/warm.trace"
grep -q -- '"--print=cfg"' "$work/warm.trace"
[[ ! -e "$CARGO_TARGET_DIR/.rustc_info.json" && ! -e "$CARGO_TARGET_DIR/.rustc-info.json" ]]
strict no-default 0 "$lust" metadata --offline --locked --manifest-path Cargo.toml --no-default-features --filter-platform x86_64-unknown-linux-gnu
strict identity 0 env LUST_CARGO_QUERY=1 "$core" -vV
grep -q '^lust ' "$work/identity.out"
! grep -q rustc "$work/identity.out"
strict refuse-compilation 2 env LUST_CARGO_QUERY=1 LUST_HOST_TOOLS=1 "$core" app/src/main.rs --emit=metadata
strict refuse-flags 101 env RUSTFLAGS=-Copt-level=3 "$lust" metadata --offline --manifest-path Cargo.toml
grep -q 'Lust Cargo query refused' "$work/refuse-flags.err"
strict refuse-arguments 2 "$lust" metadata --config build.rustc=rustc --manifest-path Cargo.toml
strict still-refuse-build 2 "$lust" check app/src/main.rs --manifest-path Cargo.toml -p app --bin app
grep -q L0532 "$work/still-refuse-build.err"
# Independent metadata oracle: rustc is permitted only outside strict traces.
CARGO_TARGET_DIR="$work/oracle" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= cargo metadata \
  --offline --locked --format-version 1 --manifest-path Cargo.toml \
  --filter-platform x86_64-unknown-linux-gnu > "$work/oracle.json"
node --input-type=module - "$work" <<'JS'
import fs from 'node:fs';
import assert from 'node:assert/strict';
const work = process.argv[2];
const read = name => JSON.parse(fs.readFileSync(`${work}/${name}`, 'utf8'));
const expected = read('oracle.json');
expected.target_directory = read('graph.out').target_directory;
expected.build_directory = read('graph.out').build_directory;
assert.deepEqual(read('graph.out'), expected);
assert.deepEqual(read('warm.out'), expected);
const leaf = read('graph.out').packages.find(p => p.name === 'leaf').id;
assert.deepEqual(read('graph.out').resolve.nodes.find(n => n.id === leaf).features, ['selected']);
assert.equal(read('no-default.out').resolve.nodes.some(n => n.id === leaf), true);
// Workspace members remain roots, but optional dependency feature activation changes.
assert.deepEqual(read('no-default.out').resolve.nodes.find(n => n.id === leaf).features, []);
JS
echo 'PASS Cargo query graph matches independent metadata oracle'
