#!/usr/bin/env bash
# Writer-only differential: parsed JSON is tested separately by the adapter suite.
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/lust-json-float.XXXXXX")
echo "JSON float writer artifacts: $work"
mkdir -p "$work/oracle/src"
cp "$root/tests/float/json_oracle.rs" "$work/oracle/src/main.rs"
cat > "$work/oracle/Cargo.toml" <<'MANIFEST'
[package]
name = "json-float-oracle"
version = "0.0.0"
edition = "2024"
[workspace]
[dependencies]
zmij = "=1.0.23"
MANIFEST
# Independent oracle preparation explicitly uses rustc, outside target execution.
CARGO_NET_OFFLINE=true timeout 600 cargo build --quiet --release --manifest-path "$work/oracle/Cargo.toml" --target-dir "$work/oracle-target" > "$work/oracle-build.out" 2> "$work/oracle-build.err"
node "$root/tests/float/json_gen.mjs" "$work/bits.txt" > "$work/vectors.json"
timeout 120 "$work/oracle-target/release/json-float-oracle" < "$work/bits.txt" > "$work/oracle.out"
timeout 120 "$root/third_party/tcc/bin/tcc" "$root/tests/float/json_harness.c" -lm -o "$work/tcc" > "$work/tcc-build.out" 2> "$work/tcc-build.err"
timeout 120 "$work/tcc" < "$work/bits.txt" > "$work/tcc.out"
cmp "$work/oracle.out" "$work/tcc.out"
if [ "${SANITIZE:-0}" = 1 ]; then
    timeout 120 gcc -O1 -g -fsanitize=address,undefined -fno-sanitize-recover=undefined -w "$root/tests/float/json_harness.c" -lm -o "$work/sanitized" > "$work/sanitize-build.out" 2> "$work/sanitize-build.err"
    ASAN_OPTIONS=detect_leaks=1 timeout 120 "$work/sanitized" < "$work/bits.txt" > "$work/sanitized.out" 2> "$work/sanitized.err"
    if rg -q 'runtime error|Sanitizer' "$work/sanitized.err"; then
        cat "$work/sanitized.err" >&2
        exit 1
    fi
    cmp "$work/oracle.out" "$work/sanitized.out"
fi
echo "JSON finite-float writer matched pinned zmij for every generated bit pattern."
