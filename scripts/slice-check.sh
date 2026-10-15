#!/usr/bin/env bash
# slice-check.sh [slice-dir]: the pinned-slice regression test (fx-stdos).
# Copies the smallest pinned ts-rust slice (default:
# bench/slices/goport-util-small) to a fresh work dir and runs, cold
# (no daemon, fresh cache):
#   1. `lust check` on the slice root,
#   2. a rustc build of the slice with the bench driver mounted, run,
#   3. a lust build of the same copy, run; stdout must match rustc's.
# A slice that stops checking (the std::os regression of d45b3d8d7,
# L0506 on every slice while the speed row only printed "no result")
# fails here, in seconds. The last line is the gate summary.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
slice=${1:-$root/bench/slices/goport-util-small}
passed=0
failed=0

summary() { echo "slice-check: $passed passed, $failed failed"; }
if [ ! -x "$lust" ]; then
  echo "error: $lust not built. Run scripts/build.sh first."
  failed=1
  summary
  exit 1
fi

work=$(mktemp -d "${TMPDIR:-/tmp}/lust-slice-check-XXXXXX")
trap 'rm -rf "$work"' EXIT
cp -r "$slice/src" "$work/src"
root_name=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["spec"]["root"])' "$slice/prune.json" 2>/dev/null || echo slice_main.rs)
entry=$work/src/$root_name
# Mount the bench driver as speed_slice.py does: it gives the build
# a program whose output the rustc oracle can compare.
if ! python3 - "$entry" <<'PY'
import pathlib, sys
p = pathlib.Path(sys.argv[1])
text = p.read_text()
if text.count("fn main() {}") != 1:
    sys.exit(1)
p.write_text(text.replace("fn main() {}", "mod bench_driver;\n\nfn main() {\n    bench_driver::run();\n}"))
PY
then
  echo "error: $entry: expected one \`fn main() {}\` to replace with the driver call"
  failed=3
  summary
  exit 1
fi
cp "$root/bench/slices/driver.rs" "$work/src/bench_driver.rs"

run_step() {
  # run_step <name> <command...>: counts one test, prints its time.
  local name=$1
  shift
  local start end
  start=$(date +%s%N)
  if "$@" >"$work/$name.log" 2>&1; then
    end=$(date +%s%N)
    echo "$name: ok ($(( (end - start) / 1000000 )) ms)"
    passed=$((passed + 1))
    return 0
  fi
  end=$(date +%s%N)
  echo "$name: FAILED ($(( (end - start) / 1000000 )) ms); first lines of the log:"
  head -5 "$work/$name.log"
  failed=$((failed + 1))
  return 1
}

export LUST_NO_DAEMON=1
export LUST_CACHE_DIR="$work/cold-cache"
run_step cold-lust-check "$lust" check "$entry" || true

rustc_out=$work/rustc.out
lust_out=$work/lust.out
if run_step rustc-oracle bash -c 'rustc --edition 2024 -C panic=abort -C overflow-checks=on -A warnings -o "$1" "$2" && "$1" > "$3"' _ "$work/prog-rustc" "$entry" "$rustc_out"; then
  if run_step lust-build-run bash -c '"$1" build "$2" -o "$3" && "$3" > "$4"' _ "$lust" "$entry" "$work/prog-lust" "$lust_out"; then
    if ! cmp -s "$rustc_out" "$lust_out"; then
      # Replace the build-run pass with an output mismatch failure.
      passed=$((passed - 1))
      failed=$((failed + 1))
      echo "lust-build-run: FAILED (stdout differs from rustc); diff:"
      diff "$rustc_out" "$lust_out" | head -10
    fi
  fi
else
  echo "lust-build-run: skipped (the rustc oracle failed)"
  failed=$((failed + 1))
fi

summary
[ "$failed" -eq 0 ]
