#!/usr/bin/env bash
# Owned ts-rust kernels (milestone 4 gate) and K1 compat fixtures.
#
#   scripts/test-kernels.sh [filter]
#       rustc mode (default): build every kernel in tests/kernels/
#       with Cargo, run its driver over tests/kernels/<k>/inputs/,
#       and diff stdout against tests/kernels/<k>/expected/. Amalgam
#       variants must give the same bytes and must be fresh (the
#       inliner output matches the committed file). Each fixture in
#       tests/compat/ builds with the panic mode in its header line
#       (`// panic-mode:`) and diffs against its .expected file.
#       Any diff fails the script.
#
#   LUST=path/to/lust scripts/test-kernels.sh [filter]
#       Report mode: try to build each kernel entry and compat
#       fixture with lust. A build failure prints "unsupported: ..."
#       with the first diagnostic and does not fail the script: the
#       kernels need milestone 4 and later work (see
#       tests/kernels/README.md feature lists). A build that
#       succeeds runs and diffs like rustc mode; a wrong-output or
#       crashing build DOES fail, because lust accepted the program.
#
# [filter] keeps only entries whose name contains the text.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
filter=${1:-}
pass=0
fail=0
unsupported=0

export CARGO_NET_OFFLINE=true
# Cold lust runs only, like difftest.sh.
export LUST_NO_DAEMON=1
export LUST_DAEMON_SOCKET="$work/no-daemon.sock"
export LUST_CACHE_DIR="$work/cache"

ok() { pass=$((pass + 1)); echo "ok $1"; }
bad() { fail=$((fail + 1)); echo "FAIL $1: $2"; }
unsup() { unsupported=$((unsupported + 1)); echo "unsupported $1: $2"; }
keep() { [ -z "$filter" ] || [[ "$1" == *"$filter"* ]]; }

# run_case <label> <binary> <expected-file> [args...]
run_case() {
  local label=$1 bin=$2 expected=$3
  shift 3
  if ! "$bin" "$@" >"$work/out" 2>"$work/err"; then
    bad "$label" "exit nonzero: $(head -3 "$work/err")"
    return
  fi
  if cmp -s "$work/out" "$expected"; then
    ok "$label"
  else
    bad "$label" "stdout differs from $(basename "$expected")"
    diff "$expected" "$work/out" | head -10
  fi
}

# kernel_cases <label> <binary> <kernel-dir-of-expected>
# Runs the driver inputs of one kernel against its expected dir.
kernel_cases() {
  local label=$1 bin=$2 kdir=$3
  local name
  name=$(basename "$kdir")
  case "$name" in
    gostring*)
      keep "$label/run" && run_case "$label/run" "$bin" "$kdir/expected/run.out"
      ;;
    json*)
      keep "$label/fixed" && run_case "$label/fixed" "$bin" "$kdir/expected/fixed.out"
      local f
      for f in "$kdir"/inputs/*.json; do
        keep "$label/$(basename "$f")" || continue
        run_case "$label/$(basename "$f")" "$bin" "$kdir/expected/$(basename "$f").out" "$f"
      done
      ;;
    scanner*)
      local f
      for f in "$kdir"/inputs/*; do
        keep "$label/$(basename "$f")" || continue
        run_case "$label/$(basename "$f")" "$bin" "$kdir/expected/$(basename "$f").out" "$f"
      done
      ;;
  esac
}

bin_name() { sed -n 's/^name = "\(.*\)-kernel"/\1-kernel/p' "$1/Cargo.toml" | head -1; }

kernels=(gostring json scanner gostring-amalgam json-amalgam scanner-amalgam)

if [ -n "${LUST:-}" ]; then
  # Report mode: lust builds the entry file of each kernel and each
  # compat fixture. Rejection is a report, not a failure.
  for k in "${kernels[@]}"; do
    case "$k" in *-amalgam) parent=$root/tests/kernels/${k%-amalgam} ;; *) parent=$root/tests/kernels/$k ;; esac
    entry=$root/tests/kernels/$k/src/main.rs
    keep "$k" || continue
    if "$LUST" build "$entry" -o "$work/$k.lust" 2>"$work/$k.err"; then
      kernel_cases "$k" "$work/$k.lust" "$parent"
    else
      unsup "$k" "$(head -1 "$work/$k.err")"
    fi
  done
  for f in "$root"/tests/compat/*.rs; do
    name=$(basename "$f" .rs)
    keep "compat/$name" || continue
    if "$LUST" build "$f" -o "$work/$name.lust" 2>"$work/$name.err"; then
      run_case "compat/$name" "$work/$name.lust" "$root/tests/compat/$name.expected"
    else
      unsup "compat/$name" "$(head -1 "$work/$name.err")"
    fi
  done
  echo "---"
  echo "lust report: $pass ok, $fail wrong, $unsupported unsupported (unsupported does not fail)"
  [ "$fail" -eq 0 ]
  exit $?
fi

# rustc mode.
for k in "${kernels[@]}"; do
  kdir=$root/tests/kernels/$k
  case "$k" in *-amalgam) parent=$root/tests/kernels/${k%-amalgam} ;; *) parent=$kdir ;; esac
  keep "$k" || continue
  # Amalgam freshness: the committed file must equal inliner output.
  if [[ "$k" == *-amalgam ]]; then
    if python3 "$root/tests/kernels/amalgamate.py" "$parent" "$work/amalgam.rs" >/dev/null \
      && cmp -s "$work/amalgam.rs" "$kdir/src/main.rs"; then
      ok "$k/fresh"
    else
      bad "$k/fresh" "committed amalgam differs from amalgamate.py output; regenerate it"
    fi
  fi
  if ! cargo build --release --manifest-path "$kdir/Cargo.toml" >"$work/$k.build" 2>&1; then
    bad "$k/build" "cargo build failed: $(grep -m2 '^error' "$work/$k.build")"
    continue
  fi
  ok "$k/build"
  kernel_cases "$k" "$kdir/target/release/$(bin_name "$kdir")" "$parent"
done

for f in "$root"/tests/compat/*.rs; do
  name=$(basename "$f" .rs)
  keep "compat/$name" || continue
  mode=$(sed -n 's|// panic-mode: ||p' "$f" | head -1)
  mode=${mode:-abort}
  if ! rustc --edition 2024 -C "panic=$mode" -C overflow-checks=on -A warnings \
    -o "$work/$name.rustc" "$f" 2>"$work/$name.err"; then
    bad "compat/$name" "rustc rejected it: $(head -3 "$work/$name.err")"
    continue
  fi
  run_case "compat/$name" "$work/$name.rustc" "$root/tests/compat/$name.expected"
done

echo "---"
echo "kernels: $pass ok, $fail failed"
[ "$fail" -eq 0 ]
