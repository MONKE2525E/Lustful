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
# Knobs (ARCH 9.3 runner rules): CASE_TIMEOUT seconds per build
# (default 300; a cold Cargo kernel build is slow), RUN_TIMEOUT
# seconds per run (default 30), SANITIZE=1 in lust mode rebuilds
# the generated C under ASan/UBSan and runs the cases on that
# binary. Missing fixture dirs fail the run; they never skip.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
filter=${1:-}
if ! command -v timeout >/dev/null 2>&1; then
  echo "FAIL: the timeout command is required for per-case timeouts"
  exit 1
fi
case_timeout=${CASE_TIMEOUT:-300}
run_timeout=${RUN_TIMEOUT:-30}
run_cc() { timeout "$case_timeout" "$@"; }
seen=0
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
  seen=$((seen + 1))
  if [ ! -f "$expected" ]; then
    bad "$label" "expected file missing: $expected"
    return
  fi
  if ! timeout "$run_timeout" "$bin" "$@" >"$work/out" 2>"$work/err"; then
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

# Fixture dirs must exist and hold cases (ARCH 9.3: no silent skips).
for k in "${kernels[@]}"; do
  if [ ! -f "$root/tests/kernels/$k/src/main.rs" ] || [ ! -f "$root/tests/kernels/$k/Cargo.toml" ]; then
    echo "FAIL fixture kernel incomplete: tests/kernels/$k (need Cargo.toml and src/main.rs)"
    exit 1
  fi
done
if ! compgen -G "$root/tests/compat/*.rs" >/dev/null; then
  echo "FAIL fixture dir missing or empty: tests/compat"
  exit 1
fi

# Builds one entry file with lust. With SANITIZE=1 the binary at $2 is
# replaced by an ASan/UBSan build of the generated C, and a sanitizer
# report at run time fails like any wrong run (run_case checks stderr
# only via exit code, so the caller keeps the unsanitized compare too:
# SANITIZE runs the cases twice, once per binary). Returns nonzero if
# lust rejects the entry (unsupported in report mode).
lust_build() {
  # $1 entry file, $2 out binary, $3 flat name
  run_cc "$LUST" build "$1" -o "$2" 2>"$work/$3.err"
}

lust_build_sanitized() {
  # $1 entry file, $2 out binary, $3 flat name. The entry is known to
  # build (lust_build just did), so a failure here is a real failure.
  run_cc "$LUST" build "$1" -o "$work/$3.tmp" --emit-c "$work/$3.san" 2>/dev/null || return 1
  gcc -O1 -w -fno-sanitize-recover=undefined -fsanitize=address,undefined -o "$2" "$work/$3.san".*.c 2>"$work/$3.san.err"
}

if [ -n "${LUST:-}" ]; then
  case "$LUST" in
    /*) ;;
    *) LUST=$PWD/$LUST ;;
  esac
  if [ ! -x "$LUST" ]; then
    echo "FAIL: LUST=$LUST is not an executable file"
    exit 1
  fi
  # Report mode: lust builds the entry file of each kernel and each
  # compat fixture. Rejection is a report, not a failure.
  for k in "${kernels[@]}"; do
    case "$k" in *-amalgam) parent=$root/tests/kernels/${k%-amalgam} ;; *) parent=$root/tests/kernels/$k ;; esac
    entry=$root/tests/kernels/$k/src/main.rs
    keep "$k" || continue
    if lust_build "$entry" "$work/$k.lust" "$k"; then
      kernel_cases "$k" "$work/$k.lust" "$parent"
      seen=$((seen + 1))
      if [ "${SANITIZE:-0}" = 1 ]; then
        if lust_build_sanitized "$entry" "$work/$k.sanbin" "$k"; then
          kernel_cases "$k/san" "$work/$k.sanbin" "$parent"
        else
          bad "$k/san" "sanitized build failed: $(head -3 "$work/$k.san.err")"
        fi
      fi
    else
      seen=$((seen + 1))
      unsup "$k" "$(head -1 "$work/$k.err")"
    fi
  done
  for f in "$root"/tests/compat/*.rs; do
    name=$(basename "$f" .rs)
    keep "compat/$name" || continue
    if lust_build "$f" "$work/$name.lust" "$name"; then
      run_case "compat/$name" "$work/$name.lust" "$root/tests/compat/$name.expected"
      if [ "${SANITIZE:-0}" = 1 ]; then
        if lust_build_sanitized "$f" "$work/$name.sanbin" "$name"; then
          run_case "compat/$name/san" "$work/$name.sanbin" "$root/tests/compat/$name.expected"
        else
          bad "compat/$name/san" "sanitized build failed: $(head -3 "$work/$name.san.err")"
        fi
      fi
    else
      seen=$((seen + 1))
      unsup "compat/$name" "$(head -1 "$work/$name.err")"
    fi
  done
  echo "---"
  echo "lust report: $pass ok, $fail wrong, $unsupported unsupported (unsupported does not fail)"
  if [ $seen -eq 0 ]; then
    echo "FAIL: no entries matched filter '${filter}'"
    exit 1
  fi
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
  seen=$((seen + 1))
  if ! run_cc cargo build --release --manifest-path "$kdir/Cargo.toml" >"$work/$k.build" 2>&1; then
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
  if ! run_cc rustc --edition 2024 -C "panic=$mode" -C overflow-checks=on -A warnings \
    -o "$work/$name.rustc" "$f" 2>"$work/$name.err"; then
    bad "compat/$name" "rustc rejected it: $(head -3 "$work/$name.err")"
    continue
  fi
  run_case "compat/$name" "$work/$name.rustc" "$root/tests/compat/$name.expected"
done

echo "---"
echo "kernels: $pass ok, $fail failed"
if [ $seen -eq 0 ]; then
  echo "FAIL: no entries matched filter '${filter}'"
  exit 1
fi
[ "$fail" -eq 0 ]
