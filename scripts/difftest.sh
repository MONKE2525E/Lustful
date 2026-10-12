#!/usr/bin/env bash
# Differential tests against rustc (the oracle). Two modes (ARCH 9.3
# runner table):
#   Default (abort mode, -C panic=abort):
#     tests/pass/*.rs: rustc and lust must both build. Stdout and exit status must match.
#                      A `// panic: <text>` comment also requires <text> in lust's stderr.
#                      Rustc's panic text is not compared (see DESIGN.md).
#     tests/fail/*.rs: rustc must reject the program, and `lust check` must report the code
#                      named on the first line (`// expect: L0301`).
#     tests/reject/*.rs: valid Rust that lust rejects on purpose (lifetimes, user macros).
#                      rustc must accept it, and `lust check` must report the expected code.
#   PANIC=unwind (rustc -C panic=unwind, overflow checks on):
#     tests/unwind/*.rs plus the panic cases in tests/pass (files with a
#     `// panic:` line). Abort mode cannot test recovered panics, poison,
#     or unwind drops, so these live only here. Rustc must build and run
#     each case. Lust has no unwinding until wave C: a lust build failure
#     is UNSUPPORTED (reported, not a failure; LUST_STRICT=1 makes it
#     fail). A lust build that runs must match rustc stdout; for the
#     uncaught-panic pass cases both exits must be nonzero (exact codes
#     differ by panic strategy until wave C: rustc unwind exits 101,
#     lust abort exits by signal). A lust build with wrong stdout is a
#     failure in every mode: lust accepted the program.
# Usage: scripts/difftest.sh [filter]
#   SANITIZE=1 also builds the generated C with gcc -fsanitize=address,undefined and runs it.
#   CASE_TIMEOUT seconds per compile (default 30), RUN_TIMEOUT per run
#   (default 10). A missing or empty fixture dir fails the run, as does
#   a filter that matches no case (ARCH 9.3: no silent skips).
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# Always compile cold: a warm daemon in this directory (or one autostarted by the first
# test) would serve later tests, and a warm `--emit-c` writes only the changed units, so
# the SANITIZE build would miss the runtime unit. Cache and daemon behaviour have their
# own gate (scripts/test-client.sh).
export LUST_NO_DAEMON=1
export LUST_DAEMON_SOCKET="$work/no-daemon.sock"
export LUST_CACHE_DIR="$work/cache"
if ! command -v timeout >/dev/null 2>&1; then
  echo "FAIL: the timeout command is required for per-case timeouts"
  exit 1
fi
case_timeout=${CASE_TIMEOUT:-30}
run_timeout=${RUN_TIMEOUT:-10}
run_cc() { timeout "$case_timeout" "$@"; }
run_to() { timeout "$run_timeout" "$@"; }
filter=${1:-}
pass=0
fail=0
seen=0
unsupported=0

report() {
  if [ "$1" = ok ]; then pass=$((pass + 1)); else fail=$((fail + 1)); echo "FAIL $2: $3"; fi
}

# A fixture dir this run needs must exist and hold .rs files.
require_dir() {
  if [ ! -d "$root/$1" ]; then
    echo "FAIL fixture dir missing: $1"
    exit 1
  fi
  if ! compgen -G "$root/$1/*.rs" >/dev/null; then
    echo "FAIL fixture dir holds no .rs files: $1"
    exit 1
  fi
}

sanitize_case() {
  # $1 fixture, $2 name, $3 expected-stdout file. Returns 0 on match.
  local f=$1 name=$2 expected=$3
  run_cc "$lust" build "$f" -o "$work/$name.tmp" --emit-c "$work/$name" 2>/dev/null || return 1
  if ! gcc -O1 -w -fno-sanitize-recover=undefined -fsanitize=address,undefined -o "$work/$name.san" "$work/$name".*.c 2>"$work/$name.san.err"; then
    echo "gcc could not build the generated C: $(head -3 "$work/$name.san.err")"
    return 1
  fi
  run_to "$work/$name.san" >"$work/$name.san.out" 2>"$work/$name.san.err"
  if grep -q "runtime error\|Sanitizer" "$work/$name.san.err"; then
    echo "sanitizer: $(grep -m2 "runtime error\|Sanitizer" "$work/$name.san.err")"
    return 1
  fi
  if ! cmp -s "$expected" "$work/$name.san.out"; then
    echo "sanitized build output differs"
    return 1
  fi
}

if [ "${PANIC:-abort}" = unwind ]; then
  require_dir tests/unwind
  require_dir tests/pass
  rustc_flags=(--edition 2024 -C panic=unwind -C overflow-checks=on -A unconditional_panic -A warnings)
  # tests/unwind cases, then the panic cases of tests/pass. The second
  # set is marked by a `// panic:` line, as in abort mode.
  unwind_cases=$(ls "$root"/tests/unwind/*.rs)
  panic_cases=$(grep -l '// panic:' "$root"/tests/pass/*.rs || true)
  if [ -z "$panic_cases" ]; then
    echo "FAIL: no panic cases in tests/pass for the unwind run"
    exit 1
  fi
  for f in $unwind_cases $panic_cases; do
    name=$(basename "$f" .rs)
    [[ "$f" == */unwind/* ]] && name="unwind-$name"
    [[ -n "$filter" && "$name" != *"$filter"* ]] && continue
    seen=$((seen + 1))
    if ! run_cc rustc "${rustc_flags[@]}" -o "$work/$name.rustc" "$f" 2>"$work/$name.rustc.err"; then
      report bad "$name" "rustc (panic=unwind) rejected it: $(head -3 "$work/$name.rustc.err")"; continue
    fi
    run_to "$work/$name.rustc" >"$work/$name.rustc.out" 2>/dev/null; rs=$?
    if ! run_cc "$lust" build "$f" -o "$work/$name.lust" 2>"$work/$name.lust.err"; then
      unsupported=$((unsupported + 1))
      echo "UNSUPPORTED $name (unwind): $(head -1 "$work/$name.lust.err")"
      continue
    fi
    run_to "$work/$name.lust" >"$work/$name.lust.out" 2>"$work/$name.lust.stderr"; ls=$?
    # Exit codes: exact for tests/unwind (a caught panic exits 0 under
    # both), nonzero-vs-nonzero for uncaught panics (see the header).
    if [[ "$f" == */unwind/* ]]; then exit_ok=$([ $rs -eq $ls ] && echo 1 || echo 0); else exit_ok=$([ $rs -ne 0 ] && [ $ls -ne 0 ] && echo 1 || echo 0); fi
    if [ "$exit_ok" = 0 ]; then
      report bad "$name" "exit status rustc=$rs lust=$ls"
    elif ! cmp -s "$work/$name.rustc.out" "$work/$name.lust.out"; then
      report bad "$name" "stdout differs:"; diff "$work/$name.rustc.out" "$work/$name.lust.out" | head -10
    elif [ "${SANITIZE:-0}" = 1 ]; then
      if msg=$(sanitize_case "$f" "$name" "$work/$name.rustc.out"); then
        report ok "$name"
      else
        report bad "$name" "sanitized build: $msg"
      fi
    else
      report ok "$name"
    fi
  done
  if [ $seen -eq 0 ]; then
    echo "FAIL: no cases matched filter '${filter}'"
    exit 1
  fi
  echo "difftest (PANIC=unwind): $pass passed, $fail failed, $unsupported unsupported (lust has no unwinding until wave C)"
  if [ "${LUST_STRICT:-0}" = 1 ] && [ $unsupported -ne 0 ]; then fail=$((fail + 1)); fi
  [ $fail -eq 0 ]
  exit $?
fi

require_dir tests/pass
require_dir tests/fail
require_dir tests/reject
rustc_flags=(--edition 2024 -C panic=abort -C overflow-checks=on -A unconditional_panic -A warnings)

for f in "$root"/tests/pass/*.rs; do
  name=$(basename "$f" .rs)
  [[ -n "$filter" && "$name" != *"$filter"* ]] && continue
  seen=$((seen + 1))
  if ! run_cc rustc "${rustc_flags[@]}" -o "$work/$name.rustc" "$f" 2>"$work/$name.rustc.err"; then
    report bad "$name" "rustc rejected it: $(head -3 "$work/$name.rustc.err")"; continue
  fi
  if ! run_cc "$lust" build "$f" -o "$work/$name.lust" 2>"$work/$name.lust.err"; then
    report bad "$name" "lust rejected it: $(head -5 "$work/$name.lust.err")"; continue
  fi
  panic_expect=$(sed -n 's|.*// panic: ||p' "$f" | head -1 | sed 's/[[:space:]]*$//')
  run_to "$work/$name.rustc" >"$work/$name.rustc.out" 2>/dev/null; rs=$?
  run_to "$work/$name.lust" >"$work/$name.lust.out" 2>"$work/$name.lust.stderr"; ls=$?
  if [ $rs -ne $ls ]; then
    report bad "$name" "exit status rustc=$rs lust=$ls"
  elif ! diff -q "$work/$name.rustc.out" "$work/$name.lust.out" >/dev/null; then
    report bad "$name" "stdout differs:"; diff "$work/$name.rustc.out" "$work/$name.lust.out" | head -10
  elif [ -n "$panic_expect" ] && ! grep -qF "$panic_expect" "$work/$name.lust.stderr"; then
    report bad "$name" "lust stderr lacks panic text '$panic_expect': $(head -3 "$work/$name.lust.stderr")"
  elif [ "${SANITIZE:-0}" = 1 ]; then
    if msg=$(sanitize_case "$f" "$name" "$work/$name.rustc.out"); then
      report ok "$name"
    else
      report bad "$name" "sanitized build: $msg"
    fi
  else
    report ok "$name"
  fi
done

for f in "$root"/tests/fail/*.rs "$root"/tests/reject/*.rs; do
  name=$(basename "$f" .rs)
  [[ -n "$filter" && "$name" != *"$filter"* ]] && continue
  seen=$((seen + 1))
  expect=$(head -1 "$f" | sed -n 's|^// expect: *\(L[0-9]*\).*|\1|p')
  run_cc rustc "${rustc_flags[@]}" -o "$work/$name.rustc" "$f" 2>/dev/null
  rustc_ok=$?
  if [[ "$f" == */fail/* && $rustc_ok -eq 0 ]]; then
    report bad "$name" "rustc accepted it, so it is not a valid negative test"; continue
  fi
  if [[ "$f" == */reject/* && $rustc_ok -ne 0 ]]; then
    report bad "$name" "rustc rejected it, so it belongs in tests/fail"; continue
  fi
  out=$(run_cc "$lust" check --json "$f" 2>&1)
  if [ $? -eq 0 ]; then
    report bad "$name" "lust accepted it (expected $expect)"
  elif ! grep -q "\"code\":\"$expect\"" <<<"$out"; then
    report bad "$name" "expected $expect, got: $(grep -o '"code":"L[0-9]*"' <<<"$out" | tr '\n' ' ')"
  else
    report ok "$name"
  fi
done

if [ $seen -eq 0 ]; then
  echo "FAIL: no cases matched filter '${filter}'"
  exit 1
fi
echo "difftest: $pass passed, $fail failed"
[ $fail -eq 0 ]
