#!/usr/bin/env bash
# Differential tests against rustc (the oracle).
#   tests/pass/*.rs: rustc and lust must both build. Stdout and exit status must match.
#   tests/fail/*.rs: rustc must reject the program, and `lust check` must report the code
#                    named on the first line (`// expect: L0301`).
#   tests/reject/*.rs: valid Rust that lust rejects on purpose (lifetimes, user macros).
#                    rustc must accept it, and `lust check` must report the expected code.
# Usage: scripts/difftest.sh [filter]
#   SANITIZE=1 also builds the generated C with gcc -fsanitize=address,undefined and runs it.
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
rustc_flags=(--edition 2024 -C panic=abort -C overflow-checks=on -A unconditional_panic -A warnings)
filter=${1:-}
pass=0
fail=0

report() {
  if [ "$1" = ok ]; then pass=$((pass + 1)); else fail=$((fail + 1)); echo "FAIL $2: $3"; fi
}

for f in "$root"/tests/pass/*.rs; do
  name=$(basename "$f" .rs)
  [[ -n "$filter" && "$name" != *"$filter"* ]] && continue
  if ! rustc "${rustc_flags[@]}" -o "$work/$name.rustc" "$f" 2>"$work/$name.rustc.err"; then
    report bad "$name" "rustc rejected it: $(head -3 "$work/$name.rustc.err")"; continue
  fi
  if ! "$lust" build "$f" -o "$work/$name.lust" 2>"$work/$name.lust.err"; then
    report bad "$name" "lust rejected it: $(head -5 "$work/$name.lust.err")"; continue
  fi
  "$work/$name.rustc" >"$work/$name.rustc.out" 2>/dev/null; rs=$?
  "$work/$name.lust" >"$work/$name.lust.out" 2>/dev/null; ls=$?
  if [ $rs -ne $ls ]; then
    report bad "$name" "exit status rustc=$rs lust=$ls"
  elif ! diff -q "$work/$name.rustc.out" "$work/$name.lust.out" >/dev/null; then
    report bad "$name" "stdout differs:"; diff "$work/$name.rustc.out" "$work/$name.lust.out" | head -10
  elif [ "${SANITIZE:-0}" = 1 ]; then
    "$lust" build "$f" -o "$work/$name.tmp" --emit-c "$work/$name" 2>/dev/null
    if ! gcc -O1 -w -fno-sanitize-recover=undefined -fsanitize=address,undefined -o "$work/$name.san" "$work/$name".*.c 2>"$work/$name.san.err"; then
      report bad "$name" "gcc could not build the generated C: $(head -3 "$work/$name.san.err")"
    else
      "$work/$name.san" >"$work/$name.san.out" 2>"$work/$name.san.err"; ss=$?
      if grep -q "runtime error\|Sanitizer" "$work/$name.san.err"; then
        report bad "$name" "sanitizer: $(grep -m2 "runtime error\|Sanitizer" "$work/$name.san.err")"
      elif ! diff -q "$work/$name.rustc.out" "$work/$name.san.out" >/dev/null; then
        report bad "$name" "sanitized build output differs"
      else
        report ok "$name"
      fi
    fi
  else
    report ok "$name"
  fi
done

for f in "$root"/tests/fail/*.rs "$root"/tests/reject/*.rs; do
  name=$(basename "$f" .rs)
  [[ -n "$filter" && "$name" != *"$filter"* ]] && continue
  expect=$(head -1 "$f" | sed -n 's|^// expect: *\(L[0-9]*\).*|\1|p')
  rustc "${rustc_flags[@]}" -o "$work/$name.rustc" "$f" 2>/dev/null
  rustc_ok=$?
  if [[ "$f" == */fail/* && $rustc_ok -eq 0 ]]; then
    report bad "$name" "rustc accepted it, so it is not a valid negative test"; continue
  fi
  if [[ "$f" == */reject/* && $rustc_ok -ne 0 ]]; then
    report bad "$name" "rustc rejected it, so it belongs in tests/fail"; continue
  fi
  out=$("$lust" check --json "$f" 2>&1)
  if [ $? -eq 0 ]; then
    report bad "$name" "lust accepted it (expected $expect)"
  elif ! grep -q "\"code\":\"$expect\"" <<<"$out"; then
    report bad "$name" "expected $expect, got: $(grep -o '"code":"L[0-9]*"' <<<"$out" | tr '\n' ' ')"
  else
    report ok "$name"
  fi
done

echo "difftest: $pass passed, $fail failed"
[ $fail -eq 0 ]
