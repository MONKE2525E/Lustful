#!/usr/bin/env bash
# `lust run` tests, cold (no daemon). Small programs (one function unit) must run in memory
# (see tcc::run_in_memory). That run forks only when the OS lists one thread in the process,
# so the in-memory check is also the thread count check at every fork point. The programs
# must behave exactly like the built executable: same stdout, same
# stderr (panic text included), same exit status. Both must also match rustc on stdout and
# exit status. Programs run with two extra arguments, so `std::env::args().count()` counts
# them. Usage: scripts/runtest.sh [filter]
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# Make sure no daemon answers (and none autostarts) and the disk cache stays out: the
# client must exec lust-core, which compiles cold and runs in memory.
export LUST_DAEMON_SOCKET="$work/no-daemon.sock"
export LUST_NO_DAEMON=1
export LUST_NO_CACHE=1
filter=${1:-}
pass=0
fail=0

report() {
  if [ "$1" = ok ]; then pass=$((pass + 1)); else fail=$((fail + 1)); echo "FAIL $2: $3"; fi
}

for f in "$root"/tests/pass/*.rs; do
  name=$(basename "$f" .rs)
  [[ -n "$filter" && "$name" != *"$filter"* ]] && continue
  (cd "$work" && rustc --edition 2024 -C panic=abort -C overflow-checks=on -A warnings -o "$work/$name.rustc" "$f" 2>/dev/null) || { report bad "$name" "rustc rejected it"; continue; }
  (cd "$work" && "$lust" build "$f" -o "$work/$name.lust" 2>"$work/$name.build.err") || { report bad "$name" "lust build rejected it"; continue; }
  "$work/$name.rustc" x y >"$work/$name.rustc.out" 2>"$work/$name.rustc.err"; rs=$?
  "$work/$name.lust" x y >"$work/$name.lust.out" 2>"$work/$name.lust.err"; bs=$?
  (cd "$work" && "$lust" run "$f" -- x y >"$work/$name.mem.out" 2>"$work/$name.mem.err"); ms=$?
  # Which run path did it take? glue_shared has three function units, so it must use the file.
  probe=$(cd "$work" && "$lust" run --timings "$f" -- x y 2>&1 >/dev/null)
  if grep -q "in memory" <<<"$probe"; then mode=mem; else mode=file; fi
  want_mode=mem; [[ "$name" == glue_shared ]] && want_mode=file
  if [ "$mode" != "$want_mode" ]; then
    report bad "$name" "run took the $mode path, want $want_mode"
  elif [ $ms -ne $bs ] || [ $ms -ne $rs ]; then
    report bad "$name" "exit status memory=$ms built=$bs rustc=$rs"
  elif ! cmp -s "$work/$name.mem.out" "$work/$name.lust.out" || ! cmp -s "$work/$name.mem.out" "$work/$name.rustc.out"; then
    report bad "$name" "stdout differs (memory vs built vs rustc)"
  elif ! cmp -s "$work/$name.mem.err" "$work/$name.lust.err"; then
    report bad "$name" "stderr differs (memory vs built)"; diff "$work/$name.mem.err" "$work/$name.lust.err" | head -5
  else
    report ok "$name"
  fi
done

echo "runtest: $pass passed, $fail failed"
[ $fail -eq 0 ]
