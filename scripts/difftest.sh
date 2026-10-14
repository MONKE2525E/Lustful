#!/usr/bin/env bash
# Differential tests against rustc (the oracle). Two modes (ARCH 9.3
# runner table):
#   Default (abort mode, -C panic=abort):
#     tests/pass/*.rs: rustc and lust must both build. Stdout and exit status must match.
#                      A `// panic: <text>` comment also requires <text> in lust's stderr.
#                      Rustc's panic text is not compared (see DESIGN.md).
#     tests/fail/*.rs: rustc must reject the program, and `lust check` must report the code
#                      named on the first line (`// expect: L0301`); `lust build` must reject it too.
#     tests/reject/*.rs: valid Rust that lust rejects on purpose (lifetimes, user macros).
#                      rustc must accept it, `lust check` must report the expected code, and
#                      `lust build` must reject it.
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
#              The gcc build uses -Werror=incompatible-pointer-types, so a
#              miscompile that passes a pointer of the wrong type (which
#              tcc accepts silently) fails loudly here.
#   CASE_TIMEOUT seconds per compile (default 30), RUN_TIMEOUT per run
#   (default 10). A missing or empty fixture dir fails the run, as does
#   a filter that matches no case (ARCH 9.3: no silent skips).
#   DIFFTEST_JOBS cases run at the same time (default nproc). Each case runs in its own dir
#   (its cwd, lust cache dir, and daemon socket path), and the report prints each case's
#   lines in case order, so the output does not depend on the job count.
#   DIFFTEST_RUSTC_CACHE caches the rustc side of each case (default
#   ~/.cache/lust-difftest; "off" turns it off): rustc's exit status and stderr, and for a
#   built program its stdout and exit status. The key hashes the rustc version, the mode,
#   the flags, the case's name and bytes, and every non-.rs file in the case's dir (the
#   include! files). Lust's side is never cached.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# Always compile cold: a warm daemon in this directory (or one autostarted by the first
# test) would serve later tests, and a warm `--emit-c` writes only the changed units, so
# the SANITIZE build would miss the runtime unit. Cache and daemon behaviour have their
# own gate (scripts/test-client.sh). run_all gives each case its own socket path and
# cache dir. The tcc runtime object in $TMPDIR is shared: it is keyed by its content and
# written by rename, so parallel builds are safe (src/tcc.rs cached_runtime_object).
export LUST_NO_DAEMON=1
if ! command -v timeout >/dev/null 2>&1; then
  echo "FAIL: the timeout command is required for per-case timeouts"
  exit 1
fi
case_timeout=${CASE_TIMEOUT:-30}
run_timeout=${RUN_TIMEOUT:-10}
run_cc() { timeout "$case_timeout" "$@"; }
run_to() { timeout "$run_timeout" "$@"; }
filter=${1:-}
jobs=${DIFFTEST_JOBS:-$(nproc)}
rustc_cache=${DIFFTEST_RUSTC_CACHE:-$HOME/.cache/lust-difftest}
[ "$rustc_cache" = off ] || mkdir -p "$rustc_cache" || rustc_cache=off
rustc_version=$(rustc -vV 2>&1)
# inc_hash[dir]: a hash of every non-.rs file in a fixture dir (the include! files), for
# the rustc cache key.
declare -A inc_hash
for d in "$root"/tests/{pass,fail,reject,unwind}; do
  inc_hash[$d]=$(for g in "$d"/*; do [[ "$g" == *.rs || ! -f "$g" ]] || { basename "$g"; cat "$g"; }; done | sha256sum)
done

# report ok|bad <name> [msg]: a case's result. Runs inside the case's subshell, in its dir.
report() {
  echo "$1" >st
  [ "$1" = ok ] || echo "FAIL $2: $3"
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

# rustc_oracle build|run <file> <rustc flags...>: runs rustc on <file> in the case dir and
# writes rustc.cc (exit status) and rustc.err (stderr); in run mode, when the build passes,
# it also runs the program and writes rustc.out (stdout) and rustc.rs (exit status).
# Results come from $rustc_cache when the key matches. A timeout is never cached.
rustc_oracle() {
  local mode=$1 f=$2; shift 2
  local key="" entry="" g cc rs=0
  if [ "$rustc_cache" != off ]; then
    key=$({
      printf 'v1\n%s\n%s\n%s\n%s\n' "$rustc_version" "$mode" "$*" "$(basename "$f")"
      # file!() and panic locations print the path; key those cases on the full path.
      grep -qE 'file!|Location' "$f" && echo "$f"
      cat "$f"
      echo "${inc_hash[$(dirname "$f")]}"
    } | sha256sum | cut -c1-40)
    entry=$rustc_cache/$key
    if [ -f "$entry/rustc.cc" ]; then
      cp "$entry"/rustc.* .
      return
    fi
  fi
  run_cc rustc "$@" -o rustc.bin "$f" 2>rustc.err; cc=$?
  echo $cc >rustc.cc
  if [ "$mode" = run ] && [ $cc -eq 0 ]; then
    run_to ./rustc.bin >rustc.out 2>/dev/null; rs=$?
    echo $rs >rustc.rs
  fi
  [ -n "$entry" ] && [ $cc -ne 124 ] && [ $cc -ne 137 ] && [ $rs -ne 124 ] && [ $rs -ne 137 ] || return 0
  local tmp
  tmp=$(mktemp -d "$rustc_cache/.tmp.XXXXXX") || return 0
  cp rustc.cc rustc.err "$tmp"/ && { [ ! -f rustc.out ] || cp rustc.out rustc.rs "$tmp"/; } \
    && mv -T "$tmp" "$entry" 2>/dev/null || rm -rf "$tmp"
}

# run_all <case fn> <file...>: runs `<case fn> <name> <file>` for each file whose name
# matches the filter, $jobs at a time. Case i runs in $work/c/i (its cwd, cache dir, and
# daemon socket path), with its report in c/i/st and its output in c/i/log. Then prints
# every log in case order and sets pass, fail, unsupported, and seen.
run_all() {
  local fn=$1; shift
  local f name i=0 running=0 st
  local names=()
  for f in "$@"; do
    name=$(basename "$f" .rs)
    [[ "$f" == */unwind/* ]] && name="unwind-$name"
    [[ -n "$filter" && "$name" != *"$filter"* ]] && continue
    if [ $running -ge "$jobs" ]; then wait -n; running=$((running - 1)); fi
    mkdir -p "$work/c/$i"
    (
      cd "$work/c/$i" || exit 1
      export LUST_DAEMON_SOCKET=$PWD/no-daemon.sock LUST_CACHE_DIR=$PWD/cache
      "$fn" "$name" "$f"
    ) >"$work/c/$i/log" 2>&1 &
    names+=("$name"); i=$((i + 1)); running=$((running + 1))
  done
  wait
  for i in "${!names[@]}"; do
    cat "$work/c/$i/log"
    st=$(cat "$work/c/$i/st" 2>/dev/null)
    case "$st" in
      ok) pass=$((pass + 1)) ;;
      unsupported) unsupported=$((unsupported + 1)) ;;
      bad) fail=$((fail + 1)) ;;
      *) fail=$((fail + 1)); echo "FAIL ${names[$i]}: the case runner gave no result" ;;
    esac
  done
  seen=$((seen + ${#names[@]}))
}

sanitize_case() {
  # $1 fixture, $2 name, $3 expected-stdout file. Returns 0 on match. Runs in the case dir.
  local f=$1 name=$2 expected=$3
  run_cc "$lust" build "$f" -o "$name.tmp" --emit-c "$name" 2>/dev/null || return 1
  if ! gcc -O1 -w -Werror=incompatible-pointer-types -fno-sanitize-recover=undefined -fsanitize=address,undefined -o "$name.san" "$name".*.c 2>"$name.san.err"; then
    echo "gcc could not build the generated C: $(head -3 "$name.san.err")"
    return 1
  fi
  run_to "./$name.san" >"$name.san.out" 2>"$name.san.err"
  if grep -q "runtime error\|Sanitizer" "$name.san.err"; then
    echo "sanitizer: $(grep -m2 "runtime error\|Sanitizer" "$name.san.err")"
    return 1
  fi
  if ! cmp -s "$expected" "$name.san.out"; then
    echo "sanitized build output differs"
    return 1
  fi
}

pass=0
fail=0
seen=0
unsupported=0

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
  # unwind_case <name> <file>: one PANIC=unwind case (see the header).
  unwind_case() {
    local name=$1 f=$2 rs ls exit_ok msg
    rustc_oracle run "$f" "${rustc_flags[@]}"
    if [ "$(cat rustc.cc)" -ne 0 ]; then
      report bad "$name" "rustc (panic=unwind) rejected it: $(head -3 rustc.err)"; return
    fi
    rs=$(cat rustc.rs)
    if ! run_cc "$lust" build "$f" -o "$name.lust" 2>"$name.lust.err"; then
      echo unsupported >st
      echo "UNSUPPORTED $name (unwind): $(head -1 "$name.lust.err")"
      return
    fi
    run_to "./$name.lust" >"$name.lust.out" 2>"$name.lust.stderr"; ls=$?
    # Exit codes: exact for tests/unwind (a caught panic exits 0 under
    # both), nonzero-vs-nonzero for uncaught panics (see the header).
    if [[ "$f" == */unwind/* ]]; then exit_ok=$([ $rs -eq $ls ] && echo 1 || echo 0); else exit_ok=$([ $rs -ne 0 ] && [ $ls -ne 0 ] && echo 1 || echo 0); fi
    if [ "$exit_ok" = 0 ]; then
      report bad "$name" "exit status rustc=$rs lust=$ls"
    elif ! cmp -s rustc.out "$name.lust.out"; then
      report bad "$name" "stdout differs:"; diff rustc.out "$name.lust.out" | head -10
    elif [ "${SANITIZE:-0}" = 1 ]; then
      if msg=$(sanitize_case "$f" "$name" rustc.out); then
        report ok "$name"
      else
        report bad "$name" "sanitized build: $msg"
      fi
    else
      report ok "$name"
    fi
  }
  run_all unwind_case $unwind_cases $panic_cases
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

# pass_case <name> <file>: one tests/pass case (see the header).
pass_case() {
  local name=$1 f=$2 rs ls panic_expect msg
  rustc_oracle run "$f" "${rustc_flags[@]}"
  if [ "$(cat rustc.cc)" -ne 0 ]; then
    report bad "$name" "rustc rejected it: $(head -3 rustc.err)"; return
  fi
  if ! run_cc "$lust" build "$f" -o "$name.lust" 2>"$name.lust.err"; then
    report bad "$name" "lust rejected it: $(head -5 "$name.lust.err")"; return
  fi
  panic_expect=$(sed -n 's|.*// panic: ||p' "$f" | head -1 | sed 's/[[:space:]]*$//')
  rs=$(cat rustc.rs)
  run_to "./$name.lust" >"$name.lust.out" 2>"$name.lust.stderr"; ls=$?
  if [ $rs -ne $ls ]; then
    report bad "$name" "exit status rustc=$rs lust=$ls"
  elif ! diff -q rustc.out "$name.lust.out" >/dev/null; then
    report bad "$name" "stdout differs:"; diff rustc.out "$name.lust.out" | head -10
  elif [ -n "$panic_expect" ] && ! grep -qF "$panic_expect" "$name.lust.stderr"; then
    report bad "$name" "lust stderr lacks panic text '$panic_expect': $(head -3 "$name.lust.stderr")"
  elif [ "${SANITIZE:-0}" = 1 ]; then
    if msg=$(sanitize_case "$f" "$name" rustc.out); then
      report ok "$name"
    else
      report bad "$name" "sanitized build: $msg"
    fi
  else
    report ok "$name"
  fi
}

# neg_case <name> <file>: one tests/fail or tests/reject case (see the header).
neg_case() {
  local name=$1 f=$2 expect rustc_ok out
  expect=$(head -1 "$f" | sed -n 's|^// expect: *\(L[0-9]*\).*|\1|p')
  # Fail cases must be rejected by rustc with its default deny lints, so
  # the fail oracle drops the `-A unconditional_panic` the pass corpus
  # needs for its runtime-panic cases. Reject cases keep the pass flags:
  # they only have to be programs rustc can build at all.
  if [[ "$f" == */fail/* ]]; then
    rustc_oracle build "$f" --edition 2024 -C panic=abort -C overflow-checks=on -A warnings
  else
    rustc_oracle build "$f" "${rustc_flags[@]}"
  fi
  rustc_ok=$(cat rustc.cc)
  if [[ "$f" == */fail/* && $rustc_ok -eq 0 ]]; then
    report bad "$name" "rustc accepted it, so it is not a valid negative test"; return
  fi
  if [[ "$f" == */reject/* && $rustc_ok -ne 0 ]]; then
    report bad "$name" "rustc rejected it, so it belongs in tests/fail"; return
  fi
  out=$(run_cc "$lust" check --json "$f" 2>&1)
  if [ $? -eq 0 ]; then
    report bad "$name" "lust accepted it (expected $expect)"
  elif ! grep -q "\"code\":\"$expect\"" <<<"$out"; then
    report bad "$name" "expected $expect, got: $(grep -o '"code":"L[0-9]*"' <<<"$out" | tr '\n' ' ')"
  elif run_cc "$lust" build "$f" -o "$name.lust" >/dev/null 2>&1; then
    # `build` checks bodies after mono, where a call can reach an
    # instance directly: it must reject what `check` rejects.
    report bad "$name" "lust check rejected it, but lust build accepted it"
  else
    report ok "$name"
  fi
}

# abort_case <name> <file>: pass_case or neg_case by the file's dir, so one job pool runs all.
abort_case() { if [[ "$2" == */pass/* ]]; then pass_case "$@"; else neg_case "$@"; fi; }
run_all abort_case "$root"/tests/pass/*.rs "$root"/tests/fail/*.rs "$root"/tests/reject/*.rs

if [ $seen -eq 0 ]; then
  echo "FAIL: no cases matched filter '${filter}'"
  exit 1
fi
echo "difftest: $pass passed, $fail failed"
[ $fail -eq 0 ]
