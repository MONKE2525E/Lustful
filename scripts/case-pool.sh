# case-pool.sh: the parallel case runner and the rustc result cache that scripts/difftest.sh
# and scripts/runtest.sh share. Source it after setting $root, $work (the run's temp dir),
# and $filter. Each case runs in its own dir; see run_all.
#   DIFFTEST_JOBS        cases at the same time (default nproc).
#   DIFFTEST_RUSTC_CACHE rustc result cache dir (default ~/.cache/lust-difftest; "off" turns
#                        it off). Only rustc's side is cached, never lust's.
#   CASE_TIMEOUT seconds per compile (default 30), RUN_TIMEOUT per run (default 10).
case_timeout=${CASE_TIMEOUT:-30}
run_timeout=${RUN_TIMEOUT:-10}
run_cc() { timeout "$case_timeout" "$@"; }
run_to() { timeout "$run_timeout" "$@"; }
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
pass=0
fail=0
seen=0
unsupported=0

# report ok|bad <name> [msg]: a case's result. Runs inside the case's subshell, in its dir.
report() {
  echo "$1" >st
  [ "$1" = ok ] || echo "FAIL $2: $3"
}

# rustc_oracle build|run <file> <rustc flags...>: runs rustc on <file> in the case dir and
# writes rustc.cc (exit status) and rustc.err (stderr); in run mode, when the build passes,
# it also runs the program with the args in $oracle_args (if set) and writes rustc.out
# (stdout) and rustc.rs (exit status). Results come from $rustc_cache when the key
# matches: a hash of the rustc version, the mode, the flags, the args, the case's name and
# bytes, and the include files of its dir. A timeout is never cached.
rustc_oracle() {
  local mode=$1 f=$2; shift 2
  local key="" entry="" cc rs=0 tmp
  local args=("${oracle_args[@]}")
  if [ "$rustc_cache" != off ]; then
    key=$({
      printf 'v1\n%s\n%s\n%s\n%s\n%s\n' "$rustc_version" "$mode" "$*" "${args[*]}" "$(basename "$f")"
      # file!() and panic locations print the path; key those cases on the full path.
      grep -qE 'file!|Location' "$f" && echo "$f"
      cat "$f"
      echo "${inc_hash[$(dirname "$f")]:-}"
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
    run_to ./rustc.bin "${args[@]}" >rustc.out 2>/dev/null; rs=$?
    echo $rs >rustc.rs
  fi
  [ -n "$entry" ] && [ $cc -ne 124 ] && [ $cc -ne 137 ] && [ $rs -ne 124 ] && [ $rs -ne 137 ] || return 0
  tmp=$(mktemp -d "$rustc_cache/.tmp.XXXXXX") || return 0
  cp rustc.cc rustc.err "$tmp"/ && { [ ! -f rustc.out ] || cp rustc.out rustc.rs "$tmp"/; } \
    && mv -T "$tmp" "$entry" 2>/dev/null || rm -rf "$tmp"
}

# run_all <case fn> <file...>: runs `<case fn> <name> <file>` for each file whose name
# matches $filter, $jobs at a time. Case i runs in $work/c/i (its cwd, lust cache dir, and
# daemon socket path), with its report in c/i/st and its output in c/i/log. Then prints
# every log in case order, so the output does not depend on the job count, and adds to
# pass, fail, unsupported, and seen.
run_all() {
  local fn=$1; shift
  local f name i=0 running=0 st
  local names=()
  rm -rf "$work/c"
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
