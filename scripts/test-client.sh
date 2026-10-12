#!/usr/bin/env bash
# Client tests: daemon autostart, the whole-request disk cache, and the release
# handoff to Cargo/rustc. Run after `cargo build --release`.
#   autostart: fresh dir, first build cold and standalone, second build served
#              by the daemon (its binary loads libbase.so). Plus LUST_NO_DAEMON,
#              a 4-way start race, and the idle timeout.
#   cache:     hit, then miss on edit, on -g, and on a compiler id change.
#              Eviction keeps the newest entries under the size cap.
#   release:   single file via rustc, a tiny Cargo project via cargo (package
#              and bin selection, --profile), and `check --rustc` as oracle.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
if [ ! -x "$lust" ]; then
  echo "error: $lust not built. Run cargo build --release first."
  exit 2
fi
unset LUST_DAEMON_SOCKET LUST_CACHE_DIR LUST_NO_DAEMON LUST_NO_CACHE \
  LUST_CACHE_COMPILER_ID LUST_CACHE_MAX_BYTES LUST_DAEMON_IDLE LUST_THREADS
work=$(mktemp -d)
pass=0
fail=0
daemon_dirs=()

ok() { pass=$((pass + 1)); echo "ok   $1"; }
bad() { fail=$((fail + 1)); echo "FAIL $1: $2"; }
# check <name> <test...> : ok when the test command succeeds.
check() { local name=$1; shift; if "$@" >/dev/null 2>&1; then ok "$name"; else bad "$name" "command failed: $*"; fi; }

stop_daemon() { # stop_daemon <dir>
  local pid
  pid=$(cat "$1/.lust-daemon.sock.lock" 2>/dev/null) || return 0
  [ -n "$pid" ] && kill "$pid" 2>/dev/null
  return 0
}
cleanup() {
  local d
  for d in "${daemon_dirs[@]}"; do stop_daemon "$d"; done
  rm -rf "$work"
}
trap cleanup EXIT

wait_socket() { # wait_socket <dir> : true when the daemon socket appears
  local i
  for i in $(seq 1 100); do [ -S "$1/.lust-daemon.sock" ] && return 0; sleep 0.05; done
  return 1
}
fresh() { # fresh <name> : a new dir with a hello.rs, prints its path
  local d=$work/$1
  mkdir -p "$d"
  printf 'fn main() { println!("hello {}", 40 + 2); }\n' >"$d/hello.rs"
  echo "$d"
}

# ---------------------------------------------------------------- autostart
d=$(fresh autostart); daemon_dirs+=("$d")
(cd "$d" && "$lust" build hello.rs -o h1) >/dev/null 2>&1
check "autostart: first build ok" test -x "$d/h1"
if ldd "$d/h1" 2>/dev/null | grep -q libbase; then
  bad "autostart: first build is standalone" "loads libbase.so, so a daemon built it"
else
  ok "autostart: first build is standalone (cold)"
fi
check "autostart: first build runs" test "$("$d/h1")" = "hello 42"
check "autostart: daemon socket appears" wait_socket "$d"
(cd "$d" && "$lust" build hello.rs -o h2) >/dev/null 2>&1
if ldd "$d/h2" 2>/dev/null | grep -q libbase; then
  ok "autostart: second build served by the daemon"
else
  bad "autostart: second build served by the daemon" "no libbase.so in ldd output"
fi
check "autostart: second build runs" test "$("$d/h2")" = "hello 42"
check "autostart: log file in cache dir" test -s "$d/.lust-cache/daemon.log"
stop_daemon "$d"; sleep 0.3

d=$(fresh nodaemon)
(cd "$d" && LUST_NO_DAEMON=1 "$lust" check hello.rs) >/dev/null 2>&1
sleep 0.5
if [ -S "$d/.lust-daemon.sock" ]; then bad "LUST_NO_DAEMON: no daemon starts" "socket exists"; else ok "LUST_NO_DAEMON: no daemon starts"; fi

d=$(fresh race); daemon_dirs+=("$d")
pids=()
for i in 1 2 3 4; do (cd "$d" && "$lust" check hello.rs) >/dev/null 2>&1 & pids+=($!); done
race_rc=0
for p in "${pids[@]}"; do wait "$p" || race_rc=1; done
check "race: 4 concurrent first commands pass" test $race_rc -eq 0
check "race: one daemon socket serves after" wait_socket "$d"
(cd "$d" && "$lust" build hello.rs -o h) >/dev/null 2>&1
if ldd "$d/h" 2>/dev/null | grep -q libbase; then ok "race: warm build after the race"; else bad "race: warm build after the race" "no libbase.so"; fi
stop_daemon "$d"; sleep 0.3

d=$(fresh idle); daemon_dirs+=("$d")
(cd "$d" && LUST_DAEMON_IDLE=1 "$lust" check hello.rs) >/dev/null 2>&1
check "idle: daemon starts" wait_socket "$d"
ipid=$(cat "$d/.lust-daemon.sock.lock" 2>/dev/null)
gone=0
for i in $(seq 1 100); do
  if ! kill -0 "$ipid" 2>/dev/null; then gone=1; break; fi
  sleep 0.1
done
check "idle: daemon exits after the idle span" test $gone -eq 1
if [ -S "$d/.lust-daemon.sock" ]; then bad "idle: socket removed on exit" "socket still there"; else ok "idle: socket removed on exit"; fi
(cd "$d" && LUST_DAEMON_IDLE=0 "$lust" check hello.rs) >/dev/null 2>&1
check "idle: next command works and restarts a daemon" wait_socket "$d"
stop_daemon "$d"; sleep 0.3

# -------------------------------------------------------------------- cache
d=$(fresh cache)
run_lust() { (cd "$d" && LUST_NO_DAEMON=1 "$lust" "$@") 2>&1; }
out=$(run_lust build hello.rs -o h --timings)
case "$out" in *"cache hit"*) bad "cache: first build misses" "reported a hit";; *) ok "cache: first build misses";; esac
check "cache: default dir next to source" test -d "$d/.lust-cache"
out=$(run_lust build hello.rs -o h --timings)
case "$out" in *"whole-request cache hit"*) ok "cache: second build hits";; *) bad "cache: second build hits" "no hit line";; esac
check "cache: hit build runs" test "$("$d/h")" = "hello 42"
run_lust check hello.rs --timings >/dev/null
out=$(run_lust check hello.rs --timings)
case "$out" in *"whole-request cache hit"*) ok "cache: second check hits";; *) bad "cache: second check hits" "no hit line";; esac
sed -i 's/40 + 2/1 + 2/' "$d/hello.rs"
out=$(run_lust build hello.rs -o h --timings)
case "$out" in *"cache hit"*) bad "cache: edit misses" "reported a hit after an edit";; *) ok "cache: edit misses";; esac
check "cache: edited build has new output" test "$("$d/h")" = "hello 3"
out=$(run_lust build hello.rs -o h -g --timings)
case "$out" in *"cache hit"*) bad "cache: -g change misses" "reported a hit";; *) ok "cache: -g change misses";; esac
out=$(run_lust build hello.rs -o h -g --timings)
case "$out" in *"cache hit"*) ok "cache: repeated -g build hits";; *) bad "cache: repeated -g build hits" "no hit line";; esac
out=$( (cd "$d" && LUST_NO_DAEMON=1 LUST_CACHE_COMPILER_ID=other-compiler "$lust" check hello.rs --timings) 2>&1 )
case "$out" in *"cache hit"*) bad "cache: compiler id change misses" "reported a hit";; *) ok "cache: compiler id change misses";; esac
out=$( (cd "$d" && LUST_NO_DAEMON=1 LUST_NO_CACHE=1 "$lust" check hello.rs --timings) 2>&1 )
case "$out" in *"cache hit"*) bad "cache: LUST_NO_CACHE never hits" "reported a hit";; *) ok "cache: LUST_NO_CACHE never hits";; esac

d=$(fresh evict)
cap=60000
evict_run() { (cd "$d" && LUST_NO_DAEMON=1 LUST_CACHE_DIR="$d/c" LUST_CACHE_MAX_BYTES=$cap "$lust" "$@") 2>&1; }
for n in 1 2 3 4 5; do
  printf 'fn main() { println!("n %s"); }\n' "$n" > "$d/f$n.rs"
  evict_run build "f$n.rs" -o "h$n" >/dev/null
  [ "$n" = 1 ] && first_entry=$(ls "$d/c" | grep '^req-' | grep -v '\.exe$' | head -1)
done
total=$(du -sb "$d/c" | cut -f1)
if [ "$total" -le $((cap + 16384)) ]; then ok "evict: cache stays near the cap ($total bytes)"; else bad "evict: cache stays near the cap" "$total bytes over cap $cap"; fi
if [ -n "${first_entry:-}" ] && [ ! -e "$d/c/$first_entry" ]; then ok "evict: oldest entry deleted first"; else bad "evict: oldest entry deleted first" "$first_entry still present"; fi
out=$(evict_run build f5.rs -o h5 --timings)
case "$out" in *"cache hit"*) ok "evict: newest entry kept";; *) bad "evict: newest entry kept" "f5 missed";; esac

# ------------------------------------------------------------------ release
d=$(fresh release1)
out=$( (cd "$d" && "$lust" build --release hello.rs -o rel) 2>&1 ); rc=$?
check "release: single file builds" test $rc -eq 0
case "$out" in *"via rustc"*) ok "release: single file names rustc";; *) bad "release: single file names rustc" "output: $out";; esac
check "release: single file runs" test "$("$d/rel")" = "hello 42"
out=$( (cd "$d" && "$lust" check --rustc hello.rs) 2>&1 ); rc=$?
check "check --rustc: valid file passes" test $rc -eq 0
case "$out" in *rustc*) ok "check --rustc: names rustc";; *) bad "check --rustc: names rustc" "output: $out";; esac
printf 'fn main() { let x: i32 = "s"; println!("{}", x); }\n' > "$d/bad.rs"
out=$( (cd "$d" && "$lust" check --rustc bad.rs) 2>&1 ); rc=$?
if [ $rc -ne 0 ]; then ok "check --rustc: bad file fails"; else bad "check --rustc: bad file fails" "exit 0"; fi
case "$out" in *E0308*) ok "check --rustc: rustc error text streams through";; *) bad "check --rustc: rustc error text streams through" "output: $out";; esac
(cd "$d" && "$lust" check --release hello.rs) >/dev/null 2>&1; rc=$?
check "release: --release on check is a usage error" test $rc -eq 2
(cd "$d" && "$lust" build --rustc hello.rs) >/dev/null 2>&1; rc=$?
check "release: --rustc on build is a usage error" test $rc -eq 2

d=$work/cargo; mkdir -p "$d"; cp -r "$root/tests/cargo-proj" "$d/proj"
out=$( (cd "$d/proj" && "$lust" build --release src/main.rs) 2>&1 ); rc=$?
check "cargo: release build passes" test $rc -eq 0
case "$out" in *"via cargo"*) ok "cargo: names cargo";; *) bad "cargo: names cargo" "output: $out";; esac
case "$out" in *"--bin tinyproj"*) ok "cargo: src/main.rs selects the package bin";; *) bad "cargo: src/main.rs selects the package bin" "output: $out";; esac
check "cargo: release binary runs" test "$("$d/proj/target/release/tinyproj")" = "tiny main 42"
if [ -e "$d/proj/target/release/extra" ]; then bad "cargo: other bin not built" "extra exists"; else ok "cargo: other bin not built"; fi
out=$( (cd "$d/proj" && "$lust" build --release src/bin/extra.rs -o "$d/extra") 2>&1 ); rc=$?
check "cargo: src/bin build passes" test $rc -eq 0
case "$out" in *"--bin extra"*) ok "cargo: src/bin/extra.rs selects --bin extra";; *) bad "cargo: src/bin/extra.rs selects --bin extra" "output: $out";; esac
check "cargo: -o copies the artifact" test "$("$d/extra")" = "tiny extra"
out=$( (cd "$d/proj" && "$lust" build --profile fast src/main.rs) 2>&1 ); rc=$?
check "cargo: --profile build passes" test $rc -eq 0
case "$out" in *"--profile fast"*) ok "cargo: --profile name passes through";; *) bad "cargo: --profile name passes through" "output: $out";; esac
check "cargo: profile binary runs" test "$("$d/proj/target/fast/tinyproj")" = "tiny main 42"

echo "test-client: $pass passed, $fail failed"
[ $fail -eq 0 ]
