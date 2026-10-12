#!/usr/bin/env bash
# Macro dependency smoke test (ARCH 6.4, W-MACRO phase 2): a daemon
# session must not serve an expansion that read a since-changed file.
# The program's output comes only from `include_str!` and `include!`
# reads, so a rebuild with no source edit at all must still change
# its answer once those files change. A deleted include must turn
# the answer into the L0803 error, not a stale success.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
if [ ! -x "$lust" ]; then
  echo "error: $lust not built. Run cargo build --release first."
  exit 2
fi
unset LUST_DAEMON_SOCKET LUST_CACHE_DIR LUST_NO_DAEMON LUST_NO_CACHE
work=$(mktemp -d)
pass=0
fail=0
ok() { pass=$((pass + 1)); echo "ok   $1"; }
bad() { fail=$((fail + 1)); echo "FAIL $1: $2"; }

sock() { local f; for f in "$1"/.lust-daemon-*.sock "$1"/.lust-daemon-*.sock.lock; do [ -e "$f" ] && { echo "${f%.lock}"; return; }; done; echo "$1/.lust-daemon-none.sock"; }
stop_daemon() {
  local pid
  pid=$(cat "$(sock "$1").lock" 2>/dev/null) || return 0
  [ -n "$pid" ] && kill "$pid" 2>/dev/null
  return 0
}
cleanup() {
  stop_daemon "$work/d"
  rm -rf "$work"
}
trap cleanup EXIT
wait_socket() {
  local i
  for i in $(seq 1 100); do [ -S "$(sock "$1")" ] && return 0; sleep 0.05; done
  return 1
}

d=$work/d
mkdir -p "$d"
cat >"$d/main.rs" <<'EOF'
include!("inc.rs");
fn main() { println!("{} {}", include_str!("data.txt"), value()); }
EOF
printf 'fn value() -> i32 { 1 }\n' >"$d/inc.rs"
printf 'one' >"$d/data.txt"

(cd "$d" && "$lust" build main.rs -o h1) >/dev/null 2>&1
if [ "$("$d/h1" 2>/dev/null)" = "one 1" ]; then ok "cold build reads the includes"; else bad "cold build" "want 'one 1', got '$("$d/h1" 2>&1 | head -2)'"; fi
if wait_socket "$d"; then ok "daemon is up"; else bad "daemon" "socket never appeared"; fi
(cd "$d" && "$lust" build main.rs -o h2) >/dev/null 2>&1
if [ "$("$d/h2" 2>/dev/null)" = "one 1" ]; then ok "daemon build repeats the answer"; else bad "daemon build" "want 'one 1', got '$("$d/h2" 2>&1 | head -2)'"; fi

printf 'fn value() -> i32 { 2 }\n' >"$d/inc.rs"
printf 'two' >"$d/data.txt"
(cd "$d" && "$lust" build main.rs -o h3) >/dev/null 2>&1
if [ "$("$d/h3" 2>/dev/null)" = "two 2" ]; then
  ok "edited includes change the daemon answer"
else
  bad "include edit" "want 'two 2', got '$("$d/h3" 2>&1 | head -2)' (stale expansion was reused)"
fi

rm "$d/data.txt"
if (cd "$d" && "$lust" build main.rs -o h4) >"$work/h4.log" 2>&1; then
  bad "deleted include" "build succeeded, want the L0803 error"
elif grep -q L0803 "$work/h4.log"; then
  ok "deleted include is the L0803 error, not a stale success"
else
  bad "deleted include" "build failed without L0803: $(head -2 "$work/h4.log")"
fi

echo "test-macro-deps: $pass passed, $fail failed"
[ "$fail" -eq 0 ]
