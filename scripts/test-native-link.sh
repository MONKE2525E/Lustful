#!/usr/bin/env bash
# Focused strict-base publication checks. Requires an already built compiler.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust="$root/target/release/lust"
work=$(mktemp -d)
cleanup() {
  rm -f "$work"/*.sock
  if [[ ${LUST_NATIVE_KEEP:-0} == 1 ]]; then
    echo "Native link artifacts: $work"
  else
    rm -rf "$work"
  fi
}
trap cleanup EXIT
unset LUST_NO_DAEMON LUST_NO_CACHE
export LUST_DAEMON_IDLE=60
mkdir "$work/deny"
export LUST_NATIVE_RUSTC_ATTEMPTS="$work/rustc-attempts"
cat > "$work/deny/rustc" <<'SH'
#!/bin/sh
printf '%s\n' 'unexpected rustc invocation' >> "$LUST_NATIVE_RUSTC_ATTEMPTS"
exit 99
SH
chmod +x "$work/deny/rustc"
export PATH="$work/deny:$PATH" RUSTC="$work/deny/rustc" \
  RUSTC_WRAPPER="$work/deny/rustc" RUSTC_WORKSPACE_WRAPPER="$work/deny/rustc"
fail() { echo "FAIL $*"; exit 1; }
wait_daemon() {
  for ((i=0; i<100; i++)); do
    [[ -S "$LUST_DAEMON_SOCKET" ]] && return
    sleep 0.1
  done
  fail 'daemon did not start'
}
write_source() {
  local missing=$1 extra=$2 growth=${3:-0} call
  if [[ $kind == scalar ]]; then
    call='abs(-17) as usize'
    [[ $missing == 0 ]] || call='lustenu_missing_native_symbol(-17) as usize'
    cat > main.rs <<'RS'
unsafe extern "C" {
    fn abs(value: i32) -> i32;
    fn lustenu_missing_native_symbol(value: i32) -> i32;
}
RS
  else
    call='strlen(b"native\0".as_ptr().cast::<i8>())'
    [[ $missing == 0 ]] || call='lustenu_missing_pointer_symbol(b"native\0".as_ptr().cast::<i8>()).is_null() as usize'
    cat > main.rs <<'RS'
unsafe extern "C" {
    fn strlen(text: *const i8) -> usize;
    fn lustenu_missing_pointer_symbol(text: *const i8) -> *mut i8;
}
RS
  fi
  printf 'fn wrap() -> usize { (unsafe { %s }) + %s }\n' "$call" "$extra" >> main.rs
  # Keep padding functions reachable so each requires a function-table slot.
  for ((j=0; j<growth; j++)); do
    printf 'fn pad%s() -> usize { 0 }\n' "$j" >> main.rs
  done
  printf 'fn main() { println!("{}", wrap()' >> main.rs
  for ((j=0; j<growth; j++)); do printf ' + pad%s()' "$j" >> main.rs; done
  printf '); }\n' >> main.rs
}
build_run() {
  local label=$1 expected=$2 status=0 actual
  local emit=()
  [[ $# -lt 3 ]] || emit=(--emit-c "$3")
  timeout 30 "$lust" build main.rs --timings "${emit[@]}" -o "$label" > "$label.log" 2>&1 || status=$?
  [[ $status == 0 ]] || { cat "$label.log"; fail "$label build status $status"; }
  actual=$(timeout 5 "./$label")
  [[ $actual == "$expected" ]] || fail "$label expected $expected, got $actual"
}
base_name() {
  local name
  # Inspect dependencies without loading the program being tested.
  name=$(readelf -d "$1" | sed -n 's/.*Shared library: \[\(libbase[^]]*\.so\)\].*/\1/p')
  [[ -n $name && $name != *$'\n'* ]] || fail "$1 has no unique daemon base"
  printf '%s' "$name"
}
bases() { find "$LUST_CACHE_DIR/bases" -maxdepth 1 -name 'libbase*.so' -printf '%f\n' | sort; }
reject_missing() {
  local label=$1 status=0 before after
  before=$(bases)
  timeout 30 "$lust" check main.rs > "$label-check.log" 2>&1 || { cat "$label-check.log"; fail "$label check failed"; }
  [[ ! -e $label ]] || fail "$label output already exists"
  timeout 30 "$lust" build main.rs -o "$label" > "$label.log" 2>&1 || status=$?
  [[ $status == 3 ]] || { cat "$label.log"; fail "$label expected link status 3, got $status"; }
  grep -q "$missing_symbol" "$label.log" || { cat "$label.log"; fail "$label missing symbol diagnostic"; }
  [[ ! -e $label ]] || fail "$label published an executable"
  after=$(bases)
  [[ $before == "$after" ]] || fail "$label published a base after rejection"
  [[ -z $(find "$LUST_CACHE_DIR/bases" -maxdepth 1 \( -name '*.check*' -o -name 'libbase-tmp-*' \) -print) ]] || fail "$label left a link temporary"
  echo "PASS $kind $label: check succeeds, build rejects with code 3 and no output"
}
for kind in scalar pointer; do
  mkdir "$work/$kind"
  cd "$work/$kind"
  export LUST_CACHE_DIR="$work/$kind/cache" LUST_DAEMON_SOCKET="$work/$kind.sock"
  mkdir -p "$LUST_CACHE_DIR/bases"
  if [[ $kind == scalar ]]; then expected=17; missing_symbol=lustenu_missing_native_symbol
  else expected=6; missing_symbol=lustenu_missing_pointer_symbol; fi
  write_source 1 0
  LUST_NO_DAEMON=1 reject_missing cold-missing
  write_source 0 0
  build_run startup "$expected"
  wait_daemon
  # This daemon has not built a base yet. Missing objects may already be cached.
  write_source 1 0
  reject_missing fresh-base-missing
  write_source 0 0
  build_run recovered "$expected"
  original=$(base_name recovered)
  write_source 0 1
  build_run overlay "$((expected + 1))"
  [[ $(base_name overlay) == "$original" ]] || fail 'body edit rebuilt base'
  grep -Eq ' [1-9][0-9]* overlays,' overlay.log || fail 'no overlay exercised'
  [[ -f "$LUST_CACHE_DIR/bases/$original" ]] || fail 'base not in test-owned cache'
  rm "$LUST_CACHE_DIR/bases/$original"
  # Keep existing overlays and add a new edit while restoring the old base.
  write_source 0 2
  build_run restored "$((expected + 2))"
  [[ $(base_name restored) == "$original" ]] || fail 'restoration changed base generation'
  grep -Eq ' [1-9][0-9]* overlays,' restored.log || fail 'restoration lost overlays'
  [[ -f "$LUST_CACHE_DIR/bases/$original" ]] || fail 'base not restored'
  echo "PASS $kind valid base restoration with existing overlays"
  write_source 1 2
  reject_missing overlay-missing
  write_source 0 3
  build_run recovered-overlay "$((expected + 3))" recovery.c
  base_name recovered-overlay > /dev/null
  # Read the actual table capacity, rather than assuming the library's slot
  # count. More new reachable functions than that capacity forces a base rebuild.
  capacity=$(sed -n 's/^lust_fnptr lust_fns\[\([0-9][0-9]*\)\];$/\1/p' recovery.c.u3.c)
  [[ $capacity =~ ^[0-9]+$ ]] || fail 'cannot read baseline table capacity'
  growth=$((capacity + 1))
  write_source 1 3 "$growth"
  reject_missing growth-missing
  write_source 0 4 "$growth"
  build_run recovered-growth "$((expected + 4))"
  [[ $(base_name recovered-growth) != $(base_name recovered-overlay) ]] || fail 'growth did not change base'
  # Stop only this test's daemon. A different socket avoids a shutdown race;
  # retain the disk cache, including missing-symbol objects from failed builds.
  rm -f "$LUST_DAEMON_SOCKET"
  export LUST_DAEMON_SOCKET="$work/$kind-restart.sock"
  timeout 30 "$lust" check main.rs > restart-check.log 2>&1
  wait_daemon
  write_source 1 4 "$growth"
  reject_missing restarted-missing
  write_source 0 5 "$growth"
  build_run recovered-restart "$((expected + 5))"
  base_name recovered-restart > /dev/null
  echo "PASS $kind recovery after each rejected build"
  rm -f "$LUST_DAEMON_SOCKET"
done
[[ ! -e "$LUST_NATIVE_RUSTC_ATTEMPTS" ]] || fail 'rustc fallback attempted'
echo 'PASS native link validation without rustc fallback'
