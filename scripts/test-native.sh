#!/usr/bin/env bash
# Native-call cold/daemon/cache regression checks. Build the compiler first.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust="$root/target/release/lust"
work=$(mktemp -d)
export LUST_DAEMON_SOCKET="$work/daemon.sock" LUST_CACHE_DIR="$work/cache" LUST_DAEMON_IDLE=30
unset LUST_NO_DAEMON LUST_NO_CACHE
cleanup() {
  # Removing this test's unique socket terminates only its own daemon.
  rm -f "$LUST_DAEMON_SOCKET"
  rm -rf "$work"
}
trap cleanup EXIT
cd "$work"
write_source() {
  local symbol=$1 before=$2 after=$3
  cat > main.rs <<RS
mod native {
    unsafe extern "C" {
        $before
        pub fn $symbol(value: i32) -> i32;
        $after
    }
}
use native::$symbol as chosen;
fn wrap<T>(_: T) -> i32 { unsafe { chosen(97) } }
fn main() { println!("{}", wrap(1u32)); }
RS
}
build_run() {
  local label=$1 expected=$2
  timeout 30 "$lust" build main.rs -o "$label" > "$label.log" 2>&1
  local actual
  actual=$(timeout 5 "./$label")
  [[ "$actual" == "$expected" ]] || { cat "$label.log"; echo "FAIL $label: expected $expected, got $actual"; exit 1; }
  echo "PASS $label"
}
write_source toupper '' ''
build_run cold 65
for ((i=0; i<100; i++)); do
  [[ -S "$LUST_DAEMON_SOCKET" ]] && break
  sleep 0.1
done
[[ -S "$LUST_DAEMON_SOCKET" ]]
build_run warm 65
dependencies=$(ldd warm)
[[ "$dependencies" == *libbase* ]] || { echo 'FAIL warm: no daemon base library'; exit 1; }
write_source toupper 'pub fn abs(value: i32) -> i32;' ''
build_run inserted 65
write_source toupper '' 'pub fn abs(value: i32) -> i32;'
build_run reordered 65
write_source tolower '' ''
build_run retargeted 97
write_source toupper '' ''
build_run restored 65
rm -f "$LUST_DAEMON_SOCKET"
LUST_NO_DAEMON=1 build_run restarted 65
cat > main.rs <<'RS'
unsafe extern "C" { fn lustenu_missing_native_symbol() -> i32; }
fn main() { println!("{}", unsafe { lustenu_missing_native_symbol() }); }
RS
if LUST_NO_DAEMON=1 timeout 30 "$lust" build main.rs -o missing > missing.log 2>&1; then
  echo 'FAIL missing native symbol linked'
  exit 1
fi
[[ ! -e missing ]]
grep -q 'lustenu_missing_native_symbol' missing.log
echo 'PASS missing symbol fails to link'
cat > main.rs <<'RS'
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() { println!("{}", unsafe { abs(-17) }); }
RS
if LUST_NO_DAEMON=1 timeout 30 "$lust" check main.rs --target aarch64-unknown-linux-gnu > target.log 2>&1; then
  echo 'FAIL unsupported native target accepted'
  exit 1
fi
grep -q L0810 target.log
echo 'PASS unsupported target rejected'
if LUST_NO_DAEMON=1 timeout 30 "$lust" build main.rs --release --target x86_64-unknown-linux-gnu -o cc-output > backend.log 2>&1; then
  echo 'FAIL unsupported native backend accepted'
  exit 1
fi
[[ ! -e cc-output ]]
grep -q L0810 backend.log
echo 'PASS unsupported backend rejected'
