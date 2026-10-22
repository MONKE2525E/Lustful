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
  if [[ ${LUST_NATIVE_KEEP:-0} == 1 ]]; then
    echo "Native test artifacts: $work"
  else
    rm -rf "$work"
  fi
}
trap cleanup EXIT
cd "$work"

# No Rust fallback is allowed while building Lust targets in this script.
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
  local status=0
  timeout 30 "$lust" build main.rs -o "$label" > "$label.log" 2>&1 || status=$?
  if [[ "$status" != 0 ]]; then
    cat "$label.log"
    echo "FAIL $label build: status $status"
    return 1
  fi
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

# Primitive pointer imports: this run owns its socket, cache, and executables.
# Compare every overlay with a daemon-free build using a separate empty cache.
write_pointer_source() {
  local kind=$1 before=$2 after=$3 extra=$4
  local symbol pointee buffer argument
  case "$kind" in
    const) symbol=strlen; pointee='*const i8'; buffer='let text = *b"native\0";'; argument='text.as_ptr().cast::<i8>()' ;;
    mut) symbol=strlen; pointee='*mut i8'; buffer='let mut text = *b"native\0";'; argument='text.as_mut_ptr().cast::<i8>()' ;;
    wide) symbol=wcslen; pointee='*const i32'; buffer='let text = [110i32, 97, 116, 105, 118, 101, 0];'; argument='text.as_ptr()' ;;
    *) echo "FAIL unknown pointer source kind: $kind"; exit 1 ;;
  esac
  cat > main.rs <<RS
mod native {
    unsafe extern "C" {
        $before
        pub fn $symbol(text: $pointee) -> usize;
        $after
    }
}
use native::$symbol as chosen;
fn wrap<T>(_: T) -> usize {
    $buffer
    let ptr = $argument;
    let captured = unsafe { || chosen(ptr) };
    captured() + $extra
}
fn main() { println!("{}", wrap(1u32)); }
RS
}
wait_pointer_daemon() {
  for ((i=0; i<100; i++)); do
    [[ -S "$LUST_DAEMON_SOCKET" ]] && return
    sleep 0.1
  done
  echo 'FAIL pointer daemon did not start'
  exit 1
}
pointer_compare() {
  local label=$1 expected=$2
  build_run "$label" "$expected"
  LUST_NO_DAEMON=1 LUST_CACHE_DIR="$work/cache-fresh-$label" build_run "fresh-$label" "$expected"
}
pointer_base_library() {
  local dependencies
  dependencies=$(ldd "$1")
  [[ "$dependencies" == *libbase* ]] || { echo "FAIL $1: no daemon base library"; exit 1; }
}
pointer_reject() {
  local label=$1 code=$2 mode status
  # Check and build must both recheck; a timeout/crash is never rejection.
  for mode in check build; do
    status=0
    if [[ "$mode" == build ]]; then
      timeout 30 "$lust" build main.rs -o "$label-output" > "$label-$mode.log" 2>&1 || status=$?
    else
      timeout 30 "$lust" check main.rs > "$label-$mode.log" 2>&1 || status=$?
    fi
    [[ "$status" -eq 1 || "$status" -eq 2 ]] || { cat "$label-$mode.log"; echo "FAIL $label $mode: status $status"; exit 1; }
    grep -q "$code" "$label-$mode.log"
  done
  [[ ! -e "$label-output" ]]
  echo "PASS $label check/build rejected with $code"
}
write_pointer_source const '' '' 0
pointer_compare ptr-cold 6
wait_pointer_daemon
pointer_compare ptr-warm 6
pointer_base_library ptr-warm
# Keep every caller byte unchanged while editing only the native declaration.
# Invalid signatures are checked, never executed against libc.
cat > main.rs <<'RS'
unsafe extern "C" { fn strlen(text: *const i8) -> usize; }
fn wrap(p: *const i8) -> usize { unsafe { strlen(p) } }
fn main() { println!("{}", wrap(b"native\0".as_ptr().cast::<i8>())); }
RS
pointer_compare ptr-signature-baseline 6
cp main.rs signature-baseline.rs
sed -i '1s/\*const i8/\*mut i8/' main.rs
pointer_reject ptr-declaration-mutability L0110
LUST_NO_DAEMON=1 LUST_CACHE_DIR="$work/fresh-declaration-mutability" pointer_reject fresh-ptr-declaration-mutability L0110
cp signature-baseline.rs main.rs
pointer_compare ptr-declaration-restored 6
sed -i '1s/\*const i8/\*const i32/' main.rs
pointer_reject ptr-declaration-pointee L0110
LUST_NO_DAEMON=1 LUST_CACHE_DIR="$work/fresh-declaration-pointee" pointer_reject fresh-ptr-declaration-pointee L0110
cp signature-baseline.rs main.rs
pointer_compare ptr-declaration-restored-again 6
write_pointer_source const '' '' 1
pointer_compare ptr-body-edit 7
# strlen accepts readable char storage. A more restrictive mutable source
# signature still calls its correct C ABI with valid caller-owned storage.
write_pointer_source mut '' '' 0
pointer_compare ptr-constness-edit 6
cat > main.rs <<'RS'
unsafe extern "C" { fn strlen(text: *mut i8) -> usize; }
fn main() {
    let text = b"native\0";
    println!("{}", unsafe { strlen(text.as_ptr().cast::<i8>()) });
}
RS
pointer_reject ptr-const-wrong-caller L0110
LUST_NO_DAEMON=1 LUST_CACHE_DIR="$work/fresh-ptr-const-reject" pointer_reject fresh-ptr-const-wrong-caller L0110
write_pointer_source mut '' '' 0
pointer_compare ptr-mut-restored 6
# wchar_t is i32 on this suite's admitted x86_64 Linux GNU target.
# Do not call strlen with an invented i32 signature just to edit a pointee.
write_pointer_source wide '' '' 0
pointer_compare ptr-pointee-and-symbol-edit 6
cat > main.rs <<'RS'
unsafe extern "C" { fn wcslen(text: *const i32) -> usize; }
fn main() {
    let text = b"native\0";
    println!("{}", unsafe { wcslen(text.as_ptr().cast::<i8>()) });
}
RS
pointer_reject ptr-pointee-wrong-caller L0110
LUST_NO_DAEMON=1 LUST_CACHE_DIR="$work/fresh-ptr-pointee-reject" pointer_reject fresh-ptr-pointee-wrong-caller L0110
write_pointer_source wide 'pub fn abs(value: i32) -> i32;' '' 0
pointer_compare ptr-inserted 6
write_pointer_source wide '' 'pub fn abs(value: i32) -> i32;' 0
pointer_compare ptr-reordered 6
write_pointer_source wide '' '' 0
pointer_compare ptr-removed 6
write_pointer_source const '' '' 0
pointer_compare ptr-restored 6
cat > main.rs <<'RS'
unsafe extern "C" { fn strlen(text: *const i8) -> usize; }
fn main() { println!("{}", strlen(b"native\0".as_ptr().cast::<i8>())); }
RS
pointer_reject ptr-unsafe-wrong-caller L0404
LUST_NO_DAEMON=1 LUST_CACHE_DIR="$work/fresh-ptr-unsafe-reject" pointer_reject fresh-ptr-unsafe-wrong-caller L0404
cat > main.rs <<'RS'
unsafe extern "C" { fn strlen(text: *const i8) -> usize; }
const N: usize = unsafe { strlen(b"native\0".as_ptr().cast::<i8>()) };
fn main() { println!("{N}"); }
RS
pointer_reject ptr-const-eval L0630
LUST_NO_DAEMON=1 LUST_CACHE_DIR="$work/fresh-ptr-const-eval" pointer_reject fresh-ptr-const-eval L0630
write_pointer_source const '' '' 0
pointer_compare ptr-after-errors 6
rm -f "$LUST_DAEMON_SOCKET"
# Keep the original cache: restart must restore identities, not arena indices.
pointer_compare ptr-restarted 6
wait_pointer_daemon
pointer_compare ptr-restarted-warm 6
pointer_base_library ptr-restarted-warm
# Native writes must survive a warm daemon/cache path too.
cp "$root/tests/pass/native_ptr_roundtrip.rs" main.rs
pointer_compare ptr-buffer-cold 'pointer return and guarded buffer: ok'
pointer_compare ptr-buffer-warm 'pointer return and guarded buffer: ok'
cp "$root/tests/pass/native_ptr_gethostname.rs" main.rs
pointer_compare ptr-hostname 'gethostname buffer: ok'
bash "$root/scripts/test-native-link.sh"
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

[[ ! -e "$LUST_NATIVE_RUSTC_ATTEMPTS" ]] || { echo "FAIL rustc fallback attempted"; exit 1; }
echo 'PASS no rustc fallback attempted'
