#!/usr/bin/env bash
# Build Lust first. Strict cases trace attempted execs; the explicitly marked
# host-enabled cases prepare real Cargo outputs to test warm-cache rejection.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust="$root/target/release/lust"
core="$root/target/release/lust-core"
work=$(mktemp -d)
export LUST_DAEMON_SOCKET="$work/daemon.sock" LUST_CACHE_DIR="$work/cache" LUST_DAEMON_IDLE=30
export CARGO_TARGET_DIR="$work/target"
export LUST_HOST_TOOLS=0
unset LUST_NO_CACHE LUST_NO_DAEMON LUST_PROBE_FAKE_DIR
trap 'rm -f "$LUST_DAEMON_SOCKET"; rm -rf "$work"' EXIT
mkdir -p "$work/pkg/src" "$work/deny" "$work/target"
cat > "$work/deny/rustc" <<'SH'
#!/bin/sh
echo 'unexpected rustc invocation' >&2
exit 97
SH
chmod +x "$work/deny/rustc"
cp "$work/deny/rustc" "$work/deny/rustc-real"
cat > "$work/pkg/Cargo.toml" <<'TOML'
[package]
name = "policy"
version = "0.1.0"
edition = "2024"
[workspace]
[features]
default = ["a"]
a = ["b"]
b = []
TOML
cat > "$work/pkg/src/main.rs" <<'RS'
#[cfg(all(feature = "a", feature = "b"))]
fn main() { println!("features"); }
#[cfg(not(all(feature = "a", feature = "b")))]
fn main() { println!("plain"); }
RS
cat > "$work/main.rs" <<'RS'
fn main() { println!("standalone"); }
#[test] fn arithmetic() { assert_eq!(2 + 2, 4); }
RS
cd "$work"
has_rustc() {
  grep -Eq 'execve(at)?\(([^,]*, )?"([^"]*/)?rustc(-real)?",|execve(at)?\([^[]*\["([^"]*/)?rustc(-real)?"' "$1"
}
# Positive control: the sentinel is a shell script, not the Rust compiler.
# It must nevertheless count as an attempted rustc execution.
rc=0
strace -f -qq -s 4096 -e trace=execve,execveat -o detector.trace "$work/deny/rustc" > detector.log 2>&1 || rc=$?
[[ "$rc" == 97 ]] && has_rustc detector.trace
echo 'PASS execution detector positive control'
strict() {
  local label=$1 expected=$2
  shift 2
  local rc=0
  PATH="$work/deny:$PATH" RUSTC="$work/deny/rustc" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= \
    LUST_NO_DAEMON=1 strace --kill-on-exit -f -qq -s 4096 -e trace=execve,execveat -o "$label.trace" \
    "$@" > "$label.log" 2>&1 || rc=$?
  [[ "$rc" == "$expected" ]] || { cat "$label.log"; echo "FAIL $label: exit $rc, expected $expected"; exit 1; }
  if has_rustc "$label.trace"; then
    cat "$label.trace"; echo "FAIL $label: attempted rustc"; exit 1
  fi
  if [[ "$expected" == 2 ]]; then grep -q L0532 "$label.log"; fi
  echo "PASS strict $label"
}
strict check 0 "$lust" check main.rs
strict build 0 "$lust" build main.rs -o standalone
[[ $(./standalone) == standalone ]]
strict run 0 "$lust" run main.rs
strict test 0 "$lust" test main.rs
strict manifest 0 "$lust" build pkg/src/main.rs --manifest-path pkg/Cargo.toml --bin policy -o package
[[ $(./package) == features ]]
strict no-default 0 "$lust" build pkg/src/main.rs --manifest-path pkg/Cargo.toml --bin policy --no-default-features -o package-none
[[ $(./package-none) == plain ]]
strict selected 0 "$lust" build pkg/src/main.rs --manifest-path pkg/Cargo.toml --bin policy --no-default-features --features a -o package-a
[[ $(./package-a) == features ]]
strict release 2 "$lust" build main.rs --release
strict profile 2 "$lust" build main.rs --profile release
strict oracle 2 "$lust" check main.rs --rustc
strict core-release 2 "$core" build main.rs --release
strict core-oracle 2 "$core" check main.rs --rustc

# A wrapper request must neither write dep-info nor delete an existing rmeta.
mkdir deps
echo sentinel > deps/libpolicy.rmeta
strict wrapper 2 env LUST_PROBE_FAKE_DIR="$work/deps" "$core" "$work/deny/rustc" \
  --crate-name policy --out-dir "$work/deps" --emit=dep-info,metadata
[[ $(cat deps/libpolicy.rmeta) == sentinel && ! -e deps/policy.d ]]

# Host-enabled preparation is intentional here, outside the strict audit.
# Start this test's daemon with Allow, then send Forbid on the same socket.
cp pkg/Cargo.toml base.toml
cat > pkg/build.rs <<'RS'
fn main() { println!("cargo::rustc-env=POLICY_HOST_OUTPUT=prepared"); }
RS
cat > pkg/src/main.rs <<'RS'
fn main() { println!("{}", env!("POLICY_HOST_OUTPUT")); }
RS
strict build-script 2 "$lust" check pkg/src/main.rs --manifest-path pkg/Cargo.toml --bin policy
CARGO_TARGET_DIR="$work/target" LUST_HOST_TOOLS=1 "$lust" build pkg/src/main.rs \
  --manifest-path pkg/Cargo.toml --bin policy -o host-built > host-build.log 2>&1 || { cat host-build.log; exit 1; }
[[ $(./host-built) == prepared ]]
[[ -S "$LUST_DAEMON_SOCKET" ]]
rc=0
LUST_HOST_TOOLS=0 "$lust" check pkg/src/main.rs --manifest-path pkg/Cargo.toml --bin policy > daemon-forbid.log 2>&1 || rc=$?
[[ "$rc" == 2 ]] && grep -q L0532 daemon-forbid.log
strict warm-build-script 2 "$lust" check pkg/src/main.rs --manifest-path pkg/Cargo.toml --bin policy
echo 'PASS daemon policy separation and warm host-output rejection'

rm pkg/build.rs
cp base.toml pkg/Cargo.toml
mkdir -p pkg/dep/src
cat > pkg/dep/Cargo.toml <<'TOML'
[package]
name = "dep"
version = "0.1.0"
edition = "2024"
TOML
echo 'pub fn value() -> i32 { 7 }' > pkg/dep/src/lib.rs
printf '\n[dependencies]\ndep = { path = "dep" }\n' >> pkg/Cargo.toml
echo 'fn main() { println!("{}", dep::value()); }' > pkg/src/main.rs
strict dependency 2 "$lust" check pkg/src/main.rs --manifest-path pkg/Cargo.toml --bin policy
CARGO_TARGET_DIR="$work/target" "$lust" build pkg/src/main.rs --manifest-path pkg/Cargo.toml \
  --bin policy --host-tools -o host-dep > host-dep.log 2>&1 || { cat host-dep.log; exit 1; }
[[ $(./host-dep) == 7 ]]
strict warm-features 2 "$lust" check pkg/src/main.rs --manifest-path pkg/Cargo.toml --bin policy
echo 'PASS host-tools policy (host-enabled cases are not rustc-free)'
