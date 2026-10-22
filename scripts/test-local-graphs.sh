#!/usr/bin/env bash
# The strict target builds use a refusing compiler and an execution trace.
# Cargo builds only the separate comparison oracle at the end.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust="$root/target/release/lust"
work=$(mktemp -d)
export LUST_DAEMON_SOCKET="$work/daemon.sock" LUST_CACHE_DIR="$work/cache" LUST_DAEMON_IDLE=30
export CARGO_TARGET_DIR="$work/target" LUST_HOST_TOOLS=0 LUST_NO_DAEMON=1
unset LUST_NO_CACHE LUST_PROBE_FAKE_DIR
trap 'rm -f "$LUST_DAEMON_SOCKET"; rm -rf "$work"' EXIT
mkdir -p "$work/ws/app/src" "$work/ws/middle/src" "$work/ws/leaf/src" "$work/deny"
mkdir -p "$work/external/src"
cat > "$work/external/Cargo.toml" <<'TOML'
[package]
name = "external"
version = "0.1.0"
edition = "2024"
[workspace]
TOML
echo 'pub fn value() -> i32 { 1 }' > "$work/external/src/lib.rs"
cat > "$work/deny/rustc" <<'SH'
#!/bin/sh
echo 'unexpected rustc invocation' >&2
exit 97
SH
chmod +x "$work/deny/rustc"
cat > "$work/ws/Cargo.toml" <<'TOML'
[workspace]
members = ["app", "middle", "leaf"]
resolver = "2"
TOML
for name in app middle leaf; do
  cat > "$work/ws/$name/Cargo.toml" <<TOML
[package]
name = "$name"
version = "0.1.0"
edition = "2024"
TOML
done
cat >> "$work/ws/app/Cargo.toml" <<'TOML'
[dependencies]
renamed = { package = "middle", path = "../middle" }
TOML
cat >> "$work/ws/middle/Cargo.toml" <<'TOML'
[dependencies]
leaf = { path = "../leaf" }
TOML
echo 'pub fn value() -> i32 { 41 }' > "$work/ws/leaf/src/lib.rs"
echo 'pub fn value() -> i32 { leaf::value() + 1 }' > "$work/ws/middle/src/lib.rs"
echo 'fn main() { println!("{}", renamed::value()); }' > "$work/ws/app/src/main.rs"
cd "$work/ws"
strict() {
  local label=$1 expected=$2 rc=0
  shift 2
  PATH="$work/deny:$PATH" RUSTC="$work/deny/rustc" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= \
    strace --kill-on-exit -f -qq -s 4096 -e trace=execve,execveat -o "$work/$label.trace" \
    "$@" > "$work/$label.log" 2>&1 || rc=$?
  [[ "$rc" == "$expected" ]] || { cat "$work/$label.log"; echo "FAIL $label: $rc"; exit 1; }
  if grep -Eq 'execve(at)?\(([^,]*, )?"([^"]*/)?rustc(-real)?",|execve(at)?\([^[]*\["([^"]*/)?rustc(-real)?"' "$work/$label.trace"; then
    cat "$work/$label.trace"; echo "FAIL $label: compiler invocation"; exit 1
  fi
  if [[ "$expected" == 2 ]]; then grep -q L0532 "$work/$label.log"; fi
  echo "PASS local graph $label"
}
build() {
  strict "$1" 0 "$lust" build app/src/main.rs --manifest-path Cargo.toml --bin app -p app -o "$work/app"
}
build transitive-renamed
[[ $("$work/app") == 42 ]]
# A source edit must be visible through the same disk cache.
echo 'pub fn value() -> i32 { 51 }' > leaf/src/lib.rs
build warm-source
[[ $("$work/app") == 52 ]]
cp leaf/Cargo.toml "$work/leaf.toml"
cp app/Cargo.toml "$work/app.toml"
for kind in features script macro optional version target registry cycle aliases external; do
  cp "$work/leaf.toml" leaf/Cargo.toml
  cp "$work/app.toml" app/Cargo.toml
  rm -f leaf/build.rs
  case "$kind" in
    features) printf '\n[features]\nextra = []\n' >> leaf/Cargo.toml ;;
    script) echo 'fn main() {}' > leaf/build.rs ;;
    macro) printf '\n[lib]\nproc-macro = true\n' >> leaf/Cargo.toml ;;
    optional) sed -i 's/path = "..\/middle"/path = "..\/middle", optional = true/' app/Cargo.toml ;;
    version) sed -i 's/path = "..\/middle"/path = "..\/middle", version = "0.1"/' app/Cargo.toml ;;
    target) sed -i 's/\[dependencies\]/[target.\x27cfg(unix)\x27.dependencies]/' app/Cargo.toml ;;
    registry) printf 'log = "0.4"\n' >> app/Cargo.toml ;;
    cycle) printf '\n[dependencies]\nmiddle = { path = "../middle" }\n' >> leaf/Cargo.toml ;;
    aliases) printf 'other = { package = "middle", path = "../middle" }\n' >> app/Cargo.toml ;;
    external) printf '\n[dependencies]\nexternal = { path = "../../external" }\n' >> leaf/Cargo.toml ;;
  esac
  strict "reject-$kind" 2 "$lust" check app/src/main.rs --manifest-path Cargo.toml --bin app -p app
done
rm -f leaf/build.rs
cp "$work/leaf.toml" leaf/Cargo.toml
cp "$work/app.toml" app/Cargo.toml
build restored
[[ $("$work/app") == 52 ]]
# Keep one traced daemon alive across source and manifest changes. The first
# trace follows the daemon; later traces follow clients connecting to it.
strict daemon-start 0 env LUST_NO_DAEMON=0 LUST_DAEMON_IDLE=3 "$lust" build app/src/main.rs \
  --manifest-path Cargo.toml --bin app -p app -o "$work/daemon-app" &
daemon_audit=$!
for ((i=0; i<150; i++)); do
  [[ -S "$LUST_DAEMON_SOCKET" && -x "$work/daemon-app" ]] && break
  sleep 0.02
done
[[ -S "$LUST_DAEMON_SOCKET" && -x "$work/daemon-app" ]]
[[ $("$work/daemon-app") == 52 ]]
echo 'pub fn value() -> i32 { 61 }' > leaf/src/lib.rs
strict daemon-source 0 env LUST_NO_DAEMON=0 "$lust" build app/src/main.rs \
  --manifest-path Cargo.toml --bin app -p app -o "$work/app"
[[ $("$work/app") == 62 ]]
printf '\n[features]\nextra = []\n' >> leaf/Cargo.toml
strict daemon-manifest 2 env LUST_NO_DAEMON=0 "$lust" check app/src/main.rs \
  --manifest-path Cargo.toml --bin app -p app
wait "$daemon_audit"
cp "$work/leaf.toml" leaf/Cargo.toml
# This is the independent oracle, outside all strict traces and caches.
CARGO_TARGET_DIR="$work/oracle" cargo run --quiet --manifest-path Cargo.toml -p app > "$work/oracle.out"
"$work/app" > "$work/lust.out"
cmp "$work/oracle.out" "$work/lust.out"
echo 'PASS local source graph output matches independent Cargo oracle'
