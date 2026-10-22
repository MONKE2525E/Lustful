#!/usr/bin/env bash
# Real dependency builds under an execution audit; Cargo oracles are separate.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust="$root/target/release/lust"
work=$(mktemp -d "${TMPDIR:-/tmp}/lust-normal-graphs.XXXXXX")
if [[ ${KEEP_ARTIFACTS:-0} == 1 ]]; then
  echo "Normal graph audit artifacts: $work"
else
  trap 'rm -rf "$work"' EXIT
fi
export CARGO_TARGET_DIR="$work/target" LUST_CACHE_DIR="$work/cache" LUST_HOST_TOOLS=0 LUST_NO_DAEMON=1
export LUST_DAEMON_SOCKET="$work/daemon.sock"
mkdir -p "$work/pkg/src" "$work/pkg/leaf/src" "$work/deny"
strict() {
  local label=$1 expected=$2 code=$3 rc=0
  shift 3
  PATH="$work/deny:$PATH" RUSTC="$work/deny/rustc" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= \
    strace --kill-on-exit -f -qq -s 4096 -e trace=execve,execveat -o "$work/$label.trace" \
    "$@" > "$work/$label.log" 2>&1 || rc=$?
  [[ "$rc" == "$expected" ]] || { cat "$work/$label.log"; echo "FAIL $label: $rc"; exit 1; }
  if grep -Eq 'execve(at)?\(([^,]*, )?"([^"]*/)?rustc(-real)?",|execve(at)?\([^[]*\["([^"]*/)?rustc(-real)?"' "$work/$label.trace"; then
    cat "$work/$label.trace"; echo "FAIL $label: compiler invocation"; exit 1
  fi
  if [[ "$code" != none ]]; then grep -q "$code" "$work/$label.log"; fi
  echo "PASS normal graph $label"
}
cat > "$work/deny/rustc" <<'SH'
#!/bin/sh
echo 'unexpected rustc invocation' >&2
exit 97
SH
chmod +x "$work/deny/rustc"
cat > "$work/pkg/Cargo.toml" <<'TOML'
[package]
name = "normal-graph"
version = "0.1.0"
edition = "2024"
[workspace]
exclude = ["leaf"]
[dependencies]
leaf = { path = "leaf" }
journal = { package = "log", version = "=0.4.34", features = ["std"], optional = true }
[features]
default = ["use-log", "leaf/extra"]
use-log = ["dep:journal"]
TOML
cat > "$work/pkg/leaf/Cargo.toml" <<'TOML'
[package]
name = "leaf"
version = "0.1.0"
edition = "2024"
[workspace]
[features]
extra = []
TOML
cat > "$work/pkg/leaf/src/lib.rs" <<'RS'
#[cfg(feature = "extra")]
pub fn value() -> i32 { 42 }
#[cfg(not(feature = "extra"))]
pub fn value() -> i32 { 7 }
RS
cat > "$work/pkg/src/main.rs" <<'RS'
#[cfg(feature = "use-log")]
mod logging {
    struct Capture;
    static CAPTURE: Capture = Capture;
    impl journal::Log for Capture {
        fn enabled(&self, _: &journal::Metadata) -> bool { true }
        fn log(&self, record: &journal::Record) { println!("{} {}", record.level(), record.args()); }
        fn flush(&self) {}
    }
    pub fn run() {
        journal::set_logger(&CAPTURE).unwrap();
        journal::set_max_level(journal::LevelFilter::Info);
        journal::debug!("must stay hidden");
        journal::info!("leaf {}", leaf::value());
    }
}
#[cfg(feature = "use-log")]
fn main() { logging::run(); println!("value {}", leaf::value()); }
#[cfg(not(feature = "use-log"))]
fn main() { println!("value {}", leaf::value()); }
RS
cd "$work/pkg"
for mode in default plain logging all; do
  flags=()
  case "$mode" in
    plain) flags=(--no-default-features) ;;
    logging) flags=(--no-default-features --features use-log) ;;
    all) flags=(--all-features) ;;
  esac
  strict "$mode" 0 none "$lust" build src/main.rs --manifest-path Cargo.toml --bin normal-graph --offline -o "$work/$mode" "${flags[@]}"
  "$work/$mode" > "$work/$mode.out"
  # Independent compilation oracle, outside each strict process trace.
  CARGO_TARGET_DIR="$work/oracle" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= \
    cargo run --quiet --offline --locked "${flags[@]}" > "$work/$mode.oracle"
  cmp "$work/$mode.out" "$work/$mode.oracle"
done
[[ $(cat "$work/default.out") == $'INFO leaf 42\nvalue 42' ]]
[[ $(cat "$work/plain.out") == 'value 7' ]]
[[ $(cat "$work/logging.out") == $'INFO leaf 7\nvalue 7' ]]
cp Cargo.toml "$work/base.toml"
cp leaf/Cargo.toml "$work/leaf.toml"
cp src/main.rs "$work/main.rs"
# Package identity and the imported library name are separate Cargo concepts.
printf '\n[lib]\nname = "actual_leaf"\n' >> leaf/Cargo.toml
printf '%s\n' 'fn main() { println!("{}", actual_leaf::value()); }' > src/main.rs
strict custom-lib 0 none "$lust" build src/main.rs --manifest-path Cargo.toml --bin normal-graph --offline -o "$work/custom-lib"
CARGO_TARGET_DIR="$work/oracle" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= cargo run --quiet --offline --locked > "$work/custom-lib.oracle"
cmp <("$work/custom-lib") "$work/custom-lib.oracle"
printf '%s\n' 'fn main() { println!("{}", leaf::value()); }' > src/main.rs
strict reject-package-name 1 L0101 "$lust" check src/main.rs --manifest-path Cargo.toml --bin normal-graph --offline
if CARGO_TARGET_DIR="$work/oracle" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= cargo check --quiet --offline --locked > "$work/package-name.oracle" 2>&1; then
  echo 'FAIL package name unexpectedly imports a differently named library in Cargo'; exit 1
fi
sed -i 's/^leaf = { path/renamed = { package = "leaf", path/; s/"leaf\/extra"/"renamed\/extra"/' Cargo.toml
printf '%s\n' 'fn main() { println!("{}", renamed::value()); }' > src/main.rs
strict renamed-custom-lib 0 none "$lust" build src/main.rs --manifest-path Cargo.toml --bin normal-graph --offline -o "$work/renamed-custom-lib"
CARGO_TARGET_DIR="$work/oracle" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= cargo run --quiet --offline > "$work/renamed-custom-lib.oracle"
cmp <("$work/renamed-custom-lib") "$work/renamed-custom-lib.oracle"
cp "$work/base.toml" Cargo.toml
cp "$work/leaf.toml" leaf/Cargo.toml
cp "$work/main.rs" src/main.rs
for kind in root-script leaf-script macro dev target unsupported-feature; do
  cp "$work/base.toml" Cargo.toml
  cp "$work/leaf.toml" leaf/Cargo.toml
  rm -f build.rs leaf/build.rs
  code=L0532
  status=2
  flags=()
  case "$kind" in
    root-script) echo 'fn main() { panic!("must not run"); }' > build.rs ;;
    leaf-script) echo 'fn main() { panic!("must not run"); }' > leaf/build.rs ;;
    macro) printf '\n[lib]\nproc-macro = true\n' >> leaf/Cargo.toml ;;
    dev) printf '\n[dev-dependencies]\nlog = "=0.4.34"\n' >> Cargo.toml ;;
    target) printf '\n[target.\x27cfg(unix)\x27.dependencies]\nlog = "=0.4.34"\n' >> leaf/Cargo.toml ;;
    unsupported-feature) printf 'unsupported = ["journal/release_max_level_off"]\n' >> Cargo.toml; code=L0508; status=1; flags=(--features unsupported) ;;
  esac
  strict "reject-$kind" "$status" "$code" "$lust" check src/main.rs --manifest-path Cargo.toml --bin normal-graph --offline "${flags[@]}"
done
cp "$work/base.toml" Cargo.toml
cp "$work/leaf.toml" leaf/Cargo.toml
rm -f build.rs leaf/build.rs
# The same disk cache must not retain the rejected adapter feature.
strict restored 0 none "$lust" build src/main.rs --manifest-path Cargo.toml --bin normal-graph --offline -o "$work/restored"
cmp <("$work/restored") "$work/default.out"
# Trace the daemon through feature selections and a dependency manifest edit.
strict daemon-start 0 none env LUST_NO_DAEMON=0 LUST_DAEMON_IDLE=3 "$lust" build src/main.rs \
  --manifest-path Cargo.toml --bin normal-graph --offline -o "$work/daemon-app" &
daemon_audit=$!
for ((i=0; i<200; i++)); do
  [[ -S "$LUST_DAEMON_SOCKET" && -x "$work/daemon-app" ]] && break
  sleep 0.02
done
[[ -S "$LUST_DAEMON_SOCKET" && -x "$work/daemon-app" ]]
cmp <("$work/daemon-app") "$work/default.out"
strict daemon-features 0 none env LUST_NO_DAEMON=0 "$lust" build src/main.rs \
  --manifest-path Cargo.toml --bin normal-graph --offline --no-default-features -o "$work/daemon-plain"
cmp <("$work/daemon-plain") "$work/plain.out"
sed -i 's/42/45/' leaf/src/lib.rs
strict daemon-source 0 none env LUST_NO_DAEMON=0 "$lust" build src/main.rs \
  --manifest-path Cargo.toml --bin normal-graph --offline -o "$work/daemon-edited"
[[ $("$work/daemon-edited") == $'INFO leaf 45\nvalue 45' ]]
echo 'fn main() { panic!("must not run"); }' > leaf/build.rs
strict daemon-manifest 2 L0532 env LUST_NO_DAEMON=0 "$lust" check src/main.rs \
  --manifest-path Cargo.toml --bin normal-graph --offline
wait "$daemon_audit"
# External workspaces can supply inherited edition and dependency settings.
# Cover both ancestor discovery and an explicit package.workspace elsewhere.
for location in ancestor explicit; do
  base="$work/inherited-$location"
  mkdir -p "$base/app/src" "$base/shared/leaf/src" "$base/owner"
  cat > "$base/app/Cargo.toml" <<'TOML'
[package]
name = "inherited-app"
version = "0.1.0"
edition = "2024"
[workspace]
[dependencies]
leaf = { path = "../shared/leaf" }
TOML
  workspace="$base/shared/Cargo.toml"
  member=leaf
  if [[ "$location" == explicit ]]; then workspace="$base/owner/Cargo.toml"; member=../shared/leaf; fi
  printf '[workspace]\nmembers = ["%s"]\nresolver = "3"\n[workspace.package]\nedition = "2024"\n' "$member" > "$workspace"
  cat > "$base/shared/leaf/Cargo.toml" <<'TOML'
[package]
name = "leaf"
version = "0.1.0"
edition.workspace = true
TOML
  if [[ "$location" == explicit ]]; then printf 'workspace = "../../owner"\n' >> "$base/shared/leaf/Cargo.toml"; fi
  printf '%s\n' 'pub fn value() -> i32 { 42 }' > "$base/shared/leaf/src/lib.rs"
  printf '%s\n' 'fn main() { println!("{}", leaf::value()); }' > "$base/app/src/main.rs"
  CARGO_TARGET_DIR="$work/inherited-oracle" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= \
    cargo run --quiet --offline --manifest-path "$base/app/Cargo.toml" > "$base/oracle.out"
  export LUST_DAEMON_SOCKET="$base/daemon.sock"
  strict "inherited-$location-start" 0 none env LUST_NO_DAEMON=0 LUST_DAEMON_IDLE=3 "$lust" build "$base/app/src/main.rs" \
    --manifest-path "$base/app/Cargo.toml" --bin inherited-app --offline -o "$base/first" &
  daemon_audit=$!
  for ((i=0; i<200; i++)); do
    [[ -S "$LUST_DAEMON_SOCKET" && -x "$base/first" ]] && break
    sleep 0.02
  done
  [[ -S "$LUST_DAEMON_SOCKET" && -x "$base/first" ]]
  cmp <("$base/first") "$base/oracle.out"
  strict "inherited-$location-warm" 0 none env LUST_NO_DAEMON=0 "$lust" build "$base/app/src/main.rs" \
    --manifest-path "$base/app/Cargo.toml" --bin inherited-app --offline -o "$base/warm"
  sed -i 's/2024/2021/' "$workspace"
  strict "inherited-$location-edition" 1 L0530 env LUST_NO_DAEMON=0 "$lust" check "$base/app/src/main.rs" \
    --manifest-path "$base/app/Cargo.toml" --bin inherited-app --offline
  strict "inherited-$location-cold" 1 L0530 "$lust" check "$base/app/src/main.rs" \
    --manifest-path "$base/app/Cargo.toml" --bin inherited-app --offline
  sed -i 's/2021/2024/' "$workspace"
  strict "inherited-$location-restored" 0 none env LUST_NO_DAEMON=0 "$lust" build "$base/app/src/main.rs" \
    --manifest-path "$base/app/Cargo.toml" --bin inherited-app --offline -o "$base/restored"
  cmp <("$base/restored") "$base/oracle.out"
  wait "$daemon_audit"
done
# The requested package can itself select a non-ancestor workspace. Its
# governing lockfile must invalidate a ready daemon even without source edits.
base="$work/request-workspace"
mkdir -p "$base/shared/app/src" "$base/owner" "$base/leaf/src"
printf '[workspace]\nmembers = ["../shared/app"]\nresolver = "3"\n' > "$base/owner/Cargo.toml"
cat > "$base/shared/app/Cargo.toml" <<'TOML'
[package]
name = "lock-app"
version = "0.1.0"
edition = "2024"
workspace = "../../owner"
[dependencies]
leaf = { path = "../../leaf" }
TOML
printf '[package]\nname = "leaf"\nversion = "0.1.0"\nedition = "2024"\n[workspace]\n' > "$base/leaf/Cargo.toml"
printf '%s\n' 'pub fn value() -> i32 { 42 }' > "$base/leaf/src/lib.rs"
printf '%s\n' 'fn main() { println!("{}", leaf::value()); }' > "$base/shared/app/src/main.rs"
CARGO_TARGET_DIR="$work/lock-oracle" RUSTC_WRAPPER= RUSTC_WORKSPACE_WRAPPER= \
  cargo run --quiet --offline --manifest-path "$base/shared/app/Cargo.toml" > "$base/oracle.out"
cp "$base/owner/Cargo.lock" "$base/lock.saved"
export LUST_DAEMON_SOCKET="$base/daemon.sock"
strict request-lock-start 0 none env LUST_NO_DAEMON=0 LUST_DAEMON_IDLE=3 "$lust" build "$base/shared/app/src/main.rs" \
  --manifest-path "$base/shared/app/Cargo.toml" --bin lock-app --offline -o "$base/first" &
daemon_audit=$!
for ((i=0; i<200; i++)); do
  [[ -S "$LUST_DAEMON_SOCKET" && -x "$base/first" ]] && break
  sleep 0.02
done
[[ -S "$LUST_DAEMON_SOCKET" && -x "$base/first" ]]
strict request-lock-warm 0 none env LUST_NO_DAEMON=0 "$lust" check "$base/shared/app/src/main.rs" \
  --manifest-path "$base/shared/app/Cargo.toml" --bin lock-app --offline
printf 'invalid = [\n' > "$base/owner/Cargo.lock"
strict request-lock-edited 2 none env LUST_NO_DAEMON=0 "$lust" check "$base/shared/app/src/main.rs" \
  --manifest-path "$base/shared/app/Cargo.toml" --bin lock-app --offline
strict request-lock-cold 2 none "$lust" check "$base/shared/app/src/main.rs" \
  --manifest-path "$base/shared/app/Cargo.toml" --bin lock-app --offline
grep -q 'lock file' "$work/request-lock-edited.log"
grep -q 'lock file' "$work/request-lock-cold.log"
cp "$base/lock.saved" "$base/owner/Cargo.lock"
strict request-lock-restored 0 none env LUST_NO_DAEMON=0 "$lust" build "$base/shared/app/src/main.rs" \
  --manifest-path "$base/shared/app/Cargo.toml" --bin lock-app --offline -o "$base/restored"
cmp <("$base/restored") "$base/oracle.out"
wait "$daemon_audit"

# Exact registry replacement admission. No oracle or warm host output is
# prepared for these cases; each uses the existing refusing compiler audit.
json="$work/json"
mkdir -p "$json/src" "$json/leaf/src" "$json/host/src"
cat > "$json/src/main.rs" <<'RS'
use renamed_json::json;
fn main() {
    let value = json!({"name": "Verenu", "items": [1, true, null]});
    println!("{}", renamed_json::to_string(&value).unwrap());
}
RS
cat > "$json/leaf/Cargo.toml" <<'TOML'
[package]
name = "json-leaf"
version = "0.1.0"
edition = "2024"
[workspace]
[dependencies]
host = { package = "json-host", path = "../host" }
TOML
cat > "$json/host/Cargo.toml" <<'TOML'
[package]
name = "json-host"
version = "0.1.0"
edition = "2024"
[workspace]
TOML
printf '%s\n' 'pub fn value() -> i32 { 1 }' > "$json/leaf/src/lib.rs"
printf '%s\n' 'pub fn value() -> i32 { 1 }' > "$json/host/src/lib.rs"
json_manifest() {
  local version=$1 features=$2
  cat > "$json/Cargo.toml" <<TOML
[package]
name = "json-admission"
version = "0.1.0"
edition = "2024"
[workspace]
exclude = ["leaf", "host"]
[dependencies]
renamed_json = { package = "serde_json", version = "=$version", default-features = false, features = [$features] }
TOML
}
json_check() {
  local label=$1 status=$2 code=$3
  strict "json-$label" "$status" "$code" "$lust" check "$json/src/main.rs" \
    --manifest-path "$json/Cargo.toml" --bin json-admission --offline
}
for features in '"default", "std"' '"std"' '"alloc"' ''; do
  json_manifest 1.0.151 "$features"
  json_check "features-${features//[^a-z]/}" 0 none
done
for feature in raw_value preserve_order arbitrary_precision float_roundtrip unbounded_depth; do
  json_manifest 1.0.151 "\"std\", \"$feature\""
  json_check "reject-$feature" 2 L0508
  if [[ $feature == preserve_order ]]; then
    grep -Eq 'feature `(preserve_order|indexmap)`' "$work/json-reject-$feature.log"
  else
    grep -q "feature .*$feature" "$work/json-reject-$feature.log"
  fi
done
# Cargo itself rejects unknown upstream features, before adapter admission.
json_manifest 1.0.151 '"unknown_lust_feature"'
json_check reject-unknown 2 none
grep -q 'metadata.*failed' "$work/json-reject-unknown.log"
# Requires this real registry version and its source in the offline cache.
json_manifest 1.0.150 '"std"'
json_check reject-version 2 L0508
grep -q 1.0.150 "$work/json-reject-version.log"
json_manifest 1.0.151 '"std"'
json_check restored 0 none
strict json-runtime 0 none "$lust" build "$json/src/main.rs" \
  --manifest-path "$json/Cargo.toml" --bin json-admission --offline -o "$json/runtime"
strict json-runtime-run 0 none "$json/runtime"
[[ $(cat "$work/json-runtime-run.log") == '{"items":[1,true,null],"name":"Verenu"}' ]]

# JSON must not hide a non-replaced transitive host package on another edge.
printf 'leaf = { package = "json-leaf", path = "leaf" }\n' >> "$json/Cargo.toml"
echo 'fn main() { panic!("must not run"); }' > "$json/host/build.rs"
json_check reject-transitive-buildscript 2 L0532
rm "$json/host/build.rs"
printf '\n[build-dependencies]\nlog = "=0.4.34"\n' >> "$json/host/Cargo.toml"
json_check reject-transitive-builddep 2 L0532
sed -i '/^\[build-dependencies\]/,$d' "$json/host/Cargo.toml"
printf '\n[lib]\nproc-macro = true\n' >> "$json/host/Cargo.toml"
json_check reject-transitive-procmacro 2 L0532
sed -i '/^\[lib\]/,$d' "$json/host/Cargo.toml"
json_check restored-transitive 0 none

# Same daemon: dependency manifest features change without touching the root
# manifest. This exercises graph watch invalidation, not just request keys.
json_manifest 1.0.151 '"std"'
printf 'leaf = { package = "json-leaf", path = "leaf" }\n' >> "$json/Cargo.toml"
printf '\nserde_json = { version = "=1.0.151", features = ["std"] }\n' >> "$json/leaf/Cargo.toml"
export LUST_DAEMON_SOCKET="$json/daemon.sock"
strict json-daemon-start 0 none env LUST_NO_DAEMON=0 LUST_DAEMON_IDLE=10 "$lust" build "$json/src/main.rs" \
  --manifest-path "$json/Cargo.toml" --bin json-admission --offline -o "$json/first" &
daemon_audit=$!
for ((i=0; i<200; i++)); do
  [[ -S "$LUST_DAEMON_SOCKET" && -x "$json/first" ]] && break
  sleep 0.02
done
[[ -S "$LUST_DAEMON_SOCKET" && -x "$json/first" ]]
sed -i 's/features = \["std"\]/features = ["std", "raw_value"]/' "$json/leaf/Cargo.toml"
strict json-daemon-feature-reject 2 L0508 env LUST_NO_DAEMON=0 "$lust" check "$json/src/main.rs" \
  --manifest-path "$json/Cargo.toml" --bin json-admission --offline
sed -i 's/"std", "raw_value"/"std"/' "$json/leaf/Cargo.toml"
strict json-daemon-restored 0 none env LUST_NO_DAEMON=0 "$lust" check "$json/src/main.rs" \
  --manifest-path "$json/Cargo.toml" --bin json-admission --offline
echo 'fn main() { panic!("must not run"); }' > "$json/host/build.rs"
strict json-daemon-transitive-reject 2 L0532 env LUST_NO_DAEMON=0 "$lust" check "$json/src/main.rs" \
  --manifest-path "$json/Cargo.toml" --bin json-admission --offline
rm "$json/host/build.rs"
wait "$daemon_audit"

echo 'PASS normal graph outputs match independent Cargo builds; host routes remain refused'
