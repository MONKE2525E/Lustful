#!/usr/bin/env bash
# Crate fixture tests (docs/ARCH.md sections 1.1, 9.2 S6, 9.3 runner table):
# every directory in tests/crates/ is a small Cargo package. Each fixture is
# built by Cargo (the oracle) and by lust from its crate root file, then both
# binaries run and stdout plus exit status must match.
#
# Per-fixture selections live in the fixture's optional fixture.txt, one
# key=value per line (# starts a comment):
#   bin=<name>        bin target to build (default: the package name)
#   root=<path>       crate root file for the lust build (default: src/main.rs)
#   manifest=<path>   manifest for both builds, relative to the fixture
#                     root (default: Cargo.toml). Workspace fixtures name
#                     the bin package's manifest here.
#   features=<a,b>    passed to cargo and to lust as --features
#   target=<triple>   passed to cargo and to lust as --target; the value
#                     `host` means the rustc host triple. No line = no flag.
#   args=<words>      program arguments (split on spaces; no quoting)
#   stderr=exact      also compare the program's stderr, with the thread id
#                     of a panic line masked (panic location fixtures; the
#                     package sets panic = "abort" so the exits match)
#   expect=<L####>    negative fixture: lust must reject with this code.
#                     Cargo must also reject unless the line cargo=pass is
#                     present (valid Rust lust rejects on purpose).
# The lust build names the same crate to the compiler:
#   lust build <root> --manifest-path <Cargo.toml> --bin <bin> [--features ..] [--target ..]
# Lust loads the crate through the Cargo graph and its module files
# (W-RESOLVE), so fixtures are real multi-file crates.
#
# Usage: scripts/test-crates.sh [filter]
#   SANITIZE=1 also builds the lust-generated C with gcc
#   -fsanitize=address,undefined and runs it, as difftest does.
# A missing tests/crates dir or an empty one fails the run; it never skips.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
fixtures=$root/tests/crates
if [ ! -x "$lust" ]; then
  echo "error: $lust not built. Run cargo build --release first."
  exit 2
fi
if [ ! -d "$fixtures" ]; then
  echo "error: fixture dir $fixtures is missing"
  exit 2
fi
if ! command -v timeout >/dev/null; then
  echo "error: timeout command not found (per-case timeout needs it)"
  exit 2
fi
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
# Cold, cache-free lust builds: daemon routing has its own gate in smoke.py.
export LUST_NO_DAEMON=1
export LUST_DAEMON_SOCKET="$work/no-daemon.sock"
export LUST_NO_CACHE=1
# Fixtures have no dependencies; keep Cargo off the network and out of the repo.
export CARGO_NET_OFFLINE=true
filter=${1:-}
pass=0
fail=0
seen=0

# A panic line names the OS thread id, which differs per run: mask it.
mask_tid() { sed -E -e "s/^thread '([^']*)' \([0-9]+\) /thread '\1' (TID) /" -e '/^timeout: the monitored command dumped core$/d' -e '/: line [0-9]+: +[0-9]+ .* timeout /d' "$1"; }

report() {
  if [ "$1" = ok ]; then pass=$((pass + 1)); echo "ok   $2"; else fail=$((fail + 1)); echo "FAIL $2: $3"; fi
}

host_triple=$(rustc -vV | sed -n 's/^host: //p')

for dir in "$fixtures"/*/; do
  name=$(basename "$dir")
  [[ -n "$filter" && "$name" != *"$filter"* ]] && continue
  seen=$((seen + 1))
  case_dir=$work/$name
  mkdir -p "$case_dir/proj"
  cp -r "$dir/." "$case_dir/proj/"

  # Fixture selections, with the defaults named in the header.
  bin=$(sed -n 's/^name = "\(.*\)"/\1/p' "$case_dir/proj/Cargo.toml" | head -1)
  manifest=Cargo.toml
  root_file=src/main.rs
  features=""
  target=""
  expect=""
  cargo_pass=""
  stderr_mode=""
  prog_args=()
  if [ -f "$case_dir/proj/fixture.txt" ]; then
    while IFS='=' read -r k v; do
      case "$k" in
        bin) bin=$v ;;
        root) root_file=$v ;;
        manifest) manifest=$v ;;
        features) features=$v ;;
        target) target=$v ;;
        expect) expect=$v ;;
        cargo) cargo_pass=$v ;;
        stderr) stderr_mode=$v ;;
        args) # split on spaces by design (see header)
          read -r -a prog_args <<<"$v" ;;
        "" | \#*) ;;
        *) report bad "$name" "unknown fixture.txt key: $k"; continue 2 ;;
      esac
    done <"$case_dir/proj/fixture.txt"
  fi
  if [ "$target" = host ]; then target=$host_triple; fi

  cargo_args=(build --manifest-path "$case_dir/proj/$manifest" --bin "$bin")
  lust_args=(build "$case_dir/proj/$root_file" -o "$case_dir/lust.bin"
    --manifest-path "$case_dir/proj/$manifest" --bin "$bin")
  if [ -n "$features" ]; then
    cargo_args+=(--features "$features")
    lust_args+=(--features "$features")
  fi
  cargo_bin=$case_dir/cargo-target/debug/$bin
  if [ -n "$target" ]; then
    cargo_args+=(--target "$target")
    lust_args+=(--target "$target")
    cargo_bin=$case_dir/cargo-target/$target/debug/$bin
  fi

  cargo_ok=1
  if ! (cd "$case_dir/proj" && timeout 60 cargo "${cargo_args[@]}" --target-dir "$case_dir/cargo-target") >"$case_dir/cargo.out" 2>"$case_dir/cargo.err"; then
    cargo_ok=0
  fi
  if [ -n "$expect" ]; then
    # Negative fixture: the oracle outcome is pinned by `cargo=pass`
    # (valid Rust lust rejects) or its absence (both must reject), and
    # lust must reject with exactly the expected code present.
    if [ "$cargo_pass" = pass ] && [ $cargo_ok -eq 0 ]; then
      report bad "$name" "cargo=pass but cargo rejects it: $(tail -3 "$case_dir/cargo.err")"
      continue
    fi
    if [ "$cargo_pass" != pass ] && [ $cargo_ok -eq 1 ]; then
      report bad "$name" "cargo accepts it; add cargo=pass if lust rejects valid Rust on purpose"
      continue
    fi
    if timeout 60 "$lust" "${lust_args[@]}" >"$case_dir/lust.out" 2>"$case_dir/lust.err"; then
      report bad "$name" "lust accepted it, want $expect"
      continue
    fi
    if grep -q "$expect" "$case_dir/lust.err"; then
      report ok "$name"
    else
      report bad "$name" "want $expect, got: $(head -3 "$case_dir/lust.err")"
    fi
    continue
  fi
  if [ $cargo_ok -eq 0 ]; then
    report bad "$name" "cargo build failed: $(tail -3 "$case_dir/cargo.err")"
    continue
  fi
  if [ ! -x "$cargo_bin" ]; then
    report bad "$name" "cargo built, but no binary at $cargo_bin"
    continue
  fi
  if ! timeout 60 "$lust" "${lust_args[@]}" >"$case_dir/lust.out" 2>"$case_dir/lust.err"; then
    report bad "$name" "lust build failed: $(head -5 "$case_dir/lust.err")"
    continue
  fi

  timeout 30 "$cargo_bin" "${prog_args[@]}" >"$case_dir/cargo.run.out" 2>"$case_dir/cargo.run.err"; cs=$?
  timeout 30 "$case_dir/lust.bin" "${prog_args[@]}" >"$case_dir/lust.run.out" 2>"$case_dir/lust.run.err"; ls_=$?
  if [ $cs -ne $ls_ ]; then
    report bad "$name" "exit status cargo=$cs lust=$ls_"
    continue
  fi
  if ! cmp -s "$case_dir/cargo.run.out" "$case_dir/lust.run.out"; then
    report bad "$name" "stdout differs:"
    diff "$case_dir/cargo.run.out" "$case_dir/lust.run.out" | head -10
    continue
  fi
  if [ "$stderr_mode" = exact ] && ! diff -q <(mask_tid "$case_dir/cargo.run.err") <(mask_tid "$case_dir/lust.run.err") >/dev/null; then
    report bad "$name" "stderr differs:"
    diff <(mask_tid "$case_dir/cargo.run.err") <(mask_tid "$case_dir/lust.run.err") | head -10
    continue
  fi

  if [ "${SANITIZE:-0}" = 1 ]; then
    emit=("${lust_args[@]}")
    emit[3]=$case_dir/lust.tmp.bin # the value after -o (lust_args[2])
    if ! timeout 60 "$lust" "${emit[@]}" --emit-c "$case_dir/emit" >"$case_dir/emit.out" 2>"$case_dir/emit.err"; then
      report bad "$name" "lust --emit-c build failed: $(head -3 "$case_dir/emit.err")"
      continue
    fi
    if ! gcc -O1 -w -fno-sanitize-recover=undefined -fsanitize=address,undefined -o "$case_dir/san.bin" "$case_dir"/emit.*.c 2>"$case_dir/san.err"; then
      report bad "$name" "gcc could not build the generated C: $(head -3 "$case_dir/san.err")"
      continue
    fi
    timeout 30 "$case_dir/san.bin" "${prog_args[@]}" >"$case_dir/san.run.out" 2>"$case_dir/san.run.err"; ss=$?
    if grep -qE "[0-9]: runtime error|Sanitizer" "$case_dir/san.run.err"; then
      report bad "$name" "sanitizer: $(grep -m2 -E '[0-9]: runtime error|Sanitizer' "$case_dir/san.run.err")"
      continue
    fi
    if [ $ss -ne $cs ] || ! cmp -s "$case_dir/cargo.run.out" "$case_dir/san.run.out"; then
      report bad "$name" "sanitized build differs (exit $ss vs cargo $cs)"
      continue
    fi
  fi
  report ok "$name"
done

if [ $seen -eq 0 ]; then
  echo "error: no fixtures matched (filter: '${filter}'); a silent skip is not a pass"
  exit 2
fi
echo "test-crates: $pass passed, $fail failed"
[ $fail -eq 0 ]
