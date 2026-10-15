#!/usr/bin/env bash
# tsrust-full.sh [--boat] [--out DIR] [census options]: compile the whole ts-rust fork with lust.
#
# The fork is the submodule third_party/ts-rust (docs/PLAN.md, BRIEF "The ts-rust fork").
# Steps: get the fork tree, build and test it with Cargo, `lust check` then `lust build` every
# lib, bin and cdylib target, and print the errors grouped by root cause. The last line is
#   tsrust-full: <ok>/<targets> check, <ok>/<bins> build, <k> root causes
# Census options go to scripts/tsrust_full.py: --skip-cargo, --skip-build, --only a,b, -j N,
# --timeout SECS, --parity (scripts/tsrust_parity.py after the builds). Results: <out>/results.json, <out>/cargo.log, <out>/bin/ (lust builds).
# Default out: $TMPDIR/tsrust-full (/tmp/tsrust-full when TMPDIR is unset).
#
# Fork tree, first source that works:
#   1. third_party/ts-rust as it is (a checked-out submodule; local edits are used as they are)
#   2. ~/up/ts-rust.tgz (a boat sandbox: --boat uploads it)
#   3. a clone from the local reference (TSRUST_REF, default /home/theo/.t3/projects/ts-rust)
#      when it has the pinned commit, so no network; else from the fork's remote, with
#      the reference for objects
#
# --deep: run scripts/tsrust_deep.py instead (lines kept out per root cause; its options:
# --only a,b, --max-rounds N). Results: <out>/deep.json and a ranked table.
# --boat: run all of this on a boat sandbox (/tmp/lust-wt/boat-run.sh, BOAT_RUN overrides).
# boat-run.sh does not pack submodule trees, so only this job uploads the fork (one tar of its
# tracked and untracked files, no target/). Results come back to ./boat-out/tsrust-full/
# (--deep: ./boat-out/tsrust-full-deep/). TSRUST_BOAT_HOURS sets the time limit (default 3).
# LUST=<path> runs another lust build (a census of a branch before it lands).
# Needs: cargo and the fork's crates in the cargo registry (offline), lust built (scripts/build.sh).
set -uo pipefail
# The lust checkout: this script's parent dir (on a boat sandbox ~/w is not a git repo).
root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
sub=third_party/ts-rust
boat=0; deep=""; out=${TMPDIR:-/tmp}/tsrust-full; args=()
while [ $# -gt 0 ]; do
  case "$1" in
    --boat) boat=1; shift;;
    --deep) deep=--deep; shift;;
    --out) out=$2; shift 2;;
    *) args+=("$1"); shift;;
  esac
done

# fork_tree: make $sub hold the fork. Prints where it came from.
fork_tree() {
  local want ref
  if [ -f "$HOME/up/ts-rust.tgz" ] && [ ! -f "$sub/Cargo.toml" ]; then
    mkdir -p "$sub" && tar -xzf "$HOME/up/ts-rust.tgz" -C "$sub" || return 1
    echo "tsrust-full: fork tree: ~/up/ts-rust.tgz ($(cat "$sub/.fork-head" 2>/dev/null))"; return 0
  fi
  want=$(git ls-files -s "$sub" | awk '{print $2}')
  [ -n "$want" ] || { echo "tsrust-full: $sub is not a submodule here" >&2; return 1; }
  if [ -f "$sub/Cargo.toml" ]; then
    local have; have=$(git -C "$sub" rev-parse HEAD 2>/dev/null || echo "unknown")
    [ "$have" = "$want" ] || echo "tsrust-full: note: fork tree at $have, lust pins $want"
    echo "tsrust-full: fork tree: $sub ($have)"; return 0
  fi
  ref=${TSRUST_REF:-/home/theo/.t3/projects/ts-rust}
  if git -C "$ref" cat-file -e "$want^{commit}" 2>/dev/null; then
    # Clone the reference itself: no network. origin then points at the fork's remote.
    rmdir "$sub" 2>/dev/null
    git clone -q --no-checkout --reference "$ref" "$ref" "$sub" && git -C "$sub" checkout -q "$want" || return 1
    git -C "$sub" remote set-url origin "$(git config -f .gitmodules submodule.$sub.url)"
    echo "tsrust-full: fork tree: clone of $ref at $want"; return 0
  fi
  git submodule update --init --reference "$ref" "$sub" || return 1
  echo "tsrust-full: fork tree: fetched $want from the fork remote"
}

if [ $boat = 1 ]; then
  fork_tree || exit 2
  W=$(mktemp -d "${TMPDIR:-/tmp}/tsrust-boat.XXXXXX")
  git -C "$sub" rev-parse HEAD > "$W/.fork-head" 2>/dev/null
  (cd "$sub" && git ls-files -co --exclude-standard -z) > "$W/files" || exit 2
  tar -czf "$W/ts-rust.tgz" -C "$sub" --null -T "$W/files" -C "$W" .fork-head || exit 2
  q=""; for x in "${args[@]}"; do q+=" $(printf %q "$x")"; done
  name=${TSRUST_BOAT_NAME:-tsrust-full${deep:+-deep}}
  "${BOAT_RUN:-/tmp/lust-wt/boat-run.sh}" --hours "${TSRUST_BOAT_HOURS:-3}" --up "$W/ts-rust.tgz" --fetch "$name" -- \
    "scripts/build.sh >/dev/null 2>&1 || { scripts/build.sh 2>&1 | tail -30; exit 8; }; scripts/tsrust-full.sh $deep --out ~/w/$name$q"
  rc=$?; rm -rf "$W"; exit $rc
fi

fork_tree || exit 2
lust=${LUST:-$root/target/release/lust}
[ -x "$lust" ] || { echo "tsrust-full: no $lust; run scripts/build.sh first" >&2; exit 2; }
export LUST_TCC_HOME=${LUST_TCC_HOME:-/home/theo/.t3/projects/lust-lang/third_party/tcc}
mkdir -p "$out"
[ -n "$deep" ] && exec python3 "$root/scripts/tsrust_deep.py" --fork "$root/$sub" --lust "$lust" --work "$out" "${args[@]}"
exec python3 "$root/scripts/tsrust_full.py" --fork "$root/$sub" --lust "$lust" --out "$out" "${args[@]}"
