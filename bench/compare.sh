#!/usr/bin/env bash
# lust vs rustc on the same generated file. rustc gets its best configuration for each number:
# the minimum over incremental, non-incremental, and the parallel front end (-Z threads=8).
# Usage: bench/compare.sh <shape: plain> <units>...   (about 15 lines per unit)
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
shape=$1
shift
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
flags=(--edition 2024 -C panic=abort -A warnings)

# Wall time of a command in seconds.
t() {
  local s e
  s=$(date +%s%N)
  "$@" >/dev/null 2>&1
  e=$(date +%s%N)
  echo "scale=4; ($e - $s) / 1000000000" | bc
}
min() { printf '%s\n' "$@" | sort -g | head -1; }
med() { printf '%s\n' "$@" | sort -g | sed -n "$(( ($# + 1) / 2 ))p"; }

printf "| %-9s | %6s | %-22s | %9s | %9s | %7s |\n" shape lines operation rustc lust speedup
printf "|%s|\n" "-----------|--------|------------------------|-----------|-----------|---------"
for units in "$@"; do
  f=$work/b$units.rs
  python3 "$root/bench/rustc-baseline/gen.py" "$shape" "$units" 0 >"$f"
  lines=$(wc -l <"$f")

  # rustc, cold check: three configurations.
  rm -rf "$work/inc"
  c1=$(t rustc "${flags[@]}" --emit=metadata -C incremental="$work/inc" -o "$work/x.rmeta" "$f")
  c2=$(t rustc "${flags[@]}" --emit=metadata -o "$work/x.rmeta" "$f")
  c3=$(t env RUSTC_BOOTSTRAP=1 rustc "${flags[@]}" -Z threads=8 --emit=metadata -o "$work/x.rmeta" "$f")
  # rustc, check after a one-line edit (incremental).
  python3 "$root/bench/rustc-baseline/gen.py" "$shape" "$units" 1 >"$work/e$units.rs"
  cp "$work/e$units.rs" "$f.edit"
  cp "$f" "$f.orig"
  cp "$f.edit" "$f"
  ce=$(t rustc "${flags[@]}" --emit=metadata -C incremental="$work/inc" -o "$work/x.rmeta" "$f")
  cp "$f.orig" "$f"

  # rustc, cold debug build: three configurations.
  rm -rf "$work/incb"
  b1=$(t rustc "${flags[@]}" -C debuginfo=2 -C incremental="$work/incb" -o "$work/r" "$f")
  b2=$(t rustc "${flags[@]}" -C debuginfo=2 -o "$work/r0" "$f")
  b3=$(t env RUSTC_BOOTSTRAP=1 rustc "${flags[@]}" -Z threads=8 -C debuginfo=2 -o "$work/r" "$f")
  cp "$f.edit" "$f"
  be=$(t rustc "${flags[@]}" -C debuginfo=2 -C incremental="$work/incb" -o "$work/r" "$f")
  cp "$f.orig" "$f"

  # lust has no incremental mode yet, so "after edit" is a full cold run.
  lc=$(med "$(t "$lust" check "$f")" "$(t "$lust" check "$f")" "$(t "$lust" check "$f")")
  lb=$(med "$(t "$lust" build "$f" -o "$work/l")" "$(t "$lust" build "$f" -o "$work/l")" "$(t "$lust" build "$f" -o "$work/l")")
  lg=$(med "$(t "$lust" build -g "$f" -o "$work/l")" "$(t "$lust" build -g "$f" -o "$work/l")" "$(t "$lust" build -g "$f" -o "$work/l")")

  # Same program, same output.
  "$work/r0" >"$work/r.out"
  "$work/l" >"$work/l.out"
  same=$(cmp -s "$work/r.out" "$work/l.out" && echo yes || echo NO)

  row() { printf "| %-9s | %6s | %-22s | %8.2fs | %8.3fs | %6.0fx |\n" "$shape" "$lines" "$1" "$2" "$3" "$(echo "$2 / $3" | bc -l)"; }
  row "check cold" "$(min "$c1" "$c2" "$c3")" "$lc"
  row "check after edit" "$ce" "$lc"
  row "debug build cold" "$(min "$b1" "$b2" "$b3")" "$lg"
  row "debug build after edit" "$be" "$lg"
  row "build cold, no debuginfo" "$(min "$b1" "$b2" "$b3")" "$lb"
  echo "|           |        | same output: $same |"
done
