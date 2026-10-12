#!/usr/bin/env bash
# Checks every `lust explain` page in docs/errors/:
#   1. Every L#### code in src/ has a page, and every page is listed in the index.
#   2. The wrong example fails under `lust build` with exactly that code present.
#   3. The wrong example fails under rustc too, unless the page carries the marker
#      `<!-- rustc-wrong: pass -->` (valid Rust that lust rejects on purpose).
#   4. The fixed example builds under both lust and rustc.
# Usage: scripts/check-explain.sh [filter]
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
filter=${1:-}
pass=0
fail=0
report() {
  if [ "$1" = ok ]; then pass=$((pass + 1)); else fail=$((fail + 1)); echo "FAIL $2: $3"; fi
}
rustc_flags=(--edition 2024 -C panic=abort -C overflow-checks=on -A unconditional_panic -A warnings)

# 0. Registry: ranges, collisions, reserved codes, explain rows (no build needed).
if ! "$root/scripts/check-codes.sh" "$root"; then
  report bad registry "scripts/check-codes.sh failed (see above)"
fi

# 1. Coverage: source codes, pages, and index must agree.
grep -rhoE 'L[0-9]{4}' "$root"/src/ | sort -u > "$work/src-codes"
ls "$root"/docs/errors/L*.md | sed 's|.*/||; s|\.md||' | sort -u > "$work/doc-codes"
if ! diff -q "$work/src-codes" "$work/doc-codes" >/dev/null; then
  report bad coverage "codes in src/ and docs/errors/ differ:"
  diff "$work/src-codes" "$work/doc-codes" | head -10
else
  report ok coverage
fi
while IFS= read -r code; do
  grep -q "$code" "$root/docs/errors/README.md" || report bad "index/$code" "not listed in docs/errors/README.md"
done < "$work/doc-codes"

# Extracts one fenced block from a page: $1 = file, $2 = Wrong|Fixed, writes to stdout.
extract() {
  awk -v want="## $2" '
    $0 == want { on = 1; next }
    on && /^```rust$/ { grab = 1; next }
    grab && /^```$/ { exit }
    grab { print }
  ' "$1"
}

for page in "$root"/docs/errors/L*.md; do
  code=$(basename "$page" .md)
  [[ -n "$filter" && "$code" != *"$filter"* ]] && continue
  extract "$page" Wrong > "$work/$code-wrong.rs"
  extract "$page" Fixed > "$work/$code-fixed.rs"
  if [ ! -s "$work/$code-wrong.rs" ] || [ ! -s "$work/$code-fixed.rs" ]; then
    report bad "$code" "missing a Wrong or Fixed example"; continue
  fi
  # 2. Wrong under lust.
  out=$("$lust" build --json "$work/$code-wrong.rs" -o "$work/$code.bin" 2>&1)
  if [ $? -eq 0 ]; then
    report bad "$code" "lust accepted the wrong example"; continue
  elif ! grep -q "\"code\":\"$code\"" <<<"$out"; then
    report bad "$code" "wrong example gives $(grep -o '"code":"L[0-9]*"' <<<"$out" | tr '\n' ' '), want $code"; continue
  fi
  # 3. Wrong under rustc (unless marked as valid Rust).
  rustc "${rustc_flags[@]}" "$work/$code-wrong.rs" -o "$work/$code.rbin" >/dev/null 2>&1
  if grep -q 'rustc-wrong: pass' "$page"; then
    [ $? -eq 0 ] || { report bad "$code" "page says rustc accepts the wrong example, but rustc rejects it"; continue; }
  else
    [ $? -ne 0 ] || { report bad "$code" "rustc accepts the wrong example; add the rustc-wrong marker if lust rejects valid Rust on purpose"; continue; }
  fi
  # 4. Fixed under both.
  if ! "$lust" build "$work/$code-fixed.rs" -o "$work/$code.bin" >"$work/$code-fixed.lerr" 2>&1; then
    report bad "$code" "lust rejects the fixed example: $(head -3 "$work/$code-fixed.lerr")"; continue
  fi
  if ! rustc "${rustc_flags[@]}" "$work/$code-fixed.rs" -o "$work/$code.rbin" >"$work/$code-fixed.rerr" 2>&1; then
    report bad "$code" "rustc rejects the fixed example: $(head -3 "$work/$code-fixed.rerr")"; continue
  fi
  report ok "$code"
done

echo "check-explain: $pass passed, $fail failed"
[ $fail -eq 0 ]
