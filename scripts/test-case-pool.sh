#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
filter=''
source "$root/scripts/case-pool.sh"
for prefix in '' '/rustc/abc123/' '/opt/rust/lib/rustlib/src/rust/'; do
  printf "thread 'main' (123) panicked at %slibrary/core/src/time.rs:201:18:\nmessage\n" "$prefix" > "$work/input"
  mask_stderr "$work/input" > "$work/actual"
  printf "thread 'main' (TID) panicked at @STD@/library/core/src/time.rs:201:18:\nmessage\n" > "$work/expected"
  cmp "$work/expected" "$work/actual"
done
printf "thread 'main' (123) panicked at library/core/src/time.rs:202:18:\nmessage\n" > "$work/input"
mask_stderr "$work/input" > "$work/actual"
if cmp -s "$work/expected" "$work/actual"; then
  echo 'FAIL normalization concealed a changed line number'
  exit 1
fi
printf 'user message: library/core/src/time.rs:201:18\n' > "$work/input"
mask_stderr "$work/input" > "$work/actual"
cmp "$work/input" "$work/actual"
echo 'case-pool normalization: passed'
