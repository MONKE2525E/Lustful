#!/usr/bin/env bash
# test-memfast.sh: the release runtime's vector mem* (src/runtime/memfast.c) and memmem
# prefilter (src/runtime/deps.c) against byte-by-byte references (tests/runtime/memfast_test.c),
# with ASan and UBSan under each C compiler found (clang, gcc), plus the word path
# (-DMF_NO_V16) that non-x86_64 targets take. Exit 1 on any failure.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
rc=0
for cc in clang gcc; do
  command -v "$cc" > /dev/null || continue
  for v in "" "-DMF_NO_V16"; do
    "$cc" -O1 -g $v -fsanitize=address,undefined -fno-sanitize-recover=undefined -fno-strict-aliasing -fsigned-char -w \
      tests/runtime/memfast_test.c -o "$out/t" || { echo "test-memfast: $cc $v: build failed"; rc=1; continue; }
    "$out/t" | sed "s/^/test-memfast ($cc $v): /" || rc=1
  done
done
exit $rc
