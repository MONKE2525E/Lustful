#!/usr/bin/env bash
# llbuild.sh <prefix> <out>: builds the units `lust build --emit-c <prefix>` wrote with the
# LLVM backend (LUST_RELEASE_C=1 LUST_RELEASE_BACKEND=llvm, src/cgen/ll.rs) into <out>, the
# way src/cc.rs does: a unit with `.ll` and `.hc` companions compiles as one module (its C and
# its helpers' C to bitcode, then the IR with both linked in, the helpers internalized), every
# other unit as plain C, the C++
# unwind unit with clang++, and clang++ links. Env: CC (default clang), CXX (clang++),
# OPT (default -O2), LLOBJ (an object cache dir keyed by the unit texts), JOBS (nproc).
set -euo pipefail
prefix=$1 out=$2
CC=${CC:-clang} CXX=${CXX:-clang++} OPT=${OPT:--O2}
F="-std=gnu11 -w -fsigned-char -fno-strict-aliasing -fwrapv -fno-delete-null-pointer-checks -fexceptions -fno-asynchronous-unwind-tables"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
one() { # one <unit .c file>: its object path on stdout
  local c=$1 ll=${1%.c}.ll hc=${1%.c}.hc key o
  if [ -f "$ll" ]; then key=$(cat "$c" "$ll" "$hc" | sha256sum | cut -c1-40); else key=$(sha256sum < "$c" | cut -c1-40); fi
  key=$key-$(echo "$CC $OPT ${FL:-}" | sha256sum | cut -c1-8)
  o=${LLOBJ:-$work}/$key.o
  if [ ! -f "$o" ]; then
    if [ -f "$ll" ]; then
      $CC $OPT ${FL:-$F} -emit-llvm -Xclang -disable-llvm-passes -Xclang -no-enable-noundef-analysis -c "$c" -o "$work/$key.$$.c.bc"
      $CC $OPT ${FL:-$F} -emit-llvm -Xclang -disable-llvm-passes -Xclang -no-enable-noundef-analysis -x c -c "$hc" -o "$work/$key.$$.h.bc"
      $CC $OPT -w -fexceptions -c "$ll" -Xclang -mlink-bitcode-file -Xclang "$work/$key.$$.c.bc" \
        -Xclang -mlink-builtin-bitcode -Xclang "$work/$key.$$.h.bc" -o "$o.$$.tmp"
    else
      $CC $OPT $F -c "$c" -o "$o.$$.tmp"
    fi
    mv -f "$o.$$.tmp" "$o"
  fi
  echo "$o"
}
export -f one
# LL_NULLCHECKS=0: the LLVM units' C halves without -fno-delete-null-pointer-checks.
[ "${LL_NULLCHECKS:-1}" = 0 ] && FL=${F/-fno-delete-null-pointer-checks/}
export CC OPT F FL work LLOBJ
mkdir -p "${LLOBJ:-$work}"
ls "$prefix".u*.c | xargs -P "${JOBS:-$(nproc)}" -I{} bash -c 'one "$@"' _ {} > "$work/objs" || { echo "llbuild: a unit failed" >&2; exit 1; }
objs=$(cat "$work/objs")
if [ -f "$prefix.eh.cc" ]; then
  $CXX -O2 -w -fexceptions -c "$prefix.eh.cc" -o "$work/eh.o"
  objs="$objs $work/eh.o"
fi
# shellcheck disable=SC2086
$CXX -o "$out" $objs -lm -lpthread
