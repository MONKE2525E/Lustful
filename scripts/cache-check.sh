#!/usr/bin/env bash
# cache-check.sh [JOBS]: edit sequences through the persistent disk cache (unit objects in
# .lust-cache) with the default thread count; every step's binary must match an uncached
# (LUST_NO_CACHE=1) build. The gate-sized run of scripts/cache_check.py (see its header):
# 40 sequences of 4 steps, about 10 s on 6 cores. warm-check.sh covers cold vs threads vs
# daemon on one source; this covers the cache across edits (fx-unitcache).
# Run after scripts/build.sh. Exit 0 = all same, 1 = a difference, 2 = setup error.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
exec python3 "$root/scripts/cache_check.py" --seqs "${SEQS:-40}" --steps 4 --seed "${SEED:-1}" --jobs "${1:-$(nproc)}"
