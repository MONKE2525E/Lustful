#!/usr/bin/env bash
# cache-check.sh [JOBS]: edit sequences through the persistent disk cache (unit objects in
# .lust-cache) with the default thread count; every step's binary must match an uncached
# (LUST_NO_CACHE=1) build. The gate-sized run of scripts/cache_check.py (see its header):
# 40 sequences of 4 steps, then a daemon run (one daemon per sequence, 12 sequences of 12
# steps, threads 1, 4, and 24 in turn) whose binaries must match too; about 12 s on boat.
# warm-check.sh covers cold vs threads vs daemon on one source; this covers the cache and
# the daemon's reused C across edits (fx-unitcache).
# Run after scripts/build.sh. Exit 0 = all same, 1 = a difference, 2 = setup error. The
# last line is the daemon run's summary; the exit code covers both runs.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
jobs=${1:-$(nproc)}
python3 "$root/scripts/cache_check.py" --seqs "${SEQS:-40}" --steps 4 --seed "${SEED:-1}" --jobs "$jobs"
rc=$?
python3 "$root/scripts/cache_check.py" --seqs "${DAEMON_SEQS:-12}" --steps 12 --seed "${SEED:-1}" --jobs "$jobs" --daemon --threads 1,4,24
drc=$?
exit $((rc > drc ? rc : drc))
