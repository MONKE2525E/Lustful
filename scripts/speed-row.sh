#!/usr/bin/env bash
# speed-row.sh [slice-dir]: the quick speed row for the landing gate (non-blocking).
# Runs the slice benchmark in --quick mode (default: bench/slices/goport-util-small)
# and prints one line per row plus a `speed-row:` summary line with the warm body
# edit ratio. Exit 1 only when the benchmark itself fails (lust and rustc disagree,
# warm and cold lust answers differ, or lust rejects the slice); speed never fails it.
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
slice=${1:-$root/bench/slices/goport-util-small}
out=${TMPDIR:-/tmp}/speed-row-$$.json
python3 "$root/scripts/scale-gate.py" --slice "$slice" --quick --json "$out" || exit 1
python3 - "$out" <<'PY'
import json, sys
d = json.load(open(sys.argv[1]))
row = {r["row"]: r for r in d["rows"]}
b = row["body edit check (one fn)"]
c = row["cold check"]
pk = b.get("patch_kept", {}).get("patch", {})
patch = f", body patch {pk['hits']} hit / {pk['misses']} miss" if pk else ""
print(f"speed-row: {d['slice']} {d['lines']} lines: warm body-edit check lust {b['lust']['median']:.0f} ms "
      f"vs rustc {b['rustc_best']['median']:.0f} ms ({b['ratio']}x median, {b.get('ratio_p95')}x p95, target 100x{patch}); "
      f"cold check {c['lust']['median']:.0f} vs {c['rustc_best']['median']:.0f} ms ({c['ratio']}x)")
PY
rm -f "$out"
