#!/usr/bin/env bash
# Adapter corpus runner (ARCH 9.3 runner table). Wave A1 part:
# the layout corpus in tests/adapters/layout/ (ARCH 4.4 gate),
# plus the const initializer corpus in tests/consts/ (ARCH
# 2.13), whose layout queries come from the layout engine.
# Later waves add std and adapter semantics dirs here.
# Usage: scripts/test-adapters.sh [filter]
# Modes and knobs: see scripts/test-corpus-lib.sh.
set -uo pipefail
# shellcheck source=scripts/test-corpus-lib.sh
source "$(dirname "$0")/test-corpus-lib.sh"

corpus_init "${1:-}"

# The committed generated corpus must be the generator's
# current output (ARCH 4.4: grammar, generator, and engine
# grow together).
if [ -f "$corpus_root/tests/adapters/layout/generate.py" ]; then
  if timeout "$case_timeout" python3 "$corpus_root/tests/adapters/layout/generate.py" >"$corpus_work/generate.out" 2>&1; then
    corpus_report ok generate-check
  else
    corpus_report bad generate-check "$(cat "$corpus_work/generate.out")"
  fi
else
  corpus_report bad generate-check "tests/adapters/layout/generate.py is missing"
fi
corpus_pass_dir tests/adapters/layout/pass
corpus_fail_dir tests/adapters/layout/fail
corpus_pass_dir tests/consts/pass
corpus_fail_dir tests/consts/fail
corpus_pass_dir tests/consts/later/pass
corpus_fail_dir tests/consts/later/fail
corpus_finish test-adapters
