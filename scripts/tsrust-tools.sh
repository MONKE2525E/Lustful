#!/usr/bin/env bash
# tsrust-tools.sh [--refresh]: gate lane for the ts-rust fork targets that check under lust
# (scripts/tsrust_tools.py): the codegen tools (pinned copy) and the fork libs (pinned fork tree).
# lust checks both tool crates (lib and bin), builds both bins, and their runs on the fork's
# schema and catalog inputs must equal the Cargo builds' (tsrust_parity TOOL_RUNS). The source
# is the pinned copy bench/tsrust-tools (gate boxes have no fork submodule); --refresh copies it
# again from third_party/ts-rust. Needs lust built (scripts/build.sh). Last line:
#   tsrust-tools: <ok> passed, <bad> failed
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
export LUST_TCC_HOME=${LUST_TCC_HOME:-/home/theo/.t3/projects/lust-lang/third_party/tcc}
exec python3 "$root/scripts/tsrust_tools.py" "$@"
