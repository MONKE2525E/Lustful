# Adapter and layout corpora (Wave A1, layout gate)

This directory is the home of `scripts/test-adapters.sh`. The
Wave A1 part is the layout corpus under `layout/`. Later waves
add std and adapter semantics cases here (ARCH 9.3 runner
table); a missing later subdirectory does not fail this gate,
but `layout/` and `tests/consts/` must exist.

Read `layout/README.md` for the fixture format.
