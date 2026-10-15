#!/usr/bin/env python3
"""Parity of the ts-rust fork's binaries: built by lust vs built by Cargo.

Two checks, both on the fork's own test inputs:
  runs   every bin on every fixture project of crates/ts_goport/tests (each dir with a
         tsconfig.json under fixtures/ and effect_fixtures/): stdout, stderr, exit code and
         every file the run writes must be byte-equal. Each run gets a fresh copy of the
         project at the same path, so paths in the output match.
  tests  the fork's integration test executables (built by `cargo test --release`) run once
         with the Cargo bins and once with the lust bins in their place. They find the bins
         through CARGO_BIN_EXE_<name>, a path fixed at build time in the cargo target dir,
         so the lust bins are copied over those paths and the Cargo ones put back after.

Usage: tsrust_parity.py --fork DIR --cargo-bins DIR --lust-bins DIR --out DIR [--tests DIR]
  --cargo-bins  <cargo target>/release (holds tsgo, goport, ...)
  --lust-bins   dir with the lust builds, named <package>-<bin> (tsrust_full.py writes them)
  --tests       <cargo target>/release/deps (the integration test executables); default from
                --cargo-bins
Last line: "tsrust-parity: <same>/<runs> runs same, <same>/<tests> test bins same"
"""
import argparse
import hashlib
import os
import shutil
import subprocess
import sys
from pathlib import Path

BINS = ["tsgo", "goport", "goport_emit", "goport_typesyms", "astdump", "goport_build", "goport_multiprog", "goport_live_programs", "goport_watch"]
TESTS = ["early_emit", "emit_pool", "fswatch_linux", "multi_program", "source_map_cut", "tsgo_launch", "tsgo_panic_hook"]


def projects(fork):
    base = fork / "crates/ts_goport/tests"
    found = sorted({p.parent for d in ("fixtures", "effect_fixtures") for p in (base / d).rglob("tsconfig.json") if "node_modules" not in p.parts})
    return [(str(p.relative_to(base)), p) for p in found]


def commands(bin_path, case):
    """The command lines run per project. `out` is a dir the run may write, inside the copy."""
    b = str(bin_path)
    name = bin_path.name
    if name.endswith("tsgo"):
        return [
            [b, "-p", "tsconfig.json", "--noEmit", "--pretty", "false"],
            [b, "-p", "tsconfig.json", "--outDir", "out", "--pretty", "false", "--listEmittedFiles"],
            [b, "-p", "tsconfig.json", "--showConfig"],
            [b, "-b", "tsconfig.json", "--pretty", "false", "--verbose"],
        ]
    if name.endswith("goport_emit"):
        return [[b, "-p", "tsconfig.json", "--outDir", "out", "--pretty", "false"]]
    if name.endswith("goport_typesyms") or name.endswith("astdump"):
        return [[b, "-p", "tsconfig.json", "-o", "out"]]
    if name.endswith("goport_build"):
        return [[b, "-b", "tsconfig.json", "--pretty", "false", "--verbose"]]
    if name.endswith("goport_live_programs"):
        return [[b, "live", "out", "check:tsconfig.json", "emit:tsconfig.json"]]
    if name.endswith("goport"):
        return [[b, "-p", "tsconfig.json", "--pretty", "false"]]
    return []  # goport_multiprog, goport_watch: covered by the multi_program test bin


def tree_digest(d):
    """Every file under d (relative path and sha256), sorted: what a run wrote."""
    out = []
    for p in sorted(d.rglob("*")):
        if p.is_file():
            out.append((str(p.relative_to(d)), hashlib.sha256(p.read_bytes()).hexdigest()))
    return out


def run_one(cmd, src, work, timeout):
    if work.exists():
        shutil.rmtree(work)
    shutil.copytree(src, work, symlinks=True)
    try:
        r = subprocess.run(cmd, cwd=work, capture_output=True, timeout=timeout)
        res = (r.returncode, r.stdout, r.stderr)
    except subprocess.TimeoutExpired:
        res = ("hang", b"", b"")
    return res, tree_digest(work)


def first_diff(a, b):
    la, lb = a.decode(errors="replace").splitlines(), b.decode(errors="replace").splitlines()
    for i, (x, y) in enumerate(zip(la, lb)):
        if x != y:
            return f"line {i + 1}: cargo {x[:120]!r} | lust {y[:120]!r}"
    return f"cargo {len(la)} lines, lust {len(lb)} lines"


def parity_runs(fork, cargo_bins, lust_bins, out, timeout):
    work = out / "parity-work" / "case"  # one path for both sides
    rows = []
    for bin_name in BINS:
        cb = cargo_bins / bin_name
        lb = lust_bins / f"ts_goport-{bin_name}"
        for case, src in projects(fork):
            for cmd in commands(cb, case):
                tag = f"{bin_name} {' '.join(cmd[1:])} @ {case}"
                if not lb.exists():
                    rows.append((tag, "no lust bin"))
                    continue
                if not cb.exists():
                    rows.append((tag, "no cargo bin"))
                    continue
                a, ta = run_one(cmd, src, work, timeout)
                b, tb = run_one([str(lb)] + cmd[1:], src, work, timeout)
                if a == b and ta == tb:
                    rows.append((tag, "same"))
                elif a[0] != b[0]:
                    rows.append((tag, f"exit cargo {a[0]} lust {b[0]}"))
                elif a[1] != b[1]:
                    rows.append((tag, "stdout " + first_diff(a[1], b[1])))
                elif a[2] != b[2]:
                    rows.append((tag, "stderr " + first_diff(a[2], b[2])))
                else:
                    da, db = dict(ta), dict(tb)
                    diff = sorted(k for k in set(da) | set(db) if da.get(k) != db.get(k))
                    rows.append((tag, f"files differ: {', '.join(diff[:5])}"))
    shutil.rmtree(out / "parity-work", ignore_errors=True)
    return rows


def test_exe(deps, name):
    """The newest integration test executable for one test target (deps/<name>-<hash>)."""
    cands = [p for p in deps.glob(f"{name}-*") if p.is_file() and os.access(p, os.X_OK) and "." not in p.name]
    return max(cands, key=lambda p: p.stat().st_mtime) if cands else None


def run_tests(exe, cwd, timeout):
    try:
        r = subprocess.run([str(exe), "--test-threads", "4"], cwd=cwd, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "hang", ""
    tail = [ln for ln in r.stdout.splitlines() if ln.startswith("test result:")]
    return r.returncode, (tail[-1] if tail else r.stderr[-300:])


def parity_tests(fork, cargo_bins, lust_bins, deps, timeout):
    """Each test bin with Cargo bins, then with lust bins at the same paths. The Cargo bins are
    restored at the end, also on an error."""
    saved = cargo_bins / "parity-saved"
    saved.mkdir(exist_ok=True)
    rows = []
    try:
        for b in BINS:
            if (cargo_bins / b).exists():
                shutil.copy2(cargo_bins / b, saved / b)
        cwd = fork / "crates/ts_goport"  # cargo test runs a test bin in its package dir
        for t in TESTS:
            exe = test_exe(deps, t)
            if exe is None:
                rows.append((t, "no test bin"))
                continue
            for b in BINS:
                shutil.copy2(saved / b, cargo_bins / b)
            a = run_tests(exe, cwd, timeout)
            missing = [b for b in BINS if not (lust_bins / f"ts_goport-{b}").exists()]
            if missing:
                rows.append((t, f"cargo bins: {a[1]}; no lust bin for {', '.join(missing)}"))
                continue
            for b in BINS:
                shutil.copy2(lust_bins / f"ts_goport-{b}", cargo_bins / b)
            l = run_tests(exe, cwd, timeout)
            rows.append((t, "same" if a[0] == l[0] == 0 else f"cargo: {a[0]} {a[1]} | lust: {l[0]} {l[1]}"))
    finally:
        for b in BINS:
            if (saved / b).exists():
                shutil.copy2(saved / b, cargo_bins / b)
        shutil.rmtree(saved, ignore_errors=True)
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fork", required=True, type=Path)
    ap.add_argument("--cargo-bins", required=True, type=Path)
    ap.add_argument("--lust-bins", required=True, type=Path)
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--tests", type=Path)
    ap.add_argument("--timeout", type=int, default=300)
    a = ap.parse_args()
    fork, cb, lb, out = a.fork.resolve(), a.cargo_bins.resolve(), a.lust_bins.resolve(), a.out.resolve()
    if not cb.exists():
        sys.exit(f"tsrust-parity: no Cargo bins at {cb}")
    runs = parity_runs(fork, cb, lb, out, a.timeout)
    tests = parity_tests(fork, cb, lb, a.tests or cb / "deps", a.timeout * 4)
    with open(out / "parity.txt", "w") as f:
        for tag, res in runs + tests:
            f.write(f"{res}\t{tag}\n")
    bad = [(t, r) for t, r in runs + tests if r != "same"]
    for t, r in bad[:40]:
        print(f"tsrust-parity: DIFF {t}: {r}")
    rs = sum(r == "same" for _, r in runs)
    ts = sum(r == "same" for _, r in tests)
    print(f"tsrust-parity: {rs}/{len(runs)} runs same, {ts}/{len(tests)} test bins same (all rows: {out / 'parity.txt'})")


if __name__ == "__main__":
    main()
