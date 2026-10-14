#!/usr/bin/env python3
"""Refresh tools/lust-port/features.json by testing lust against rustc.

Each probe in tools/lust-port/tests/features/ is one small program for
one feature id. This script builds it with rustc (edition 2024) and
with `lust check` plus `lust run`, then derives one status per
feature: supported (every probe matches rustc), partial (some probes
match), or unsupported (no probe matches). A lust build that runs with
wrong output is a false accept and fails the run.

Modes:
  (default)       run the probes and print the status table
  --write         also write status and milestone into features.json
                  (supported sets milestone 0; notes stay hand-written)
  --coverage      run lust-port on ts-rust, refresh docs/ts-rust-gaps.json,
                  and write docs/ts-rust-coverage.md for the core CLI scope

Probes with `// oracle: lust-only` have no single-file rustc oracle
(a proc macro). They never set supported by themselves: a lust reject
records unsupported, a lust accept is reported for a human call.

Probes with `// cargo-dep: <dependency line>` headers (one per line,
as written under [dependencies]) use a registry crate: the probe runs
as the bin of a temporary Cargo package with those dependencies. Cargo
builds and runs it against the real crate (offline, from the local
registry cache) as the oracle, and lust builds it from the same
manifest, which swaps in the lust adapter (docs/ARCH.md 3.6).

Env: LUST (lust binary), LUST_PORT (scanner binary), TS_RUST (ts-rust
checkout), LUST_TCC_HOME (passed through to lust).
"""
import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROBES = ROOT / "tools/lust-port/tests/features"
FEATURES_JSON = ROOT / "tools/lust-port/features.json"
COMPILE_TIMEOUT = 30
RUN_TIMEOUT = 10
NOT_CORE = {"ls", "lsp", "project", "api", "effect", "format", "fswatch", "ipc", "contentmapper"}
# Owner per feature for the coverage report. Unlisted features fall back
# to a root-cause owner in OWNER_BY_CAUSE.
OWNER = {
    "threads.thread_local": "W-TLS",
    "lifetimes.static_anon": "W-BORROW",
    "lifetimes.named": "W-BORROW",
    "lifetimes.hrtb": "W-BORROW",
    "closures.fn_ptr_lifetime": "W-BORROW",
    "threads.sync": "wave C (threads)",
    "threads.send_sync_bounds": "wave C (threads)",
    "panic.recovery": "wave C (panics)",
    "cinterop.system": "wave C (shims)",
    "ext.unknown_crate": "wave D",
}
OWNER_BY_CAUSE = {
    "std-runtime": "W-STD-B",
    "external-crates": "W-DEPS",
    "traits-generics": "W-CHECK-G",
    "closures": "W-CHECK-G",
    "dyn-trait": "W-CHECK-G",
    "iterators": "W-CHECK-G",
    "attrs-cfg": "W-CHECK-G",
    "macros": "W-CHECK-G",
    "lifetimes": "W-BORROW",
    "unsafe": "wave C (shims)",
}


def run(cmd, timeout, env=None):
    """Run one command; return (exit_code, stdout, stderr). Exit 124 on timeout."""
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, env=env)
        return p.returncode, p.stdout, p.stderr
    except subprocess.TimeoutExpired:
        return 124, "", "timeout"


def parse_header(path):
    head = {}
    for line in path.read_text().splitlines():
        m = re.match(r"//\s*([a-z-]+):\s*(.+)", line)
        if m:
            head[m.group(1)] = m.group(2).strip()
        elif line.strip() and not line.startswith("//"):
            break
    return head


def first_code(stderr):
    m = re.search(r"L\d{4}", stderr)
    return m.group(0) if m else ""


def cargo_package(path, deps, tmp):
    """A temporary Cargo package whose bin `probe` is the probe file.
    Returns (manifest path, bin source path)."""
    pkg = tmp / (path.stem + "-pkg")
    (pkg / "src").mkdir(parents=True, exist_ok=True)
    (pkg / "src/main.rs").write_text(path.read_text())
    lines = ["[package]", 'name = "probe"', 'version = "0.0.0"', 'edition = "2024"', "", "[dependencies]", *deps, "", "[workspace]", ""]
    (pkg / "Cargo.toml").write_text("\n".join(lines))
    return pkg / "Cargo.toml", pkg / "src/main.rs"


def probe_one(path, lust, tmp, env):
    """Test one probe file. Returns a result dict."""
    head = parse_header(path)
    res = {"file": path.name, "feature": head.get("feature", ""), "form": head.get("form", "")}
    if head.get("helper") == "true":
        res["verdict"] = "helper"
        return res
    deps = re.findall(r"^//\s*cargo-dep:\s*(.+?)\s*$", path.read_text(), re.M)
    if deps:
        return probe_package(path, deps, lust, tmp, env, res)
    lust_only = head.get("oracle") == "lust-only"
    panic = head.get("rustc-panic", "abort")
    # A probe that needs unwinding builds lust with the same strategy.
    mode = ["-C", "panic=unwind"] if panic == "unwind" else []
    if not lust_only:
        rbin = tmp / (path.stem + ".rustc")
        code, _, err = run(
            ["rustc", "--edition", "2024", "-C", f"panic={panic}", "-o", str(rbin), str(path)],
            COMPILE_TIMEOUT,
        )
        if code != 0:
            res.update(verdict="rustc-reject", detail=err.strip().splitlines()[-1][:160] if err.strip() else "")
            return res
        rcode, rout, _ = run([str(rbin)], RUN_TIMEOUT)
        res["rustc_stdout"] = rout
        res["rustc_exit"] = rcode
    ccode, _, cerr = run([str(lust), "check", *mode, str(path)], COMPILE_TIMEOUT, env)
    res["lust_code"] = first_code(cerr)
    if ccode != 0:
        res["verdict"] = "reject"
        return res
    lcode, lout, lerr = run([str(lust), "run", *mode, str(path)], COMPILE_TIMEOUT, env)
    res["lust_stdout"] = lout
    res["lust_exit"] = lcode
    if lust_only:
        res["verdict"] = "lust-only-accept" if lcode == 0 else "lust-only-runfail"
        return res
    same_exit = lcode == res["rustc_exit"] or (lcode != 0 and res["rustc_exit"] != 0)
    if lout == res["rustc_stdout"] and same_exit:
        res["verdict"] = "pass"
    elif lcode == 124 or (lcode != 0 and not lout):
        res.update(verdict="runfail", detail=first_code(lerr) or "lust run failed after check passed")
    else:
        res.update(verdict="wrong", detail=f"lust stdout {lout!r} != rustc {res['rustc_stdout']!r}")
    return res


def probe_package(path, deps, lust, tmp, env, res):
    """A `cargo-dep` probe: Cargo with the real crate is the oracle."""
    manifest, src = cargo_package(path, deps, tmp)
    cenv = dict(env, CARGO_NET_OFFLINE="true")
    target = manifest.parent / "target"
    code, _, err = run(["cargo", "build", "-q", "--manifest-path", str(manifest), "--target-dir", str(target)], 300, cenv)
    if code != 0:
        res.update(verdict="rustc-reject", detail=err.strip().splitlines()[-1][:160] if err.strip() else "")
        return res
    rcode, rout, _ = run([str(target / "debug/probe")], RUN_TIMEOUT)
    res["rustc_stdout"] = rout
    res["rustc_exit"] = rcode
    lbin = manifest.parent / "probe.lust"
    ccode, _, cerr = run([str(lust), "build", str(src), "-o", str(lbin), "--manifest-path", str(manifest), "--bin", "probe"], COMPILE_TIMEOUT, cenv)
    res["lust_code"] = first_code(cerr)
    if ccode != 0:
        res["verdict"] = "reject"
        return res
    lcode, lout, _ = run([str(lbin)], RUN_TIMEOUT)
    res["lust_stdout"] = lout
    res["lust_exit"] = lcode
    same_exit = lcode == rcode or (lcode != 0 and rcode != 0)
    if lout == rout and same_exit:
        res["verdict"] = "pass"
    elif lcode == 124 or (lcode != 0 and not lout):
        res.update(verdict="runfail", detail="lust build ran and failed")
    else:
        res.update(verdict="wrong", detail=f"lust stdout {lout!r} != cargo {rout!r}")
    return res


def feature_status(results):
    """Derive one status from the probe verdicts of one feature."""
    vs = [r["verdict"] for r in results]
    if all(v == "pass" for v in vs):
        return "supported"
    if any(v == "pass" for v in vs):
        return "partial"
    if all(v in ("reject", "runfail") for v in vs):
        return "unsupported"
    return "manual"  # lust-only accepts, or a wrong-output probe


def do_probes(args):
    lust = Path(os.environ.get("LUST", ROOT / "target/release/lust"))
    if not lust.exists():
        sys.exit(f"lust binary not found: {lust} (build with cargo build --release)")
    table = json.loads(FEATURES_JSON.read_text())
    known = {f["id"] for f in table["features"]}
    env = dict(os.environ)
    env["LUST_NO_DAEMON"] = "1"
    tmp = Path(tempfile.mkdtemp(prefix="port-scan-sync-"))
    env["LUST_CACHE_DIR"] = str(tmp / "cache")
    env["LUST_DAEMON_SOCKET"] = str(tmp / "none.sock")
    results = [probe_one(p, lust, tmp, env) for p in sorted(PROBES.glob("*.rs"))]
    by_feature = {}
    for r in results:
        if r["verdict"] != "helper":
            by_feature.setdefault(r["feature"], []).append(r)
    derived = {fid: feature_status(rs) for fid, rs in by_feature.items()}
    old = {f["id"]: f["status"] for f in table["features"]}

    print(f"{'feature':32} {'old':12} {'probe says':12} probes")
    for fid in sorted(by_feature):
        marks = ", ".join(f"{r['file']}:{r['verdict']}" + (f"({r['lust_code']})" if r.get("lust_code") else "") for r in by_feature[fid])
        print(f"{fid:32} {old.get(fid, 'NOT IN TABLE'):12} {derived[fid]:12} {marks}")
    unprobed = sorted(known - set(by_feature))
    unknown = sorted(set(by_feature) - known)
    if unprobed:
        print("no probe (status not checked):", ", ".join(unprobed))
    if unknown:
        print("probe id not in features.json:", ", ".join(unknown))

    bad = [r for r in results if r["verdict"] in ("wrong", "rustc-reject")]
    for r in bad:
        print(f"FAIL {r['file']}: {r['verdict']} {r.get('detail', '')}")
    if args.json:
        Path(args.json).write_text(json.dumps({"probes": results, "derived": derived}, indent=1) + "\n")
    if args.write:
        for f in table["features"]:
            d = derived.get(f["id"])
            if d in ("supported", "partial", "unsupported"):
                f["status"] = d
                if d == "supported":
                    f["milestone"] = 0
        FEATURES_JSON.write_text(json.dumps(table, indent=1) + "\n")
        print(f"wrote {FEATURES_JSON}")
    if bad:
        sys.exit(2)
    return derived


def module_of(path):
    """Top module of a ts-rust file, the inventory coverage.py rule."""
    rest = path.replace("crates/ts_goport/src/", "")
    return rest.split("/")[0].replace(".rs", "")


def curve(files, feats):
    """Files and lines that compile after each milestone, report.rs style."""
    total_files = len(files)
    total_lines = sum(f["lines"] for f in files)
    rows = []
    for n in [0, 4, 5, 6, 7, 8]:
        ok = [
            f
            for f in files
            if not f["parse_error"]
            and all((feats.get(fid) or {}).get("milestone") is not None and feats[fid]["milestone"] <= n for fid in f["missing_features"])
        ]
        lines = sum(f["lines"] for f in ok)
        rows.append((n, len(ok), lines, 100.0 * len(ok) / max(total_files, 1), 100.0 * lines / max(total_lines, 1)))
    return rows


def do_coverage(args):
    scanner = Path(os.environ.get("LUST_PORT", ROOT / "tools/lust-port/target/release/lust-port"))
    ts_rust = Path(os.environ.get("TS_RUST", "/home/theo/.t3/projects/ts-rust"))
    if not scanner.exists():
        sys.exit(f"scanner not found: {scanner} (build with cargo build --release --manifest-path tools/lust-port/Cargo.toml)")
    manifest = ts_rust / "Cargo.toml"
    code, out, err = run(
        [str(scanner), "scan", "--manifest-path", str(manifest), "--target", "x86_64-unknown-linux-gnu", "--json", "--summary"],
        600,
    )
    if code != 0:
        sys.exit(f"scan failed: {err[-500:]}")
    gaps_path = ROOT / "docs/ts-rust-gaps.json"
    gaps_path.write_text(out if out.endswith("\n") else out + "\n")
    rep = json.loads(out)
    table = json.loads(FEATURES_JSON.read_text())
    feats = {f["id"]: f for f in table["features"]}

    prod = [f for f in rep["files"] if f["cat"] == "prod" and f["scope"] == "active"]
    core = [f for f in prod if module_of(f["file"]) not in NOT_CORE]
    today = [f for f in core if not f["missing_features"] and not f["parse_error"]]
    today_lines = sum(f["lines"] for f in today)
    core_lines = sum(f["lines"] for f in core)

    blockers = []
    for fid, feat in feats.items():
        if feat["status"] == "supported":
            continue
        hit = [f for f in core if fid in f["missing_features"]]
        if not hit:
            continue
        sole = [f for f in hit if len(f["missing_features"]) == 1]
        blockers.append(
            {
                "id": fid,
                "title": feat["title"],
                "status": feat["status"],
                "milestone": feat["milestone"],
                "owner": OWNER.get(fid) or OWNER_BY_CAUSE.get(feat["root_cause"], "wave D"),
                "files": len(hit),
                "lines": sum(f["lines"] for f in hit),
                "sole_files": len(sole),
                "sole_lines": sum(f["lines"] for f in sole),
            }
        )
    blockers.sort(key=lambda b: (-b["lines"], b["id"]))
    top = blockers[:15]

    head = subprocess.run(["git", "-C", str(ts_rust), "rev-parse", "--short", "HEAD"], capture_output=True, text=True)
    ts_head = head.stdout.strip() or "unknown"
    lust_head = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short", "HEAD"], capture_output=True, text=True).stdout.strip()

    def curve_table(files):
        rows = ["| after milestone | files | files % | lines % |", "|---|---|---|---|"]
        for n, nfiles, _lines, fpct, lpct in curve(files, feats):
            label = "supported today" if n == 0 else f"milestone {n}"
            rows.append(f"| {label} | {nfiles} | {fpct:.1f} | {lpct:.1f} |")
        return rows

    md = [
        "# ts-rust coverage",
        "",
        "Generated by `python3 scripts/port-scan-sync.py --coverage`. Do not edit the numbers by hand.",
        "Feature statuses come from the probes in `tools/lust-port/tests/features/`",
        "(`python3 scripts/port-scan-sync.py --write`). A file counts as compiling",
        "when every construct the scanner sees in it maps to a supported feature.",
        "The scanner has no type data, so this is an upper bound.",
        "",
        f"lust commit: `{lust_head}` (the scanned tree, landed on `next`). ts-rust: `{ts_head}`.",
        "`docs/ts-rust-gaps.md` still holds the milestone-3 table scan and its inventory comparison; this file is the current burn-down.",
        f"scan: {rep['totals']['files']} files, {rep['totals']['lines']} lines, target x86_64-unknown-linux-gnu.",
        "",
        "## Core CLI scope today",
        "",
        "Core scope is the PLAN.md milestone 8 set, with the inventory rule:",
        "prod files active on this target whose top module is not ls, lsp, project,",
        "api, effect, format, fswatch, ipc, or contentmapper.",
        "The inventory counted 402 files and 388,041 lines on the same ts-rust commit.",
        "This scanner counts 406: it adds the 5 codegen tool files cargo reports as",
        "lib and bin targets, and drops `cmd/tsgo/isprocessalive_other.rs`, which is",
        "inactive on this target.",
        "",
        f"Core: {len(core)} files, {core_lines} lines. Compiles today: {len(today)} files, {today_lines} lines"
        f" ({100.0 * len(today) / max(len(core), 1):.1f}% of files, {100.0 * today_lines / max(core_lines, 1):.1f}% of lines).",
        "",
        "All active prod files: "
        f"{rep['coverage']['supported_today_files']} of {rep['coverage']['total_files']} files compile today"
        f" ({rep['coverage']['by_plan_milestone'][0]['lines_pct']}% of lines).",
        "",
        "## Top 15 blocking features, core scope",
        "",
        "`lines blocked` counts every core file that uses the feature. `sole` counts",
        "files where this feature is the only blocker: land it and those files compile.",
        "",
        "| # | feature | status | milestone | owner | files | lines blocked | sole files | sole lines |",
        "|---|---|---|---|---|---|---|---|---|",
    ]
    for i, b in enumerate(top, 1):
        ms = "none" if b["milestone"] is None else str(b["milestone"])
        md.append(
            f"| {i} | `{b['id']}` | {b['status']} | {ms} | {b['owner']} | {b['files']} | {b['lines']} | {b['sole_files']} | {b['sole_lines']} |"
        )
    md += ["", "## Core CLI curve", ""] + curve_table(core)
    md += ["", "## All active prod curve", ""] + curve_table(prod)
    md += [
        "",
        "## Reproduce",
        "",
        "```sh",
        "export LUST_TCC_HOME=/home/theo/.t3/projects/lust-lang/third_party/tcc",
        "cargo build --release",
        "cargo build --release --manifest-path tools/lust-port/Cargo.toml",
        "python3 scripts/port-scan-sync.py --write",
        "python3 scripts/port-scan-sync.py --coverage",
        "```",
        "",
    ]
    out_path = ROOT / "docs/ts-rust-coverage.md"
    out_path.write_text("\n".join(md))
    print(f"wrote {gaps_path}")
    print(f"wrote {out_path}")
    print(f"core: {len(core)} files, {core_lines} lines; today {len(today)} files, {today_lines} lines")
    for b in top[:5]:
        print(f"  blocker {b['id']}: {b['lines']} lines, sole {b['sole_lines']}")


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--write", action="store_true", help="write probe statuses into features.json")
    ap.add_argument("--json", help="write raw probe results to this file")
    ap.add_argument("--coverage", action="store_true", help="scan ts-rust and write the coverage docs")
    args = ap.parse_args()
    if args.coverage:
        do_coverage(args)
    else:
        do_probes(args)


if __name__ == "__main__":
    main()
