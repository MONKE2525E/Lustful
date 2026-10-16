#!/usr/bin/env python3
"""Deep census of the ts-rust fork: how many lines each lust root cause keeps out.

`lust check` stops a crate at its first failing stage (often one error), so a plain census
shows only the front. This works on a scratch copy of the fork: check a target, remove the
innermost item that holds each error (bench/slices/prune.py's item tool and rules), and
repeat until the target checks or no error can be located. Every removal is charged to a
root cause: its own (code, normalized message), or, when its error names an item an earlier
removal took away, that item's root cause (a cascade).

The copy is scratch: nothing here is a fork change. Fix the causes in lust or in the fork,
then run the plain census (scripts/tsrust-full.sh).

Usage: tsrust_deep.py --fork DIR --lust PATH --work DIR [--only a,b] [--max-rounds N]
Targets default to the three library crates in dependency order (goport_util,
goport_lsproto, ts_goport). Output: <work>/deep.json and a ranked table on stdout.
"""
import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "bench/slices"))
import prune  # noqa: E402  (bench/slices/prune.py: items_of, prune_round, located)
import tsrust_full  # noqa: E402

DEFAULT = ["goport_util", "goport_lsproto", "ts_goport"]


def errors(lust, t, work, env):
    """Located errors of one lust check: (file, line, code, message). Line 0 when the span is
    not where the file on disk says (lust std source shown under a user file)."""
    r = subprocess.run(tsrust_full.lust_cmd(lust, "check", t, work), cwd=work, env=env, capture_output=True, text=True, timeout=3600)
    out = []
    for line in r.stdout.splitlines():
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("kind") != "diagnostic" or d.get("severity") != "error":
            continue
        sp = d.get("span") or {}
        f = d.get("file") or ""
        ln = sp.get("line", 0) if f and prune.located(f, sp) else 0
        out.append((f, ln, d.get("code", "?"), d.get("message", "")))
    return r.returncode, out, r.stderr


def in_item(err, cache):
    """True when a removable item holds the error's line (else prune.py would search by name)."""
    f = str(Path(err[0]).resolve())
    return any(it[0] <= err[1] <= it[1] for it in prune.items_of(f, cache))


def remove_users(copy, names, cause_of_name, removed, target):
    """Remove every innermost item of the copy whose text names one of `names` as a word.
    Each removal is a cascade of that name's root cause. Returns the number removed."""
    pat = re.compile(r"\b(" + "|".join(map(re.escape, sorted(names))) + r")\b")
    n = 0
    for p in sorted(copy.rglob("*.rs")):
        # Only files a lib or bin target compiles: no integration tests, benches or examples.
        if {"target", "tests", "benches", "examples"} & set(p.relative_to(copy).parts):
            continue
        lines = p.read_text().split("\n")
        items = prune.items_of(str(p), {})
        hits = {}
        for i, line in enumerate(lines, 1):
            m = pat.search(line.split("//")[0])
            if not m:
                continue
            inner = [it for it in items if it[0] <= i <= it[1]]
            if inner:
                it = max(inner, key=lambda t: (t[2], -(t[1] - t[0])))
                hits.setdefault((it[0], it[1]), (it, m.group(1)))
        spans = sorted(hits)
        outer = []
        for sp in spans:
            if outer and sp[0] >= outer[-1][0] and sp[1] <= outer[-1][1]:
                continue
            outer.append(sp)
        for sp in sorted(outer, reverse=True):
            it, nm = hits[sp]
            del lines[sp[0] - 1:sp[1]]
            removed.append({"file": os.path.relpath(p, copy), "kind": it[3], "name": it[4], "lines": sp[1] - sp[0] + 1,
                            "by": "users", "code": "USES", "message": f"uses removed `{nm}`",
                            "cause": list(cause_of_name[nm]), "target": target})
            cause_of_name.setdefault(it[4], cause_of_name[nm])
            n += 1
        if outer:
            p.write_text("\n".join(lines))
    return n


def names_in(msg):
    """Item names an error message points at: the last path segment of each `...` text."""
    out = set()
    for q in re.findall(r"`([^`]+)`", msg):
        seg = re.split(r"::", q.strip("&* "))[-1]
        m = re.match(r"[A-Za-z_]\w*", seg)
        if m:
            out.add(m.group(0))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fork", required=True, type=Path)
    ap.add_argument("--lust", required=True)
    ap.add_argument("--work", required=True, type=Path)
    ap.add_argument("--only", default=",".join(DEFAULT))
    ap.add_argument("--max-rounds", type=int, default=200)
    a = ap.parse_args()
    prune.build_items_tool()
    work = a.work.resolve()
    copy = work / "fork"
    if copy.exists():
        shutil.rmtree(copy)
    shutil.copytree(a.fork.resolve(), copy, ignore=shutil.ignore_patterns("target", ".git", ".lust-cache"))
    env = dict(os.environ, LUST_NO_DAEMON="1", LUST_CACHE_DIR=str(work / "lust-cache"), CARGO_TARGET_DIR=str(work / "cargo-target"))
    by_name = {t["name"]: t for t in tsrust_full.targets(copy)}
    removed, cause_of_name, status = [], {}, {}
    # One check of every target on the unpruned copy first: a target that needs a build script
    # record lust has not stored yet (the tsgo bin) gets it through `cargo check` now. After the
    # pruning, rustc can reject the copy (a removed item whose only user is cfg'd out for lust).
    for name in a.only.split(","):
        errors(a.lust, by_name[name], work, env)
    for name in a.only.split(","):
        t = by_name[name]
        for rnd in range(1, a.max_rounds + 1):
            rc, errs, stderr = errors(a.lust, t, work, env)
            if rc == 0:
                status[name] = f"ok after {rnd - 1} rounds"
                break
            if not errs:
                status[name] = f"stopped: exit {rc} with no diagnostic: {tsrust_full.crash_reason({'stderr': stderr, 'rc': rc})}"
                break
            # Only errors with a span on disk inside an item: prune.py's fallback for the others
            # (remove every item whose text names the error's one `name`) takes out unrelated code.
            # Each round's errors are kept in <work>/round-<target>-<n>.json.
            (work / f"round-{name}-{rnd}.json").write_text(json.dumps(errs))
            cache = {}
            located = [e for e in errs if e[1] > 0 and Path(e[0]).resolve().is_relative_to(copy) and in_item(e, cache)]
            if not located:
                # Errors with no span on disk that name an item an earlier round removed (macro
                # output that used it): remove the items that mention that name, as its cascade.
                # `main` is no item name another item uses (every bin has one).
                gone = {n for e in errs for n in names_in(e[3]) if n in cause_of_name and n != "main"}
                if not gone or not remove_users(copy, gone, cause_of_name, removed, name):
                    status[name] = f"stopped: no located error: {errs[0][2]} {errs[0][3][:160]}"
                    break
                print(f"tsrust-deep: {name} round {rnd}: removed users of {sorted(gone)}", flush=True)
                continue
            before = len(removed)
            try:
                prune.prune_round(located, "lust", removed, copy, [], lambda c, m: None)
            except SystemExit as e:
                status[name] = f"stopped: {e}"
                break
            if len(removed) == before:
                status[name] = f"stopped: nothing removed for {errs[0][2]} {errs[0][3][:120]}"
                break
            for r in removed[before:]:
                key = (r["code"], tsrust_full.norm_message(r["message"], copy).removeprefix("unlocated: "))
                parent = next((cause_of_name[n] for n in names_in(r["message"]) if n in cause_of_name), None)
                r["cause"] = list(parent or key)
                r["target"] = name
                cause_of_name.setdefault(r["name"], tuple(r["cause"]))
            (work / "deep.json").write_text(json.dumps({"status": status, "removed": removed}, indent=0))  # partial, each round
            print(f"tsrust-deep: {name} round {rnd}: {len(errs)} errors, {len(removed) - before} items removed", flush=True)
        else:
            status[name] = f"stopped: {a.max_rounds} rounds"
        print(f"tsrust-deep: {name}: {status[name]}", flush=True)
    causes = {}
    for r in removed:
        c = causes.setdefault(tuple(r["cause"]), {"own": 0, "cascade": 0, "items": 0, "files": set(), "example": f"{r['file']} `{r['name']}`"})
        own = (r["code"], tsrust_full.norm_message(r["message"], copy).removeprefix("unlocated: ")) == tuple(r["cause"])
        c["own" if own else "cascade"] += r["lines"]
        c["items"] += 1
        c["files"].add(r["file"])
    rows = sorted(causes.items(), key=lambda kv: -(kv[1]["own"] + kv[1]["cascade"]))
    (work / "deep.json").write_text(json.dumps({"status": status, "removed": removed}, indent=0))
    print("\n| # | code | message | own lines | cascade lines | items | files | example |\n|---|---|---|---:|---:|---:|---:|---|")
    for i, (k, v) in enumerate(rows, 1):
        print(f"| {i} | {k[0]} | {k[1][:110]} | {v['own']} | {v['cascade']} | {v['items']} | {len(v['files'])} | {v['example']} |")
    print(f"tsrust-deep: {sum(r['lines'] for r in removed)} lines removed in {len(removed)} items, {len(rows)} root causes")


if __name__ == "__main__":
    main()
