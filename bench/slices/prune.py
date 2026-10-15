#!/usr/bin/env python3
"""Build a pinned ts-rust slice: the part of a ts-rust crate that lust accepts today.

The slice is ts-rust source, copied verbatim, minus whole items. The loop:
run `lust check` on the slice root, remove the innermost removable item that
holds each error (bench/slices/items lists the items), and repeat until lust
accepts. Then run rustc on the result and prune its errors the same way, then
lust again, until both accept. Every removed item is recorded with the
compiler and the error code that removed it. A rustc-only error means lust
accepted code rustc rejects; the manifest lists those separately (they are
rule-zero bugs or prune side effects, for a human to read). Last, `lust build`
must pass too (the benchmark has build rows); a build failure or panic removes
the fn that causes it, found by the same bisect, and is listed separately.

Removing an item makes its users fail to resolve, so the loop also removes
them: the slice is closed under its own dependencies by construction. It
grows by itself when lust supports more: rerun this script on the same spec.

Usage: prune.py <spec.json> <out-dir> [--lust PATH] [--max-rounds N]

spec.json (see bench/slices/*/spec.json):
  tsrust_dir   ts-rust checkout (read only; default /home/theo/.t3/projects/ts-rust)
  src_dir      dir in ts-rust that holds the crate's files (copied whole)
  root_from    the crate root file in src_dir; copied to `root` with `append` added
  root         new root file name, written next to root_from (the bin crate entry)
  append       text appended to the root (stand-in mods, fn main)
  support      extra files copied into src_dir of the slice: {dest: path-in-lust-repo}
  rewrite      extern crate names whose paths become `crate::<name>::` (stand-ins)
  root_replace optional [[old, new], ...] text edits of the root (the root is bench text,
               not a ts-rust module file; use it to unmount a module lust cannot take)

Only the files in root_from's module tree are copied.
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
ROOT = HERE.parent.parent
ITEMS = HERE / "items/target/release/slice-items"


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def build_items_tool():
    if not ITEMS.exists():
        r = sh(["cargo", "build", "--release", "-q", "--offline"], cwd=HERE / "items")
        if r.returncode != 0:
            sys.exit(f"slice-items build failed:\n{r.stderr[-2000:]}")


def copy_tree(spec, out):
    src = Path(spec.get("tsrust_dir", "/home/theo/.t3/projects/ts-rust")) / spec["src_dir"]
    dst = out / "src"
    r = sh([str(ITEMS), "--tree", str(src / spec["root_from"])])
    if r.returncode != 0:
        sys.exit(f"slice-items --tree: {r.stderr.strip()}")
    for line in r.stdout.splitlines():
        rel = Path(line).relative_to(src)
        (dst / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(line, dst / rel)
    for d, s in spec.get("support", {}).items():
        (dst / d).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy(ROOT / s, dst / d)
    root_text = (src / spec["root_from"]).read_text()
    for old, new in spec.get("root_replace", []):
        if old not in root_text:
            sys.exit(f"root_replace: text not found: {old!r}")
        root_text = root_text.replace(old, new, 1)
    (dst / spec["root"]).write_text(root_text + spec.get("append", ""))
    names = spec.get("rewrite", [])
    if names:
        pat = re.compile(r"(?<![\w:])(" + "|".join(map(re.escape, names)) + r")::")
        for p in dst.rglob("*.rs"):
            if str(p.relative_to(dst)) in spec.get("support", {}):
                continue
            t = p.read_text()
            n = pat.sub(r"crate::\1::", t)
            if n != t:
                p.write_text(n)
    return dst / spec["root"]


def lust_errors(lust, root, env, strict=True, verb="check"):
    """Located lust errors of `lust <verb>`. A build that fails with no located error
    (a panic) gives one error at line 0, which the caller bisects."""
    cmd = [lust, verb, str(root), "--json", "--max-errors", "100000"]
    if verb == "build":
        cmd += ["-o", str(Path(env["LUST_CACHE_DIR"]) / "slice-bin")]
    r = sh(cmd, env=env)
    errs, other = [], []
    for line in r.stdout.splitlines() + r.stderr.splitlines():
        if not line.startswith("{"):
            continue
        try:
            d = json.loads(line)
        except ValueError:
            continue
        if d.get("severity") != "error":
            continue
        sp = d.get("span") or {}
        if d.get("file") and sp.get("line"):
            line = sp["line"] if located(d["file"], sp) else 0
            errs.append((d["file"], line, d.get("code", ""), d.get("message", "")))
        else:
            other.append(d.get("message", ""))
    if verb == "build" and r.returncode != 0 and not errs:
        first = next((l for l in r.stderr.splitlines() if l.strip()), "")
        return [(str(root), 0, "BUILD", re.sub(r"\(\d+\)", "", first)[:200])]
    if strict and r.returncode != 0 and not errs:
        tail = (r.stderr or r.stdout)[-1500:]
        sys.exit(f"lust failed with no located error (exit {r.returncode}):\n{other}\n{tail}")
    return errs


def located(path, sp):
    """True when the span's byte offset is at its line and column in the file on disk.

    lust reports some spans in its own std source under the user's root file name;
    those fail this check and go to the bisect instead.
    """
    try:
        data = Path(path).read_bytes()
    except OSError:
        return False
    off = sp.get("start", -1)
    if not 0 <= off <= len(data):
        return False
    line = data.count(b"\n", 0, off) + 1
    col = len(data[data.rfind(b"\n", 0, off) + 1:off].decode("utf-8", "replace")) + 1
    return line == sp["line"] and col == sp.get("col", col)


def rustc_errors(root, work):
    r = sh(["rustc", "--edition", "2024", "--crate-type", "bin", "--emit=metadata", "-A", "warnings",
            "--error-format=short", "-o", str(work / "slice.rmeta"), str(root)])
    errs = []
    for line in r.stderr.splitlines():
        m = re.match(r"^(.+?\.rs):(\d+):(\d+): error(\[E\d+\])?: (.*)$", line)
        if m:
            f = m.group(1)
            if not os.path.isabs(f):
                f = str((Path.cwd() / f).resolve())
            errs.append((f, int(m.group(2)), (m.group(4) or "").strip("[]"), m.group(5)))
    if r.returncode != 0 and not errs:
        sys.exit(f"rustc failed with no located error:\n{r.stderr[-1500:]}")
    return errs


def items_of(path, cache):
    if path not in cache:
        r = sh([str(ITEMS), path])
        if r.returncode != 0:
            sys.exit(f"slice-items: {r.stderr.strip()}")
        cache[path] = [(int(a), int(b), int(c), k, n) for a, b, c, k, n in (l.split() for l in r.stdout.splitlines())]
    return cache[path]


def prune_round(errs, tool, removed, src_root, unlocated, relocate):
    """Remove the innermost item holding each error. Returns the number of items removed."""
    by_file = {}
    cache = {}

    def innermost(f, line):
        hits = [it for it in items_of(f, cache) if it[0] <= line <= it[1]]
        # The deepest; on a tie (an impl and its fn share a line) the shortest.
        return max(hits, key=lambda t: (t[2], -(t[1] - t[0]))) if hits else None

    for f, line, code, msg in errs:
        f = str(Path(f).resolve())
        if not f.startswith(str(src_root)):
            sys.exit(f"error outside the slice ({f}:{line}): {code} {msg}")
        it = innermost(f, line)
        if it:
            by_file.setdefault(f, {})[(it[0], it[1])] = (it, code, msg)
            continue
        # No usable location: lust put the span on line 1, or on one of its std lines
        # that it reports under the root file. Find the fn by bisecting body stubs.
        hit = relocate(code, msg)
        if hit:
            p, fn_line = hit
            it = innermost(p, fn_line)
            by_file.setdefault(p, {})[(it[0], it[1])] = (it, code, "unlocated: " + msg)
            unlocated.append({"code": code, "message": msg[:160], "found_in": f"{os.path.relpath(p, src_root)}:{fn_line}"})
            continue
        # Not in a body (a bound or an impl header). When the message names one item,
        # as in "unknown trait `TryFrom`", remove the items whose text names it.
        names = re.findall(r"`([A-Za-z_][A-Za-z0-9_]*)`", msg)
        if len(names) != 1:
            sys.exit(f"cannot locate the error reported at {f}:{line}: {code} {msg}")
        found = []
        for p in sorted(src_root.rglob("*.rs")):
            for i, l in enumerate(p.read_text().split("\n"), 1):
                if re.search(rf"\b{names[0]}\b", l) and (it := innermost(str(p), i)):
                    by_file.setdefault(str(p), {})[(it[0], it[1])] = (it, code, "unlocated: " + msg)
                    found.append(f"{os.path.relpath(p, src_root)}:{i}")
        if not found:
            sys.exit(f"cannot locate the error reported at {f}:{line}: {code} {msg}")
        unlocated.append({"code": code, "message": msg[:160], "found_in": found[:20]})
    n = 0
    for f, spans in by_file.items():
        lines = Path(f).read_text().split("\n")
        # Drop nested duplicates: keep outer spans only when an outer one is also listed.
        keep = sorted(spans)
        outer = []
        for s in keep:
            if outer and s[0] >= outer[-1][0] and s[1] <= outer[-1][1]:
                continue
            outer.append(s)
        for s in sorted(outer, reverse=True):
            it, code, msg = spans[s]
            del lines[s[0] - 1:s[1]]
            removed.append({"file": os.path.relpath(f, src_root), "kind": it[3], "name": it[4],
                            "lines": s[1] - s[0] + 1, "by": tool, "code": code, "message": msg[:160]})
            n += 1
        Path(f).write_text("\n".join(lines))
    return n


def bisect(lust, root, env, src_root, code, msg, verb="check"):
    """Find the fn whose body makes lust report (code, msg) with no usable span.

    Stubs fn bodies as `{ loop {} }` in halves: a body set that makes the error go
    away when stubbed holds the culprit. Files are restored after every probe.
    Returns (file, first line of the fn) or None when no body explains the error.
    """
    bodies = []
    for p in sorted(src_root.rglob("*.rs")):
        r = sh([str(ITEMS), "--bodies", str(p)])
        rows = sorted(tuple(map(int, l.split())) for l in r.stdout.splitlines())
        outer = []
        for b in rows:
            if outer and (b[0], b[1]) <= (outer[-1][2], outer[-1][3]):
                continue  # nested in the previous body
            outer.append(b)
        bodies += [(str(p), b) for b in outer]
    originals = {}

    def has_error(stub):
        by = {}
        for p, b in stub:
            by.setdefault(p, []).append(b)
        for p, bs in by.items():
            text = originals.setdefault(p, Path(p).read_text())
            lines = text.split("\n")
            for ol, oc, cl, cc, _ in sorted(bs, reverse=True):
                head = lines[ol - 1][:oc - 1]
                tail = lines[cl - 1][cc:]
                lines[ol - 1:cl] = [head + "{ loop {} }" + tail]
            Path(p).write_text("\n".join(lines))
        try:
            return any(c == code and m == msg for _, _, c, m in lust_errors(lust, root, env, strict=False, verb=verb))
        finally:
            for p in by:
                Path(p).write_text(originals[p])

    if has_error(bodies):
        return None
    zero, cand = [], bodies
    while len(cand) > 1:
        half, rest = cand[:len(cand) // 2], cand[len(cand) // 2:]
        if not has_error(zero + half):
            cand = half
        else:
            zero, cand = zero + half, rest
    p, b = cand[0]
    return p, b[4]


def write_manifest(path, m):
    """prune.json: the summary fields indented, then one removed item per line."""
    by_code = {}
    for r in m["removed"]:
        k = r["by"] + " " + r["code"]
        by_code[k] = by_code.get(k, 0) + r["lines"]
    m = dict(m, removed_lines_by_oracle_and_code=dict(sorted(by_code.items(), key=lambda kv: -kv[1])))
    head = {k: v for k, v in m.items() if k != "removed"}
    text = json.dumps(head, indent=1)[:-2] + ',\n "removed": [\n'
    text += ",\n".join("  " + json.dumps(r) for r in m["removed"]) + "\n ]\n}\n"
    path.write_text(text)


def count_lines_file(p):
    return sum(1 for _ in open(p))


def nonblank_lines(src):
    return sum(sum(1 for l in open(p) if l.strip() and not l.strip().startswith("//")) for p in src.rglob("*.rs"))


def count_lines(src):
    return sum(sum(1 for _ in open(p)) for p in src.rglob("*.rs"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("spec")
    ap.add_argument("out")
    ap.add_argument("--lust", default=str(ROOT / "target/release/lust"))
    ap.add_argument("--max-rounds", type=int, default=400)
    a = ap.parse_args()
    spec = json.loads(Path(a.spec).read_text())
    out = Path(a.out).resolve()
    if out.exists():
        shutil.rmtree(out)
    build_items_tool()
    root = copy_tree(spec, out)
    src_root = (out / "src").resolve()
    start_lines = count_lines(src_root)
    env = dict(os.environ, LUST_NO_DAEMON="1", LUST_CACHE_DIR=str(out / ".lust-cache"))
    removed = []
    unlocated = []
    rounds = 0
    # Three oracles in turn until all accept: lust check, rustc, lust build.
    tools = ["lust", "rustc", "lust-build"]
    tool = "lust"
    clean = set()
    while rounds < a.max_rounds:
        rounds += 1
        if tool == "rustc":
            errs = rustc_errors(root, out)
        else:
            errs = lust_errors(a.lust, root, env, verb="build" if tool == "lust-build" else "check")
        if not errs:
            clean.add(tool)
            if len(clean) == len(tools):
                break
            tool = tools[(tools.index(tool) + 1) % len(tools)]
            continue
        clean = set()
        verb = "build" if tool == "lust-build" else "check"
        n = prune_round(errs, tool, removed, src_root, unlocated,
                        lambda c, m: bisect(a.lust, root, env, src_root, c, m, verb))
        print(f"round {rounds} ({tool}): {len(errs)} errors, removed {n} items, {count_lines(src_root)} lines left", flush=True)
    else:
        sys.exit("prune did not converge")
    # Keep only the files rustc loads on this target: cfg-disabled modules (windows,
    # darwin) and unmounted files are not part of the crate. Both compilers must
    # still accept after that.
    dep = out / "slice.d"
    sh(["rustc", "--edition", "2024", "--crate-type", "bin", "--emit=dep-info", "-A", "warnings",
        "-o", str(dep), str(root)])
    loaded = {str(Path(t).resolve()) for t in re.findall(r"(\S+\.rs):", dep.read_text())}
    dropped = 0
    for p in list(src_root.rglob("*.rs")):
        if str(p.resolve()) not in loaded:
            dropped += count_lines_file(p)
            p.unlink()
    for d in sorted((x for x in src_root.rglob("*") if x.is_dir()), reverse=True):
        if not any(d.iterdir()):
            d.rmdir()
    if lust_errors(a.lust, root, env) or rustc_errors(root, out) or lust_errors(a.lust, root, env, verb="build"):
        sys.exit("the slice no longer checks after dropping unloaded files")
    dep.unlink()
    shutil.rmtree(out / ".lust-cache", ignore_errors=True)
    (out / "slice.rmeta").unlink(missing_ok=True)
    ts = Path(spec.get("tsrust_dir", "/home/theo/.t3/projects/ts-rust"))
    commit = sh(["git", "-C", str(ts), "rev-parse", "HEAD"]).stdout.strip()
    lust_commit = sh(["git", "-C", str(ROOT), "rev-parse", "HEAD"]).stdout.strip()
    manifest = {
        "tsrust_commit": commit, "lust_commit": lust_commit, "spec": spec,
        "lines_before": start_lines, "lines": count_lines(src_root),
        "code_lines": nonblank_lines(src_root), "unloaded_lines_dropped": dropped, "rounds": rounds,
        "removed_items": len(removed),
        "removed_by_rustc": [r for r in removed if r["by"] == "rustc"],
        "removed_by_lust_build": [r for r in removed if r["by"] == "lust-build"],
        "unlocated_errors": unlocated,
        "removed": removed,
    }
    write_manifest(out / "prune.json", manifest)
    print(f"slice: {manifest['lines']} lines ({manifest['code_lines']} code) of {start_lines} kept, {len(removed)} items removed "
          f"({len(manifest['removed_by_rustc'])} by rustc), {rounds} rounds")


if __name__ == "__main__":
    main()
