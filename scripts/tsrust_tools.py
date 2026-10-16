#!/usr/bin/env python3
"""The ts-rust codegen tools under lust: the first fork targets that check and build.

Gate form (no argument): the pinned copy in bench/tsrust-tools (the fork's two tool crates,
their inputs, and a workspace manifest; no dependencies) is checked by lust (both libs and
both bins), the two bins are built by lust and by Cargo, and the parity runner's tool runs
(tsrust_parity.TOOL_RUNS) must give the same exit code, stdout, stderr and files.
A lust timeout is a hang: a failure, never a reject.
Last line: "tsrust-tools: <ok> passed, <bad> failed".

--refresh: copy the tools and their inputs again from third_party/ts-rust (the pinned fork).
Run it after a fork bump that changes tools/, then commit bench/tsrust-tools.
"""
import argparse
import os
import shutil
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import tsrust_full  # noqa: E402
import tsrust_parity  # noqa: E402

ROOT = HERE.parent
PINNED = ROOT / "bench/tsrust-tools"
TOOLS = ["ts_ast_codegen", "ts_diagnostics_codegen"]
# Fork files the tool runs read (tsrust_parity.TOOL_RUNS), at the same relative paths.
INPUTS = [
    "crates/ts_goport/src/astdata/syntax_kind.rs",
    "crates/ts_goport/src/astdata/ast_generated.rs",
    "crates/ts_goport/data/effect/effectDiagnosticMessages.json",
]


def refresh():
    fork = ROOT / "third_party/ts-rust"
    if not (fork / "Cargo.toml").exists():
        sys.exit("tsrust-tools: third_party/ts-rust is not checked out")
    if PINNED.exists():
        shutil.rmtree(PINNED)
    for t in TOOLS:
        shutil.copytree(fork / "tools" / t, PINNED / "tools" / t)
    for f in INPUTS:
        (PINNED / f).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(fork / f, PINNED / f)
    # The workspace keeps the fork's package and lint tables, with only the two tools.
    ws = tomllib.loads((fork / "Cargo.toml").read_text())["workspace"]
    text = (fork / "Cargo.toml").read_text()
    start = text.index("[workspace.package]")
    members = "".join(f'    "tools/{t}",\n' for t in TOOLS)
    head = f'# Pinned copy of the ts-rust fork\'s codegen tools (scripts/tsrust_tools.py --refresh).\n[workspace]\nresolver = "{ws.get("resolver", "2")}"\nmembers = [\n{members}]\n\n'
    (PINNED / "Cargo.toml").write_text(head + text[start:])
    head_rev = subprocess.run(["git", "-C", str(fork), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    (PINNED / "FORK_REV").write_text(head_rev + "\n")
    r = subprocess.run(["cargo", "generate-lockfile", "--offline"], cwd=PINNED)
    print(f"tsrust-tools: refreshed {PINNED.relative_to(ROOT)} from fork {head_rev[:9]}")
    return r.returncode


def gate(lust, timeout):
    bad, ok = [], 0
    with tempfile.TemporaryDirectory(prefix="tsrust-tools.") as tmp:
        out = Path(tmp)
        (out / "bin").mkdir()
        work = out / "fork"
        shutil.copytree(PINNED, work)
        ts = tsrust_full.targets(work)
        for t in ts:
            r = tsrust_full.run_lust(lust, "check", t, out, timeout)
            line = f"check {t['name']}: {r['status']}"
            if r["status"] == "ok":
                ok += 1
            else:
                bad.append(line + f" {r['diags'][0]['message'][:120] if r['diags'] else r['stderr'][-200:]}")
            print(f"tsrust-tools: {line}", flush=True)
        for t in (t for t in ts if t["kind"] == "bin"):
            r = tsrust_full.run_lust(lust, "build", t, out, timeout)
            line = f"build {t['name']}: {r['status']}"
            if r["status"] == "ok":
                ok += 1
            else:
                bad.append(line + f" {r['diags'][0]['message'][:120] if r['diags'] else r['stderr'][-200:]}")
            print(f"tsrust-tools: {line}", flush=True)
        c = subprocess.run(["cargo", "build", "--release", "--offline", "--bins", "-q"], cwd=work,
                           env={**os.environ, "CARGO_TARGET_DIR": str(out / "cargo-target")}, capture_output=True, text=True)
        if c.returncode != 0:
            bad.append(f"cargo build failed: {c.stderr[-300:]}")
        else:
            for tag, res in tsrust_parity.parity_tools(work, out / "cargo-target/release", out / "bin", out, timeout):
                if res == "same":
                    ok += 1
                else:
                    bad.append(f"parity {tag}: {res}")
    for b in bad:
        print(f"tsrust-tools: FAIL {b}")
    print(f"tsrust-tools: {ok} passed, {len(bad)} failed")
    return 1 if bad else 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--refresh", action="store_true")
    ap.add_argument("--lust", default=str(ROOT / "target/release/lust"))
    ap.add_argument("--timeout", type=int, default=300)
    a = ap.parse_args()
    sys.exit(refresh() if a.refresh else gate(a.lust, a.timeout))


if __name__ == "__main__":
    main()
