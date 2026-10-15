#!/usr/bin/env python3
"""The speed benchmark on a pinned ts-rust slice (bench/slices/<name>): lust vs cargo.

Entry point: `scripts/scale-gate.py --slice bench/slices/<name> [options]` (this file
holds the slice mode). The promise it tracks: 100x faster WARM checks after a
one-function edit, on identical source. Cold check, build, and restart are
separate rows.

Both compilers work on ONE source tree, so every measured state is the same
source for both. Per slice it records:
  - cold check and cold build: lust one-shot (no daemon, empty cache) vs
    `cargo check` / `cargo build` after `cargo clean`
  - daemon first check (new session, empty cache), cached restart (new daemon,
    disk cache), no-op check (warm daemon, nothing changed) vs a no-op cargo check
  - body edits: 100+ edits that alternate across fns in different files; each
    inserts or changes one `let` in one fn body; check after every edit
  - signature, type, impl, error, and fix edits from the slice's edits.json,
    each applied and reverted in several cycles
  - warm build after a body edit (a subset of the body edits)
  - wall median, p95, worst per row; lust phase times (--timings) per row;
    C bytes, units compiled, and link time (LUST_STATS, build rows); peak RSS
    (the lust daemon's VmHWM; for cargo, the largest process in its tree)

rustc runs in two configs, each with its own target dir: `default` (stable dev
profile, incremental on) and `threads8` (RUSTC_BOOTSTRAP=1, -Z threads=8). Both
use debuginfo 0. The ratio uses the faster config's median per row.

Exactness, checked on every state: lust and cargo agree on pass or fail (exit
code). Every `--cold-every` states, and on every non-body edit, a cold one-shot
lust check runs on the same state; its stdout, stderr (timing lines removed),
and exit code must equal the warm daemon answer. A mismatch stops the run.

The slice's `main` is empty today, so build rows measure the build of the
whole crate's reachable code, and there is no run row.
"""
import json
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LUST = ROOT / "target/release/lust"
ITEMS = ROOT / "bench/slices/items/target/release/slice-items"
EDIT_TAG = "_lust_bench_edit"
TIMING_LINE = re.compile(r"^  \S.*\s[\d.]+ ms$")
# The --timings header line names the request mode (full, bodies, ...), which
# differs between a warm and a cold answer by design.
TIMING_HEAD = re.compile(r"^lust (check|build) .*: ok \(")

RUSTC_CONFIGS = {
    "default": {},
    "threads8": {"RUSTC_BOOTSTRAP": "1", "RUSTFLAGS": "-Z threads=8"},
}


def pct(xs, p):
    xs = sorted(xs)
    if not xs:
        return None
    k = (len(xs) - 1) * p / 100
    lo = int(k)
    hi = min(lo + 1, len(xs) - 1)
    return xs[lo] + (xs[hi] - xs[lo]) * (k - lo)


def summary(xs):
    if not xs:
        return None
    return {"n": len(xs), "median": round(statistics.median(xs), 2), "p95": round(pct(xs, 95), 2),
            "worst": round(max(xs), 2)}


def parse_timings(stderr):
    """lust --timings stage lines -> {stage: ms}."""
    out = {}
    for line in stderr.splitlines():
        if TIMING_LINE.match(line):
            name, ms = line.strip().rsplit(None, 2)[0], line.strip().rsplit(None, 2)[1]
            try:
                out[name.strip()] = out.get(name.strip(), 0.0) + float(ms)
            except ValueError:
                pass
    return out


def parse_stats(stderr):
    out = {}
    for line in stderr.splitlines():
        if line.startswith("lust-stats:"):
            for kv in line.split(":", 1)[1].split():
                k, _, v = kv.partition("=")
                out[k] = int(v) if v.isdigit() else v
    return out


def strip_noise(text):
    return "\n".join(l for l in text.splitlines()
                     if not TIMING_LINE.match(l) and not TIMING_HEAD.match(l) and not l.startswith("lust-stats:"))


class Bench:
    def __init__(self, slice_dir, opts):
        self.opts = opts
        self.slice_dir = Path(slice_dir).resolve()
        self.manifest = json.loads((self.slice_dir / "prune.json").read_text())
        self.edits_spec = json.loads((self.slice_dir / "edits.json").read_text())
        base = Path(os.environ.get("TMPDIR", "/tmp"))
        self.work = Path(tempfile.mkdtemp(prefix="lust-speed-", dir=base))
        self.crate = self.work / "crate"
        shutil.copytree(self.slice_dir / "src", self.crate / "src")
        root = self.manifest["spec"]["root"]
        self.root = self.crate / "src" / root
        (self.crate / "Cargo.toml").write_text(
            f'[package]\nname = "slice"\nversion = "0.0.0"\nedition = "2024"\n\n'
            f'[[bin]]\nname = "slice"\npath = "src/{root}"\n\n[profile.dev]\ndebug = 0\n\n[workspace]\n')
        self.env = dict(os.environ, LUST_DAEMON_SOCKET=str(self.work / "s.sock"),
                        LUST_CACHE_DIR=str(self.work / "cache"), LUST_DAEMON_IDLE="3600s")
        self.env.pop("LUST_NO_DAEMON", None)
        self.daemon = None
        self.rows = {}
        self.cold_n = 0
        self.states = 0
        self.mismatches = []
        self.rustc_cfgs = [] if opts["no_rustc"] else list(RUSTC_CONFIGS)

    # ---- process helpers

    def run(self, cmd, env=None, cwd=None):
        t = time.perf_counter()
        r = subprocess.run(cmd, cwd=cwd or self.crate, env=env or self.env, capture_output=True, text=True)
        return (time.perf_counter() - t) * 1000, r

    def lust(self, verb, extra_env=None, cold=False):
        env = dict(self.env, **(extra_env or {}))
        if cold:
            self.cold_n += 1
            env = dict(env, LUST_NO_DAEMON="1", LUST_CACHE_DIR=str(self.work / f"cold-{self.cold_n}"))
        cmd = [str(LUST), verb, "--timings", str(self.root)]
        if verb == "build":
            cmd += ["-o", str(self.work / "prog")]
        ms, r = self.run(cmd, env)
        if cold:
            shutil.rmtree(self.work / f"cold-{self.cold_n}", ignore_errors=True)
        return ms, r

    def cargo(self, cfg, verb):
        env = dict(os.environ, CARGO_TARGET_DIR=str(self.work / f"target-{cfg}"), CARGO_NET_OFFLINE="true",
                   **RUSTC_CONFIGS[cfg])
        env.pop("RUSTFLAGS", None) if cfg == "default" else None
        return self.run(["cargo", verb, "-q"], env)

    def cargo_rss_cold(self, cfg, verb):
        """Cold cargo run in a child Python so RUSAGE_CHILDREN covers only that tree."""
        code = ("import resource,subprocess,sys,os;"
                "r=subprocess.run(sys.argv[1:],capture_output=True);"
                "print(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)")
        env = dict(os.environ, CARGO_TARGET_DIR=str(self.work / f"target-{cfg}-rss"), CARGO_NET_OFFLINE="true",
                   **RUSTC_CONFIGS[cfg])
        r = subprocess.run([sys.executable, "-c", code, "cargo", verb, "-q"], cwd=self.crate, env=env,
                           capture_output=True, text=True)
        shutil.rmtree(self.work / f"target-{cfg}-rss", ignore_errors=True)
        return int(r.stdout.strip() or 0)

    def start_daemon(self):
        self.daemon = subprocess.Popen([str(LUST), "daemon"], cwd=self.crate, env=self.env,
                                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        for _ in range(400):
            if (self.work / "s.sock").exists():
                return
            time.sleep(0.025)
        sys.exit("daemon did not start")

    def kill_daemon(self):
        if self.daemon:
            self.daemon.kill()
            self.daemon.wait()
            self.daemon = None
        for f in ("s.sock", "s.sock.lock"):
            (self.work / f).unlink(missing_ok=True)

    def daemon_hwm_kb(self):
        try:
            for line in open(f"/proc/{self.daemon.pid}/status"):
                if line.startswith("VmHWM:"):
                    return int(line.split()[1])
        except (OSError, AttributeError):
            return None

    # ---- recording

    def row(self, name):
        return self.rows.setdefault(name, {"lust": [], "phases": [], "stats": [], **{c: [] for c in self.rustc_cfgs}})

    def measure_check(self, name, expect_ok=True, cold_compare=False):
        """Time a warm lust check and the cargo checks on the current state; check agreement."""
        self.states += 1
        ms, r = self.lust("check")
        rec = self.row(name)
        rec["lust"].append(ms)
        rec["phases"].append(parse_timings(r.stderr))
        ok = r.returncode == 0
        if ok != expect_ok:
            self.fail(f"{name}: lust check exit {r.returncode}, expected {'ok' if expect_ok else 'error'}\n{r.stderr[-1500:]}")
        for cfg in self.rustc_cfgs:
            cms, cr = self.cargo(cfg, "check")
            rec[cfg].append(cms)
            if (cr.returncode == 0) != ok:
                self.fail(f"{name}: lust exit {r.returncode} but cargo check ({cfg}) exit {cr.returncode}\n{cr.stderr[-1500:]}")
        if cold_compare or (self.opts["cold_every"] and self.states % self.opts["cold_every"] == 0):
            _, c = self.lust("check", cold=True)
            if (c.returncode, c.stdout, strip_noise(c.stderr)) != (r.returncode, r.stdout, strip_noise(r.stderr)):
                self.fail(f"{name}: warm daemon answer differs from a cold one-shot check\n"
                          f"warm exit {r.returncode}: {strip_noise(r.stderr)[-800:]}\n"
                          f"cold exit {c.returncode}: {strip_noise(c.stderr)[-800:]}")
            rec.setdefault("cold_compares", 0)
            rec["cold_compares"] += 1
        return ms

    def measure_build(self, name):
        ms, r = self.lust("build", {"LUST_STATS": "1"})
        if r.returncode != 0:
            self.fail(f"{name}: lust build failed\n{r.stderr[-1500:]}")
        rec = self.row(name)
        rec["lust"].append(ms)
        rec["phases"].append(parse_timings(r.stderr))
        st = parse_stats(r.stderr)
        st["link_ms"] = parse_timings(r.stderr).get("link", 0.0)
        rec["stats"].append(st)
        for cfg in self.rustc_cfgs:
            cms, cr = self.cargo(cfg, "build")
            rec[cfg].append(cms)
            if cr.returncode != 0:
                self.fail(f"{name}: cargo build ({cfg}) failed\n{cr.stderr[-1500:]}")
        lr = subprocess.run([str(self.work / "prog")], capture_output=True, text=True)
        if self.rustc_cfgs:
            rr = subprocess.run([str(self.work / f"target-{self.rustc_cfgs[0]}/debug/slice")], capture_output=True, text=True)
            if (lr.returncode, lr.stdout) != (rr.returncode, rr.stdout):
                self.fail(f"{name}: program output differs (lust exit {lr.returncode}, rustc exit {rr.returncode})")

    def fail(self, msg):
        self.kill_daemon()
        print(f"FAIL {msg}", file=sys.stderr)
        print(f"work dir kept: {self.work}", file=sys.stderr)
        sys.exit(1)

    # ---- edits

    def body_targets(self):
        """Fns for body edits: one per file, largest files first, brace on its own line."""
        files = sorted((p for p in (self.crate / "src").rglob("*.rs") if p.name != "support.rs"),
                       key=lambda p: (-p.stat().st_size, str(p)))
        out = []
        for p in files:
            lines = p.read_text().split("\n")
            rows = subprocess.run([str(ITEMS), "--bodies", str(p)], capture_output=True, text=True).stdout.split("\n")
            for row in rows:
                if not row:
                    continue
                ol, oc, cl, cc, start = map(int, row.split())
                head = lines[start - 1]
                if cl - ol < 3 or lines[ol - 1][oc:].strip() or "const fn" in head:
                    continue
                out.append((p, ol))
                break
            if len(out) == self.opts["units"]:
                break
        return out

    def body_edit(self, target, value):
        """Insert or change the bench `let` on the line after one fn body's open brace."""
        p, ol = target
        lines = p.read_text().split("\n")
        indent = " " * (len(lines[ol - 1]) - len(lines[ol - 1].lstrip()) + 4)
        new = f"{indent}let {EDIT_TAG}: u32 = {value};"
        if EDIT_TAG in lines[ol]:
            lines[ol] = new
        else:
            lines.insert(ol, new)
        p.write_text("\n".join(lines))

    def text_edit(self, pairs):
        for rel, old, new in pairs:
            p = self.crate / "src" / rel
            t = p.read_text()
            if t.count(old) != 1:
                self.fail(f"edit anchor must occur once in {rel}: {old!r} (found {t.count(old)})")
            p.write_text(t.replace(old, new))

    # ---- the run

    def go(self):
        o = self.opts
        if not ITEMS.exists():
            subprocess.run(["cargo", "build", "--release", "-q", "--offline"], cwd=ITEMS.parent.parent.parent, check=True)
        lines = sum(1 for p in (self.crate / "src").rglob("*.rs") for _ in open(p))
        print(f"slice {self.slice_dir.name}: {lines} lines, ts-rust {self.manifest['tsrust_commit'][:9]}, work {self.work}", flush=True)
        rss = {}

        # Cold rows, interleaved per rep.
        for _ in range(o["reps"]):
            for verb in ("check", "build"):
                ms, r = self.lust(verb, {"LUST_STATS": "1"}, cold=True)
                if r.returncode != 0:
                    self.fail(f"cold {verb}: lust rejects the slice\n{r.stderr[-1500:]}")
                rec = self.row(f"cold {verb}")
                rec["lust"].append(ms)
                rec["phases"].append(parse_timings(r.stderr))
                if verb == "build":
                    st = parse_stats(r.stderr)
                    st["link_ms"] = parse_timings(r.stderr).get("link", 0.0)
                    rec["stats"].append(st)
                for cfg in self.rustc_cfgs:
                    shutil.rmtree(self.work / f"target-{cfg}", ignore_errors=True)
                    cms, cr = self.cargo(cfg, verb)
                    if cr.returncode != 0:
                        self.fail(f"cold cargo {verb} ({cfg}) failed\n{cr.stderr[-1500:]}")
                    rec[cfg].append(cms)
        # One-shot peak RSS (a child process tree each).
        rss["lust_cold_check_kb"] = self.cold_rss("check")
        for cfg in self.rustc_cfgs:
            rss[f"cargo_cold_check_kb_{cfg}"] = self.cargo_rss_cold(cfg, "check")
        # Prime both cargo configs for the warm rows (check and build artifacts).
        for cfg in self.rustc_cfgs:
            self.cargo(cfg, "check")
            self.cargo(cfg, "build")

        self.start_daemon()
        self.measure_check("daemon first check (new session, empty cache)")
        for _ in range(o["reps"]):
            self.measure_check("no-op check (warm daemon)")
        for _ in range(o["reps"]):
            self.kill_daemon()
            self.start_daemon()
            self.measure_check("cached restart check (new daemon, disk cache)")

        targets = self.body_targets()
        if len(targets) < 2:
            self.fail("fewer than 2 body edit targets")
        build_every = max(1, o["edits"] // o["build_samples"]) if o["build_samples"] else 0
        for i in range(o["edits"]):
            self.body_edit(targets[i % len(targets)], i + 1)
            self.measure_check("body edit check (one fn)")
            if build_every and i % build_every == 0:
                self.measure_build("body edit build (one fn)")

        e = self.edits_spec
        for _ in range(o["cycles"]):
            for kind in ("signature", "type", "impl"):
                spec = e[kind]
                pairs = [(x["file"], x["old"], x["new"]) for x in spec["edits"]]
                self.text_edit(pairs)
                self.measure_check(f"{kind} edit check", cold_compare=True)
                self.text_edit([(f, n, old) for f, old, n in pairs])
                self.measure_check(f"{kind} edit check", cold_compare=True)
            self.body_edit(targets[0], '"not a u32"')
            self.measure_check("error edit check (both reject)", expect_ok=False, cold_compare=True)
            self.body_edit(targets[0], 7)
            self.measure_check("fix edit check", cold_compare=True)
        rss["lust_daemon_hwm_kb"] = self.daemon_hwm_kb()
        self.kill_daemon()
        return self.report(lines, rss, targets)

    def cold_rss(self, verb):
        code = ("import resource,subprocess,sys;subprocess.run(sys.argv[1:],capture_output=True);"
                "print(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)")
        env = dict(self.env, LUST_NO_DAEMON="1", LUST_CACHE_DIR=str(self.work / "rss-cache"))
        r = subprocess.run([sys.executable, "-c", code, str(LUST), verb, str(self.root)], env=env,
                           capture_output=True, text=True)
        shutil.rmtree(self.work / "rss-cache", ignore_errors=True)
        return int(r.stdout.strip() or 0)

    def report(self, lines, rss, targets):
        rows = []
        for name, rec in self.rows.items():
            lust = summary(rec["lust"])
            rus = {c: summary(rec[c]) for c in self.rustc_cfgs if rec[c]}
            best = min(rus.items(), key=lambda kv: kv[1]["median"]) if rus else None
            phases = {}
            for ph in rec["phases"]:
                for k, v in ph.items():
                    phases.setdefault(k, []).append(v)
            stats = {}
            for st in rec["stats"]:
                for k in ("c_bytes", "units_compiled", "unit_cache_hits", "link_ms"):
                    if isinstance(st.get(k), (int, float)):
                        stats.setdefault(k, []).append(st[k])
            rows.append({
                "row": name, "lust": lust, "rustc": rus,
                "rustc_best": {"config": best[0], **best[1]} if best else None,
                "ratio": round(best[1]["median"] / lust["median"], 1) if best and lust["median"] else None,
                "lust_phases_median_ms": {k: round(statistics.median(v), 2) for k, v in phases.items()},
                "build_stats_median": {k: statistics.median(v) for k, v in stats.items()},
                "cold_compares": rec.get("cold_compares", 0),
            })
        lust_commit = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--short", "HEAD"],
                                     capture_output=True, text=True).stdout.strip()
        rustc_v = subprocess.run(["rustc", "--version"], capture_output=True, text=True).stdout.strip()
        out = {
            "slice": self.slice_dir.name, "lines": lines, "code_lines": self.manifest.get("code_lines"),
            "tsrust_commit": self.manifest["tsrust_commit"], "lust_commit": lust_commit, "rustc": rustc_v,
            "host": {"nproc": os.cpu_count(), "load_at_end": os.getloadavg()[0]},
            "opts": self.opts, "states_checked": self.states,
            "body_edit_targets": [f"{p.relative_to(self.crate / 'src')}:{ol}" for p, ol in targets],
            "peak_rss": rss, "rows": rows,
        }
        shutil.rmtree(self.work, ignore_errors=True)
        return out


def print_table(res):
    print(f"\n{res['slice']}: {res['lines']} lines ({res['code_lines']} code), ts-rust {res['tsrust_commit'][:9]}, "
          f"lust {res['lust_commit']}, {res['rustc']}, {res['host']['nproc']} cpus")
    print(f"{'row':<48} {'lust med':>9} {'p95':>8} {'worst':>8} {'n':>4} {'rustc med':>10} {'cfg':>9} {'ratio':>7}")
    for r in res["rows"]:
        l, b = r["lust"], r["rustc_best"]
        print(f"{r['row']:<48} {l['median']:>9.1f} {l['p95']:>8.1f} {l['worst']:>8.1f} {l['n']:>4} "
              f"{(b['median'] if b else float('nan')):>10.1f} {(b['config'] if b else '-'):>9} "
              f"{(str(r['ratio']) + 'x') if r['ratio'] else '-':>7}")
    print(f"peak RSS: {res['peak_rss']}")
    print(f"states checked: {res['states_checked']} (lust and cargo agree on every one)")


def main(argv):
    opts = {"edits": 120, "reps": 5, "cycles": 5, "units": 24, "build_samples": 12, "cold_every": 10,
            "no_rustc": False}
    slice_dir = None
    json_out = None
    args = list(argv)
    while args:
        a = args.pop(0)
        if a == "--slice":
            slice_dir = args.pop(0)
        elif a == "--json":
            json_out = args.pop(0)
        elif a == "--quick":
            opts.update(edits=20, reps=3, cycles=1, build_samples=2, cold_every=10)
        elif a == "--no-rustc":
            opts["no_rustc"] = True
        elif a.startswith("--") and a[2:].replace("-", "_") in opts:
            opts[a[2:].replace("-", "_")] = int(args.pop(0))
        else:
            sys.exit(f"unknown argument: {a}")
    if not slice_dir:
        sys.exit("usage: scale-gate.py --slice bench/slices/<name> [--quick] [--edits N] [--reps N] [--cycles N] "
                 "[--units N] [--build-samples N] [--cold-every N] [--no-rustc] [--json out.json]")
    if not LUST.exists():
        sys.exit(f"{LUST} not built; run cargo build --release first")
    res = Bench(slice_dir, opts).go()
    print_table(res)
    if json_out:
        Path(json_out).write_text(json.dumps(res, indent=1) + "\n")
        print(f"json: {json_out}")


if __name__ == "__main__":
    main(sys.argv[1:])
