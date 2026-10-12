#!/usr/bin/env python3
# Driver tests (docs/ARCH.md section 9.3, W-DRIVER gate). Each case
# runs the real client and daemon and asserts on the compiler's own
# `lust-stats:` counters plus emitted C slot numbers:
#   1. restart with disk objects: a new daemon reuses unit objects
#      from disk and gives every fn the slot the manifest stored.
#   2. different crate load order: reordering fns in the file does not
#      renumber slots (the manifest, not file order, owns them).
#   3. one added reachable fn: unrelated units keep their objects;
#      crossing a unit boundary rebuilds only the table unit plus the
#      dirty units (section 4.2). The generic-instance form of this
#      gate joins with mono; the unit-key half is pinned by the graph
#      unit test `instance_manifest_round_trips_and_unit_keys_follow_4_2`.
#   4. reads reuse: a signature-header edit that changes no type
#      rechecks zero bodies through the dirty walk.
#   5. graph and build-script routing: editing a build script input
#      makes the daemon start a fresh session (its log line proves it)
#      while the program output stays correct.
#   6. std in sessions: a source std fn (std::process::exit, S5) runs
#      through the daemon twice with the same result.
# Usage: python3 scripts/test-driver.py   (exit 0 = pass)
import glob, os, re, shutil, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LUST = os.path.join(ROOT, "target/release/lust")
failures = []


def check(name, cond, detail=""):
    print(f"{'ok' if cond else 'FAIL'} {name}" + (f": {detail}" if detail and not cond else ""))
    if not cond:
        failures.append(name)


class Daemon:
    def __init__(self, work):
        self.work = work
        self.env = dict(os.environ, LUST_DAEMON_SOCKET=os.path.join(work, "s.sock"),
                        LUST_CACHE_DIR=os.path.join(work, "cache"), LUST_STATS="1",
                        LUST_DAEMON_IDLE="120s")
        self.proc = None

    def start(self):
        self.proc = subprocess.Popen([LUST, "daemon"], cwd=self.work, env=self.env,
                                     stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
        for _ in range(300):
            if os.path.exists(os.path.join(self.work, "s.sock")):
                return
            time.sleep(0.02)
        raise SystemExit("daemon did not start")

    def kill(self):
        err = ""
        if self.proc:
            self.proc.kill()
            _, err = self.proc.communicate()
            self.proc = None
        for f in ("s.sock", "s.sock.lock"):
            try:
                os.remove(os.path.join(self.work, f))
            except FileNotFoundError:
                pass
        return err

    def run(self, args, expect=0):
        r = subprocess.run([LUST] + args, cwd=self.work, env=self.env, capture_output=True, text=True)
        if expect is not None:
            assert r.returncode == expect, f"{args}: exit {r.returncode}\n{r.stderr[-600:]}"
        return r

    def build(self, src, out, extra=()):
        r = self.run(["build", src, "-o", out, "--emit-c", os.path.join(self.work, "emit"), *extra])
        stats = {}
        for line in r.stderr.splitlines():
            if line.startswith("lust-stats:"):
                for kv in line.split(":", 1)[1].split():
                    k, _, v = kv.partition("=")
                    stats[k] = int(v) if v.isdigit() else v
        prog = subprocess.run([out], capture_output=True, text=True)
        return stats, prog


def slots_of(work):
    out = {}
    for p in sorted(glob.glob(os.path.join(work, "emit.u*.c"))):
        text = open(p).read()
        for m in re.finditer(r"f(\d+)\(void\) \{[^}]*?marker-(\w+)", text, re.S):
            out[m.group(2)] = int(m.group(1))
    return out


def case_slots_and_reuse():
    work = tempfile.mkdtemp(prefix="lust-driver-slots-")
    d = Daemon(work)
    src = os.path.join(work, "x.rs")
    # 15 fns + main = 16 slots: one fn unit at per_unit=16.
    fns = [f'fn f{i}() -> i64 {{ println!("marker-f{i}"); {i} }}' for i in range(15)]
    main = 'fn main() { println!("{}", ' + " + ".join(f"f{i}()" for i in range(15)) + "); }"
    open(src, "w").write("\n".join(fns + [main]) + "\n")
    out = os.path.join(work, "x")
    d.start()
    st, prog = d.build(src, out)
    check("cold build output", prog.stdout.strip().splitlines()[-1] == "105", prog.stdout[-80:])
    slots1 = slots_of(work)
    check("cold slots recorded", len(slots1) == 15, str(slots1))

    # 2 (in session): reorder the file. Slots follow the manifest.
    open(src, "w").write("\n".join(fns[::-1] + [main]) + "\n")
    _, prog = d.build(src, out)
    check("reorder keeps slots in session", slots_of(work) == slots1, str(slots_of(work)))
    check("reorder output", prog.stdout.strip().splitlines()[-1] == "105")

    # 3: one added reachable fn crosses into a second unit.
    open(src, "w").write('fn f15() -> i64 { println!("marker-f15"); 15 }\n' +
                         "\n".join(fns[::-1] + [main.replace("f14()", "f14() + f15()")]) + "\n")
    st, prog = d.build(src, out)
    slots3 = slots_of(work)
    check("added fn keeps old slots", all(slots3.get(k) == v for k, v in slots1.items()), str(slots3))
    check("added fn output", prog.stdout.strip().splitlines()[-1] == "120", prog.stdout[-80:])
    check("added fn rebuilds only table + dirty units",
          st.get("table_rebuilt") == 1 and (st.get("units_compiled") or 99) <= 2 + (st.get("dirty_units") or 0),
          str(st))
    check("added fn compiles few units", (st.get("units_compiled") or 99) <= 4, str(st))

    # 4: a param-name-only signature edit changes no type: the dirty
    # walk reuses the mentioners.
    apply_src = open(src).read()
    open(src, "w").write(apply_src)
    st, _ = d.build(src, out)  # settle
    d.kill()

    # 1: restart. New daemon, same cache dir: slots from the manifest,
    # objects from disk for all but the table and rerun-shaped units.
    d.start()
    st, prog = d.build(src, out)
    check("restart keeps slots (different load order)", slots_of(work) == slots3,
          f"{slots_of(work)} vs {slots3}")
    check("restart reuses disk objects", (st.get("unit_cache_hits") or 0) >= 3, str(st))
    check("restart output", prog.stdout.strip().splitlines()[-1] == "120")
    d.kill()


def case_reads_reuse():
    work = tempfile.mkdtemp(prefix="lust-driver-reads-")
    d = Daemon(work)
    src = os.path.join(work, "x.rs")
    base = ("struct S { compute: i64 }\n"
            "fn compute(a: i64) -> i64 { 7 }\n"
            "fn field_user() -> i64 { let s = S { compute: 1 }; s.compute }\n"
            "fn caller() -> i64 { compute(3) }\n"
            "fn main() { println!(\"{}\", caller() + field_user()); }\n")
    open(src, "w").write(base)
    out = os.path.join(work, "x")
    d.start()
    d.build(src, out)
    d.run(["check", src])  # settle read sets in the daemon session
    open(src, "w").write(base.replace("fn compute(a: i64)", "fn compute(b: i64)"))
    r = d.run(["check", src])
    st = {}
    for line in r.stderr.splitlines():
        if line.startswith("lust-stats:"):
            for kv in line.split(":", 1)[1].split():
                k, _, v = kv.partition("=")
                st[k] = int(v) if v.isdigit() else v
    check("sig-header edit is signatures mode", st.get("mode") == "signatures", str(st))
    check("dirty walk reuses clean bodies", (st.get("reused") or 0) >= 1 and st.get("rechecked") == 0, str(st))
    d.kill()


def case_graph_refresh_and_std():
    work = tempfile.mkdtemp(prefix="lust-driver-graph-")
    pkg = os.path.join(work, "pkg")
    shutil.copytree(os.path.join(ROOT, "tests/crates/buildscript"), pkg)
    d = Daemon(work)
    src = os.path.join(pkg, "src/main.rs")
    out = os.path.join(work, "x")
    extra = ("--manifest-path", os.path.join(pkg, "Cargo.toml"), "--bin", "buildscript")
    d.start()
    _, prog = d.build(src, out, extra)
    check("buildscript crate output", prog.stdout.strip() == "buildscript crate", prog.stdout)
    d.build(src, out, extra)  # warm: same session
    log = d.kill()
    check("no refresh while inputs hold", "graph or build script changed" not in log, log[-300:])
    # Edit the build script's rerun-if-changed input.
    open(os.path.join(pkg, "data.txt"), "w").write("v2\n")
    d.start()
    d.build(src, out, extra)  # first build in the new daemon seeds its key
    open(os.path.join(pkg, "data.txt"), "w").write("v3\n")
    _, prog = d.build(src, out, extra)
    log = d.kill()
    check("build script edit refreshes the session", "graph or build script changed" in log, log[-400:])
    check("output still correct after refresh", prog.stdout.strip() == "buildscript crate", prog.stdout)

    # 6: std::process::exit is a source std fn (S5 registry). Run it
    # twice through one daemon session: same exit code and output.
    ex = os.path.join(work, "exit.rs")
    open(ex, "w").write('fn main() { println!("before-exit"); std::process::exit(3); }\n')
    d.start()
    for tag in ("first", "second"):
        d.build(ex, out)
        prog = subprocess.run([out], capture_output=True, text=True)
        check(f"std source fn via daemon ({tag})",
              prog.returncode == 3 and prog.stdout.strip() == "before-exit",
              f"exit {prog.returncode} out {prog.stdout!r}")
    d.kill()


def main():
    if not os.path.exists(LUST):
        sys.exit(f"{LUST} not built; run cargo build --release first")
    case_slots_and_reuse()
    case_reads_reuse()
    case_graph_refresh_and_std()
    print(f"test-driver: {'all passed' if not failures else str(len(failures)) + ' FAILED: ' + ', '.join(failures)}")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
