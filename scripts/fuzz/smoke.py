#!/usr/bin/env python3
# Smoke tests for daemon wire and base-library behavior that the random-edit fuzzer
# does not reach: odd file names, odd run arguments, and old binaries staying valid
# after the daemon rebuilds its base library.
# Usage: python3 scripts/fuzz/smoke.py   (exit 0 = pass)
import glob, os, shutil, subprocess, sys, tempfile, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LUST = os.path.join(ROOT, "target/release/lust")
failures = []


def check(name, cond, detail=""):
    print(f"{'ok' if cond else 'FAIL'} {name}" + (f": {detail}" if detail and not cond else ""))
    if not cond:
        failures.append(name)


def main():
    work = tempfile.mkdtemp(prefix="lust-smoke-")
    sock = os.path.join(work, "d.sock")
    env = dict(os.environ, LUST_DAEMON_SOCKET=sock)
    log = open(os.path.join(work, "daemon.log"), "w")
    daemon = subprocess.Popen([LUST, "daemon"], cwd=work, env=env, stderr=log)
    t0 = time.time()
    while not os.path.exists(sock):
        if time.time() - t0 > 10 or daemon.poll() is not None:
            print("daemon start failed")
            return 2
        time.sleep(0.005)

    def run_lust(args, timeout=20):
        r = subprocess.run([LUST] + args, cwd=work, env=env, capture_output=True,
                           text=True, timeout=timeout)
        return r.returncode, r.stdout, r.stderr

    try:
        # 1. A tab (and a newline) in a file name goes through the daemon.
        for name in ("with\ttab.rs", "with newline\nname.rs"):
            p = os.path.join(work, name)
            open(p, "w").write('fn main() { println!("hi"); }\n')
            rc, out, err = run_lust(["run", p, "-o", os.path.join(work, "x.bin")])
            check(f"file name {name!r}", rc == 0 and out == "hi\n", f"rc={rc} out={out!r} err={err!r}")

        # 2. Run args with separator bytes survive: one arg, argc must stay 2.
        src = os.path.join(work, "args.rs")
        open(src, "w").write('fn main() { println!("argc={}", std::env::args().count()); }\n')
        for arg in ("a\x1fb", "a\tb", "a b", "a\nb"):
            rc, out, err = run_lust(["run", src, "-o", os.path.join(work, "a.bin"), "--", arg])
            check(f"run arg {arg!r}", rc == 0 and out == "argc=2\n", f"rc={rc} out={out!r} err={err!r}")

        # 3. A file with one `(` gets an error fast, and no internal ids in any error.
        bad = os.path.join(work, "bad.rs")
        open(bad, "w").write("(")
        t0 = time.time()
        rc, out, err = run_lust(["check", bad], timeout=10)
        check("paren file errors fast", rc == 1 and time.time() - t0 < 5, f"rc={rc}")
        open(bad, "w").write("fn main() { let x = some_name + ; }\n")
        rc, out, err = run_lust(["check", bad])
        check("no Sym(id) in errors", "Sym(" not in err and rc == 1, f"err={err!r}")

        # 4. Rebuilding the base library must not change a binary built earlier, and old
        # base generations must be cleaned up (at most 4 kept).
        prog = os.path.join(work, "prog.rs")
        open(prog, "w").write('fn val() -> i64 { 1 }\nfn main() { println!("v{}", val()); }\n')
        rc, out, err = run_lust(["build", prog, "-o", os.path.join(work, "p1.bin")])
        check("build v1", rc == 0, err)
        r = subprocess.run([os.path.join(work, "p1.bin")], capture_output=True, text=True)
        check("v1 runs", r.stdout == "v1\n", r.stdout)
        # Many signature edits force several base rebuilds (overlay cap is 32 units, so
        # add many functions to outgrow the table instead).
        for v in range(2, 10):
            fns = "\n".join(f"fn filler_{v}_{i}() -> i64 {{ {i} }}" for i in range(40))
            open(prog, "w").write(f'fn val() -> i64 {{ {v} }}\nfn main() {{ println!("v{{}}", val()); }}\n{fns}\n')
            rc, out, err = run_lust(["build", prog, "-o", os.path.join(work, "p2.bin")])
            if rc != 0:
                break
        check("builds after base rebuilds", rc == 0, err)
        r = subprocess.run([os.path.join(work, "p1.bin")], capture_output=True, text=True)
        check("old binary unchanged after base rebuilds", r.stdout == "v1\n",
              f"stdout={r.stdout!r} stderr={r.stderr!r}")
        r = subprocess.run([os.path.join(work, "p2.bin")], capture_output=True, text=True)
        check("new binary has new output", r.stdout == "v9\n", r.stdout)
        per_dir = {}
        for b in glob.glob(os.path.join(tempfile.gettempdir(), f"lust-daemon-{daemon.pid}", "*", "libbase-*.so")):
            per_dir.setdefault(os.path.dirname(b), []).append(b)
        # Per session: the newest 4 generations plus any still referenced by a live binary
        # (here libbase-1, used by p1.bin). Unreferenced old generations must be gone.
        worst = max((len(v) for v in per_dir.values()), default=0)
        check("base generations bounded per session", 0 < worst <= 5,
              f"per-dir counts: {[len(v) for v in per_dir.values()]}")

        # 5. Regression: a chunk that ends inside a `//` comment must not be reused in front
        # of new text. The `/*` below is inside the line comment, so `b` is real code and
        # both cold and daemon must reject the second state.
        lc = os.path.join(work, "lc.rs")
        open(lc, "w").write("// note")
        rc1, _, _ = run_lust(["check", lc])
        open(lc, "w").write("// note/* a\nb\nfn fake() {}\n*/\n")
        rc2, _, err2 = run_lust(["check", lc])
        check("line-comment chunk reuse", rc1 == 0 and rc2 == 1, f"rc1={rc1} rc2={rc2}")

        # 6. The daemon is still alive and correct after all of it.
        check("daemon alive", daemon.poll() is None)
    finally:
        daemon.terminate()
        log.close()
        shutil.rmtree(work, ignore_errors=True)
    print(f"smoke: {'FAIL ' + ', '.join(failures) if failures else 'all passed'}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
