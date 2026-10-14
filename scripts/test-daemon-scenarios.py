#!/usr/bin/env python3
# Daemon edit scenarios: every tests/daemon/<name>/ version sequence runs
# against one warm daemon, a cold lust, and rustc. The warm answer must
# match the cold answer (a check or run that rejects must give the same
# first error code) and, when lust accepts the program, the rustc answer. This is the regression net for the dependency edges of
# docs/ARCH.md 8.1-8.3 (const/static values from const fns, consts in
# patterns, derived impls under type edits, layout answers in bodies).
#
# Usage: python3 scripts/test-daemon-scenarios.py [scenario ...]
# Env: LUST_BIN (default target/release/lust), DAEMON_SCENARIO_JOBS.
# Exit 0 = pass, 1 = a mismatch, 2 = setup error.
import os, re, shutil, signal, subprocess, sys, tempfile, time
from concurrent.futures import ProcessPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LUST = os.environ.get("LUST_BIN", os.path.join(ROOT, "target/release/lust"))
SCEN = os.path.join(ROOT, "tests/daemon")


def run(cmd, cwd, env, timeout=60):
    r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
    return r.returncode, r.stdout, r.stderr


def first_code(stderr):
    """The first `error[L####]` code in a diagnostic text, or None."""
    m = re.search(r"error\[(L\d+)\]", stderr)
    return m.group(1) if m else None


def scenario(srcdir):
    """Returns (name, problems, notes). One temp dir and one daemon per
    scenario; versions are applied in order with strictly rising mtimes."""
    name = os.path.basename(srcdir.rstrip("/"))
    work = tempfile.mkdtemp(prefix=f"lust-scen-{name}-")
    sock = os.path.join(work, "d.sock")
    env = dict(os.environ, LUST_DAEMON_SOCKET=sock, LUST_NO_CACHE="1")
    env.pop("LUST_NO_DAEMON", None)
    log = open(os.path.join(work, "daemon.log"), "w")
    daemon = subprocess.Popen([LUST, "daemon"], cwd=work, env=env, stderr=log,
                              start_new_session=True)
    main = os.path.join(work, "main.rs")
    problems, notes = [], []
    try:
        t0 = time.time()
        while not os.path.exists(sock):
            if time.time() - t0 > 10 or daemon.poll() is not None:
                return name, [f"{name}: daemon start failed"], notes
            time.sleep(0.005)
        versions = sorted(
            f for f in os.listdir(srcdir)
            if f.startswith("v") and (f.endswith(".rs") or os.path.isdir(os.path.join(srcdir, f))))
        mtime = int(time.time())
        for v in versions:
            mtime += 2
            vpath = os.path.join(srcdir, v)
            if os.path.isdir(vpath):
                for f in os.listdir(work):
                    if f.endswith(".rs"):
                        os.remove(os.path.join(work, f))
                for f in os.listdir(vpath):
                    dst = os.path.join(work, f)
                    shutil.copyfile(os.path.join(vpath, f), dst)
                    os.utime(dst, (mtime, mtime))
            else:
                shutil.copyfile(vpath, main)
                os.utime(main, (mtime, mtime))
            # Check first, then run, like an agent loop: a check request
            # consumes the edit, so the build request after it sees an
            # unchanged file. Built state (statics, glue) must still be
            # current (this ordering caught a real statics bug).
            wkc, _, wkerr = run([LUST, "check", main], work, env)
            cold_env = dict(env, LUST_NO_DAEMON="1")
            ckc, _, ckerr = run([LUST, "check", main], work, cold_env)
            # Same rule as the edit fuzzer: both accept, or both reject with the same first code.
            if (wkc == 0) != (ckc == 0) or first_code(wkerr) != first_code(ckerr):
                problems.append(f"{name} {v}: warm check != cold check: warm rc={wkc} {wkerr[:160]!r}, "
                                f"cold rc={ckc} {ckerr[:160]!r}")
            wrc, wout, werr = run([LUST, "run", main, "-o", os.path.join(work, "w.bin")], work, env)
            crc, cout, cerr = run([LUST, "run", main, "-o", os.path.join(work, "c.bin")], work, cold_env)
            rrc, rout, _ = run(["rustc", "--edition", "2024", "-C", "panic=abort",
                                "-C", "overflow-checks=on", main, "-o", os.path.join(work, "r.bin")], work, env)
            rustc_ok = rrc == 0
            if rustc_ok:
                rrc, rout, _ = run([os.path.join(work, "r.bin")], work, env)
            tag = f"{name} {v}"
            if (wrc == 0) != (crc == 0) or (wrc == 0 and wout != cout) or first_code(werr) != first_code(cerr):
                problems.append(
                    f"{tag}: warm != cold: warm=({wrc},{wout!r},{werr[:160]!r}) "
                    f"cold=({crc},{cout!r},{cerr[:160]!r})")
            if not rustc_ok:
                if wrc == 0:
                    problems.append(f"{tag}: warm accepts but rustc rejects; warm out={wout!r}")
                if crc == 0:
                    problems.append(f"{tag}: cold accepts but rustc rejects; cold out={cout!r}")
            elif wrc == 0 or crc == 0:
                if wrc == 0 and (wrc, wout) != (rrc, rout):
                    problems.append(f"{tag}: warm wrong: warm=({wrc},{wout!r}) rustc=({rrc},{rout!r})")
                if crc == 0 and (crc, cout) != (rrc, rout):
                    problems.append(f"{tag}: cold wrong: cold=({crc},{cout!r}) rustc=({rrc},{rout!r})")
            else:
                notes.append(f"{tag}: lust rejects valid Rust in both modes (unsupported today)")
    finally:
        try:
            os.killpg(os.getpgid(daemon.pid), signal.SIGTERM)
        except Exception:
            daemon.terminate()
        log.close()
        shutil.rmtree(work, ignore_errors=True)
    return name, problems, notes


def main():
    if not os.path.exists(LUST):
        print(f"{LUST} missing; run: cargo build --release", file=sys.stderr)
        return 2
    names = sys.argv[1:]
    dirs = [os.path.join(SCEN, n) for n in names] if names else sorted(
        os.path.join(SCEN, d) for d in os.listdir(SCEN)
        if os.path.isdir(os.path.join(SCEN, d)))
    jobs = int(os.environ.get("DAEMON_SCENARIO_JOBS", "8"))
    with ProcessPoolExecutor(max_workers=jobs) as pool:
        results = list(pool.map(scenario, dirs))
    results.sort()
    bad = 0
    notes = 0
    for name, problems, ns in results:
        notes += len(ns)
        if problems:
            bad += 1
            for p in problems:
                print(f"FAIL {p}")
        else:
            print(f"ok   {name}" + (f" ({len(ns)} unsupported version(s))" if ns else ""))
    print(f"daemon scenarios: {len(dirs) - bad}/{len(dirs)} ok"
          + (f", {notes} unsupported version(s)" if notes else ""))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
