#!/usr/bin/env python3
# Smoke tests for daemon wire and base-library behavior that the random-edit fuzzer
# does not reach: odd file names, odd run arguments, and old binaries staying valid
# after the daemon rebuilds its base library.
# Usage: python3 scripts/fuzz/smoke.py   (exit 0 = pass)
import glob, os, re, shutil, subprocess, sys, tempfile, time

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
    env = dict(os.environ, LUST_DAEMON_SOCKET=sock, LUST_NO_CACHE="1")
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
        # base generations must be cleaned up (at most 4 kept). Bases live in the
        # persistent `.lust-cache/bases` dir under content names, not in the
        # daemon's temp dir, so they survive the daemon (section 12).
        bases_dir = os.path.join(work, ".lust-cache", "bases")

        def base_of(binpath):
            m = re.search(rb"libbase-\d+-[0-9a-f]+\.so", open(binpath, "rb").read())
            return m.group(0).decode() if m else None

        bases_before = set(glob.glob(os.path.join(bases_dir, "libbase-*.so")))
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
        # This session's bases: the newest 4 generations plus any still referenced by a
        # live binary (here p1.bin's base). Unreferenced old generations must be gone.
        new_bases = set(glob.glob(os.path.join(bases_dir, "libbase-*.so"))) - bases_before
        p1_base = base_of(os.path.join(work, "p1.bin"))
        check("base generations bounded per session",
              0 < len(new_bases) <= 5 and p1_base is not None
              and os.path.exists(os.path.join(bases_dir, p1_base)),
              f"new bases: {sorted(os.path.basename(b) for b in new_bases)}, p1 base: {p1_base}")

        # 5. Regression: a chunk that ends inside a `//` comment must not be reused in front
        # of new text. The `/*` below is inside the line comment, so `b` is real code and
        # both cold and daemon must reject the second state.
        lc = os.path.join(work, "lc.rs")
        open(lc, "w").write("fn main() {}\n// note")
        rc1, _, _ = run_lust(["check", lc])
        open(lc, "w").write("fn main() {}\n// note/* a\nb\nfn fake() {}\n*/\n")
        rc2, _, err2 = run_lust(["check", lc])
        check("line-comment chunk reuse", rc1 == 0 and rc2 == 1 and "L0001" in err2,
              f"rc1={rc1} rc2={rc2}")

        # 6. Regression: a body-only edit that deletes a byte must move the spans of
        # unchanged functions later in the same chunk. Warm and cold panic locations
        # must match; the warm column used to be one too high (fuzz seed 21, iter 774).
        pc = os.path.join(work, "panic_col.rs")
        open(pc, "w").write("fn price(c: i64) -> i64 { c / 100 }\nfn main() {\n    assert_eq!(price(500), 5);\n}\n")
        rc1, _, _ = run_lust(["check", pc])
        open(pc, "w").write("fn price(c: i64) -> i64 { c / 20 }\nfn main() {\n    assert_eq!(price(500), 5);\n}\n")
        rc, out, err = run_lust(["run", pc, "-o", os.path.join(work, "pc.bin")])
        cold_env = dict(env, LUST_NO_DAEMON="1", LUST_DAEMON_SOCKET=os.path.join(work, "none"))
        r = subprocess.run([LUST, "run", pc, "-o", os.path.join(work, "pc2.bin")], cwd=work,
                           env=cold_env, capture_output=True, text=True, timeout=20)
        warm_loc = re.search(r"panicked at [^:\n]*:(\d+):(\d+)", err)
        cold_loc = re.search(r"panicked at [^:\n]*:(\d+):(\d+)", r.stderr)
        check("panic column after body edit",
              rc1 == 0 and warm_loc is not None and cold_loc is not None
              and warm_loc.groups() == cold_loc.groups() == ("3", "5"),
              f"rc1={rc1} warm={warm_loc.groups() if warm_loc else None} "
              f"cold={cold_loc.groups() if cold_loc else None}")

        # 7. Routing (S6): two feature selections of one file in one daemon
        # stay in separate sessions, and a repeat selection reuses its own.
        # Proof is the daemon's own session records: one "new session" log
        # line per key naming a distinct session dir, plus each binary
        # naming a distinct base library. Since W-RESOLVE the program also
        # branches on cfg(feature), so the two binaries must print
        # different lines.
        feat = os.path.join(work, "feat.rs")
        feat_src = ('#[cfg(feature = "alpha")]\nfn which() -> i64 { 11 }\n'
                    '#[cfg(not(feature = "alpha"))]\nfn which() -> i64 { 22 }\n'
                    'fn main() { println!("feat {}", which()); }\n')
        open(feat, "w").write(feat_src)
        logpath = os.path.join(work, "daemon.log")

        def session_dirs_for(root_path):
            log.flush()
            dirs = {}
            for line in open(logpath):
                if "new session for crate" in line and f"root={root_path}" in line:
                    m = re.search(r"features=\[([^\]]*)\].* in (\S+)$", line.strip())
                    if m:
                        dirs[m.group(1)] = m.group(2)
            return dirs

        rc, out, err = run_lust(["build", feat, "-o", os.path.join(work, "fa.bin"), "--features", "alpha"])
        check("routing: alpha build", rc == 0, err)
        rc, out, err = run_lust(["build", feat, "-o", os.path.join(work, "fb.bin"), "--features", "beta"])
        check("routing: beta build", rc == 0, err)
        dirs = session_dirs_for(feat)
        check("routing: alpha and beta are separate sessions",
              set(dirs) == {"alpha", "beta"} and dirs.get("alpha") != dirs.get("beta"),
              f"dirs={dirs}")
        fa_base, fb_base = base_of(os.path.join(work, "fa.bin")), base_of(os.path.join(work, "fb.bin"))
        check("routing: each session built its own base",
              fa_base is not None and fb_base is not None and fa_base != fb_base
              and os.path.exists(os.path.join(bases_dir, fa_base))
              and os.path.exists(os.path.join(bases_dir, fb_base)),
              f"alpha base={fa_base} beta base={fb_base}")
        r = subprocess.run([os.path.join(work, "fa.bin")], capture_output=True, text=True)
        r2 = subprocess.run([os.path.join(work, "fb.bin")], capture_output=True, text=True)
        check("routing: cfg(feature) differs per session",
              r.stdout == "feat 11\n" and r2.stdout == "feat 22\n",
              f"alpha={r.stdout!r} beta={r2.stdout!r}")
        # Two targets in one daemon: the host triple named explicitly and
        # the default also key separate sessions (lust builds host only).
        host = subprocess.run(["rustc", "-vV"], capture_output=True, text=True).stdout
        host = re.search(r"host: (\S+)", host).group(1)
        rc, out, err = run_lust(["build", feat, "-o", os.path.join(work, "ft.bin"), "--target", host])
        check("routing: named host target build", rc == 0, err)
        log.flush()
        target_dirs = set()
        for line in open(logpath):
            if "new session for crate" in line and f"root={feat}" in line:
                m = re.search(r"target=(\S+) .* in (\S+)$", line.strip())
                if m:
                    target_dirs.add(m.group(2))
        check("routing: two targets, separate sessions", len(target_dirs) >= 3,
              f"dirs={target_dirs}")
        before = session_dirs_for(feat)
        rc, out, err = run_lust(["check", feat, "--features", "alpha"])
        check("routing: alpha again ok", rc == 0, err)
        dirs = session_dirs_for(feat)
        check("routing: repeat selection reuses its session", dirs == before,
              f"dirs={dirs} before={before}")
        # An error under alpha must not poison beta: the same source error is
        # reported by both, and after the fix each answers from its own state.
        open(feat, "w").write('fn main() { let x: i64 = "s"; println!("{}", x); }\n')
        rca, _, ea = run_lust(["check", feat, "--features", "alpha"])
        rcb, _, eb = run_lust(["check", feat, "--features", "beta"])
        check("routing: both selections reject the bad edit",
              rca == 1 and rcb == 1 and ea.splitlines()[:1] == eb.splitlines()[:1],
              f"alpha rc={rca}, beta rc={rcb}")
        open(feat, "w").write(feat_src)
        rca, _, ea = run_lust(["check", feat, "--features", "alpha"])
        rcb, _, eb = run_lust(["check", feat, "--features", "beta"])
        check("routing: both selections accept the fix", rca == 0 and rcb == 0,
              f"alpha rc={rca} {ea!r}, beta rc={rcb} {eb!r}")
        # Background guards for the two error answers must settle with no
        # mismatch: wait for every started check's done line in the log.
        t0 = time.time()
        settled = False
        while time.time() - t0 < 30:
            text = open(logpath).read()
            if text.count("guard-check: start ") == text.count("guard-check: done ") \
                    and "guard-check: start " in text:
                settled = True
                break
            time.sleep(0.02)
        text = open(logpath).read()
        check("routing: background guards settled, none fired",
              settled and "guard:" not in text,
              f"settled={settled} guard_lines={[l for l in text.splitlines() if 'guard:' in l]}")

        # 8. Regression (fuzz seed 42, iter 1034): a return-type edit must
        # recheck the changed fn's own body. The body of `classify` returns
        # an i64 expression, so `-> i32` makes the program invalid; the
        # daemon reused the body on its clean read set (its own signature
        # was not in the set) and accepted it while cold rejected with
        # L0110. Both sides must now answer the same, byte for byte.
        sig_prev = '''struct Point {
    x: i64,
    y: i64,
}

fn main() {
    let mut pts: Vec<Point> = Vec::new();
    pts.push(Point { x: 1, y: 2 });
    pts.push(Point { x: 3, y: 4 });
    pts[0].bump(5);
    let t = total(&pts);
    let c = classify(Shape::Pair(2, 3));
    let nums = vec![2, 20, 30];
    println!("{} {} {} {}", label(t), c, pick(&nums, 1), pts.len());
}

enum Shape {
    Dot,
    Pair(i64, i64),
}

impl Point {
    fn sum(&self) -> i64 {
        self.x + self.y
    }

    fn bump(&mut self, d: i64) {
        self.x += d;
        self.y += d * 2;
    }
}

fn classify(s: Shape) -> i64 {
    match s {
        Shape::Dot => 0,
        Shape::Pair(a, b) => a * 2 + b,
    }
}

fn total(pts: &Vec<Point>) -> i64 {
    let mut acc = 0;
    let mut i = 0;
    while i < pts.len() {
        acc += pts[i].sum();
        i += 1;
    }
    acc
}

fn added_75576() -> i64 { 13 }
fn label(n: i64) -> String {
    let mut s = String::from("n=");
    s.push_str(&n.to_string());
    s
}

fn pick(v: &Vec<i64>, i: usize) -> i64 {
    v[i]
}

fn grown() -> i64 { 1 }
'''
        sig_cur = sig_prev.replace("fn classify(s: Shape) -> i64", "fn classify(s: Shape) -> i32")
        assert sig_cur != sig_prev
        sg = os.path.join(work, "sigedit.rs")
        open(sg, "w").write(sig_prev)
        rc1, _, _ = run_lust(["check", sg])
        open(sg, "w").write(sig_cur)
        rcw, _, errw = run_lust(["check", sg])
        cold_env = dict(env, LUST_NO_DAEMON="1", LUST_DAEMON_SOCKET=os.path.join(work, "none"))
        r = subprocess.run([LUST, "check", sg], cwd=work, env=cold_env,
                           capture_output=True, text=True, timeout=20)
        check("own return-type edit rechecks the body (seed 42 iter 1034)",
              rc1 == 0 and rcw == 1 and r.returncode == 1
              and "L0110" in errw and errw == r.stderr,
              f"rc1={rc1} warm rc={rcw} err={errw[:120]!r} cold rc={r.returncode}")

        # 9. The daemon is still alive and correct after all of it.
        check("daemon alive", daemon.poll() is None)

        # 10. Regression (fuzz seed 29, iter 562): a bodies-only edit whose
        # later function has a body syntax error must not mark the earlier
        # changed bodies as up to date. Step 2 changes `label` to a body
        # with a check error and breaks `main`'s body syntax, so the
        # compile stops at the syntax error. Step 3 only fixes `main`;
        # the daemon must still report `label`'s error, like cold does.
        # The bug: step 2 stored `label`'s new body hash while `ok` stayed
        # true from step 1, so step 3 never rechecked it.
        pz = os.path.join(work, "poison.rs")
        open(pz, "w").write('fn label() -> i64 { 1 }\nfn main() { println!("{}", label()); }\n')
        rc1, _, _ = run_lust(["check", pz])
        open(pz, "w").write('fn label() -> i64 { x }\nfn main() { println!("{}", label());\n')
        rc2, _, _ = run_lust(["check", pz])
        open(pz, "w").write('fn label() -> i64 { x }\nfn main() { println!("{}", label()); }\n')
        rcw, _, errw = run_lust(["check", pz])
        cold_env = dict(env, LUST_NO_DAEMON="1", LUST_DAEMON_SOCKET=os.path.join(work, "none"))
        r = subprocess.run([LUST, "check", pz], cwd=work, env=cold_env,
                           capture_output=True, text=True, timeout=20)
        check("syntax-error edit does not poison earlier bodies (seed 29 iter 562)",
              rc1 == 0 and rc2 == 1 and rcw == 1 and r.returncode == 1
              and "L0101" in errw and errw == r.stderr,
              f"rc1={rc1} rc2={rc2} warm rc={rcw} err={errw[:120]!r} cold rc={r.returncode}")

        # 11. Regression (fuzz realish seed 107, iter 585): resolver routing
        # must not stay sticky after the trigger item is deleted. Step 1
        # routes to the resolver (a `static` item) and fails with the
        # struct syntax error. Step 2 deletes the static and breaks a
        # macro name. A fresh session compiles step 2 through the chunk
        # front end and reports the unknown macro (L0802) first; the
        # sticky warm session kept the resolver front end and reported
        # the syntax error. Both sides must answer the same, byte for byte.
        rt = os.path.join(work, "route.rs")
        open(rt, "w").write('static S: i64 = 1;\nstruct P {\n    fn f() {}\n}\nfn main() { println!("{}", format!("{}", S)); }\n')
        rc1, _, _ = run_lust(["check", rt])
        open(rt, "w").write('struct P {\n    fn f() {}\n}\nfn main() { println!("{}", xformat!("{}", 1)); }\n')
        rcw, _, errw = run_lust(["check", rt])
        cold_env = dict(env, LUST_NO_DAEMON="1", LUST_DAEMON_SOCKET=os.path.join(work, "none"))
        r = subprocess.run([LUST, "check", rt], cwd=work, env=cold_env,
                           capture_output=True, text=True, timeout=20)
        check("resolver routing unsticks when the trigger goes (realish seed 107 iter 585)",
              rc1 == 1 and rcw == 1 and r.returncode == 1
              and "L0802" in errw and errw == r.stderr,
              f"rc1={rc1} warm rc={rcw} err={errw[:120]!r} cold rc={r.returncode}")
        # The route fall-back drops resolver-built session state; the
        # session must still build and run the fixed program after it.
        open(rt, "w").write('fn main() { println!("route {}", 40 + 2); }\n')
        rc, out, err = run_lust(["run", rt, "-o", os.path.join(work, "rt.bin")])
        check("session builds after the route fall-back",
              rc == 0 and out == "route 42\n", f"rc={rc} out={out!r} err={err!r}")

        # 11b. A deleted bases dir under a live session heals: outside
        # tools may delete `.lust-cache` as a cache (the multi-file edit
        # fuzzer rewrites the crate tree every edit, seed 7 iter 25).
        # The next build relinks the same base from its objects. A
        # subdirectory source keeps this check away from section 12's
        # bases.
        sub = os.path.join(work, "heal")
        os.makedirs(sub)
        heal = os.path.join(sub, "heal.rs")
        open(heal, "w").write('fn main() { println!("heal {}", 1); }\n')
        rc, out, err = run_lust(["build", heal, "-o", os.path.join(sub, "h1.bin")])
        check("vanished bases dir: first build ok", rc == 0, err)
        shutil.rmtree(os.path.join(sub, ".lust-cache", "bases"))
        open(heal, "w").write('fn main() { println!("heal {}", 2); }\n')
        rc, out, err = run_lust(["build", heal, "-o", os.path.join(sub, "h2.bin")])
        check("vanished bases dir: build still works", rc == 0, err)
        r = subprocess.run([os.path.join(sub, "h2.bin")], capture_output=True, text=True)
        check("vanished bases dir: binary runs", r.stdout == "heal 2\n",
              f"stdout={r.stdout!r} stderr={r.stderr!r}")

        # 12. Temp cleanup: SIGTERM removes the daemon's temp dir, and
        # executables built against its base libraries still run (bases
        # live in `.lust-cache/bases`, section 4).
        daemon_dir = os.path.join(tempfile.gettempdir(), f"lust-daemon-{daemon.pid}")
        check("temp: daemon temp dir exists while running", os.path.isdir(daemon_dir), daemon_dir)
        daemon.terminate()
        daemon.wait(timeout=10)
        check("temp: daemon temp dir removed on SIGTERM", not os.path.exists(daemon_dir), daemon_dir)
        r = subprocess.run([os.path.join(work, "p1.bin")], capture_output=True, text=True)
        check("temp: kept binary still runs after daemon exit", r.stdout == "v1\n",
              f"stdout={r.stdout!r} stderr={r.stderr!r}")
        p1_base_path = os.path.join(bases_dir, p1_base) if p1_base else ""
        check("temp: kept binary's base survives daemon exit",
              bool(p1_base_path) and os.path.exists(p1_base_path), p1_base_path)
        # Once the executable is deleted, the next daemon's first base
        # build sweeps its base via the manifest, while bases of kept
        # executables (fa.bin) stay.
        os.remove(os.path.join(work, "p1.bin"))
        sock2 = os.path.join(work, "d2.sock")
        env2 = dict(env, LUST_DAEMON_SOCKET=sock2)
        with open(os.path.join(work, "daemon2.log"), "w") as log2:
            daemon2 = subprocess.Popen([LUST, "daemon"], cwd=work, env=env2, stderr=log2)
            try:
                t0 = time.time()
                while not os.path.exists(sock2):
                    if time.time() - t0 > 10 or daemon2.poll() is not None:
                        break
                    time.sleep(0.005)
                open(prog, "w").write('fn val() -> i64 { 10 }\nfn main() { println!("v{}", val()); }\n')
                r = subprocess.run([LUST, "build", prog, "-o", os.path.join(work, "p3.bin")],
                                   cwd=work, env=env2, capture_output=True, text=True, timeout=20)
                check("temp: second daemon builds", r.returncode == 0, r.stderr)
            finally:
                daemon2.terminate()
                daemon2.wait(timeout=10)
        check("temp: deleted binary's base swept by the next daemon",
              bool(p1_base_path) and not os.path.exists(p1_base_path), p1_base_path)
        r = subprocess.run([os.path.join(work, "fa.bin")], capture_output=True, text=True)
        check("temp: another kept binary still runs after the sweep", r.stdout == "feat 11\n",
              f"stdout={r.stdout!r} stderr={r.stderr!r}")
    finally:
        daemon.terminate()
        log.close()
        shutil.rmtree(work, ignore_errors=True)
    print(f"smoke: {'FAIL ' + ', '.join(failures) if failures else 'all passed'}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
