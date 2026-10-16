#!/usr/bin/env python3
# Derive edit differential (PLAN P3.1): "-Copy, -Clone through Option<A>
# and tuples". Each generated program defines one Adt A with a derive list
# and uses A only through compound types (tuples, Option, arrays, Vec,
# generic bounds, closures, a wrapper that derives over a field of A). A
# sequence of versions then drops and adds Copy and Clone (and sometimes
# Debug or PartialEq) on A's derive list. Every version runs on one warm
# daemon (check, then run), a cold lust (LUST_NO_DAEMON=1), and rustc 1.99.
#
# Classes per version: false accept (lust accepts, rustc rejects), false
# reject (lust rejects valid Rust; counted, not a failure: a lust gap in
# both modes), warm != cold, wrong output, hang (a lust timeout; never a
# reject). Exit 1 on any false accept, warm != cold, wrong output, or hang.
#
# Usage: python3 scripts/derive_sweep.py [--count N] [--seed S] [--jobs J] [--keep DIR]
# Env: LUST_BIN (default target/release/lust).
import argparse, os, random, re, shutil, signal, subprocess, sys, tempfile, time
from concurrent.futures import ProcessPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LUST = os.environ.get("LUST_BIN", os.path.join(ROOT, "target/release/lust"))
TIMEOUT = 60

# Each shape is (fn items, main statements). `A` is the Adt type, `mk()`
# builds one, `show(&a)` prints a field of one without any derive.
SHAPES = {
    "tuple_copy": ("", "let t = (mk(), 1u8);\n    let u = t;\n    println!(\"{} {}\", show(&t.0), u.1);"),
    "option_copy": ("", "let o = Some(mk());\n    let p = o;\n    println!(\"{} {}\", o.is_some(), show(&p.unwrap()));"),
    "nested_copy": ("", "let n = Some((mk(), [mk(), mk()]));\n    let m = n;\n    println!(\"{} {}\", n.is_some(), show(&m.unwrap().1[1]));"),
    "array_repeat": ("", "let arr = [mk(); 3];\n    println!(\"{}\", show(&arr[2]));"),
    "generic_copy": (
        "fn twice<T: Copy>(t: T) -> (T, T) {\n    (t, t)\n}\n",
        "let w = twice(Some(mk()));\n    println!(\"{}\", show(&w.1.unwrap()));",
    ),
    "generic_copy_tuple": (
        "fn first<T: Copy, U: Copy>(p: (T, U)) -> T {\n    let q = p;\n    let _r = p;\n    q.0\n}\n",
        "println!(\"{}\", show(&first((mk(), 2i32))));",
    ),
    "option_clone": ("", "let o = Some(mk());\n    let c = o.clone();\n    println!(\"{}\", show(&c.unwrap()));"),
    "tuple_clone": ("", "let t = (mk(), String::from(\"s\"));\n    let c = t.clone();\n    println!(\"{} {}\", show(&c.0), t.1);"),
    "generic_clone": (
        "fn dup<T: Clone>(t: &T) -> T {\n    t.clone()\n}\n",
        "let v = vec![Some((mk(), 3u16))];\n    let d = dup(&v);\n    println!(\"{}\", show(&d[0].as_ref().unwrap().0));",
    ),
    "iter_copied": ("", "let v = vec![mk(), mk()];\n    let w: Vec<A> = v.iter().copied().collect();\n    println!(\"{}\", show(&w[1]));"),
    "iter_cloned": ("", "let v = vec![mk()];\n    let w: Vec<A> = v.iter().cloned().collect();\n    println!(\"{}\", show(&w[0]));"),
    "closure_move": ("", "let a = mk();\n    let f = move || show(&a);\n    println!(\"{} {}\", f(), show(&a));"),
    "option_unwrap_or": ("", "let o: Option<A> = None;\n    let x = o.unwrap_or(mk());\n    let y = o.unwrap_or(x);\n    println!(\"{} {}\", show(&x), show(&y));"),
    "ref_clone": ("", "let a = mk();\n    let r = &a;\n    let c = r.clone();\n    println!(\"{}\", show(&c));"),
    "vec_clone": ("", "let v = vec![(mk(), 'x')];\n    let w = v.clone();\n    println!(\"{} {}\", show(&w[0].0), v.len());"),
    "wrapper_derive": (
        "#[derive(Clone, Copy)]\nstruct H {\n    inner: A,\n    k: u8,\n}\n",
        "let h = H { inner: mk(), k: 4 };\n    let g = h;\n    println!(\"{} {}\", show(&h.inner), g.k);",
    ),
    "generic_wrapper": (
        "#[derive(Clone, Copy)]\nstruct G<T> {\n    t: T,\n}\nfn copy_g<T: Copy>(g: G<T>) -> (G<T>, G<T>) {\n    (g, g)\n}\n",
        "let g = G { t: Some(mk()) };\n    let (x, _y) = copy_g(g);\n    println!(\"{}\", show(&x.t.unwrap()));",
    ),
    "debug_option": ("", "let o = Some((mk(), 1u8));\n    println!(\"{:?}\", o);"),
    "eq_tuple": ("", "let t = (mk(), 1u8);\n    let s = (mk(), 1u8);\n    println!(\"{}\", t == s);"),
    "method_copy_self": (
        "impl A {\n    fn twice(self) -> (A, A) {\n        (self, self)\n    }\n}\n",
        "let (x, _y) = mk().twice();\n    println!(\"{}\", show(&x));",
    ),
}

# Adt forms: (definition after the derive line, mk body, show body).
ADTS = [
    ("struct A {\n    x: u8,\n    y: i64,\n}\n", "A { x: 1, y: -2 }", "format!(\"{}\", a.x as i64 + a.y)"),
    ("struct A(u32, char);\n", "A(7, 'q')", "format!(\"{}{}\", a.0, a.1)"),
    ("enum A {\n    P,\n    Q(i8),\n}\n", "A::Q(3)", "match a {\n        A::P => String::from(\"p\"),\n        A::Q(n) => format!(\"q{}\", n),\n    }"),
    ("struct A {\n    r: &'static str,\n    o: Option<u8>,\n}\n", "A { r: \"z\", o: Some(5) }", "format!(\"{}{:?}\", a.r, a.o)"),
]

FULL = ["Clone", "Copy", "Debug", "PartialEq"]


def program(adt, derives, shapes):
    defn, mk, show = adt
    out = []
    if derives:
        out.append(f"#[derive({', '.join(derives)})]\n")
    out.append(defn)
    out.append(f"fn mk() -> A {{\n    {mk}\n}}\n")
    out.append(f"fn show(a: &A) -> String {{\n    {show}\n}}\n")
    for s in shapes:
        out.append(SHAPES[s][0])
    out.append("fn main() {\n")
    for s in shapes:
        out.append("    {\n    " + SHAPES[s][1] + "\n    }\n")
    out.append("}\n")
    return "".join(out)


def versions(rng):
    """A derive-list sequence that starts and ends full and drops and
    adds Copy and Clone in between."""
    seq = [FULL]
    steps = [
        ["Clone", "Debug", "PartialEq"],  # -Copy
        ["Debug", "PartialEq"],  # -Copy -Clone
        ["Copy", "Debug", "PartialEq"],  # -Clone (Copy needs Clone)
        ["Clone", "Copy", "PartialEq"],  # -Debug
        ["Clone", "Copy", "Debug"],  # -PartialEq
        ["Clone", "Copy"],
    ]
    for _ in range(rng.randint(2, 4)):
        seq.append(rng.choice(steps))
        if rng.random() < 0.5:
            seq.append(FULL)
    if seq[-1] != FULL:
        seq.append(FULL)
    return seq


def gen(seed):
    rng = random.Random(seed)
    adt = rng.choice(ADTS)
    shapes = rng.sample(sorted(SHAPES), rng.randint(2, 5))
    return [program(adt, d, shapes) for d in versions(rng)]


def first_code(stderr):
    m = re.search(r"error\[(L\d+)\]", stderr)
    return m.group(1) if m else None


def run(cmd, cwd, env):
    try:
        r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, text=True, timeout=TIMEOUT)
        return r.returncode, r.stdout, r.stderr
    except subprocess.TimeoutExpired:
        return None, "", "timeout"


def case(args):
    seed, keep = args
    vs = gen(seed)
    work = tempfile.mkdtemp(prefix=f"lust-dsweep-{seed}-")
    sock = os.path.join(work, "d.sock")
    env = dict(os.environ, LUST_DAEMON_SOCKET=sock, LUST_NO_CACHE="1")
    env.pop("LUST_NO_DAEMON", None)
    cold_env = dict(env, LUST_NO_DAEMON="1")
    log = open(os.path.join(work, "daemon.log"), "w")
    daemon = subprocess.Popen([LUST, "daemon"], cwd=work, env=env, stderr=log, start_new_session=True)
    main = os.path.join(work, "main.rs")
    res = {"versions": 0, "fa": [], "fr": 0, "wc": [], "wrong": [], "hang": [], "rustc_rejects": 0}
    try:
        t0 = time.time()
        while not os.path.exists(sock):
            if time.time() - t0 > 10 or daemon.poll() is not None:
                res["hang"].append(f"seed {seed}: daemon start failed")
                return seed, res
            time.sleep(0.005)
        mtime = int(time.time())
        for i, src in enumerate(vs):
            mtime += 2
            with open(main, "w") as f:
                f.write(src)
            os.utime(main, (mtime, mtime))
            tag = f"seed {seed} v{i + 1}"
            res["versions"] += 1
            wck = run([LUST, "check", main], work, env)
            cck = run([LUST, "check", main], work, cold_env)
            wr = run([LUST, "run", main, "-o", os.path.join(work, "w.bin")], work, env)
            cr = run([LUST, "run", main, "-o", os.path.join(work, "c.bin")], work, cold_env)
            rr = run(["rustc", "--edition", "2024", "-C", "panic=abort", main, "-o", os.path.join(work, "r.bin")], work, env)
            rustc_ok = rr[0] == 0
            rout = run([os.path.join(work, "r.bin")], work, env) if rustc_ok else None
            res["rustc_rejects"] += 0 if rustc_ok else 1
            hung = [n for n, r in (("warm check", wck), ("cold check", cck), ("warm run", wr), ("cold run", cr)) if r[0] is None]
            if hung:
                res["hang"].append(f"{tag}: {', '.join(hung)} timed out")
                break
            if (wck[0] == 0) != (cck[0] == 0) or first_code(wck[2]) != first_code(cck[2]):
                res["wc"].append(f"{tag}: check warm rc={wck[0]} {wck[2][:200]!r} cold rc={cck[0]} {cck[2][:200]!r}")
            if (wr[0] == 0) != (cr[0] == 0) or (wr[0] == 0 and wr[1] != cr[1]) or first_code(wr[2]) != first_code(cr[2]):
                res["wc"].append(f"{tag}: run warm=({wr[0]},{wr[1][:80]!r},{wr[2][:160]!r}) cold=({cr[0]},{cr[1][:80]!r},{cr[2][:160]!r})")
            for name, r in (("warm check", wck), ("cold check", cck), ("warm run", wr), ("cold run", cr)):
                if r[0] == 0 and not rustc_ok:
                    res["fa"].append(f"{tag}: {name} accepts, rustc rejects: {rr[2][:200]!r}")
            if rustc_ok:
                for name, r in (("warm run", wr), ("cold run", cr)):
                    if r[0] == 0 and (r[0], r[1]) != (rout[0], rout[1]):
                        res["wrong"].append(f"{tag}: {name} out {r[1][:80]!r} rustc {rout[1][:80]!r}")
                if wck[0] != 0 and cck[0] != 0:
                    res["fr"] += 1
        bad = res["fa"] or res["wc"] or res["wrong"] or res["hang"]
        if bad and keep:
            d = os.path.join(keep, f"seed{seed}")
            os.makedirs(d, exist_ok=True)
            for i, src in enumerate(vs):
                with open(os.path.join(d, f"v{i + 1}.rs"), "w") as f:
                    f.write(src)
    finally:
        try:
            os.killpg(os.getpgid(daemon.pid), signal.SIGTERM)
        except Exception:
            daemon.terminate()
        log.close()
        shutil.rmtree(work, ignore_errors=True)
    return seed, res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=100)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--keep", default="")
    a = ap.parse_args()
    if not os.path.exists(LUST):
        print(f"{LUST} missing; run scripts/build.sh", file=sys.stderr)
        return 2
    seeds = [(a.seed + i, a.keep) for i in range(a.count)]
    with ProcessPoolExecutor(max_workers=a.jobs) as pool:
        results = list(pool.map(case, seeds))
    tot = {"versions": 0, "fa": 0, "fr": 0, "wc": 0, "wrong": 0, "hang": 0, "rustc_rejects": 0}
    for seed, r in sorted(results):
        for k in ("fa", "wc", "wrong", "hang"):
            for line in r[k]:
                print(f"{k.upper()} {line}")
            tot[k] += len(r[k])
        for k in ("versions", "fr", "rustc_rejects"):
            tot[k] += r[k]
    print(f"derive-sweep: {a.count} programs, {tot['versions']} versions ({tot['rustc_rejects']} rustc rejects): "
          f"false_accepts={tot['fa']} warm_ne_cold={tot['wc']} wrong={tot['wrong']} hangs={tot['hang']} "
          f"false_rejects={tot['fr']}")
    return 1 if tot["fa"] or tot["wc"] or tot["wrong"] or tot["hang"] else 0


if __name__ == "__main__":
    sys.exit(main())
