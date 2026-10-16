#!/usr/bin/env python3
# Derive edit differential (PLAN P3.1, extended for P3.2): "-Copy, -Clone
# through Option<A> and tuples". Odd seeds take the round 3 programs: all
# nine derivable traits, generic Adts, fields through Box/Vec/Option,
# wrappers of wrappers, consts and const fn bounds, WF bounds, supertraits,
# a user blanket impl, and `main` returning `Result<(), A>`. Each generated program defines one Adt A with a derive list
# and uses A only through compound types (tuples, Option, arrays, Vec,
# generic bounds, closures, a wrapper that derives over a field of A). A
# sequence of versions then drops and adds Copy and Clone (and sometimes
# Debug or PartialEq) on A's derive list. Every version runs on one warm
# daemon (check, then run), a cold lust (LUST_NO_DAEMON=1), and rustc 1.99.
#
# Classes per version: false accept (lust accepts, rustc rejects), false
# reject (lust rejects valid Rust; counted, not a failure: a lust gap in
# both modes), warm != cold, wrong output, hang (a lust timeout; never a
# reject). Exit 1 on any false accept, warm != cold, wrong output, or hang,
# and under LUST_CHECK_ITEMPATCH=1 on any patch oracle failure or a program
# the oracle never checked.
#
# Usage: python3 scripts/derive_sweep.py [--count N] [--seed S] [--jobs J] [--keep DIR] [--resolver]
# --resolver adds a `const` item to every program, so the daemon takes the resolver path (with
# its body patch) instead of the single-file chunk path. The patch oracle (LUST_CHECK_ITEMPATCH=1)
# covers both paths.
# Env: LUST_BIN (default target/release/lust).
import argparse, os, random, re, shutil, signal, subprocess, sys, tempfile, time
from concurrent.futures import ProcessPoolExecutor
import oracle_log  # scripts/oracle_log.py

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
    # Round 3 (P3.2): every derivable trait, fields through Box/Vec/Option,
    # wrappers of wrappers, consts and const fn bounds, WF, supertraits,
    # a user blanket impl, and Hash/Eq/Ord users.
    "hash_map": ("", "let mut m = std::collections::HashMap::new();\n    m.insert(mk(), 1u8);\n    println!(\"{}\", m.len());"),
    "btree_set": ("", "let mut s = std::collections::BTreeSet::new();\n    s.insert(mk());\n    s.insert(mk());\n    println!(\"{}\", s.len());"),
    "sort_vec": ("", "let mut v = vec![mk(), mk()];\n    v.sort();\n    println!(\"{}\", show(&v[1]));"),
    "cmp_lt": ("", "println!(\"{} {:?}\", mk() < mk(), mk().partial_cmp(&mk()));"),
    "ne_eq": ("", "println!(\"{} {}\", mk() != mk(), Some(mk()) == None);"),
    "box_vec_wrapper": (
        "#[derive(Clone, Debug, PartialEq)]\nstruct BW {\n    b: Box<A>,\n    v: Vec<A>,\n    o: Option<A>,\n}\n",
        "let w = BW { b: Box::new(mk()), v: vec![mk()], o: None };\n    let c = w.clone();\n    println!(\"{} {:?}\", c == w, c.o.is_none());",
    ),
    "wrapper_of_wrapper": (
        "#[derive(Clone, Copy)]\nstruct W1 {\n    a: A,\n}\n#[derive(Clone, Copy)]\nstruct W2 {\n    w: W1,\n    n: u8,\n}\n",
        "let w = W2 { w: W1 { a: mk() }, n: 2 };\n    let v = w;\n    println!(\"{} {}\", show(&w.w.a), v.n);",
    ),
    "hash_wrapper": (
        "#[derive(PartialEq, Eq, Hash)]\nstruct HK {\n    k: (A, u8),\n}\n",
        "let mut m = std::collections::HashSet::new();\n    m.insert(HK { k: (mk(), 1) });\n    println!(\"{}\", m.len());",
    ),
    "ord_wrapper": (
        "#[derive(PartialEq, Eq, PartialOrd, Ord)]\nstruct OK {\n    k: Option<A>,\n}\n",
        "println!(\"{:?}\", OK { k: Some(mk()) }.cmp(&OK { k: None }));",
    ),
    "default_wrapper": (
        "#[derive(Default)]\nstruct DW {\n    a: Option<A>,\n    v: Vec<A>,\n}\n",
        "let d = DW::default();\n    println!(\"{} {}\", d.a.is_none(), d.v.len());",
    ),
    "supertrait_impl": (
        "trait Dup: Clone {\n    fn dup2(&self) -> (Self, Self) {\n        (self.clone(), self.clone())\n    }\n}\nimpl Dup for A {}\n",
        "let (x, _) = mk().dup2();\n    println!(\"{}\", show(&x));",
    ),
    "wf_bound": (
        "struct NeedCopy<T: Copy>(T);\nfn wrap_nc(a: A) -> NeedCopy<A> {\n    NeedCopy(a)\n}\n",
        "let n = wrap_nc(mk());\n    println!(\"{}\", show(&n.0));",
    ),
    "blanket_debug": (
        "trait Show2 {\n    fn s2(&self) -> String;\n}\nimpl<T: std::fmt::Debug> Show2 for T {\n    fn s2(&self) -> String {\n        format!(\"<{:?}>\", self)\n    }\n}\n",
        "println!(\"{}\", mk().s2());",
    ),
    "generic_default": (
        "fn make_d<T: Default>() -> T {\n    T::default()\n}\n",
        "let d: A = make_d();\n    println!(\"{}\", show(&d));",
    ),
    "const_item": (
        "const CA: A = MK_CONST;\nconst ARR: [A; 2] = [CA; 2];\n",
        "let a = CA;\n    let b = ARR;\n    println!(\"{} {}\", show(&a), show(&b[1]));",
    ),
    "const_fn_bound": (
        "const fn ident_c<T: Copy>(t: T) -> T {\n    t\n}\nconst CB: A = ident_c(MK_CONST);\n",
        "println!(\"{}\", show(&CB));",
    ),
    "const_pattern": (
        "const CP: A = MK_CONST;\n",
        "let m = match mk() {\n        CP => 1,\n        _ => 2,\n    };\n    println!(\"{}\", m);",
    ),
    "assoc_bound": (
        "trait HasOut {\n    type Out: Clone;\n    fn out(&self) -> Self::Out;\n}\nimpl HasOut for u8 {\n    type Out = A;\n    fn out(&self) -> A {\n        mk()\n    }\n}\n",
        "let o = 3u8.out();\n    println!(\"{}\", show(&o));",
    ),
    "where_trivial": ("fn needs_where() -> u8\nwhere\n    A: Copy,\n{\n    1\n}\n", "println!(\"{}\", needs_where());"),
    "impl_on_vec": (
        "trait Tr2: Clone {\n    fn n2(&self) -> usize;\n}\nimpl Tr2 for Vec<A> {\n    fn n2(&self) -> usize {\n        self.len()\n    }\n}\n",
        "let v: Vec<A> = vec![mk()];\n    println!(\"{}\", v.n2());",
    ),
    "assoc_impl_bound": (
        "trait Pick {\n    type Out;\n}\nstruct Holder<T>(T);\nimpl<T: Clone> Pick for Holder<T> {\n    type Out = T;\n}\nfn pick_out(h: Holder<A>) -> <Holder<A> as Pick>::Out {\n    h.0\n}\n",
        "let o = pick_out(Holder(mk()));\n    println!(\"{}\", show(&o));",
    ),
    # R13 v2: A under user blanket impls bounded by a toggled trait.
    "blanket_overlap": (
        "trait Show3 {\n    fn s3(&self) -> u8 {\n        1\n    }\n}\nimpl<T: std::fmt::Debug> Show3 for T {}\nimpl Show3 for A {}\n",
        "println!(\"{}\", mk().s3());",
    ),
    "blanket_super": (
        "trait Base: std::fmt::Debug {}\nimpl<T: std::fmt::Debug> Base for T {}\ntrait Up {\n    fn up(&self) -> u8 {\n        2\n    }\n}\nimpl<T: Base> Up for T {}\n",
        "println!(\"{}\", mk().up());",
    ),
    "blanket_eq": (
        "trait Same {\n    fn same(&self, o: &Self) -> bool;\n}\nimpl<T: PartialEq> Same for T {\n    fn same(&self, o: &Self) -> bool {\n        self == o\n    }\n}\n",
        "println!(\"{}\", mk().same(&mk()));",
    ),
    "blanket_dyn": (
        "trait Show4 {\n    fn s4(&self) -> String;\n}\nimpl<T: std::fmt::Debug> Show4 for T {\n    fn s4(&self) -> String {\n        format!(\"{:?}\", self)\n    }\n}\n",
        "let b: Box<dyn Show4> = Box::new(mk());\n    println!(\"{}\", b.s4());",
    ),
}

ROUND1_SHAPES = sorted(list(SHAPES)[: list(SHAPES).index("hash_map")])

# Shapes that need a trait an Adt form cannot derive: Default (enum forms).
NEEDS_DEFAULT = {"generic_default"}
# Shapes a generic Adt form leaves out: lust rejects `#[derive(Copy)]` over a
# field of a generic Adt instance (`AG<u8>`) in both modes (a false reject).
NOT_GENERIC = {"wrapper_derive", "wrapper_of_wrapper"}

# Adt forms: (definition after the derive line, mk body, show body, alias
# line or "", derives Default). A generic form derives on `AG<T>` and the
# programs name the instance through `type A = AG<..>;`.
ADTS = [
    ("struct A {\n    x: u8,\n    y: i64,\n}\n", "A { x: 1, y: -2 }", "format!(\"{}\", a.x as i64 + a.y)", "", True),
    ("struct A(u32, char);\n", "A(7, 'q')", "format!(\"{}{}\", a.0, a.1)", "", True),
    ("enum A {\n    P,\n    Q(i8),\n}\n", "A::Q(3)", "match a {\n        A::P => String::from(\"p\"),\n        A::Q(n) => format!(\"q{}\", n),\n    }", "", False),
    ("struct A {\n    r: &'static str,\n    o: Option<u8>,\n}\n", "A { r: \"z\", o: Some(5) }", "format!(\"{}{:?}\", a.r, a.o)", "", True),
    ("struct AG<T> {\n    x: T,\n    y: i64,\n}\n", "AG { x: 1, y: -2 }", "format!(\"{}\", a.x as i64 + a.y)", "type A = AG<u8>;\n", True),
    ("enum AG<T> {\n    P,\n    Q(T),\n}\n", "AG::Q(3)", "match a {\n        AG::P => String::from(\"p\"),\n        AG::Q(n) => format!(\"q{}\", n),\n    }", "type A = AG<i8>;\n", False),
    ("struct AG<T>(Option<T>, u8);\n", "AG(Some(4), 9)", "format!(\"{:?}{}\", a.0, a.1)", "type A = AG<u16>;\n", True),
]

FULL = ["Clone", "Copy", "Debug", "PartialEq"]
# The round 3 list: every derivable trait (Default only on forms that take it).
FULL3 = ["Clone", "Copy", "Debug", "PartialEq", "Eq", "Hash", "PartialOrd", "Ord"]


def program(adt, derives, shapes, resolver=False, main_result=False):
    defn, mk, show, alias, _ = adt
    out = ["const _ROUTE: u8 = 0;\n"] if resolver else []
    if derives:
        out.append(f"#[derive({', '.join(derives)})]\n")
    out.append(defn)
    out.append(alias)
    out.append(f"fn mk() -> A {{\n    {mk}\n}}\n")
    out.append(f"fn show(a: &A) -> String {{\n    {show}\n}}\n")
    for sh in shapes:
        out.append(SHAPES[sh][0].replace("MK_CONST", mk))
    out.append("fn main() -> Result<(), A> {\n" if main_result else "fn main() {\n")
    for sh in shapes:
        out.append("    {\n    " + SHAPES[sh][1] + "\n    }\n")
    if main_result:
        out.append("    if false {\n        return Err(mk());\n    }\n    Ok(())\n")
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


def versions3(rng, full):
    """Round 3: from the full list, drop one to three traits (any), often
    go back to full, and sometimes add a trait back one at a time."""
    seq = [full]
    cur = list(full)
    for _ in range(rng.randint(3, 6)):
        r = rng.random()
        if r < 0.35:
            cur = list(full)
        elif r < 0.55 and len(cur) < len(full):
            missing = [t for t in full if t not in cur]
            cur = [t for t in full if t in cur or t == rng.choice(missing)]
        else:
            drop = rng.sample(cur, min(len(cur), rng.randint(1, 3)))
            cur = [t for t in cur if t not in drop]
        seq.append(cur)
    if seq[-1] != full:
        seq.append(full)
    return seq


def gen(seed, resolver=False):
    rng = random.Random(seed)
    if seed % 2 == 0:
        # The round 1 programs: the first four Adt forms, the first shapes.
        adt = rng.choice(ADTS[:4])
        shapes = rng.sample(ROUND1_SHAPES, rng.randint(2, 5))
        return [program(adt, d, shapes, resolver) for d in versions(rng)]
    adt = rng.choice(ADTS)
    full = FULL3 + (["Default"] if adt[4] else [])
    pool = [sh for sh in sorted(SHAPES) if (adt[4] or sh not in NEEDS_DEFAULT) and not (adt[3] and sh in NOT_GENERIC)]
    shapes = rng.sample(pool, rng.randint(2, 6))
    main_result = rng.random() < 0.2
    return [program(adt, d, shapes, resolver, main_result) for d in versions3(rng, full)]


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
    seed, keep, resolver = args
    vs = gen(seed, resolver)
    work = tempfile.mkdtemp(prefix=f"lust-dsweep-{seed}-")
    sock = os.path.join(work, "d.sock")
    env = dict(os.environ, LUST_DAEMON_SOCKET=sock, LUST_NO_CACHE="1")
    env.pop("LUST_NO_DAEMON", None)
    cold_env = dict(env, LUST_NO_DAEMON="1")
    oracle_path = oracle_log.setup(env, work)
    log = open(os.path.join(work, "daemon.log"), "w")
    daemon = subprocess.Popen([LUST, "daemon"], cwd=work, env=env, stderr=log, start_new_session=True)
    main = os.path.join(work, "main.rs")
    res = {"versions": 0, "fa": [], "fr": 0, "wc": [], "wrong": [], "hang": [], "oracle": [], "oracle_ok": 0, "rustc_rejects": 0}
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
        ok, fails = oracle_log.collect(oracle_path)
        res["oracle_ok"] = ok
        res["oracle"] = oracle_log.problems(ok, fails, f"seed {seed}")
        shutil.rmtree(work, ignore_errors=True)
    return seed, res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=100)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--keep", default="")
    ap.add_argument("--resolver", action="store_true", help="route every program to the resolver path")
    a = ap.parse_args()
    if not os.path.exists(LUST):
        print(f"{LUST} missing; run scripts/build.sh", file=sys.stderr)
        return 2
    seeds = [(a.seed + i, a.keep, a.resolver) for i in range(a.count)]
    with ProcessPoolExecutor(max_workers=a.jobs) as pool:
        results = list(pool.map(case, seeds))
    tot = {"versions": 0, "fa": 0, "fr": 0, "wc": 0, "wrong": 0, "hang": 0, "oracle": 0, "oracle_ok": 0, "rustc_rejects": 0}
    for seed, r in sorted(results):
        for k in ("fa", "wc", "wrong", "hang", "oracle"):
            for line in r[k]:
                print(f"{k.upper()} {line}")
            tot[k] += len(r[k])
        for k in ("versions", "fr", "rustc_rejects", "oracle_ok"):
            tot[k] += r[k]
    print(f"derive-sweep: {a.count} programs, {tot['versions']} versions ({tot['rustc_rejects']} rustc rejects): "
          f"false_accepts={tot['fa']} warm_ne_cold={tot['wc']} wrong={tot['wrong']} hangs={tot['hang']} "
          f"false_rejects={tot['fr']}" + (f" oracle_checks={tot['oracle_ok']} oracle_failures={tot['oracle']}" if oracle_log.on() else ""))
    return 1 if tot["fa"] or tot["wc"] or tot["wrong"] or tot["hang"] or tot["oracle"] else 0


if __name__ == "__main__":
    sys.exit(main())
