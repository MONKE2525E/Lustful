#!/usr/bin/env python3
# Release builds through a front image vs one-shot release builds, on a small corpus of
# layout-sensitive edits (rel-front, after b24cbd1a6's c_layout phase cache made WRONG CODE in
# image builds only: a cache hit skipped a body's Layout read, so the body kept old field
# offsets when a type it reads through a pointer grew). Each sequence is one program edited
# step by step in its own directory; every step builds twice:
#   image     the release driver (release C) with a front image kept across the steps
#             (LUST_FRONT_STATE, LUST_FRONT_SAVE=background, as scripts/release-x64.sh FRONT=1
#             does), one codegen thread (so bodies share one thread's caches), the disk cache on;
#   one-shot  the same with no image and no cache (LUST_NO_CACHE=1), 4 threads.
# Both write their units (--emit-c); the unit files must be equal byte for byte (compared by
# content), and both binaries must give the same exit status and stdout. Every sequence runs
# with release C and with the LLVM backend (LUST_RELEASE_BACKEND=llvm; LUST_CC=clang where no
# zig is on PATH and cc is not clang). The corpus: a type held by value inside a struct that
# fns read through a pointer grows (directly, as an enum payload, behind Option, as an array,
# as a generic arg), statics and thread_local keys are added, and tests/daemon/dt01's six
# versions. A step that fails to build must fail on both sides with the same status.
# Two sequences cover the LLVM units' inputs that zig's compile cache cannot see (b41791434):
# an edit that changes a unit's helpers' C but not its IR (zig keyed the object on the IR and
# served the last one at that path: the old string printed), and a merge that removes items,
# built with a profile (PGO unit names, per-unit profiles). The PGO one trains at its first
# step (an instrumented one-shot build, run once) and needs zig plus a clang and llvm-profdata
# of zig's LLVM major (LUST_PGO_CC, LUST_PROFDATA, or clang-<N> and llvm-profdata-<N> on PATH);
# without them it is skipped and says so.
# Three dt01 sequences take the shapes of CI jobs (rel-cache's merge 12 replay, 2026-10-18): image
# builds that emit no C before the compared build, a jump over versions no build saw, and builds
# that each start again from an older state (a CI disk whose commits did not land).
# The image side runs B1's oracle (LUST_CHECK_UNIT_FP=1); dt01-b1-skip runs B1's skipping
# (LUST_B1=1) in builds that emit no C.
#
# LUST_BIN overrides the lust binary (default target/release/lust).
# Usage: front_check.py [--jobs N] [--keep DIR] [--only NAME]
# Exit 0 = all same, 1 = a difference or a build failure on one side, 2 = setup error.
import argparse, hashlib, os, re, shutil, subprocess, sys, tempfile, time
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LUST = os.environ.get("LUST_BIN") or os.path.join(ROOT, "target/release/lust")
BUILD_TIMEOUT = 180
RUN_TIMEOUT = 20


def nested(fields_t, init_t, use_t):
    """Two fns read `y` through `&S`, `S { t: T, y: u64 }`; `T`'s fields are the edit."""
    return f'''struct T {{
{fields_t}
}}

struct S {{
    t: T,
    y: u64,
}}

#[inline(never)]
fn get_a(p: &S) -> u64 {{
    p.y
}}

#[inline(never)]
fn get_b(p: &S) -> u64 {{
    p.y + 1
}}

#[inline(never)]
fn both(p: &S) -> u64 {{
    get_a(p) * 100 + get_b(p)
}}

fn main() {{
    let s = S {{ t: {init_t}, y: 42 }};
    println!("{{}} {{}} {{}} {{}}", get_a(&s), get_b(&s), both(&s), {use_t});
}}
'''


def enum_payload(variants, arms, extra_main):
    return f'''#[derive(Clone, Copy)]
enum E {{
{variants}
}}

struct S {{
    e: E,
    y: u64,
}}

#[inline(never)]
fn read_y(p: &S) -> u64 {{
    p.y
}}

#[inline(never)]
fn read_y2(p: &S) -> u64 {{
    p.y * 2
}}

#[inline(never)]
fn read_e(p: &S) -> u64 {{
    match p.e {{
{arms}
    }}
}}

fn main() {{
    let s = S {{ e: E::B(7, 3), y: 42 }};
    let t = S {{ e: E::A(5), y: 9 }};
    println!("{{}} {{}} {{}} {{}}", read_y(&s), read_y2(&t), read_e(&s), read_e(&t));
{extra_main}
}}
'''


def generic(fields_inner, init_inner, fields_w, init_w_extra, use_inner):
    return f'''struct Inner {{
{fields_inner}
}}

struct W<T> {{
    t: T,
{fields_w}
    n: u64,
}}

#[inline(never)]
fn get<T>(w: &W<T>) -> u64 {{
    w.n
}}

#[inline(never)]
fn get_plus(w: &W<Inner>) -> u64 {{
    w.n + 1
}}

fn main() {{
    let w = W {{ t: {init_inner},{init_w_extra} n: 40 }};
    let v = W {{ t: 7u8,{init_w_extra} n: 3 }};
    println!("{{}} {{}} {{}} {{}}", get(&w), get_plus(&w), get(&v), {use_inner});
}}
'''


def option_wrap(fields_t, init_t):
    return f'''struct T {{
{fields_t}
}}

struct S {{
    o: Option<T>,
    y: u64,
}}

#[inline(never)]
fn get_a(p: &S) -> u64 {{
    p.y
}}

#[inline(never)]
fn get_b(p: &S) -> u64 {{
    p.y + 1
}}

fn main() {{
    let s = S {{ o: Some({init_t}), y: 42 }};
    let n = S {{ o: None, y: 5 }};
    println!("{{}} {{}} {{}} {{}}", get_a(&s), get_b(&s), get_b(&n), s.o.is_some());
}}
'''


def array_len(n):
    return f'''struct T {{
    buf: [u8; {n}],
}}

struct S {{
    t: T,
    y: u64,
}}

#[inline(never)]
fn get_a(p: &S) -> u64 {{
    p.y
}}

#[inline(never)]
fn get_b(p: &S) -> u64 {{
    p.y + p.t.buf[0] as u64
}}

fn main() {{
    let s = S {{ t: T {{ buf: [1; {n}] }}, y: 42 }};
    println!("{{}} {{}} {{}}", get_a(&s), get_b(&s), s.t.buf.len());
}}
'''


def statics(first_keys, uses):
    return f'''use std::cell::Cell;

thread_local! {{
{first_keys}
    static B: Cell<u64> = Cell::new(20);
}}

static NAMES: [&str; 3] = ["x", "y", "z"];

fn bump_b() -> u64 {{
    B.with(|b| {{
        b.set(b.get() + 1);
        b.get()
    }})
}}

fn main() {{
    println!("{{}} {{}} {{}}", bump_b(), bump_b(), NAMES[2]);
{uses}
}}
'''


def helper_edit(label, step):
    """Only `main`'s string and constant change: the LLVM unit's IR stays, its helpers' C moves."""
    return f'''struct Acc {{
    total: u64,
    hits: u32,
}}

impl Acc {{
    #[inline(never)]
    fn add(&mut self, x: u64) {{
        self.total += x;
        self.hits += 1;
    }}

    #[inline(never)]
    fn report(&self) -> String {{
        format!("total={{}} hits={{}}", self.total, self.hits)
    }}
}}

#[inline(never)]
fn run(n: u64) -> Acc {{
    let mut a = Acc {{ total: 0, hits: 0 }};
    for i in 0..n {{
        if i % 3 == 0 {{
            a.add(i * 7);
        }}
    }}
    a
}}

fn main() {{
    let a = run(10);
    println!("{{}} [{label}] {{}}", a.report(), {step});
}}
'''


def shapes(with_tag):
    """Methods in several impl blocks of one type, called across fns; a merge removes one."""
    tag_impl = '''impl Shape {
    #[inline(never)]
    fn tag(&self) -> &'static str {
        if self.w > self.h { "wide" } else { "tall" }
    }
}

''' if with_tag else ""
    tag_use = '''    println!("{}", v[0].tag());
''' if with_tag else ""
    return f'''struct Shape {{
    w: u32,
    h: u32,
}}

impl Shape {{
    #[inline(never)]
    fn area(&self) -> u32 {{
        self.w * self.h
    }}
}}

{tag_impl}impl Shape {{
    #[inline(never)]
    fn perim(&self) -> u32 {{
        2 * (self.w + self.h)
    }}
}}

impl Shape {{
    fn scaled(&self, k: u32) -> Shape {{
        Shape {{ w: self.w * k, h: self.h * k }}
    }}
}}

#[inline(never)]
fn total(v: &[Shape]) -> u64 {{
    let mut t = 0u64;
    for s in v {{
        t += s.area() as u64 + s.perim() as u64;
    }}
    t
}}

#[inline(never)]
fn describe(s: &Shape) -> String {{
    format!("{{}}x{{}} p={{}} a={{}}", s.w, s.h, s.perim(), s.area())
}}

fn main() {{
    let mut v = Vec::new();
    for i in 1..200u32 {{
        v.push(Shape {{ w: i % 7 + 1, h: i % 5 + 2 }}.scaled(2));
    }}
    let mut sum = 0u64;
    for _ in 0..50 {{
        sum += total(&v);
    }}
    println!("{{}} {{}}", sum, describe(&v[2]));
{tag_use}}}
'''


def lifetime_variants(swap):
    """Two instances of `M` that differ only in lifetimes share one C type,
    named by the variant registered first (`register_adt_instance`): one
    body names the `'a` variants as local types, another calls a method
    on the `'static` ones (which makes them as its instance's owner). A
    build that makes a request's instance before an earlier body's turn
    (c847cb8b6, reverted) registers them in another order than an image
    build: the C name moved (tsgo replay states 9-11). `swap` puts the
    two bodies the other way round."""
    first = """#[inline(never)]
fn first<'a>(r: Rc<dyn Tr + 'a>, s: &'a str) -> u32 {
    let m: M<Rc<dyn Tr + 'a>> = M { t: r, n: 5 };
    let w: M<&'a str> = M { t: s, n: 1 };
    m.n + m.t.v() + w.n + w.t.len() as u32
}
"""
    second = """#[inline(never)]
fn second(r: Rc<dyn Tr>, s: &'static str) -> u32 {
    let m = M { t: r, n: 7 };
    let w = M { t: s, n: 2 };
    m.get() + w.get()
}
"""
    a, b = (second, first) if swap else (first, second)
    return """use std::rc::Rc;

trait Tr {
    fn v(&self) -> u32;
}

struct K(u32);

impl Tr for K {
    fn v(&self) -> u32 {
        self.0
    }
}

struct M<T> {
    t: T,
    n: u32,
}

impl<T> M<T> {
    #[inline(never)]
    fn get(&self) -> u32 {
        self.n
    }
}

""" + a + "\n" + b + """
fn main() {
    let k: Rc<dyn Tr> = Rc::new(K(3));
    println!("{} {}", first(k.clone(), "abc"), second(k, "de"));
}
"""


def corpus():
    """(name, [sources]) of every sequence."""
    seqs = [
        ("nested-grow", [
            nested("    a: u64,", "T { a: 1 }", "s.t.a"),
            nested("    a: u64,\n    b: u64,", "T { a: 1, b: 2 }", "s.t.a + s.t.b"),
            nested("    a: u64,\n    b: u64,\n    c: u32,", "T { a: 1, b: 2, c: 3 }", "s.t.a + s.t.b + s.t.c as u64"),
            nested("    a: u64,", "T { a: 1 }", "s.t.a"),
        ]),
        ("enum-payload", [
            enum_payload("    A(u8),\n    B(u32, u16),", "        E::A(x) => x as u64,\n        E::B(a, b) => a as u64 + b as u64,", ""),
            enum_payload("    A(u8),\n    B(u32, u16),\n    C(u64, u64),",
                         "        E::A(x) => x as u64,\n        E::B(a, b) => a as u64 + b as u64,\n        E::C(a, b) => a + b,",
                         "    let c = S { e: E::C(1, 2), y: 3 };\n    println!(\"{}\", read_e(&c) + read_y(&c));"),
            enum_payload("    C(u64, u64),\n    A(u8),\n    B(u32, u16),",
                         "        E::A(x) => x as u64,\n        E::B(a, b) => a as u64 + b as u64,\n        E::C(a, b) => a + b,",
                         "    let c = S { e: E::C(1, 2), y: 3 };\n    println!(\"{}\", read_e(&c) + read_y(&c));"),
        ]),
        ("generic-arg", [
            generic("    a: u32,", "Inner { a: 1 }", "", "", "w.t.a"),
            generic("    a: u32,\n    b: u64,\n    c: u64,", "Inner { a: 1, b: 2, c: 3 }", "", "", "w.t.a as u64 + w.t.b + w.t.c"),
            generic("    a: u32,\n    b: u64,\n    c: u64,", "Inner { a: 1, b: 2, c: 3 }", "    m: [u64; 2],", " m: [5, 6],", "w.t.a as u64 + w.m[1]"),
        ]),
        ("option-wrap", [
            option_wrap("    a: u64,", "T { a: 1 }"),
            option_wrap("    a: u64,\n    b: [u64; 3],", "T { a: 1, b: [2, 3, 4] }"),
        ]),
        ("array-len", [array_len(4), array_len(20), array_len(1)]),
        ("statics", [
            statics("", ""),
            statics("    static A: Cell<u64> = Cell::new(10);",
                    "    A.with(|a| a.set(a.get() + 5));\n    println!(\"{}\", A.with(|a| a.get()));"),
            statics("    static A: Cell<u64> = Cell::new(10);\n    static AA: Cell<u32> = Cell::new(1);",
                    "    A.with(|a| a.set(a.get() + 5));\n    AA.with(|a| a.set(a.get() * 3));\n    println!(\"{} {}\", A.with(|a| a.get()), AA.with(|a| a.get()));"),
        ]),
    ]
    seqs.append(("lifetime-variant-order", [lifetime_variants(False), lifetime_variants(True), lifetime_variants(False)]))
    seqs.append(("llvm-helper-only-edit", [helper_edit("v1", 1), helper_edit("v2-label", 1), helper_edit("v2-label", 3)]))
    seqs.append(("remove-impl-pgo", [shapes(True), shapes(False), shapes(True)], {"pgo": True}))
    dt = os.path.join(ROOT, "tests/daemon/dt01_deep_type_edits")
    dt01 = [open(os.path.join(dt, f"v{k}.rs")).read() for k in range(1, 7)]
    seqs.append(("dt01", dt01))
    # A CI job's shapes on the image (check_seq): five builds without emitted C before the compared
    # one, a jump over three versions, and four builds that each start from the second's state.
    seqs.append(("dt01-quiet", dt01, {"quiet": True}))
    seqs.append(("dt01-jump", dt01, {"steps": [0, 1, 5]}))
    seqs.append(("dt01-stale", dt01, {"stale_after": 1}))
    # B1's skipping itself: builds that emit no C skip the units their reads call clean; their
    # programs' output must match the one-shot builds'.
    seqs.append(("dt01-b1-skip", dt01, {"quiet": True, "b1": "skip"}))
    return seqs


def units(d):
    """The unit files `--emit-c` wrote into `d`, by content hash."""
    out = {}
    for f in sorted(os.listdir(d)):
        b = open(os.path.join(d, f), "rb").read()
        out.setdefault(hashlib.sha256(b).hexdigest(), []).append((f, b))
    return out


def unit_diff(dw, dc):
    """'' when the two unit sets are equal by content, else a short account."""
    w, c = units(dw), units(dc)
    only_w = [x for h, fs in w.items() for x in fs[len(c.get(h, [])):]]
    only_c = [x for h, fs in c.items() for x in fs[len(w.get(h, [])):]]
    if not only_w and not only_c:
        return ""
    msg = f"units differ: image-only {[f for f, _ in only_w][:4]}, one-shot-only {[f for f, _ in only_c][:4]}"
    by_name = {f: b for f, b in only_c}
    for f, b in only_w[:2]:
        if f in by_name:
            a, o = b.split(b"\n"), by_name[f].split(b"\n")
            n = next((i for i in range(min(len(a), len(o))) if a[i] != o[i]), min(len(a), len(o)))
            msg += f"; {f} line {n + 1}: image {a[n][:160] if n < len(a) else b''!r} vs one-shot {o[n][:160] if n < len(o) else b''!r}"
    return msg


def run_bin(path, cwd):
    try:
        r = subprocess.run([path], cwd=cwd, capture_output=True, timeout=RUN_TIMEOUT)
        return (r.returncode, r.stdout)
    except subprocess.TimeoutExpired:
        return ("timeout", b"")


def build(cmd, env, cwd):
    """(exit status or 'hang', stderr head)."""
    try:
        r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, timeout=BUILD_TIMEOUT)
    except subprocess.TimeoutExpired:
        return ("hang", "")
    return (r.returncode, r.stderr.decode(errors="replace")[-400:].replace("\n", " "))


def check_seq(name, srcs, backend, args, work, opts):
    """One sequence on one backend: (name, backend, problems, steps); steps is 0 when skipped."""
    d = os.path.join(work, f"{name}-{backend}")
    os.makedirs(d, exist_ok=True)
    drop = ("LUST_DAEMON_SOCKET", "LUST_CACHE_DIR", "LUST_NO_CACHE", "LUST_THREADS", "LUST_FRONT_STATE", "LUST_RELEASE_BACKEND",
            "LUST_PGO_USE", "LUST_PGO_GEN", "LUST_PGO_CC", "LUST_PROFDATA")
    base = {k: v for k, v in os.environ.items() if k not in drop}
    base.update(LUST_RELEASE_C="1", LUST_NO_DAEMON="1")
    if backend == "llvm":
        base["LUST_RELEASE_BACKEND"] = "llvm"
        if args.llvm_cc:
            base["LUST_CC"] = args.llvm_cc
    rel = ["--release", "--target", args.host]
    if opts.get("pgo"):
        if not args.pgo:
            return name, backend, [], 0
        # The profile both sides use: an instrumented one-shot build of the first step, run once.
        with open(os.path.join(d, "main.rs"), "w") as f:
            f.write(srcs[0])
        raw = os.path.join(d, "raw")
        gen = dict(base, LUST_NO_CACHE="1", LUST_THREADS="4", LUST_PGO_GEN="1", LUST_PGO_CC=args.pgo["cc"])
        rg, eg = build([LUST, "build", "main.rs", *rel, "-o", "gen.bin"], gen, d)
        if rg != 0:
            return name, backend, [f"{name} {backend}: the instrumented build failed ({rg}): {eg[:300]}"], len(srcs)
        subprocess.run([os.path.join(d, "gen.bin")], cwd=d, env=dict(os.environ, LLVM_PROFILE_FILE=os.path.join(raw, "%p.profraw")),
                       capture_output=True, timeout=RUN_TIMEOUT)
        prof = os.path.join(d, "train.profdata")
        m = subprocess.run([args.pgo["profdata"], "merge", "-o", prof, raw], capture_output=True, text=True)
        if m.returncode != 0:
            return name, backend, [f"{name} {backend}: llvm-profdata merge failed: {m.stderr[:300]}"], len(srcs)
        base.update(LUST_PGO_USE=prof, LUST_PROFDATA=args.pgo["profdata"])
    img = dict(base, LUST_FRONT_STATE=os.path.join(d, "front"), LUST_FRONT_SAVE="background", LUST_CACHE_DIR=os.path.join(d, "cache"), LUST_THREADS="1")
    # B1 (release C fn units a warm build does not assemble): the image side runs its oracle
    # (LUST_CHECK_UNIT_FP=1: every unit assembles, and one its recorded reads call clean must
    # have the same text), or with `b1` skip the skipping itself (LUST_B1=1).
    img.update({"LUST_B1": "1"} if opts.get("b1") == "skip" else {"LUST_CHECK_UNIT_FP": "1"})
    one = dict(base, LUST_NO_CACHE="1", LUST_THREADS="4")
    problems = []
    lock = os.path.join(d, "front", "lock")

    def saved():
        """Waits for the last background image save."""
        if os.path.exists(lock):
            subprocess.run(["flock", lock, "true"], timeout=BUILD_TIMEOUT)

    # CI job shapes (opts): `steps`, the steps the image side builds (a jump skips the rest);
    # `quiet`, emitted C only at the last step (a CI job's builds emit none); `stale_after`, a
    # step whose state (image and cache) every later step starts from again (a CI disk whose
    # commits did not land: merges 10, 11 and 12 each built from merge 9's state).
    order = opts.get("steps", list(range(len(srcs))))
    snap = None
    for step in order:
        with open(os.path.join(d, "main.rs"), "w") as f:
            f.write(srcs[step])
        where = f"{name} {backend} step {step + 1}"
        if snap:
            saved()
            for sub in ("front", "cache"):
                shutil.rmtree(os.path.join(d, sub), ignore_errors=True)
                shutil.copytree(os.path.join(snap, sub), os.path.join(d, sub), symlinks=True)
        emit = not opts.get("quiet") or step == order[-1]
        for side in ("ew", "ec"):
            shutil.rmtree(os.path.join(d, side), ignore_errors=True)
            os.makedirs(os.path.join(d, side))
        ce = lambda side: ["--emit-c", os.path.join(d, side, "t")] if emit else []
        rw, ew = build([LUST, "build", "main.rs", *rel, "-o", "image.bin", *ce("ew")], img, d)
        rc, ec = build([LUST, "build", "main.rs", *rel, "-o", "one.bin", *ce("ec")], one, d)
        if rw != rc:
            problems.append(f"{where}: build status image {rw} vs one-shot {rc}: {(ew if rw else ec)[:300]}")
            break
        if opts.get("stale_after") == step:
            saved()
            snap = os.path.join(d, "snap")
            for sub in ("front", "cache"):
                shutil.copytree(os.path.join(d, sub), os.path.join(snap, sub), symlinks=True)
        if rw != 0:
            continue
        diff = unit_diff(os.path.join(d, "ew"), os.path.join(d, "ec")) if emit else ""
        if diff:
            problems.append(f"{where}: {diff}")
        ow, oc = run_bin(os.path.join(d, "image.bin"), d), run_bin(os.path.join(d, "one.bin"), d)
        if ow != oc:
            problems.append(f"{where}: output image {ow!r} vs one-shot {oc!r}"[:600])
        if problems:
            break
    # The last background image save ends before the directory goes.
    saved()
    if problems and args.keep:
        shutil.copytree(d, os.path.join(args.keep, f"{name}-{backend}"), dirs_exist_ok=True)
    return name, backend, problems, len(srcs)


def is_clang(cmd):
    try:
        return "clang" in subprocess.run([cmd, "--version"], capture_output=True, text=True).stdout
    except OSError:
        return False


def pgo_tools():
    """{cc, profdata} for the PGO sequences: zig's LLVM major in both, and a profile runtime that
    links; None when any is missing."""
    if not shutil.which("zig"):
        return None
    v = subprocess.run(["zig", "cc", "--version"], capture_output=True, text=True).stdout
    m = re.search(r"clang version (\d+)", v)
    if not m:
        return None
    major = m.group(1)
    cc = os.environ.get("LUST_PGO_CC") or shutil.which(f"clang-{major}")
    pd = os.environ.get("LUST_PROFDATA") or shutil.which(f"llvm-profdata-{major}")
    if not cc or not pd:
        return None
    with tempfile.TemporaryDirectory() as t:
        src = os.path.join(t, "p.c")
        with open(src, "w") as f:
            f.write("int main(void) { return 0; }\n")
        if subprocess.run([cc, "-fprofile-generate", src, "-o", os.path.join(t, "p")], capture_output=True).returncode != 0:
            return None
    return {"cc": cc, "profdata": pd, "major": major}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--jobs", type=int, default=min(14, os.cpu_count() or 4))
    ap.add_argument("--keep", help="copy each failing sequence's directory here")
    ap.add_argument("--only", help="run only the sequences whose name has this text")
    args = ap.parse_args()
    if not os.access(LUST, os.X_OK):
        print(f"error: {LUST} not built. Run scripts/build.sh first.")
        return 2
    v = subprocess.run(["rustc", "-vV"], capture_output=True, text=True).stdout
    args.host = next((l.split()[1] for l in v.splitlines() if l.startswith("host:")), "x86_64-unknown-linux-gnu")
    # The LLVM units need a clang: zig cc is one, else cc when it is clang, else clang.
    args.llvm_cc = None
    if not shutil.which("zig") and not os.environ.get("LUST_CC") and not is_clang("cc"):
        if not shutil.which("clang"):
            print("error: the LLVM backend needs clang (or zig) on PATH")
            return 2
        args.llvm_cc = "clang"
    args.pgo = None if args.llvm_cc else pgo_tools()
    seqs = [s if len(s) == 3 else (*s, {}) for s in corpus() if not args.only or args.only in s[0]]
    if any(o.get("pgo") for _, _, o in seqs) and not args.pgo:
        print("front-check: PGO sequences skipped: they need zig, and clang and llvm-profdata of zig's LLVM major with a profile runtime")
    work = tempfile.mkdtemp(prefix="front-check.", dir=os.environ.get("TMPDIR"))
    jobs = [(n, srcs, b, o) for n, srcs, o in seqs for b in ("c", "llvm")]
    t0 = time.time()
    bad = steps = 0
    with ThreadPoolExecutor(max(1, args.jobs)) as pool:
        for name, backend, problems, n in pool.map(lambda j: check_seq(j[0], j[1], j[2], args, work, j[3]), jobs):
            steps += n
            for p in problems:
                bad += 1
                print(f"front-check: DIFFERENT {p}")
    shutil.rmtree(work, ignore_errors=True)
    print(f"front-check: {steps} steps, {bad} different ({len(seqs)} sequences, release C and LLVM, image vs one-shot, {time.time() - t0:.0f} s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
