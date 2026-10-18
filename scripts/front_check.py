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
#
# LUST_BIN overrides the lust binary (default target/release/lust).
# Usage: front_check.py [--jobs N] [--keep DIR] [--only NAME]
# Exit 0 = all same, 1 = a difference or a build failure on one side, 2 = setup error.
import argparse, hashlib, os, shutil, subprocess, sys, tempfile, time
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
    dt = os.path.join(ROOT, "tests/daemon/dt01_deep_type_edits")
    seqs.append(("dt01", [open(os.path.join(dt, f"v{k}.rs")).read() for k in range(1, 7)]))
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


def check_seq(name, srcs, backend, args, work):
    """One sequence on one backend: (name, backend, problems, steps)."""
    d = os.path.join(work, f"{name}-{backend}")
    os.makedirs(d, exist_ok=True)
    drop = ("LUST_DAEMON_SOCKET", "LUST_CACHE_DIR", "LUST_NO_CACHE", "LUST_THREADS", "LUST_FRONT_STATE", "LUST_RELEASE_BACKEND")
    base = {k: v for k, v in os.environ.items() if k not in drop}
    base.update(LUST_RELEASE_C="1", LUST_NO_DAEMON="1")
    if backend == "llvm":
        base["LUST_RELEASE_BACKEND"] = "llvm"
        if args.llvm_cc:
            base["LUST_CC"] = args.llvm_cc
    img = dict(base, LUST_FRONT_STATE=os.path.join(d, "front"), LUST_FRONT_SAVE="background", LUST_CACHE_DIR=os.path.join(d, "cache"), LUST_THREADS="1")
    one = dict(base, LUST_NO_CACHE="1", LUST_THREADS="4")
    rel = ["--release", "--target", args.host]
    problems = []
    for step, src in enumerate(srcs):
        with open(os.path.join(d, "main.rs"), "w") as f:
            f.write(src)
        where = f"{name} {backend} step {step + 1}"
        for side in ("ew", "ec"):
            shutil.rmtree(os.path.join(d, side), ignore_errors=True)
            os.makedirs(os.path.join(d, side))
        rw, ew = build([LUST, "build", "main.rs", *rel, "-o", "image.bin", "--emit-c", os.path.join(d, "ew", "t")], img, d)
        rc, ec = build([LUST, "build", "main.rs", *rel, "-o", "one.bin", "--emit-c", os.path.join(d, "ec", "t")], one, d)
        if rw != rc:
            problems.append(f"{where}: build status image {rw} vs one-shot {rc}: {(ew if rw else ec)[:300]}")
            break
        if rw != 0:
            continue
        diff = unit_diff(os.path.join(d, "ew"), os.path.join(d, "ec"))
        if diff:
            problems.append(f"{where}: {diff}")
        ow, oc = run_bin(os.path.join(d, "image.bin"), d), run_bin(os.path.join(d, "one.bin"), d)
        if ow != oc:
            problems.append(f"{where}: output image {ow!r} vs one-shot {oc!r}"[:600])
        if problems:
            break
    # The last background image save ends before the directory goes.
    lock = os.path.join(d, "front", "lock")
    if os.path.exists(lock):
        subprocess.run(["flock", lock, "true"], timeout=BUILD_TIMEOUT)
    if problems and args.keep:
        shutil.copytree(d, os.path.join(args.keep, f"{name}-{backend}"), dirs_exist_ok=True)
    return name, backend, problems, len(srcs)


def is_clang(cmd):
    try:
        return "clang" in subprocess.run([cmd, "--version"], capture_output=True, text=True).stdout
    except OSError:
        return False


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
    seqs = [s for s in corpus() if not args.only or args.only in s[0]]
    work = tempfile.mkdtemp(prefix="front-check.", dir=os.environ.get("TMPDIR"))
    jobs = [(n, srcs, b) for n, srcs in seqs for b in ("c", "llvm")]
    t0 = time.time()
    bad = steps = 0
    with ThreadPoolExecutor(max(1, args.jobs)) as pool:
        for name, backend, problems, n in pool.map(lambda j: check_seq(j[0], j[1], j[2], args, work), jobs):
            steps += n
            for p in problems:
                bad += 1
                print(f"front-check: DIFFERENT {p}")
    shutil.rmtree(work, ignore_errors=True)
    print(f"front-check: {steps} steps, {bad} different ({len(seqs)} sequences, release C and LLVM, image vs one-shot, {time.time() - t0:.0f} s)")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
