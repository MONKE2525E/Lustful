#!/usr/bin/env python3
# Edit sequences through the persistent disk cache (.lust-cache unit objects), checked
# against uncached builds. Each sequence is one program edited step by step in its own
# directory. Every step builds twice:
#   cached  `lust build` with the disk cache on, the cache kept from the earlier steps;
#   ref     the same with LUST_NO_CACHE=1 (a fresh compile of every unit).
# Both binaries run; stdout and exit status must match. With --rustc, rustc's binary
# must match too. With --daemon, a third build goes through one daemon per sequence
# (cache on) and must match as well.
#
# The programs are made to have many C units (filler fns give them several hundred KB
# of C) and the edits change what decides a unit's C: closures added and removed
# (closure slots move), calls, generic instances, fn pointers, dyn calls, fns moved in
# the source (slots and unit membership move), filler size (unit boundaries move), and,
# with --threads, the thread count (the unit byte target). fx-unitcache: the unit key
# missed a closure slot that an adapter chain called, so an edit that removed earlier
# closures served the old object and the binary called the wrong closure.
#
# LUST_BIN overrides the lust binary (default target/release/lust).
# Usage: cache_check.py --seqs 40 --steps 4 [--seed 1] [--jobs N] [--threads 1,4,24]
#                       [--rustc] [--daemon] [--keep DIR]
# Sequence 0 of every run is the fx-unitcache repro shape. Exit 0 = all same, 1 = a
# difference, a build failure on one side, or a hang; 2 = setup error.
import argparse, os, random, shutil, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LUST = os.environ.get("LUST_BIN") or os.path.join(ROOT, "target/release/lust")
BUILD_TIMEOUT = 120
RUN_TIMEOUT = 20

PRELUDE = '''trait Area {
    fn area(&self) -> u64;
}
struct Sq(u64);
struct Rect(u64, u64);
impl Area for Sq {
    fn area(&self) -> u64 {
        self.0 * self.0
    }
}
impl Area for Rect {
    fn area(&self) -> u64 {
        self.0 * self.1 + 1
    }
}
fn show<T: std::fmt::Debug>(tag: &str, x: T) {
    println!("{tag} {x:?}");
}
fn apply<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}
'''

GEN_VALUES = ["7u8", "-3i64", "(4u32, true)", "Some(9u16)", '"txt"', "vec![1u8, 2]", "[5i32, 6]", "'c'", "2.5f64", "(1u8, (2i16, 3u64))"]
ADAPTERS = [
    ".filter(|x| *x % {a} != {b})",
    ".map(|x| x.wrapping_mul({c}) % 1000)",
    ".inspect(|x| if *x < {d} {{ println!(\"{tag} pull {{x}}\") }})",
    ".skip({e})",
    ".take({g})",
    ".step_by({f})",
    ".peekable()",
    ".enumerate().map(|(i, x)| x + i as u32)",
]
TERMINALS = [
    ".count()",
    ".sum::<u32>()",
    ".max()",
    ".last()",
    ".fold(0u32, |acc, x| acc.wrapping_add(x * {c}))",
    ".any(|x| x == {b})",
    ".position(|x| x > {d})",
]


def stmt(rng, tag, n_fill, callees):
    """One random statement for a worker fn. `tag` names it in the output."""
    r = {k: rng.randint(1, 9) for k in "abcdefg"}
    r["tag"] = tag
    kind = rng.choice(["chain", "chain", "chain", "call", "generic", "apply", "fnptr", "dyn", "closure", "sort"])
    if kind == "call" and callees:
        return f"    println!(\"{tag} {{}}\", w{rng.choice(callees)}(v));"
    if kind == "generic":
        return f"    show(\"{tag}\", {rng.choice(GEN_VALUES)});"
    if kind == "apply":
        return f"    println!(\"{tag} {{}}\", apply(|x| x * {r['a']} + {r['b']}, {r['c']}));"
    if kind == "fnptr":
        return f"    let fp: fn(u64) -> u64 = filler{rng.randrange(n_fill)};\n    println!(\"{tag} {{}}\", fp({r['a']}));"
    if kind == "dyn":
        shape = rng.choice([f"Sq({r['a']})", f"Rect({r['b']}, {r['c']})"])
        return f"    let d: Box<dyn Area> = Box::new({shape});\n    println!(\"{tag} {{}}\", d.area());"
    if kind == "closure":
        return f"    let c = |x: u32| x * {r['a']} + {r['b']};\n    println!(\"{tag} {{}}\", c({r['c']}) + c({r['d']}));"
    if kind == "sort":
        return f"    let mut s: Vec<u32> = v.to_vec();\n    s.sort_by_key(|x| (*x * {r['a']}) % {r['b'] + 3});\n    println!(\"{tag} {{:?}}\", s);"
    chain = "".join(a.format(**r) for a in rng.sample(ADAPTERS, rng.randint(1, 5)))
    term = rng.choice(TERMINALS).format(**r)
    return f"    let n = v.iter().copied(){chain}{term};\n    println!(\"{tag} {{:?}}\", n);"


def filler(i, size):
    arms = "\n".join(f"        if s % {7 + j} == {j % 5} {{ s = s.wrapping_add({i * 13 + j}); }}" for j in range(size))
    return (f"fn filler{i}(x: u64) -> u64 {{\n    let mut s = x ^ {i};\n    for k in 0..{i % 5 + 2} {{\n"
            f"        s = s.wrapping_mul(31).wrapping_add(k);\n{arms}\n    }}\n"
            f"    if s % 7 == 0 {{ println!(\"f{i} {{}}\", s % 100); }}\n    s\n}}\n")


class Prog:
    """A program state: workers (id -> list of stmts), the source order of all items,
    and filler sizes. Worker `w<i>` calls only workers with a smaller id (no cycles)."""

    def __init__(self, rng, n_fill):
        self.rng = rng
        self.fill = [rng.randint(2, 12) for _ in range(n_fill)]
        self.workers = {}
        self.order = [("f", i) for i in range(n_fill)]
        self.next_id = 0
        self.next_tag = 0
        for _ in range(rng.randint(3, 6)):
            self.add_worker()

    def tag(self):
        self.next_tag += 1
        return f"t{self.next_tag}"

    def add_worker(self):
        w = self.next_id
        self.next_id += 1
        callees = list(self.workers)
        self.workers[w] = [stmt(self.rng, self.tag(), len(self.fill), callees) for _ in range(self.rng.randint(1, 4))]
        self.order.insert(self.rng.randint(0, len(self.order)), ("w", w))

    def remove_worker(self):
        if len(self.workers) <= 2:
            return
        w = self.rng.choice(list(self.workers))
        del self.workers[w]
        self.order.remove(("w", w))
        for body in self.workers.values():
            body[:] = [s for s in body if f" w{w}(v)" not in s]

    def edit(self):
        """One random edit."""
        op = self.rng.choice(["add_stmt", "add_stmt", "del_stmt", "del_stmt", "swap_stmt", "add_worker",
                              "del_worker", "move", "move", "resize"])
        w = self.rng.choice(list(self.workers))
        body = self.workers[w]
        callees = [c for c in self.workers if c < w]
        if op == "add_stmt":
            body.insert(self.rng.randint(0, len(body)), stmt(self.rng, self.tag(), len(self.fill), callees))
        elif op == "del_stmt" and len(body) > 1:
            body.pop(self.rng.randrange(len(body)))
        elif op == "swap_stmt" and body:
            body[self.rng.randrange(len(body))] = stmt(self.rng, self.tag(), len(self.fill), callees)
        elif op == "add_worker":
            self.add_worker()
        elif op == "del_worker":
            self.remove_worker()
        elif op == "move":
            item = self.order.pop(self.rng.randrange(len(self.order)))
            self.order.insert(self.rng.randint(0, len(self.order)), item)
        elif op == "resize":
            i = self.rng.randrange(len(self.fill))
            self.fill[i] = max(1, self.fill[i] + self.rng.choice([-3, -1, 1, 4]))

    def source(self):
        out = [PRELUDE]
        for kind, i in self.order:
            if kind == "f":
                out.append(filler(i, self.fill[i]))
            else:
                out.append(f"fn w{i}(v: &[u32]) -> usize {{\n" + "\n".join(self.workers[i]) + f"\n    v.len() + {i}\n}}\n")
        main = ["fn main() {", "    let v: Vec<u32> = (1..=12).collect();", "    let mut acc = 0u64;"]
        main += [f"    acc = acc.wrapping_add(filler{i}(acc));" for i in range(len(self.fill))]
        main.append("    println!(\"acc {acc}\");")
        main += [f"    println!(\"w{w} -> {{}}\", w{w}(&v));" for w in sorted(self.workers)]
        main.append("}")
        out.append("\n".join(main) + "\n")
        return "\n".join(out)


def repro_steps():
    """The fx-unitcache shape: fn `edited` loses one of two closures; a later fn's
    adapter chain calls its own closure through a slot that moves down by one."""
    def src(two):
        fill = [filler(i, 6) for i in range(160)]
        edited = ("fn edited(v: &[u32]) -> usize {\n    v.iter().filter(|x| **x > 2)"
                  + (".filter(|_| true)" if two else "") + ".count()\n}\n")
        tail = ("fn tail() {\n    let n = (0..10u32).inspect(|x| if *x < 3 { println!(\"pull {x}\") })"
                ".skip(1).peekable().step_by(2).skip(0).take(30).skip(2).count();\n    println!(\"{n}\");\n}\n")
        main = ("fn main() {\n    let v: Vec<u32> = (1..=9).collect();\n    println!(\"{}\", edited(&v));\n    let mut acc = 0u64;\n"
                + "".join(f"    acc = acc.wrapping_add(filler{i}(acc));\n" for i in range(160))
                + "    println!(\"{acc}\");\n    tail();\n}\n")
        return "\n".join(fill[:40] + [edited] + fill[40:120] + [tail] + fill[120:] + [main])
    return [src(True), src(False), src(True)]


def sequence(seed, steps, n_fill):
    rng = random.Random(seed)
    p = Prog(rng, n_fill)
    out = [p.source()]
    for _ in range(steps - 1):
        for _ in range(rng.randint(1, 3)):
            p.edit()
        out.append(p.source())
    return out


def run_bin(path, cwd):
    try:
        r = subprocess.run([path], cwd=cwd, capture_output=True, timeout=RUN_TIMEOUT)
        return (r.returncode, r.stdout)
    except subprocess.TimeoutExpired:
        return ("timeout", b"")


def build(cmd, env, cwd):
    """Returns 'ok', 'fail: <stderr head>', or 'hang'."""
    try:
        r = subprocess.run(cmd, cwd=cwd, env=env, capture_output=True, timeout=BUILD_TIMEOUT)
    except subprocess.TimeoutExpired:
        return "hang"
    return "ok" if r.returncode == 0 else "fail: " + r.stderr.decode(errors="replace")[:300].replace("\n", " ")


def check_seq(idx, srcs, threads, args, work):
    """Runs one sequence. Returns (idx, problems, stats)."""
    d = os.path.join(work, f"s{idx}")
    os.makedirs(d, exist_ok=True)
    base = {k: v for k, v in os.environ.items() if k not in ("LUST_DAEMON_SOCKET", "LUST_CACHE_DIR", "LUST_NO_CACHE", "LUST_THREADS")}
    problems, stats = [], {"steps": 0, "invalid": 0}
    for step, src in enumerate(srcs):
        with open(os.path.join(d, "main.rs"), "w") as f:
            f.write(src)
        t = threads[step % len(threads)] if threads else None
        tenv = dict(base, **({"LUST_THREADS": str(t)} if t else {}))
        where = f"seq {idx} step {step}" + (f" threads={t}" if t else "")
        outs = {}
        if args.rustc:
            r = build(["rustc", "--edition", "2024", "-C", "panic=abort", "-C", "overflow-checks=on", "-A", "warnings",
                       "main.rs", "-o", "rustc.bin"], base, d)
            if r != "ok":
                stats["invalid"] += 1
                problems.append(f"{where}: generator made a program rustc rejects: {r[:200]}")
                break
            outs["rustc"] = run_bin("./rustc.bin", d)
        ref = build([LUST, "build", "main.rs", "-o", "ref.bin"], dict(tenv, LUST_NO_CACHE="1", LUST_NO_DAEMON="1"), d)
        cached = build([LUST, "build", "main.rs", "-o", "cached.bin"], dict(tenv, LUST_NO_DAEMON="1"), d)
        sides = [("ref", ref), ("cached", cached)]
        if args.daemon:
            sides.append(("daemon", build([LUST, "build", "main.rs", "-o", "daemon.bin"], tenv, d)))
        if ref != "ok" and all(r == ref for _, r in sides):
            # lust rejects the program on every path: a lust gap, not a cache bug. With
            # --rustc it is a reject of valid Rust; report it so it is not lost.
            if args.rustc:
                problems.append(f"{where}: lust rejects a program rustc accepts: {ref[:200]}")
            break
        for name, r in sides:
            if r != "ok":
                problems.append(f"{where}: {name} build {r[:200]}")
            else:
                outs[name] = run_bin(f"./{name}.bin", d)
        ref_out = outs.get("rustc", outs.get("ref"))
        for name, o in outs.items():
            if o != ref_out:
                a, b = ref_out[1].decode(errors="replace").splitlines(), o[1].decode(errors="replace").splitlines()
                first = next((i for i in range(max(len(a), len(b))) if (a[i:i + 1] != b[i:i + 1])), 0)
                problems.append(f"{where}: {name} differs (exit {ref_out[0]} vs {o[0]}; line {first + 1}: "
                                f"{a[first:first + 1]} vs {b[first:first + 1]})")
        stats["steps"] += 1
        if problems:
            break
    for sock in [f for f in os.listdir(d) if f.startswith(".lust-daemon-") and f.endswith(".sock")]:
        os.unlink(os.path.join(d, sock))  # removing the socket stops the daemon
    if problems and args.keep:
        dest = os.path.join(args.keep, f"s{idx}")
        os.makedirs(dest, exist_ok=True)
        for step, src in enumerate(srcs):
            with open(os.path.join(dest, f"step{step}.rs"), "w") as f:
                f.write(src)
    if not args.keep or not problems:
        shutil.rmtree(d, ignore_errors=True)
    return idx, problems, stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seqs", type=int, default=40)
    ap.add_argument("--steps", type=int, default=4)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--fill", type=int, default=80, help="filler fns per program (about 6 KB of C each)")
    ap.add_argument("--jobs", type=int, default=os.cpu_count())
    ap.add_argument("--threads", default="", help="comma list of LUST_THREADS values, cycled per step")
    ap.add_argument("--rustc", action="store_true")
    ap.add_argument("--daemon", action="store_true")
    ap.add_argument("--keep", help="copy the steps of each failing sequence here")
    args = ap.parse_args()
    if not os.access(LUST, os.X_OK):
        print(f"error: {LUST} not built. Run scripts/build.sh first.")
        return 2
    threads = [int(t) for t in args.threads.split(",") if t]
    work = tempfile.mkdtemp(prefix="cache-check.", dir=os.environ.get("TMPDIR"))
    jobs = []
    for i in range(args.seqs):
        srcs = repro_steps() if i == 0 else sequence(args.seed * 1_000_003 + i, args.steps, args.fill)
        # Each sequence rotates the thread list, so every count builds first somewhere.
        th = threads[i % len(threads):] + threads[:i % len(threads)] if threads else []
        jobs.append((i, srcs, th))
    bad = steps = invalid = 0
    with ThreadPoolExecutor(max(1, args.jobs)) as pool:
        for idx, problems, stats in pool.map(lambda j: check_seq(j[0], j[1], j[2], args, work), jobs):
            steps += stats["steps"]
            invalid += stats["invalid"]
            if problems:
                bad += 1
                for p in problems:
                    print("bad", p, flush=True)
    shutil.rmtree(work, ignore_errors=True)
    print(f"cache-check: {args.seqs} sequences, {steps} steps checked, {bad} with problems, {invalid} invalid programs")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
