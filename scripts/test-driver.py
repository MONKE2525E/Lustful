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
#      rechecks only the changed fn itself (its body is checked
#      against its own signature; seed 42) and reuses every clean
#      mentioning body through the dirty walk.
#   5. graph and build-script routing: editing a build script input
#      makes the daemon start a fresh session (its log line proves it)
#      while the program output stays correct.
#   6. std in sessions: a source std fn (std::process::exit, S5) runs
#      through the daemon twice with the same result.
#   7. resolver-path incremental: body, type, import, and new-file
#      edits in a multi-file crate recheck only the bodies whose
#      recorded reads changed, with matching program output.
#   8. slot compaction: renumbered survivors re-emit C from cached
#      IR (reemitted counter) with correct output.
#   9. restart with an added file in the middle: the persisted def
#      order keeps Adt and static numbering across a daemon
#      restart, so old units still hit the disk cache and output
#      stays exact. A corrupted def-order file is a cache miss:
#      the new daemon numbers fresh and output stays exact.
#  10. empty-slot units after a restart: two fn units that hold only
#      generic template slots have the same instance content, but each
#      registers under its own unit number; a restarted daemon must
#      not serve one unit the other's disk object.
#  11. panic positions in reused bodies: an edit that only moves text
#      (spaces inside a body, comment lines above a fn) keeps a warm
#      build's panic line and column equal to a cold build's, on the
#      single-file and the multi-file path.
#  12. generic reuse: in a program with traits, generic fns, and
#      closures, a body edit rechecks only what it touched (template
#      checks and discovery counters), check and build requests
#      alternate, and every answer equals a cold one-shot build,
#      including panic lines and columns after edits that only move
#      text (comment lines above a closure, spaces inside a body).
#      Item edits outside the trait system (a new fn, a bound added to
#      a generic fn) keep the other templates' checks, and a bound the
#      caller cannot meet rejects warm exactly as cold.
#  13. moved instance Adt ids: an edit that makes a new generic Adt
#      instance first in discovery moves the ids (and C names) of the
#      others; a warm build must rebuild the glue unit and every unit
#      whose names moved, and print what a cold build prints.
#  14. a new fn unit with no C: a 16-slot program gains an unused
#      generic fn, whose template slot starts a unit of its own; the
#      warm build must still link (every base unit needs an object).
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
    # The changed fn (compute) always rechecks: its body is checked
    # against its own signature, which no recorded read set covers
    # (fuzz seed 42, iter 1034). Bodies that only mention it reuse.
    check("dirty walk reuses clean bodies, changed fn rechecks",
          (st.get("reused") or 0) >= 1 and st.get("rechecked") == 1, str(st))
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


def parse_stats(stderr):
    st = {}
    for line in stderr.splitlines():
        if line.startswith("lust-stats:"):
            for kv in line.split(":", 1)[1].split():
                k, _, v = kv.partition("=")
                st[k] = int(v) if v.isdigit() else v
    return st


def case_multi_incremental():
    # 7. Resolver-path incremental (W-DRIVER phase 2): a multi-file
    # crate in one daemon session. A body edit in one file rechecks
    # one body; a type edit rechecks only the bodies that read the
    # type (dirty walk in full mode); an import edit that changes a
    # binding rechecks its readers; a new file adds one body.
    work = tempfile.mkdtemp(prefix="lust-driver-multi-")
    d = Daemon(work)
    main_rs = os.path.join(work, "main.rs")
    a_rs = os.path.join(work, "a.rs")
    b_rs = os.path.join(work, "b.rs")
    out = os.path.join(work, "x")
    open(main_rs, "w").write(
        "mod a;\nmod b;\n\nuse crate::a::value as av;\n\n"
        "fn main() {\n    let p = a::Point { x: av(), y: b::value() };\n"
        "    println!(\"{}\", p.sum() + b::other());\n}\n")
    open(a_rs, "w").write(
        "pub struct Point {\n    pub x: i64,\n    pub y: i64,\n}\n\n"
        "impl Point {\n    pub fn sum(&self) -> i64 {\n        self.x + self.y\n    }\n}\n\n"
        "pub fn value() -> i64 {\n    3\n}\n")
    open(b_rs, "w").write(
        "pub fn value() -> i64 {\n    4\n}\n\npub fn other() -> i64 {\n    10\n}\n")
    d.start()
    _, prog = d.build(main_rs, out)
    check("multi cold output", prog.stdout.strip() == "17", prog.stdout)

    def edit(path, old, new):
        text = open(path).read()
        assert old in text, f"edit not found in {path}: {old!r}"
        open(path, "w").write(text.replace(old, new, 1))

    # Body edit in one file: one body rechecks, output tracks it.
    edit(b_rs, "    4\n", "    5\n")
    st = parse_stats(d.run(["check", main_rs]).stderr)
    check("multi body edit rechecks one body", st.get("mode") == "bodies" and st.get("rechecked") == 1, str(st))
    _, prog = d.build(main_rs, out)
    check("multi body edit output", prog.stdout.strip() == "18", prog.stdout)

    # Type edit (field order swap in a.rs): full mode, but the dirty
    # walk reuses the bodies that never read Point's layout (both
    # b.rs bodies); a.rs's method and main (the literal) recheck.
    edit(a_rs, "    pub x: i64,\n    pub y: i64,", "    pub y: i64,\n    pub x: i64,")
    st = parse_stats(d.run(["check", main_rs]).stderr)
    check("multi type edit is full mode with reuse",
          st.get("mode") == "full" and (st.get("reused") or 0) >= 2 and (st.get("rechecked") or 99) <= 3, str(st))
    _, prog = d.build(main_rs, out)
    check("multi type edit output", prog.stdout.strip() == "18", prog.stdout)

    # Import edit: point the alias at the other module's fn. The
    # binding main read changes, so main rechecks and output moves.
    edit(main_rs, "use crate::a::value as av;", "use crate::b::value as av;")
    st = parse_stats(d.run(["check", main_rs]).stderr)
    check("multi import edit rechecks its reader", (st.get("rechecked") or 0) >= 1, str(st))
    _, prog = d.build(main_rs, out)
    check("multi import edit output", prog.stdout.strip() == "20", prog.stdout)

    # New file: one new body checks, the rest of the crate stands.
    open(os.path.join(work, "c.rs"), "w").write("pub fn extra() -> i64 {\n    1\n}\n")
    edit(main_rs, "p.sum() + b::other()", "p.sum() + b::other() + c::extra()")
    edit(main_rs, "mod a;", "mod c;\nmod a;")
    st = parse_stats(d.run(["check", main_rs]).stderr)
    check("multi new file rechecks only new and edited bodies",
          (st.get("rechecked") or 99) <= 2, str(st))
    _, prog = d.build(main_rs, out)
    check("multi new file output", prog.stdout.strip() == "21", prog.stdout)
    d.kill()


def case_compaction_reemit():
    # 8. Slot compaction re-emits C from cached IR (section 4.2):
    # delete most fns and edit a type in the same step (full mode,
    # dead slots past the compaction threshold). Survivors renumber;
    # their C re-emits from cached IR instead of rechecking, and the
    # program still prints the right answer.
    work = tempfile.mkdtemp(prefix="lust-driver-compact-")
    d = Daemon(work)
    src = os.path.join(work, "x.rs")
    out = os.path.join(work, "x")
    fillers = [f"fn filler{i}() -> i64 {{ {i} }}" for i in range(100)]
    head = "struct S { x: i64 }\nfn keep(a: i64) -> i64 { a + 1 }\n"
    main = 'fn main() { let s = S { x: 40 }; println!("{}", keep(s.x) + keep(1)); }\n'
    # Fillers first, so the survivors' slots actually move when the
    # dead fillers compact away.
    open(src, "w").write("\n".join(fillers) + "\n" + head + main)
    d.start()
    _, prog = d.build(src, out)
    check("compaction cold output", prog.stdout.strip() == "43", prog.stdout)
    # Full-mode edit: type change plus deleting 95 of 100 fillers.
    keep = "\n".join(fillers[:5])
    open(src, "w").write("struct S { x: i64, y: i64 }\nfn keep(a: i64) -> i64 { a + 1 }\n" + keep + "\n" +
                         'fn main() { let s = S { x: 40, y: 1 }; println!("{}", keep(s.x) + keep(1) + s.y); }\n')
    st = parse_stats(d.run(["check", src]).stderr)
    check("compaction edit is full mode", st.get("mode") == "full", str(st))
    st, prog = d.build(src, out)
    check("compaction re-emits from cached IR", (st.get("reemitted") or 0) >= 1, str(st))
    check("compaction output", prog.stdout.strip() == "44", prog.stdout)
    d.kill()


def case_restart_add_file():
    # 9. Restart with a file added in the middle (W-DRIVER phase 4):
    # the def order persists to disk, so a restarted daemon numbers
    # Adts and statics as the old daemon did. The new file's defs
    # append; old units keep valid indices and hit the disk cache.
    work = tempfile.mkdtemp(prefix="lust-driver-restart-add-")
    d = Daemon(work)
    main_rs = os.path.join(work, "main.rs")
    out = os.path.join(work, "x")
    open(main_rs, "w").write(
        "mod a;\nmod z;\n\nfn main() {\n    println!(\"{}\", a::get() + z::get());\n}\n")
    open(os.path.join(work, "a.rs"), "w").write(
        "pub struct Alpha {\n    pub x: i64,\n    pub y: i64,\n}\n\n"
        "pub static ABASE: i64 = 100;\n\n"
        "pub fn get() -> i64 {\n    let a = Alpha { x: 1, y: 2 };\n    a.x * 10 + a.y + ABASE\n}\n")
    open(os.path.join(work, "z.rs"), "w").write(
        "pub struct Zed {\n    pub x: i64,\n    pub y: i64,\n}\n\n"
        "pub static ZBASE: i64 = 1000;\n\n"
        "pub fn get() -> i64 {\n    let z = Zed { x: 3, y: 4 };\n    z.x * 10 + z.y + ZBASE\n}\n")
    d.start()
    _, prog = d.build(main_rs, out)
    check("restart-add cold output", prog.stdout.strip() == "1146", prog.stdout)
    d.kill()

    def_order_files = glob.glob(os.path.join(work, "cache", "**", "defs-*.bin"), recursive=True)
    check("def order persisted to disk", len(def_order_files) == 1, str(def_order_files))

    # New file in the middle of the mod list, with new Adts and a
    # static, then a fresh daemon on the same cache dir.
    open(os.path.join(work, "m.rs"), "w").write(
        "pub struct Mid1 {\n    pub x: i64,\n    pub y: i64,\n}\n\n"
        "pub struct Mid2 {\n    pub x: i64,\n    pub y: i64,\n}\n\n"
        "pub struct Mid3 {\n    pub x: i64,\n    pub y: i64,\n}\n\n"
        "pub static MBASE: i64 = 7;\n\n"
        "pub fn get() -> i64 {\n    let a = Mid1 { x: 0, y: 0 };\n    let b = Mid2 { x: 5, y: 6 };\n"
        "    let c = Mid3 { x: 0, y: 0 };\n    a.x + b.x * 10 + b.y + c.y + MBASE\n}\n")
    text = open(main_rs).read()
    open(main_rs, "w").write(text.replace("mod a;\nmod z;", "mod a;\nmod m;\nmod z;")
                             .replace("a::get() + z::get()", "a::get() + m::get() + z::get()"))
    d.start()
    st, prog = d.build(main_rs, out)
    check("restart-add output after restart", prog.stdout.strip() == "1209", prog.stdout)
    check("restart-add old units hit the disk cache", (st.get("unit_cache_hits") or 0) >= 1, str(st))
    d.kill()

    # A corrupted def-order file falls back to fresh numbering:
    # output stays exact (only hits may drop).
    for path in glob.glob(os.path.join(work, "cache", "**", "defs-*.bin"), recursive=True):
        open(path, "wb").write(b"garbage, not a def order")
    d.start()
    _, prog = d.build(main_rs, out)
    check("corrupt def order falls back, output exact", prog.stdout.strip() == "1209", prog.stdout)
    d.kill()


def case_empty_units_restart():
    # 10. 40 generic fns first in the file: at 16 slots per unit, the
    # first two fn units hold only template slots (no C content).
    work = tempfile.mkdtemp(prefix="lust-driver-empty-units-")
    d = Daemon(work)
    src = os.path.join(work, "x.rs")
    fns = [f"fn g{i}<T: Copy>(t: T) -> T {{ t }}" for i in range(40)]
    main = 'fn main() { println!("{}", ' + " + ".join(f"g{i}({i}i64)" for i in range(40)) + "); }"
    open(src, "w").write("\n".join(fns + [main]) + "\n")
    out = os.path.join(work, "x")
    d.start()
    _, prog = d.build(src, out)
    check("empty units cold output", prog.stdout.strip() == "780", prog.stdout)
    d.kill()
    d.start()
    r = d.run(["build", src, "-o", out], expect=None)
    check("empty units restart build", r.returncode == 0, r.stderr[-300:])
    prog = subprocess.run([out], capture_output=True, text=True)
    check("empty units restart output", prog.stdout.strip() == "780", prog.stdout)
    d.kill()


def case_positions():
    # 11. Body hashes cover each fn's own text, not only its tokens.
    work = tempfile.mkdtemp(prefix="lust-driver-positions-")
    d = Daemon(work)
    main_rs = os.path.join(work, "main.rs")
    a_rs = os.path.join(work, "a.rs")
    single = os.path.join(work, "x.rs")
    out = os.path.join(work, "x")
    open(single, "w").write("fn other() -> u8 {\n    250\n}\n\nfn main() {\n    let a = other();\n    let r = a + 9;\n    println!(\"{}\", r);\n}\n")
    open(main_rs, "w").write("mod a;\nfn main() {\n    println!(\"{}\", a::f(250));\n}\n")
    open(a_rs, "w").write("pub fn f(a: u8) -> u8 {\n    let r = a + 9;\n    r\n}\n")

    def edit(path, old, new):
        text = open(path).read()
        assert old in text, old
        open(path, "w").write(text.replace(old, new, 1))

    def cold(src):
        env = dict(d.env, LUST_NO_DAEMON="1", LUST_CACHE_DIR=os.path.join(work, f"cold{len(os.listdir(work))}"))
        cout = os.path.join(work, "xc")
        subprocess.run([LUST, "build", src, "-o", cout], cwd=work, env=env, capture_output=True)
        return subprocess.run([cout], capture_output=True, text=True).stderr

    d.start()
    for src, path, old, new in [(single, single, "    let r = a + 9;", "    let r =     a + 9;"),
                                (single, single, "fn other() -> u8 {", "// one\n\nfn other() -> u8 {"),
                                (main_rs, a_rs, "    let r = a + 9;", "    let r =   a + 9;")]:
        d.build(src, out)
        edit(path, old, new)
        _, prog = d.build(src, out)
        check(f"positions after {new.strip()!r}: warm panic equals cold", prog.stderr == cold(src), prog.stderr)
    d.kill()


def case_generic_reuse():
    # 12. Generic reuse (driver/gen_reuse.rs).
    work = tempfile.mkdtemp(prefix="lust-driver-generic-")
    d = Daemon(work)
    src = os.path.join(work, "x.rs")
    out = os.path.join(work, "x")
    text = (
        "trait Score {\n    fn score(&self) -> u8;\n    fn twice(&self) -> u8 {\n        self.score() * 2\n    }\n}\n\n"
        "struct A {\n    v: u8,\n}\n\nimpl Score for A {\n    fn score(&self) -> u8 {\n        self.v\n    }\n}\n\n"
        "fn total<T: Score>(xs: &[T]) -> u8 {\n    let mut s = 0;\n    for x in xs {\n        s += x.twice();\n    }\n    s\n}\n\n"
        "fn apply<F: Fn(u8) -> u8>(f: F, x: u8) -> u8 {\n    f(x)\n}\n\n"
        "fn other() -> u8 {\n    1\n}\n\n"
        "fn main() {\n    let xs = [A { v: 3 }, A { v: 4 }];\n    let t = total(&xs);\n    let k = 2;\n"
        "    let r = apply(|v| v + 240 + k, t + other());\n    println!(\"{} {}\", t, r);\n}\n")
    open(src, "w").write(text)

    def cold():
        env = dict(d.env, LUST_NO_DAEMON="1", LUST_CACHE_DIR=os.path.join(work, f"cold{len(os.listdir(work))}"))
        cout = os.path.join(work, "xc")
        subprocess.run([LUST, "build", src, "-o", cout], cwd=work, env=env, capture_output=True)
        r = subprocess.run([cout], capture_output=True, text=True)
        return r.returncode, r.stdout, r.stderr

    def edit(old, new):
        text = open(src).read()
        assert old in text, old
        open(src, "w").write(text.replace(old, new, 1))

    def same(name, st, prog):
        check(f"generic {name}: warm equals cold", (prog.returncode, prog.stdout, prog.stderr) == cold(),
              f"{prog.stdout}{prog.stderr} {st}")

    d.start()
    st, prog = d.build(src, out)
    same("cold build", st, prog)
    # A template body edit: one template check, no plain fn rechecked.
    edit("        s += x.twice();", "        s += x.twice() + 1;")
    r = d.run(["check", src])
    cst = {k: int(v) for k, _, v in (kv.partition("=") for kv in r.stderr.split("lust-stats:")[-1].split()) if v.isdigit()}
    check("generic template edit checks one template", cst.get("templates") == 1 and cst.get("discovered") == 0, str(cst))
    st, prog = d.build(src, out)
    same("template edit", st, prog)
    check("generic template edit rebuilds only its instances", (st.get("rechecked") or 99) <= 2, str(st))
    # Comment lines above `other` move the panic in main's closure down.
    edit("fn other() -> u8 {", "// one\n// two\nfn other() -> u8 {")
    st, prog = d.build(src, out)
    same("lines moved above a closure", st, prog)
    check("generic moved lines recheck nothing", st.get("rechecked") == 0, str(st))
    # Spaces inside the closure move the panic column.
    edit("|v| v + 240 + k", "|v|   v + 240 + k")
    st, prog = d.build(src, out)
    same("spaces inside a body", st, prog)
    # An item edit seen only by a check (full mode, caches cleared, no
    # generic fn instances made), then a body edit, then a build: the
    # instance slots of the trait default method must not come back
    # as passing with no C.
    edit("struct A {", "struct Unused {\n    n: u8,\n}\n\nstruct A {")
    d.run(["check", src])
    edit("    1\n}", "    2\n}")
    d.run(["check", src])
    st, prog = d.build(src, out)
    same("item edit, check, body edit, check, build", st, prog)

    def check_stats():
        r = d.run(["check", src], expect=None)
        line = r.stderr.split("lust-stats:")[-1].split("\n")[0]
        return r, {k: int(v) for k, _, v in (kv.partition("=") for kv in line.split()) if v.isdigit()}

    # A new fn: an item edit outside the trait system. No template
    # reads the new name, so every template check is reused.
    edit("fn other() -> u8 {", "fn added() -> u8 {\n    9\n}\n\nfn other() -> u8 {")
    _, cst = check_stats()
    check("generic new fn reuses template checks", cst.get("templates") == 0, str(cst))
    st, prog = d.build(src, out)
    same("new fn", st, prog)
    # A bound the caller meets, then one it cannot meet: the warm
    # answer must reject exactly as a cold check does (rule zero).
    edit("fn total<T: Score>(", "fn total<T: Score + Sized>(")
    st, prog = d.build(src, out)
    same("bound added, caller meets it", st, prog)
    edit("fn total<T: Score + Sized>(", "fn total<T: Score + Copy>(")
    r, _ = check_stats()
    env = dict(d.env, LUST_NO_DAEMON="1", LUST_CACHE_DIR=os.path.join(work, "cold-reject"))
    c = subprocess.run([LUST, "check", src], cwd=work, env=env, capture_output=True, text=True)
    strip = lambda t: "\n".join(l for l in t.splitlines() if not l.startswith("lust-stats:"))
    check("generic unmet bound rejects warm as cold", (r.returncode, strip(r.stderr)) == (c.returncode, strip(c.stderr)) and r.returncode != 0,
          f"warm {r.returncode} {r.stderr[-300:]} cold {c.returncode} {c.stderr[-300:]}")
    # A type error in a template body rejects warm as cold; fixing it is
    # a body edit again (the error kept the item state).
    edit("fn total<T: Score + Copy>(", "fn total<T: Score>(")
    d.run(["check", src], expect=None)
    edit("        s += x.twice() + 1;", "        s += x.twice() + true;")
    r, _ = check_stats()
    c = subprocess.run([LUST, "check", src], cwd=work, env=env, capture_output=True, text=True)
    check("generic template body error rejects warm as cold", (r.returncode, strip(r.stderr)) == (c.returncode, strip(c.stderr)) and r.returncode != 0,
          f"warm {r.returncode} {r.stderr[-300:]} cold {c.returncode} {c.stderr[-300:]}")
    edit("        s += x.twice() + true;", "        s += x.twice() + 1;")
    r, cst = check_stats()
    check("generic fix after a template error is a body edit", r.returncode == 0 and cst.get("rechecked", 99) <= 2, f"{r.returncode} {cst}")
    st, prog = d.build(src, out)
    same("fix after a template error", st, prog)
    d.kill()


def case_moved_instance_ids():
    # 13. W<u8> and W<u16> Debug glue is each shared by several units;
    # the edit adds W<u32> at the top of the first fn.
    work = tempfile.mkdtemp(prefix="lust-driver-moved-ids-")
    d = Daemon(work)
    src = os.path.join(work, "x.rs")
    out = os.path.join(work, "x")
    fns = ["#[derive(Debug, Clone)]\nstruct W<T> {\n    a: T,\n    b: u8,\n}\n",
           "fn f0() -> usize {\n    let w = W { a: 5u8, b: 6 };\n    format!(\"{:?}\", w).len()\n}\n"]
    fns += [f"fn f{i}() -> usize {{\n    let w = W {{ a: {i}u8, b: 9 }};\n    format!(\"{{:?}}\", w).len()\n}}\n" for i in range(1, 49)]
    fns += [f"fn f{i}() -> usize {{\n    let w = W {{ a: {i}u16, b: 3 }};\n    format!(\"{{:?}}\", w).len()\n}}\n" for i in range(49, 97)]
    main = ("fn main() {\n    let mut t = 0;\n" + "".join(f"    t += f{i}();\n" for i in range(97))
            + "    println!(\"{}\", t);\n    println!(\"{:?}\", W { a: 1u8, b: 2 });\n}\n")
    open(src, "w").write("\n".join(fns) + main)
    d.start()
    d.build(src, out)
    text = open(src).read()
    open(src, "w").write(text.replace("fn f0() -> usize {\n", "fn f0() -> usize {\n    let z = W { a: 70000u32, b: 1 };\n"
                                      "    let _ = format!(\"{:?}\", z);\n", 1))
    _, prog = d.build(src, out)
    env = dict(d.env, LUST_NO_DAEMON="1", LUST_CACHE_DIR=os.path.join(work, "cold"))
    subprocess.run([LUST, "build", src, "-o", out + "c"], cwd=work, env=env, capture_output=True)
    cold = subprocess.run([out + "c"], capture_output=True, text=True)
    check("moved instance ids: warm equals cold", prog.stdout == cold.stdout and prog.returncode == cold.returncode,
          f"warm {prog.stdout[-60:]!r} cold {cold.stdout[-60:]!r}")
    d.kill()


def case_new_empty_unit():
    # 14. 15 fns + main fill one 16-slot unit; the template is slot 17.
    work = tempfile.mkdtemp(prefix="lust-driver-empty-unit-")
    d = Daemon(work)
    src = os.path.join(work, "x.rs")
    out = os.path.join(work, "x")
    fns = [f"fn f{i}() -> i64 {{ {i} }}" for i in range(15)]
    main = 'fn main() { println!("{}", ' + " + ".join(f"f{i}()" for i in range(15)) + "); }"
    open(src, "w").write("\n".join(fns + [main]) + "\n")
    d.start()
    d.build(src, out)
    open(src, "a").write("fn g<T: Copy>(t: T) -> T {\n    t\n}\n")
    r = d.run(["build", src, "-o", out], expect=None)
    prog = subprocess.run([out], capture_output=True, text=True)
    check("new template-only unit links", r.returncode == 0 and prog.stdout.strip() == "105", r.stderr[-200:] + prog.stdout)
    d.kill()


def case_nested_items():
    # 15. A single file whose fns hold nested fns, edited in each parse
    # mode. Bodies and signatures mode parsed into the old Ast and kept
    # the replaced nested fn, so the program had one fn more than slots:
    # builds panicked (the daemon answered from a fresh session), and a
    # check never checked the new copy's body (warm false accept).
    work = tempfile.mkdtemp(prefix="lust-driver-nested-")
    d = Daemon(work)
    src = os.path.join(work, "x.rs")
    out = os.path.join(work, "x")
    base = ("fn a(x: i64) -> i64 {\n    fn na() -> i64 { 1 }\n    na() + x\n}\n\n"
            "fn b() -> i64 {\n    fn nb() -> i64 { 20 }\n    nb()\n}\n\n"
            "fn main() {\n    println!(\"{} {}\", a(0), b());\n}\n")
    d.start()
    # Checks only, first in the session: the nested body no longer fits
    # its signature (`b` prints it, which fits both), and cold rejects.
    printed = base.replace("    nb()\n}", "    println!(\"{}\", nb());\n    20\n}")
    open(src, "w").write(printed)
    d.run(["check", src])
    open(src, "w").write(printed.replace("fn nb() -> i64", "fn nb() -> bool"))
    c = d.run(["check", src], expect=None)
    check("nested items, nested signature only: rejects", c.returncode == 1, c.stderr[-200:])
    edits = [
        ("outer body", [("na() + x", "na() + x + 2")], "3 20"),
        ("nested body", [("{ 20 }", "{ 30 }")], "1 30"),
        ("outer signature", [("fn a(x: i64)", "fn a(x: i64, _y: i64)"), ("a(0)", "a(0, 0)")], "1 20"),
        ("later outer signature", [("fn b()", "fn b(_y: i64)"), (", b()", ", b(0)")], "1 20"),
    ]
    for name, subs, want in edits:
        text = base
        for old, new in subs:
            text = text.replace(old, new)
        for step, body, expect in ((f"{name}: base", base, "1 20"), (name, text, want)):
            open(src, "w").write(body)
            c = d.run(["check", src], expect=None)
            b = d.run(["build", src, "-o", out], expect=None)
            prog = subprocess.run([out], capture_output=True, text=True) if b.returncode == 0 else None
            got = prog.stdout.strip() if prog else b.stderr[-200:]
            check(f"nested items, {step}", c.returncode == 0 and got == expect, f"check {c.returncode}: {got!r}")
    err = d.kill()
    check("nested items: no warm panic", "panicked" not in err, err[-300:])


def case_moved_and_revived_slots():
    # 16. A nested fn's identity holds its `#nested{k}` stmt index.
    # (a) A removed fn's slot kept its body hash while marked passing
    # with no C, so the same fn put back was reused unchecked: a check
    # that cold rejects passed warm. (b) An item added to an earlier
    # body moves every later nested fn to a new slot while its parent's
    # text stays: the parent's reused C called the dead old slots, and
    # the warm binary crashed.
    work = tempfile.mkdtemp(prefix="lust-driver-moved-slots-")
    d = Daemon(work)
    src = os.path.join(work, "x.rs")
    out = os.path.join(work, "x")
    d.start()
    bad = "fn f() -> i64 {\n    fn g() -> bool { 5 }\n    1\n}\n\nfn main() {\n    println!(\"{}\", f());\n}\n"
    codes = []
    for text in (bad, bad.replace("    fn g() -> bool { 5 }\n", ""), bad):
        open(src, "w").write(text)
        codes.append(d.run(["check", src], expect=None).returncode)
    check("revived nested fn rechecks", codes == [1, 0, 1], str(codes))

    def tree(first):
        # The const routes the file through the resolver path.
        parts = []
        for name, k, nested in (("f0", 9, first), ("f1", 5, [2, 1]), ("f2", 5, [4, 4]), ("f3", 9, [8, 7])):
            lines = [f"fn {name}() -> i64 {{"] + [f"    fn {name}_g{j}() -> i64 {{ {v} }}" for j, v in enumerate(nested)]
            terms = [str(k)] + [f"{name}_g{j}()" for j in range(len(nested))]
            if name == "f1":
                lines.append("    const K: i64 = 6;")
                terms.append("K")
            parts.append("\n".join(lines + ["    " + " + ".join(terms), "}"]))
        return "\n\n".join(parts + ['fn main() {\n    println!("{}", f0() + f1() + f2() + f3());\n}']) + "\n"

    for name, text, want in (("moved nested slots: base", tree([]), "60"), ("moved nested slots", tree([7]), "67")):
        open(src, "w").write(text)
        r = d.run(["build", src, "-o", out], expect=None)
        prog = subprocess.run([out], capture_output=True, text=True) if r.returncode == 0 else None
        got = (prog.returncode, prog.stdout.strip()) if prog else r.stderr[-200:]
        check(name, got == (0, want), str(got))
    d.kill()


def main():
    if not os.path.exists(LUST):
        sys.exit(f"{LUST} not built; run cargo build --release first")
    case_slots_and_reuse()
    case_reads_reuse()
    case_graph_refresh_and_std()
    case_multi_incremental()
    case_compaction_reemit()
    case_restart_add_file()
    case_empty_units_restart()
    case_positions()
    case_generic_reuse()
    case_moved_instance_ids()
    case_new_empty_unit()
    case_nested_items()
    case_moved_and_revived_slots()
    print(f"test-driver: {'all passed' if not failures else str(len(failures)) + ' FAILED: ' + ', '.join(failures)}")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
