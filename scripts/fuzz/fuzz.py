#!/usr/bin/env python3
# Random-edit fuzzer: one long-lived daemon session vs a cold compile, same bytes.
#
# Equivalence rule (the gate). For every edited source, the daemon answer and the cold
# answer must match on:
#   - pass/fail (exit code zero or not),
#   - the first error code (first `error[L####]`), when both fail,
#   - the first error span (first `--> file:line:col`), when both fail,
#   - for `run`: program stdout, program exit status, and the first panic span
#     (`panicked at file:line:col`), when the program panics.
# A daemon crash, a daemon hang, or a cold-compile crash (exit 101, signal, hang) is a
# failure by itself. One exception: for `run`, a timeout on both sides means the
# edited program itself does not terminate, which is the same behavior both ways,
# not a compiler hang. A `check` timeout is always a compiler hang. `--strict`
# also requires the full stderr text to match.
#
# Usage:
#   fuzz.py run --edits 2000 --seed 7 --crate small|small2|small3|realish|multi|multi2|multi3 [--modules 40] [--strict]
#   fuzz.py replay --prev A.rs --cur B.rs
#   fuzz.py shrink --prev A.rs --cur B.rs --out DIR
# Exit status: 0 = clean, 1 = a failure was found, 2 = setup error.
import argparse, os, random, re, shutil, signal, subprocess, sys, tempfile, time
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LUST = os.path.join(ROOT, "target/release/lust")

SMALL_CRATE = '''#[derive(Debug, Clone, PartialEq)]
struct Point {
    x: i64,
    y: i64,
}

#[derive(Debug)]
enum Shape {
    Dot,
    Pair(i64, i64),
}

const fn seed_val() -> i64 {
    3
}

const SEED: i64 = seed_val();

static TABLE: [i64; 2] = [SEED, SEED + 1];

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
        Shape::Pair(a, b) => a * 10 + b,
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

fn label(n: i64) -> String {
    let mut s = String::from("n=");
    s.push_str(&n.to_string());
    s
}

fn pick(v: &Vec<i64>, i: usize) -> i64 {
    v[i]
}

fn hit(n: i64) -> i64 {
    match n {
        SEED => 1,
        _ => 0,
    }
}

fn main() {
    let mut pts: Vec<Point> = Vec::new();
    pts.push(Point { x: 1, y: 2 });
    pts.push(Point { x: 3, y: 4 });
    pts[0].bump(5);
    let t = total(&pts);
    let c = classify(Shape::Pair(2, 3));
    let nums = vec![10, 20, 30];
    println!("{} {} {} {} {} {} {:?} {}", label(t), c, pick(&nums, 1), pts.len(),
             TABLE[1], hit(3), pts[0].clone(), std::mem::size_of::<Point>());
}
'''

# small2: the small crate plus the newer features (a trait and its impl,
# Result, a closure, byte literals), so the same edit ops hit their
# invalidation edges. A separate crate kind on purpose: SMALL_CRATE,
# SNIPPETS, and the edit ops stay byte-identical, so old seeds on
# small/multi/realish keep the exact edit sequences they have always
# covered. Feature edits (make_feature_edit) run only for small2.
SMALL2_CRATE = '''#[derive(Debug, Clone, PartialEq)]
struct Point {
    x: i64,
    y: i64,
}

#[derive(Debug)]
enum Shape {
    Dot,
    Pair(i64, i64),
}

const fn seed_val() -> i64 {
    3
}

const SEED: i64 = seed_val();

static TABLE: [i64; 2] = [SEED, SEED + 1];

static BYTES: &[u8; 3] = b"abc";

impl Point {
    fn sum(&self) -> i64 {
        self.x + self.y
    }

    fn bump(&mut self, d: i64) {
        self.x += d;
        self.y += d * 2;
    }
}

trait Score {
    fn score(&self) -> i64;
}

impl Score for Point {
    fn score(&self) -> i64 {
        self.x * 10 + self.y
    }
}

fn classify(s: Shape) -> i64 {
    match s {
        Shape::Dot => 0,
        Shape::Pair(a, b) => a * 10 + b,
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

fn label(n: i64) -> String {
    let mut s = String::from("n=");
    s.push_str(&n.to_string());
    s
}

fn pick(v: &Vec<i64>, i: usize) -> i64 {
    v[i]
}

fn hit(n: i64) -> i64 {
    match n {
        SEED => 1,
        _ => 0,
    }
}

fn try_pick(v: &Vec<i64>, i: usize) -> Result<i64, String> {
    if i < v.len() {
        Ok(v[i])
    } else {
        Err(String::from("oob"))
    }
}

fn pick_or(v: &Vec<i64>, i: usize) -> Result<i64, String> {
    match try_pick(v, i) {
        Ok(x) => Ok(x + 1),
        Err(e) => Err(e),
    }
}

fn use_closure(n: i64) -> i64 {
    let add_seed = |x: i64| x + SEED;
    add_seed(n)
}

fn byte_sum() -> i64 {
    let c = b'z';
    BYTES[0] as i64 + c as i64
}

fn main() {
    let mut pts: Vec<Point> = Vec::new();
    pts.push(Point { x: 1, y: 2 });
    pts.push(Point { x: 3, y: 4 });
    pts[0].bump(5);
    let t = total(&pts);
    let c = classify(Shape::Pair(2, 3));
    let nums = vec![10, 20, 30];
    println!("{} {} {} {} {} {} {:?} {}", label(t), c, pick(&nums, 1), pts.len(),
             TABLE[1], hit(3), pts[0].clone(), std::mem::size_of::<Point>());
    println!("{} {:?} {} {}", pts[0].score(), pick_or(&nums, 0), use_closure(10), byte_sum());
}
'''

# small3: the small2 crate plus the shapes the fuzzers missed when the
# daemon bugs in them were found by hand: a trait brought in by `use`
# (removing the use must reject), nested fns in a body, a file inner
# attribute, lifetime-only signatures, a generic fn, and a dyn impl
# behind a live vtable. A separate crate kind, like small2: every older
# constant and edit op stays byte-identical, so old seeds keep their
# exact streams. Feature edits (make_feature3_edit) run only for small3,
# on their own RNG and cadence.
SMALL3_CRATE = "#![allow(dead_code)]\n" + SMALL2_CRATE.replace("fn main() {", '''mod mm {
    pub trait Go {
        fn go(&self) -> i64;
    }

    pub struct Wrap(pub i64);

    impl Go for Wrap {
        fn go(&self) -> i64 {
            self.0 + 1
        }
    }

    pub fn wv() -> i64 {
        7
    }
}

use mm::Go;

fn use_go() -> i64 {
    mm::Wrap(4).go()
}

fn gid<T>(x: T) -> T {
    x
}

fn idref(x: &i64) -> &i64 {
    x
}

fn uref(x: &'_ i64) -> &'_ i64 {
    x
}

fn sref() -> &'static str {
    "hi"
}

fn slabel(s: &str) -> &str {
    s
}

fn take_s(s: &str) -> usize {
    s.len()
}

trait Dv {
    fn dv(&self) -> i64;
}

impl Dv for Point {
    fn dv(&self) -> i64 {
        self.x * 3
    }
}

fn via_dyn(d: &dyn Dv) -> i64 {
    d.dv()
}

fn outer_nested() -> i64 {
    fn inn_a(x: i64) -> i64 {
        x + 5
    }
    fn inn_b(x: i64) -> i64 {
        inn_a(x) * 2
    }
    inn_b(10)
}

fn main() {''', 1).replace('    println!("{} {:?} {} {}", pts[0].score(), pick_or(&nums, 0), use_closure(10), byte_sum());',
                            '    println!("{} {:?} {} {}", pts[0].score(), pick_or(&nums, 0), use_closure(10), byte_sum());\n'
                            '    let n9 = 9;\n'
                            '    println!("{} {} {} {} {} {} {}", use_go(), gid(3i64), via_dyn(&pts[0]), outer_nested(), *idref(&n9) + *uref(&n9), slabel(sref()).len(), take_s(&label(3)));', 1)

SNIPPETS = ["/*", "*/", '"', "fn zz() {", "}", "#[derive(Debug)]\n", "\n\n", "pub ",
            "struct Qq {", "// note\n", "x", "123", "->", "impl Qq {", 'let q = "abc\n',
            "/* a\nb\nfn fake() {}\n*/\n", "#[derive(Clone)]\n\n", "fn", "(", "/*\n\n\n",
            'static S: &str = "a\nfn fake2() {}\nb";\n',
            # Cross-item value flows: const/static/derive items whose edits
            # must invalidate the bodies and glue that baked their values in.
            "const K9: i64 = 3;\n", "const K9: i64 = 4;\n", "static S9: i64 = 4;\n",
            "const fn cf9() -> i64 { 5 }\n", "const fn cf9() -> i64 { 6 }\n",
            "const K9: i64 = cf9();\n", "static S9: i64 = K9;\n",
            "#[derive(Debug, Clone, PartialEq)]\n", "#[derive(Copy, Clone)]\n",
            "const K9: usize = std::mem::size_of::<i64>();\n", "SEED", "seed_val()"]
ITEM_STARTS = ("fn ", "pub ", "struct ", "enum ", "impl ", "#[", "use ")
ERR_CODE = re.compile(r"error\[(L\d+)\]")
ERR_SPAN = re.compile(r"-->[^:\n]*:(\d+):(\d+)")
PANIC_SPAN = re.compile(r"panicked at [^:\n]*:(\d+):(\d+)")


def summarize(cmd, rc, stdout, stderr):
    """The parts of one answer the equivalence rule compares."""
    if cmd == "run":
        m = PANIC_SPAN.search(stderr)
        return (rc == 0, rc, stdout, (m.group(1), m.group(2)) if m else None)
    code = ERR_CODE.search(stderr)
    span = ERR_SPAN.search(stderr)
    return (rc == 0, code.group(1) if code else None,
            (span.group(1), span.group(2)) if span else None)


def crash_kind(cmd, rc):
    """None for a normal compiler answer, else a short reason."""
    if rc == "TIMEOUT":
        return "hang"
    if cmd == "check" and rc not in (0, 1, 2, 3):
        return f"crash rc={rc}"
    return None


class Harness:
    """One temp dir, one daemon, one crate file. `check(text, daemon)` writes and compiles.

    The daemon's fresh-session guard runs in the background, so guard lines
    can land after the client answer returns. `wait_guard_idle` restores the
    old synchronous-guard reading: it polls the daemon log's paired
    `guard-check: start/done` lines until every started check has been
    applied, and only then is `guard_count` exact for the edits so far."""

    keep_work = False

    def __init__(self, timeout):
        self.timeout = timeout
        # Incremental daemon-log counters (see _poll_log). The baselines are
        # reset at each daemon start, so checks left pending by a dead
        # daemon never block the new daemon's idle wait.
        self._log_off = 0
        self._log_partial = ""
        self._guard = 0
        self._gstart = 0
        self._gdone = 0
        self._gstart_base = 0
        self._gdone_base = 0
        self.work = tempfile.mkdtemp(prefix="lust-fuzz-")
        self.crate = os.path.join(self.work, "crate.rs")
        self.sock = os.path.join(self.work, "d.sock")
        # LUST_NO_CACHE keeps a one-shot fallback from answering out of the disk cache.
        # The cold side also gets LUST_NO_DAEMON so the client cannot autostart a daemon
        # at the dummy socket and turn the oracle into a second warm session.
        self.env = dict(os.environ, LUST_DAEMON_SOCKET=self.sock, LUST_NO_CACHE="1")
        self.cold = dict(os.environ, LUST_DAEMON_SOCKET=os.path.join(self.work, "none"),
                         LUST_NO_CACHE="1", LUST_NO_DAEMON="1")
        self.logpath = os.path.join(self.work, "daemon.log")
        self.log = open(self.logpath, "w")
        self.daemon = None
        self.start_daemon()

    def start_daemon(self):
        if os.path.exists(self.sock):
            os.unlink(self.sock)
        # Own session, so kill_daemon can take down the whole group: an
        # in-memory `run` forks the user program from the daemon, and a
        # non-terminating program must die with its daemon, not spin on
        # as an orphan.
        self.daemon = subprocess.Popen([LUST, "daemon"], cwd=self.work, env=self.env,
                                       stderr=self.log, start_new_session=True)
        # Any guard check the previous daemon left pending is dead with it.
        self._poll_log()
        self._gstart_base = self._gstart
        self._gdone_base = self._gdone
        t0 = time.time()
        while not os.path.exists(self.sock):
            if time.time() - t0 > 10 or self.daemon.poll() is not None:
                raise RuntimeError("daemon start failed")
            time.sleep(0.005)

    def kill_daemon(self):
        try:
            os.killpg(os.getpgid(self.daemon.pid), signal.SIGKILL)
        except Exception:
            try:
                self.daemon.kill()
            except Exception:
                pass
        try:
            self.daemon.wait(timeout=5)
        except Exception:
            pass

    def run_cmd(self, cmd, use_daemon):
        args = [LUST, cmd, self.crate]
        if cmd != "check":
            args += ["-o", os.path.join(self.work, "prog")]
        # Own session per request: on timeout the whole group dies, client
        # and the program it ran alike. Killing only the client used to
        # leave a non-terminating edited program spinning as an orphan.
        p = subprocess.Popen(args, cwd=self.work,
                             env=self.env if use_daemon else self.cold,
                             stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                             text=True, start_new_session=True)
        try:
            out, err = p.communicate(timeout=self.timeout)
            return (p.returncode, out, err)
        except subprocess.TimeoutExpired:
            try:
                os.killpg(os.getpgid(p.pid), signal.SIGKILL)
            except Exception:
                pass
            try:
                p.communicate(timeout=5)
            except Exception:
                pass
            return ("TIMEOUT", "", "")

    def write(self, text):
        with open(self.crate, "w") as f:
            f.write(text)

    def daemon_alive(self):
        return self.daemon.poll() is None

    def _poll_log(self):
        """Reads only the daemon log bytes new since the last poll and folds
        complete lines into the guard counters. O(new bytes) per call, so
        polling during a long run stays cheap."""
        self.log.flush()
        try:
            with open(self.logpath) as f:
                f.seek(self._log_off)
                data = f.read()
                self._log_off = f.tell()
        except OSError:
            return
        lines = (self._log_partial + data).split("\n")
        self._log_partial = lines.pop()
        for line in lines:
            if "guard:" in line:
                self._guard += 1
            if "guard-check: start " in line:
                self._gstart += 1
            if "guard-check: done " in line:
                self._gdone += 1

    def guard_count(self):
        self._poll_log()
        return self._guard

    def guard_pending(self):
        """Background guard checks started by the current daemon, not yet applied."""
        self._poll_log()
        return (self._gstart - self._gstart_base) - (self._gdone - self._gdone_base)

    def wait_guard_idle(self):
        """Waits until every background guard check has been applied (or the
        daemon dies, which the caller's liveness checks will report). After
        this returns, `guard_count` covers every answer given so far, so a
        background mismatch counts exactly like the old synchronous guard.
        A timeout raises, because a stuck check would skew every verdict."""
        deadline = time.time() + max(60.0, self.timeout * 6)
        while self.daemon_alive() and self.guard_pending() > 0:
            if time.time() > deadline:
                raise RuntimeError("background guard checks did not finish")
            time.sleep(0.005)

    def close(self):
        self.kill_daemon()
        self.log.close()
        if self.keep_work:
            print(f"kept work dir {self.work} (daemon log: {self.logpath})")
        else:
            shutil.rmtree(self.work, ignore_errors=True)


def compare(h, cmd, strict):
    """Runs cmd both ways on the current crate bytes. Returns (ok, why, da, cold).

    A `run` timeout on the daemon side is not yet a verdict: the edited
    program may simply not terminate. The cold side decides: a cold
    timeout too is a matching program hang (ok, why "program hang");
    a cold answer makes it a daemon hang. The caller restarts the
    daemon after any daemon-side run timeout, because the daemon may
    still be waiting on the program it forked for an in-memory run."""
    da = h.run_cmd(cmd, True)
    if not h.daemon_alive():
        return False, "daemon died", da, None
    ck = crash_kind(cmd, da[0])
    if ck and not (cmd == "run" and da[0] == "TIMEOUT"):
        return False, f"daemon {ck}", da, None
    co = h.run_cmd(cmd, False)
    if cmd == "run" and da[0] == "TIMEOUT":
        if co[0] == "TIMEOUT":
            return True, "program hang", da, co
        return False, "daemon hang", da, co
    ck = crash_kind(cmd, co[0])
    if ck:
        return False, f"cold {ck}", da, co
    if summarize(cmd, *da) != summarize(cmd, *co):
        return False, "mismatch", da, co
    if strict and da[2] != co[2]:
        return False, "strict stderr mismatch", da, co
    return True, "", da, co


def item_bounds(lines):
    return [i for i, l in enumerate(lines) if l.startswith(ITEM_STARTS)]


def make_edit(rng, text, snapshots):
    op = rng.choices(
        ["truncate", "restore", "grow_prefix", "insert_snippet", "delete_lines",
         "delete_bytes", "move_item", "insert_fn", "insert_item", "const_edit", "word_sub", "dup_lines",
         "join_line", "split_line", "swap_lines"],
        weights=[10, 10, 8, 14, 8, 6, 8, 6, 7, 8, 8, 5, 5, 5, 5])[0]
    lines = text.splitlines(keepends=True)
    if op == "truncate" and len(text) > 2:
        return text[:rng.randrange(1, len(text))], op
    if op == "restore":
        return rng.choice(snapshots), op
    if op == "grow_prefix":
        for s in snapshots:
            if s.startswith(text) and len(s) > len(text):
                return s[:rng.randrange(len(text), len(s) + 1)], op
        return text + "\nfn grown() -> i64 { 1 }\n", op
    if op == "insert_snippet":
        sn = rng.choice(SNIPPETS)
        if rng.random() < 0.5 and lines:
            i = rng.randrange(len(lines) + 1)
            lines.insert(i, sn if sn.endswith("\n") or rng.random() < .5 else sn + "\n")
            return "".join(lines), f"{op}:{sn[:12]!r}@line{i}"
        k = rng.randrange(len(text) + 1)
        return text[:k] + sn + text[k:], f"{op}:{sn[:12]!r}@byte{k}"
    if op == "delete_lines" and lines:
        i = rng.randrange(len(lines))
        del lines[i:min(len(lines), i + rng.randint(1, 20))]
        return "".join(lines), op
    if op == "delete_bytes" and len(text) > 10:
        k = rng.randrange(len(text))
        return text[:k] + text[min(len(text), k + rng.randint(1, 200)):], op
    if op == "move_item":
        b = item_bounds(lines)
        if len(b) >= 3:
            i = rng.randrange(len(b) - 1)
            block = lines[b[i]:b[i + 1]]
            rest = lines[:b[i]] + lines[b[i + 1]:]
            at = rng.choice(item_bounds(rest) or [0])
            rest[at:at] = block
            return "".join(rest), op
        return text, op
    if op == "insert_fn":
        b = item_bounds(lines)
        i = rng.choice(b) if b else 0
        n = rng.randint(0, 10**6)
        lines.insert(i, f"fn added_{n}() -> i64 {{ {n % 97} }}\n")
        return "".join(lines), op
    if op == "insert_item":
        # Whole items that carry values across items: a const fn feeding a
        # const feeding a static, or a derived struct. Later edits (word
        # subs, moves, restores) then mutate one side of those edges.
        b = item_bounds(lines)
        i = rng.choice(b) if b else 0
        n = rng.randint(0, 10**6)
        item = rng.choice([
            f"const fn cf{n}() -> i64 {{ {n % 53} }}\nconst C{n}: i64 = cf{n}();\nstatic T{n}: i64 = C{n};\n",
            f"const C{n}: i64 = {n % 89};\nstatic T{n}: [i64; 2] = [C{n}, C{n} + 1];\n",
            f"#[derive(Debug, Clone, PartialEq)]\nstruct D{n} {{\n    a: i64,\n    b: bool,\n}}\n",
            f"const C{n}: usize = std::mem::size_of::<i64>();\n",
        ])
        lines.insert(i, item)
        return "".join(lines), op
    if op == "const_edit":
        # Bump one integer that feeds const evaluation: a const or static
        # initializer literal, or a const fn's one-line body literal. The
        # value flows into other items (patterns, lengths, statics), so
        # the run loops run-compare right after this op, not only every
        # 25 edits: a stale baked value passes `check` and only a run
        # shows it.
        pats = [r"\bconst\s+(?:fn\s+\w+\s*\([^)]*\)\s*->\s*\w+\s*\{|[A-Za-z_][\w]*\s*:[^=;]+=\s*)\s*(-?\d+)",
                r"\bstatic\s+[A-Za-z_][\w]*\s*:[^=;]+=\s*(-?\d+)"]
        hits = []
        for pat in pats:
            hits += [(m.start(1), m.end(1)) for m in re.finditer(pat, text)]
        if hits:
            s, e = rng.choice(hits)
            return text[:s] + str(int(text[s:e]) + rng.choice([1, 1, 7, -1])) + text[e:], op
        return text, op
    if op == "word_sub":
        pairs = [("10", "2"), ("100", "7"), ("i64", "i32"), ("true", "false"), ("+", "-"),
                 ("x: i64", "x: bool"), ("y: i64", "y: u8"), ("SEED", "3"),
                 ("derive(Debug)", "derive(Debug, Clone)"), ("= seed_val()", "= 3")]
        rng.shuffle(pairs)
        for a, bb in pairs:
            idxs = [i for i in range(len(text)) if text.startswith(a, i)]
            if idxs:
                k = rng.choice(idxs)
                return text[:k] + bb + text[k + len(a):], op
        return text, op
    if op == "dup_lines" and lines:
        i = rng.randrange(len(lines))
        j = min(len(lines), i + rng.randint(1, 10))
        lines[j:j] = lines[i:j]
        return "".join(lines), op
    if op == "join_line":
        idxs = [i for i, c in enumerate(text) if c == "\n"]
        if idxs:
            k = rng.choice(idxs)
            return text[:k] + text[k + 1:], op
        return text, op
    if op == "split_line" and text:
        k = rng.randrange(len(text))
        return text[:k] + "\n" + text[k:], op
    if op == "swap_lines" and len(lines) > 2:
        i, j = rng.randrange(len(lines)), rng.randrange(len(lines))
        lines[i], lines[j] = lines[j], lines[i]
        return "".join(lines), op
    return text, op


def drop_block(text, head):
    """Deletes the brace block that starts at `head` (naive brace count;
    the generated items have no braces in strings). None if absent."""
    i = text.find(head)
    if i < 0:
        return None
    j = text.find("{", i)
    if j < 0:
        return None
    depth = 0
    for k in range(j, len(text)):
        depth += (text[k] == "{") - (text[k] == "}")
        if depth == 0:
            return text[:i] + text[k + 1:]
    return None


def make_feature_edit(rng, text):
    """Edits that aim at the newer features (small2 only, on its own RNG
    and a fixed cadence, so the main edit stream is untouched): trait
    impls added, duplicated (coherence must reject), and removed;
    closures; Result and `?` (`?` is rejected today, so both sides must
    agree on the reject, and the case turns into an accept test the day
    `?` lands); byte literals; derive list cycles; Result signature
    flips (the own-signature reuse class)."""
    op = rng.choice(["feat_trait_impl", "feat_dup_impl", "feat_impl_toggle",
                     "feat_closure", "feat_result_q", "feat_bytes",
                     "feat_derive", "feat_result_sig"])
    lines = text.splitlines(keepends=True)
    b = item_bounds(lines)
    at = rng.choice(b) if b else 0
    n = rng.randint(0, 10**6)
    if op == "feat_trait_impl":
        lines.insert(at, f"trait Tr{n} {{\n    fn tr_val(&self) -> i64;\n}}\n"
                         f"impl Tr{n} for Point {{\n    fn tr_val(&self) -> i64 {{\n"
                         f"        self.x + {n % 7}\n    }}\n}}\n"
                         f"fn use_tr{n}(p: &Point) -> i64 {{\n    p.tr_val()\n}}\n")
        return "".join(lines), op
    if op == "feat_dup_impl":
        lines.insert(at, "impl Score for Point {\n    fn score(&self) -> i64 {\n        0\n    }\n}\n")
        return "".join(lines), op
    if op == "feat_impl_toggle":
        cut = drop_block(text, "impl Score for Point")
        if cut is not None:
            return cut, op
        lines.insert(at, "impl Score for Point {\n    fn score(&self) -> i64 {\n"
                         "        self.x * 10 + self.y\n    }\n}\n")
        return "".join(lines), op
    if op == "feat_closure":
        item = rng.choice([
            f"fn clo{n}(v: i64) -> i64 {{\n    let f = |x: i64| x * 2 + {n % 5};\n    f(v)\n}}\n",
            f"fn clo{n}(v: i64) -> i64 {{\n    let k = {n % 9};\n    let f = |x: i64| x + k;\n    f(v)\n}}\n",
        ])
        lines.insert(at, item)
        return "".join(lines), op
    if op == "feat_result_q":
        lines.insert(at, f"fn try{n}(v: i64) -> Result<i64, i64> {{\n"
                         f"    if v < 0 {{ Err(v) }} else {{ Ok(v + {n % 3}) }}\n}}\n"
                         f"fn try{n}_up(v: i64) -> Result<i64, i64> {{\n"
                         f"    let x = try{n}(v)?;\n    Ok(x * 2)\n}}\n")
        return "".join(lines), op
    if op == "feat_bytes":
        lines.insert(at, f'const BS{n}: &[u8; 2] = b"hi";\n'
                         f"fn bc{n}() -> i64 {{\n    BS{n}[1] as i64 + b'a' as i64\n}}\n")
        return "".join(lines), op
    if op == "feat_derive":
        cycle = ["Debug, Clone, PartialEq", "Debug, Clone", "Debug",
                 "Debug, Copy, Clone, PartialEq"]
        m = re.search(r"#\[derive\(([^)]*)\)\]\nstruct Point", text)
        if m and m.group(1) in cycle:
            nxt = cycle[(cycle.index(m.group(1)) + 1) % len(cycle)]
            return text[:m.start(1)] + nxt + text[m.end(1):], op
        return text, op
    if op == "feat_result_sig":
        hits = [(m.start(), m.group(0)) for m in
                re.finditer(r"Result<i64, (?:String|i64)>", text)]
        if hits:
            k, cur = rng.choice(hits)
            nxt = "Result<i64, i64>" if cur.endswith("String>") else "Result<i64, String>"
            return text[:k] + nxt + text[k + len(cur):], op
        return text, op
    return text, op


def make_feature3_edit(rng, text):
    """Edits for the classes no fuzzer reached before (small3 only, own
    RNG and cadence, run-compare after each): `use` add/remove/rename
    for a trait and for an item, nested items in fn bodies added,
    removed, and added back, file inner attributes, lifetime-only
    signature edits (elided, '_ and 'static forms only), an early
    generic instance (its Adt ids shift the later ones), dyn impl
    add/remove/body edits behind the live `via_dyn` vtable, and
    visibility flips inside the module. Some results are invalid Rust
    on purpose; both sides must reject the same way."""
    op = rng.choice(["feat3_use_trait", "feat3_use_item", "feat3_nested",
                     "feat3_inner_attr", "feat3_lifetime", "feat3_early_inst",
                     "feat3_dyn", "feat3_vis"])
    n = rng.randint(0, 10**6)
    if op == "feat3_use_trait":
        if "use mm::Go;\n" in text:
            return text.replace("use mm::Go;\n",
                                rng.choice(["", "use mm::Go as GoAlias;\n"]), 1), op
        if "use mm::Go as GoAlias;\n" in text:
            return text.replace("use mm::Go as GoAlias;\n", "use mm::Go;\n", 1), op
        return text.replace("mod mm {", "use mm::Go;\n\nmod mm {", 1) if "mod mm {" in text else text, op
    if op == "feat3_use_item":
        for form in ("use mm::Wrap;\n", "use mm::*;\n", "use mm::wv;\n"):
            if form in text:
                return text.replace(form, "", 1), op
        lines = text.splitlines(keepends=True)
        b = item_bounds(lines)
        lines.insert(rng.choice(b) if b else 0,
                     rng.choice(["use mm::Wrap;\n", "use mm::*;\n", "use mm::wv;\n"]))
        return "".join(lines), op
    if op == "feat3_nested":
        cut = None
        for head in ("    fn inn_b(x: i64) -> i64 {", "    fn inn_a(x: i64) -> i64 {"):
            cut = drop_block(text, head)
            if cut is not None:
                break
        if cut is not None and rng.random() < 0.5:
            return cut, op
        # Insert a nested fn at the start of one body. Every later nested
        # fn moves to a new slot, and a body that had none gains one.
        hosts = [m.end() for m in re.finditer(r"fn (?:outer_nested|use_closure|byte_sum|hit)\([^)]*\)[^{]*\{\n", text)]
        if hosts:
            k = rng.choice(hosts)
            return text[:k] + f"    fn nest{n}(x: i64) -> i64 {{\n        x + {n % 11}\n    }}\n" \
                   + f"    let _nv{n} = nest{n}(1);\n" + text[k:], op
        return text, op
    if op == "feat3_inner_attr":
        lines = text.splitlines(keepends=True)
        if lines and lines[0].startswith("#!"):
            if rng.random() < 0.5:
                return "".join(lines[1:]), op
            lines[0] = lines[0].replace("dead_code", "unused") \
                if "dead_code" in lines[0] else lines[0].replace("unused", "dead_code")
            return "".join(lines), op
        return rng.choice(["#![allow(dead_code)]\n", "//! crate doc\n"]) + text, op
    if op == "feat3_lifetime":
        pairs = [("fn idref(x: &i64) -> &i64", "fn idref(x: &'_ i64) -> &'_ i64"),
                 ("fn sref() -> &'static str", "fn sref() -> &str"),
                 ("fn slabel(s: &str) -> &str", "fn slabel(s: &str) -> &'static str"),
                 ("fn uref(x: &'_ i64) -> &'_ i64", "fn uref(x: &i64) -> &i64"),
                 # Param-side 'static: the callee still checks, so only a
                 # caller recheck (borrowck against the new region sig)
                 # can reject; a stale caller verdict is a false accept.
                 ("fn take_s(s: &str) -> usize", "fn take_s(s: &'static str) -> usize")]
        rng.shuffle(pairs)
        for a, b in pairs:
            if a in text:
                return text.replace(a, b, 1), op
            if b in text:
                return text.replace(b, a, 1), op
        return text, op
    if op == "feat3_early_inst":
        # A caller near the top of the file names a new gid instance
        # before every existing one in discovery order; removing it
        # shifts them back.
        line = rng.choice(["fn early_inst() -> bool { gid(true) }\n",
                           "fn early_inst() -> u8 { gid(3u8) }\n",
                           "fn early_inst() -> i32 { gid(-2i32) }\n"])
        m = re.search(r"fn early_inst\(\)[^\n]*\n", text)
        if m:
            return (text[:m.start()] + text[m.end():], op) if rng.random() < 0.5 \
                else (text[:m.start()] + line + text[m.end():], op)
        b = item_bounds(text.splitlines(keepends=True))
        lines = text.splitlines(keepends=True)
        lines.insert(b[0] if b else 0, line)
        return "".join(lines), op
    if op == "feat3_dyn":
        impl_shape = ("impl Dv for Shape {\n    fn dv(&self) -> i64 {\n"
                      "        match self {\n            Shape::Dot => 1,\n"
                      "            Shape::Pair(a, _) => *a,\n        }\n    }\n}\n")
        if "impl Dv for Shape" in text:
            cut = drop_block(text, "impl Dv for Shape")
            return (cut, op) if cut is not None else (text, op)
        if rng.random() < 0.5 and "self.x * 3" in text:
            # Body edit inside the impl behind the live vtable: `check`
            # still passes, only the run-compare sees a stale body.
            return text.replace("self.x * 3", "self.x * 4", 1), op
        if "self.x * 4" in text:
            return text.replace("self.x * 4", "self.x * 3", 1), op
        lines = text.splitlines(keepends=True)
        b = item_bounds(lines)
        lines.insert(rng.choice(b) if b else 0, impl_shape)
        return "".join(lines), op
    if op == "feat3_vis":
        pairs = [("pub trait Go", "trait Go"), ("pub struct Wrap", "struct Wrap"),
                 ("pub fn wv", "fn wv")]
        rng.shuffle(pairs)
        for a, b in pairs:
            if a in text:
                return text.replace(a, b, 1), op
            if b in text:
                return text.replace(b, a, 1), op
        return text, op
    return text, op


def crate_text(kind, modules):
    if kind == "small":
        return SMALL_CRATE
    if kind == "small2":
        return SMALL2_CRATE
    if kind == "small3":
        return SMALL3_CRATE
    if kind == "realish":
        make = os.path.join(ROOT, "bench/realish/make.py")
        return subprocess.run([sys.executable, make, str(modules)], capture_output=True,
                              text=True, check=True).stdout
    with open(kind) as f:
        return f.read()


def save_pair(out, tag, prev, cur):
    os.makedirs(out, exist_ok=True)
    for name, text in ((f"{tag}-prev.rs", prev), (f"{tag}-cur.rs", cur)):
        with open(os.path.join(out, name), "w") as f:
            f.write(text)


def cmd_run(a):
    if a.crate in ("multi", "multi2", "multi3"):
        return cmd_run_multi(a, rename=a.crate in ("multi2", "multi3"),
                             feat3=a.crate == "multi3")
    rng = random.Random(a.seed)
    # Feature edits draw from their own RNG so the main stream keeps
    # the sequence old seeds have always covered (see SMALL2_CRATE).
    frng = random.Random(a.seed ^ 0xFEA7)
    frng3 = random.Random(a.seed ^ 0x5EED3)
    original = crate_text(a.crate, a.modules)
    Harness.keep_work = a.keep_work
    h = Harness(a.timeout)
    failures = 0
    ops, bad_ops = Counter(), Counter()
    t0 = time.time()
    try:
        if a.record:
            os.makedirs(a.record, exist_ok=True)
            with open(os.path.join(a.record, "0000.rs"), "w") as f:
                f.write(original)
        h.write(original)
        ok, why, da, co = compare(h, "check", a.strict)
        if not ok:
            print(f"SEED-CRATE FAILURE ({why}) on the unedited crate", flush=True)
            return 1
        snapshots = [original]
        text = original
        seen_guard = 0
        for it in range(a.edits):
            prev = text
            if a.crate == "small2" and it % 13 == 7:
                text, op = make_feature_edit(frng, text)
            elif a.crate == "small3" and it % 11 == 5:
                text, op = make_feature3_edit(frng3, text)
            else:
                text, op = make_edit(rng, text, snapshots)
            ops[op.split(":")[0]] += 1
            if a.record:
                with open(os.path.join(a.record, f"{it + 1:04d}.rs"), "w") as f:
                    f.write(text)
            h.write(text)
            if not h.daemon_alive():
                failures += 1
                bad_ops["daemon died"] += 1
                save_pair(a.out, f"crash-{it}", prev, text)
                print(f"FAIL daemon dead before iter {it} op {op}", flush=True)
                h.start_daemon()
                text = original
                h.write(original)
                h.run_cmd("check", True)
                continue
            ok, why, da, co = compare(h, "check", a.strict)
            # The guard now runs behind the answer. Wait for it before
            # counting or editing again, so a mismatch is charged to this
            # edit (and the next edit never races the background check).
            h.wait_guard_idle()
            g = h.guard_count()
            if g > seen_guard:
                # The warm answer differed from a fresh session (found in the
                # background). Save the pair: it is a real incremental bug.
                save_pair(a.out, f"guard-{it}", prev, text)
                print(f"GUARD iter {it} op {op}: warm answer differed; pair guard-{it} saved",
                      flush=True)
                seen_guard = g
            if not ok:
                failures += 1
                bad_ops[why] += 1
                save_pair(a.out, f"bad-{it}", prev, text)
                print(f"FAIL[{why}] iter {it} op {op}\n"
                      f"  daemon={da[0]} {da[2][:200]!r}\n"
                      f"  cold  ={co[0] if co else '-'} {(co[2][:200] if co else '')!r}",
                      flush=True)
                print(f"  pair saved under {a.out}; shrink: fuzz.py shrink "
                      f"--prev {a.out}/bad-{it}-prev.rs --cur {a.out}/bad-{it}-cur.rs "
                      f"--out {a.out}", flush=True)
                if why in ("daemon hang", "daemon died"):
                    h.kill_daemon()
                    h.start_daemon()
                text = original
                h.write(original)
                h.run_cmd("check", True)
                if a.stop_first:
                    break
                continue
            if da[0] == 0 and len(snapshots) < 40 and rng.random() < 0.05:
                snapshots.append(text)
            # A const_edit can move a baked-in value while `check` still
            # passes; run-compare right after it, not only every 25 edits.
            # Feature edits get the same treatment: a derive or impl edit
            # can change which glue a body runs while `check` still passes.
            if (it % 25 == 24 or op == "const_edit" or op.startswith(("feat_", "feat3_"))) and da[0] == 0:
                ok, why, ra, rb = compare(h, "run", a.strict)
                if ok and why == "program hang":
                    # The edited program does not terminate on either side:
                    # same behavior, not a failure. The daemon may still be
                    # waiting on the copy it forked, so restart it; the next
                    # edit primes the fresh session.
                    print(f"note: program hang at iter {it} op {op} (both sides); daemon restarted",
                          flush=True)
                    h.kill_daemon()
                    h.start_daemon()
                if not ok:
                    failures += 1
                    bad_ops[f"run {why}"] += 1
                    save_pair(a.out, f"runbad-{it}", prev, text)
                    print(f"FAIL[run {why}] iter {it} op {op}\n"
                          f"  daemon={ra[0]} out={ra[1][:160]!r} err={ra[2][:160]!r}\n"
                          f"  cold  ={rb[0] if rb else '-'} out={(rb[1][:160] if rb else '')!r} "
                          f"err={(rb[2][:160] if rb else '')!r}", flush=True)
                    if why in ("daemon hang", "daemon died"):
                        h.kill_daemon()
                        h.start_daemon()
                        text = original
                        h.write(original)
                        h.run_cmd("check", True)
                    if a.stop_first:
                        break
            if (it + 1) % 250 == 0:
                print(f"... {it + 1}/{a.edits} failures={failures} "
                      f"{time.time() - t0:.0f}s", flush=True)
        h.wait_guard_idle()
        guard = h.guard_count()
        print(f"RESULT seed={a.seed} crate={a.crate} modules={a.modules} edits={a.edits} "
              f"failures={failures} guard_fired={guard} wall={time.time() - t0:.0f}s")
        print("ops:", dict(ops))
        print("bad:", dict(bad_ops))
        if a.fail_on_guard and guard > 0:
            print(f"FAIL fresh-session guard fired {guard} time(s)")
            failures += guard
        return 1 if failures else 0
    finally:
        h.close()


MULTI_SEED = {
    "main.rs": """mod a;
mod b;

use crate::a::Point;

const FROM_A: i64 = a::make(2);

static TALLY: i64 = FROM_A + a::K;

fn helper() -> i64 {
    100
}

fn hit(n: i64) -> i64 {
    match n {
        FROM_A => 1,
        _ => 0,
    }
}

fn main() {
    let p = Point { x: a::value(), y: b::value() };
    let q = Point { x: 3, y: 4 };
    println!("multi {} {} {} {} {} {}", p.sum(), a::inner::deep(), helper(),
             TALLY, hit(6), p == q);
}
""",
    "a.rs": """pub mod inner;

#[derive(Clone, PartialEq)]
pub struct Point {
    pub x: i64,
    pub y: i64,
}

impl Point {
    pub fn sum(&self) -> i64 {
        self.x + self.y
    }
}

pub const K: i64 = 3;

pub const fn make(x: i64) -> i64 {
    x * K
}

pub fn value() -> i64 {
    3
}
""",
    "a/inner.rs": """pub fn deep() -> i64 {
    super::value() + 10
}
""",
    "b/mod.rs": """pub fn value() -> i64 {
    4
}
""",
}


# multi2: the multi seed plus plain readers in the crate root of a.rs
# fields, tuple fields, a tuple constructor, and patterns, so visibility
# pulses reach every member privacy check. Plain multi keeps its seed.
MULTI2_SEED = dict(MULTI_SEED)
MULTI2_SEED["a.rs"] = MULTI_SEED["a.rs"] + """
pub struct Pair(pub i64, pub i64);

pub fn pair() -> Pair {
    Pair(1, 2)
}

pub fn origin() -> Point {
    Point { x: 0, y: 0 }
}
"""
MULTI2_SEED["main.rs"] = MULTI_SEED["main.rs"].replace("fn main() {", """fn reads() -> i64 {
    let o = a::origin();
    let a::Pair(l, _) = a::pair();
    let Point { y, .. } = a::origin();
    o.x + a::pair().1 + l + y + a::Pair(5, 6).0
}

fn main() {""", 1).replace('println!("multi {} {} {} {} {} {}", p.sum(),', 'println!("multi {} {} {} {} {} {} {}", reads(), p.sum(),', 1)

# multi3: the multi2 seed plus the same missed classes across files: a
# trait in a.rs brought in by `use` in main.rs, a generic fn, a dyn
# impl and vtable call, a lifetime-only signature, and file inner
# attributes. Feature edits (make_feature3_multi) run only for multi3.
MULTI3_SEED = dict(MULTI2_SEED)
MULTI3_SEED["a.rs"] = "#![allow(dead_code)]\n" + MULTI2_SEED["a.rs"] + """
pub trait TrA {
    fn ta(&self) -> i64;
}

impl TrA for Point {
    fn ta(&self) -> i64 {
        self.x - self.y
    }
}

pub trait DvA {
    fn dv(&self) -> i64;
}

impl DvA for Point {
    fn dv(&self) -> i64 {
        self.x * 3
    }
}

pub fn via_a(d: &dyn DvA) -> i64 {
    d.dv()
}

pub fn gid<T>(x: T) -> T {
    x
}

pub fn idref(x: &i64) -> &i64 {
    x
}

pub fn with_nested() -> i64 {
    fn inn_a(x: i64) -> i64 {
        x + 5
    }
    inn_a(10)
}
"""
MULTI3_SEED["main.rs"] = "#![allow(dead_code)]\n" + MULTI2_SEED["main.rs"].replace(
    "use crate::a::Point;\n", "use crate::a::Point;\nuse crate::a::TrA;\n", 1).replace(
    "    o.x + a::pair().1 + l + y + a::Pair(5, 6).0",
    "    o.x + a::pair().1 + l + y + a::Pair(5, 6).0 + o.ta() + a::via_a(&o) + a::gid(2i64) + *a::idref(&y) + a::with_nested()", 1)

# Visibility pulse sites: every written visibility, and the empty one in
# front of a private item at a line start.
VIS_PUB = re.compile(r"\bpub(?:\([^)\n]*\))?[ \t]+")
VIS_PRIVATE_ITEM = re.compile(r"^[ \t]*()(?=(?:const|static|fn|struct|enum|mod|use|trait|type)\b)", re.M)
VIS_FORMS = ["", "pub ", "pub(crate) ", "pub(super) ", "pub(self) ", "pub(in crate::a) "]


def vis_flip(rng, fs):
    """One visibility edit for the multi crates: a written visibility (on an
    item, field, tuple field, method, `mod`, or `use`) or a private item's
    empty one takes another form from VIS_FORMS. Returns (files, op), or
    (None, op) when the files have no site."""
    sites = []
    for rel in sorted(fs):
        sites += [(rel, m.start(), m.end()) for m in VIS_PUB.finditer(fs[rel])]
        sites += [(rel, m.start(1), m.end(1)) for m in VIS_PRIVATE_ITEM.finditer(fs[rel])]
    if not sites:
        return None, "vis_flip:none"
    rel, s, e = rng.choice(sites)
    old = fs[rel][s:e].strip()
    new = rng.choice([v for v in VIS_FORMS if v.strip() != old])
    out = dict(fs)
    out[rel] = fs[rel][:s] + new + fs[rel][e:]
    return out, f"vis_flip:{rel}:{old or 'private'}->{new.strip() or 'private'}"


def make_feature3_multi(rng, fs):
    """The make_feature3_edit classes across files (multi3 only).
    Returns (files, op). The visibility pulse in cmd_run_multi covers
    visibility flips for this crate too."""
    op = rng.choice(["feat3_use_trait", "feat3_use_item", "feat3_nested",
                     "feat3_inner_attr", "feat3_lifetime", "feat3_early_inst",
                     "feat3_dyn"])
    fs = dict(fs)
    main = fs.get("main.rs", "")
    atext = fs.get("a.rs", "")
    if op == "feat3_use_trait" and "main.rs" in fs:
        if "use crate::a::TrA;\n" in main:
            fs["main.rs"] = main.replace("use crate::a::TrA;\n",
                                         rng.choice(["", "use crate::a::TrA as TrAlias;\n"]), 1)
        elif "use crate::a::TrA as TrAlias;\n" in main:
            fs["main.rs"] = main.replace("use crate::a::TrA as TrAlias;\n", "use crate::a::TrA;\n", 1)
        elif "use crate::a::Point;\n" in main:
            fs["main.rs"] = main.replace("use crate::a::Point;\n",
                                         "use crate::a::Point;\nuse crate::a::TrA;\n", 1)
        return fs, op
    if op == "feat3_use_item" and "main.rs" in fs:
        for old, new in (("use crate::a::Point;\n", "use crate::a::Point as Pt;\n"),
                         ("use crate::a::*;\n", "")):
            if old in main:
                fs["main.rs"] = main.replace(old, new, 1)
                return fs, op
        if "use crate::a::Point as Pt;\n" in main:
            fs["main.rs"] = main.replace("use crate::a::Point as Pt;\n", "use crate::a::Point;\n", 1)
            return fs, op
        fs["main.rs"] = "use crate::a::*;\n" + main
        return fs, op
    if op == "feat3_nested" and "a.rs" in fs:
        cut = drop_block(atext, "    fn inn_a(x: i64) -> i64 {")
        if cut is not None and rng.random() < 0.5:
            fs["a.rs"] = cut
            return fs, op
        n = rng.randint(0, 10**6)
        host = "pub fn with_nested() -> i64 {\n"
        if host in atext:
            fs["a.rs"] = atext.replace(host, host
                                       + f"    fn nest{n}(x: i64) -> i64 {{\n        x + {n % 11}\n    }}\n"
                                       + f"    let _nv{n} = nest{n}(1);\n", 1)
        return fs, op
    if op == "feat3_inner_attr":
        rel = rng.choice([r for r in ("main.rs", "a.rs") if r in fs] or ["main.rs"])
        lines = fs.get(rel, "").splitlines(keepends=True)
        if lines and lines[0].startswith("#!"):
            fs[rel] = "".join(lines[1:]) if rng.random() < 0.5 else \
                fs[rel].replace("dead_code", "unused", 1) if "dead_code" in lines[0] \
                else fs[rel].replace("unused", "dead_code", 1)
        elif rel in fs:
            fs[rel] = "#![allow(dead_code)]\n" + fs[rel]
        return fs, op
    if op == "feat3_lifetime" and "a.rs" in fs:
        a, b = "pub fn idref(x: &i64) -> &i64", "pub fn idref(x: &'_ i64) -> &'_ i64"
        if a in atext:
            fs["a.rs"] = atext.replace(a, b, 1)
        elif b in atext:
            fs["a.rs"] = atext.replace(b, a, 1)
        return fs, op
    if op == "feat3_early_inst" and "main.rs" in fs:
        line = rng.choice(["fn early_inst() -> bool { a::gid(true) }\n",
                           "fn early_inst() -> u8 { a::gid(3u8) }\n"])
        m = re.search(r"fn early_inst\(\)[^\n]*\n", main)
        if m:
            fs["main.rs"] = (main[:m.start()] + main[m.end():]) if rng.random() < 0.5 \
                else (main[:m.start()] + line + main[m.end():])
        else:
            at = main.find("\nfn ")  # first fn: the instance lands early
            fs["main.rs"] = main[:at + 1] + line + main[at + 1:] if at >= 0 else line + main
        return fs, op
    if op == "feat3_dyn" and "a.rs" in fs:
        impl_pair = ("impl DvA for Pair {\n    fn dv(&self) -> i64 {\n"
                     "        self.0 + self.1\n    }\n}\n")
        if "impl DvA for Pair" in atext:
            cut = drop_block(atext, "impl DvA for Pair")
            if cut is not None:
                fs["a.rs"] = cut
            return fs, op
        if rng.random() < 0.5 and "self.x * 3" in atext:
            fs["a.rs"] = atext.replace("self.x * 3", "self.x * 4", 1)
        elif "self.x * 4" in atext:
            fs["a.rs"] = atext.replace("self.x * 4", "self.x * 3", 1)
        else:
            fs["a.rs"] = atext + "\n" + impl_pair
        return fs, op
    return fs, op


def cmd_run_multi(a, rename=False, feat3=False):
    """Multi-file mode (W-RESOLVE): the seed crate is a small module tree.
    Each edit applies the single-file edit ops to one random file, or a
    structural op (add/remove a module file, toggle its `mod` line).
    The equivalence rule is the same: daemon answer == cold answer, and
    the fresh-session guard must never fire. Failure pairs are saved as
    one bundle of files per side (replay/shrink stay single-file tools).
    With rename=True (crate multi2), a module rename also fires on a
    fixed cadence from its own RNG, and the seed has more readers
    (MULTI2_SEED); plain multi keeps its old stream. Both run a
    visibility pulse on a fixed cadence from a third RNG (see the
    loop): the pulse restores the files, so the stream stays the same.
    """
    rng = random.Random(a.seed)
    frng = random.Random(a.seed ^ 0xFEA7)
    vrng = random.Random(a.seed ^ 0x715)
    frng3 = random.Random(a.seed ^ 0x5EED3)
    seed_files = MULTI3_SEED if feat3 else MULTI2_SEED if rename else MULTI_SEED
    Harness.keep_work = a.keep_work
    h = Harness(a.timeout)
    base = os.path.join(h.work, "multi")
    h.crate = os.path.join(base, "main.rs")
    files = dict(seed_files)
    snapshots = [dict(files)]
    failures = 0
    ops, bad_ops = Counter(), Counter()
    t0 = time.time()

    def write_all(fs):
        if os.path.isdir(base):
            shutil.rmtree(base)
        for rel, text in fs.items():
            p = os.path.join(base, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w") as f:
                f.write(text)

    def save_bundle(tag, prev_fs, cur_fs):
        for side, fs in (("prev", prev_fs), ("cur", cur_fs)):
            d = os.path.join(a.out, f"{tag}-{side}")
            os.makedirs(d, exist_ok=True)
            for rel, text in fs.items():
                p = os.path.join(d, rel)
                os.makedirs(os.path.dirname(p), exist_ok=True)
                with open(p, "w") as f:
                    f.write(text)

    def structural(rng, fs):
        fs = dict(fs)
        op = rng.choice(["add_mod", "drop_file", "toggle_mod", "restore_files"])
        if op == "add_mod" and "c.rs" not in fs and "main.rs" in fs:
            fs["c.rs"] = "pub fn extra() -> i64 { 5 }\n"
            fs["main.rs"] = "mod c;\n" + fs["main.rs"]
            return fs, op
        if op == "drop_file":
            victims = [k for k in fs if k != "main.rs"]
            if victims:
                victim = rng.choice(victims)
                del fs[victim]
                return fs, f"{op}:{victim}"
        if op == "toggle_mod" and "mod b;" in fs["main.rs"]:
            fs["main.rs"] = fs["main.rs"].replace("mod b;", "//mod b;", 1)
            return fs, op
        if op == "toggle_mod" and "//mod b;" in fs["main.rs"]:
            fs["main.rs"] = fs["main.rs"].replace("//mod b;", "mod b;", 1)
            return fs, op
        return dict(rng.choice(snapshots)), "restore_files"

    def rename_mod(rng, fs):
        """Renames one module and its uses, or renames it back: b <-> bb
        (file move plus `mod` line and `b::` paths) or a::inner <->
        a::deeper. A rename moves every def in the module to a new
        stable path, so stale per-file caches show up at once."""
        fs = dict(fs)
        main = fs.get("main.rs", "")
        if rng.choice(["b", "inner"]) == "b":
            if "b/mod.rs" in fs and "mod b;" in main:
                fs["bb/mod.rs"] = fs.pop("b/mod.rs")
                fs["main.rs"] = main.replace("mod b;", "mod bb;").replace("b::", "bb::")
                return fs, "rename_mod:b2bb"
            if "bb/mod.rs" in fs and "mod bb;" in main:
                fs["b/mod.rs"] = fs.pop("bb/mod.rs")
                fs["main.rs"] = main.replace("mod bb;", "mod b;").replace("bb::", "b::")
                return fs, "rename_mod:bb2b"
        else:
            atext = fs.get("a.rs", "")
            if "a/inner.rs" in fs and "pub mod inner;" in atext:
                fs["a/deeper.rs"] = fs.pop("a/inner.rs")
                fs["a.rs"] = atext.replace("pub mod inner;", "pub mod deeper;")
                fs["main.rs"] = main.replace("a::inner::", "a::deeper::")
                return fs, "rename_mod:inner2deeper"
            if "a/deeper.rs" in fs and "pub mod deeper;" in atext:
                fs["a/inner.rs"] = fs.pop("a/deeper.rs")
                fs["a.rs"] = atext.replace("pub mod deeper;", "pub mod inner;")
                fs["main.rs"] = main.replace("a::deeper::", "a::inner::")
                return fs, "rename_mod:deeper2inner"
        return fs, "rename_mod:noop"

    try:
        write_all(files)
        ok, why, da, co = compare(h, "check", a.strict)
        if not ok:
            print(f"SEED-CRATE FAILURE ({why}) on the unedited multi-file crate", flush=True)
            return 1
        seen_guard = 0
        for it in range(a.edits):
            prev = files
            if feat3 and it % 17 == 9:
                files, op = make_feature3_multi(frng3, files)
            elif rename and it % 47 == 23:
                files, op = rename_mod(frng, files)
            elif rng.random() < 0.2:
                files, op = structural(rng, files)
            else:
                rel = rng.choice(sorted(files))
                text, op = make_edit(rng, files[rel], [s.get(rel, files[rel]) for s in snapshots])
                files = dict(files)
                files[rel] = text
                op = f"{rel}:{op}"
            ops[op.split(":")[0]] += 1
            write_all(files)
            if not h.daemon_alive():
                failures += 1
                save_bundle(f"crash-{it}", prev, files)
                print(f"FAIL daemon dead before iter {it} op {op}", flush=True)
                h.start_daemon()
                files = dict(seed_files)
                write_all(files)
                h.run_cmd("check", True)
                continue
            ok, why, da, co = compare(h, "check", a.strict)
            h.wait_guard_idle()
            g = h.guard_count()
            if g > seen_guard:
                save_bundle(f"guard-{it}", prev, files)
                print(f"GUARD iter {it} op {op}: warm answer differed; bundle guard-{it} saved", flush=True)
                seen_guard = g
            if not ok:
                failures += 1
                bad_ops[why] += 1
                save_bundle(f"bad-{it}", prev, files)
                print(f"FAIL[{why}] iter {it} op {op}\n"
                      f"  daemon={da[0]} {da[2][:200]!r}\n"
                      f"  cold  ={co[0] if co else '-'} {(co[2][:200] if co else '')!r}", flush=True)
                if why in ("daemon hang", "daemon died"):
                    h.kill_daemon()
                    h.start_daemon()
                files = dict(seed_files)
                write_all(files)
                h.run_cmd("check", True)
                if a.stop_first:
                    break
                continue
            if da[0] == 0 and len(snapshots) < 40 and rng.random() < 0.05:
                snapshots.append(dict(files))
            if (it % 25 == 24 or op.endswith(":const_edit") or op.startswith("feat3_")) and da[0] == 0:
                ok, why, ra, rb = compare(h, "run", a.strict)
                if ok and why == "program hang":
                    # Same as single-file mode: matching program hang, but
                    # the daemon may still wait on its forked copy.
                    print(f"note: program hang at iter {it} op {op} (both sides); daemon restarted",
                          flush=True)
                    h.kill_daemon()
                    h.start_daemon()
                if not ok:
                    failures += 1
                    bad_ops[f"run {why}"] += 1
                    save_bundle(f"runbad-{it}", prev, files)
                    print(f"FAIL[run {why}] iter {it} op {op}", flush=True)
                    if why in ("daemon hang", "daemon died"):
                        h.kill_daemon()
                        h.start_daemon()
                        files = dict(seed_files)
                        write_all(files)
                        h.run_cmd("check", True)
                    if a.stop_first:
                        break
            # Visibility pulse: one visibility flips (vis_flip), then the
            # exact files come back, and both states must get the cold
            # answer: a narrowed member rejects warm, the widened one
            # accepts warm, from whatever state the stream reached.
            if it % 7 == 3:
                vfiles, vop = vis_flip(vrng, files)
                ops["vis_flip"] += 1
                steps = [] if vfiles is None else [(files, vfiles, vop), (vfiles, files, vop + ":back")]
                for before, state, vtag in steps:
                    write_all(state)
                    ok, why, da, co = compare(h, "check", a.strict)
                    h.wait_guard_idle()
                    g = h.guard_count()
                    if g > seen_guard:
                        save_bundle(f"guard-{it}v", before, state)
                        print(f"GUARD iter {it} op {vtag}: warm answer differed; bundle guard-{it}v saved", flush=True)
                        seen_guard = g
                    if not ok:
                        failures += 1
                        bad_ops[why] += 1
                        save_bundle(f"bad-{it}v", before, state)
                        print(f"FAIL[{why}] iter {it} op {vtag}\n"
                              f"  daemon={da[0]} {da[2][:200]!r}\n"
                              f"  cold  ={co[0] if co else '-'} {(co[2][:200] if co else '')!r}", flush=True)
                        if why in ("daemon hang", "daemon died"):
                            h.kill_daemon()
                            h.start_daemon()
                        files = dict(seed_files)
                        write_all(files)
                        h.run_cmd("check", True)
                        break
                if failures and a.stop_first:
                    break
            if (it + 1) % 250 == 0:
                print(f"... {it + 1}/{a.edits} failures={failures} {time.time() - t0:.0f}s", flush=True)
        h.wait_guard_idle()
        guard = h.guard_count()
        print(f"RESULT seed={a.seed} crate={a.crate} edits={a.edits} failures={failures} "
              f"guard_fired={guard} wall={time.time() - t0:.0f}s")
        print("ops:", dict(ops))
        print("bad:", dict(bad_ops))
        if a.fail_on_guard and guard > 0:
            failures += guard
        return 1 if failures else 0
    finally:
        h.close()


def replay_pair(prev, cur, timeout, strict=False):
    """Fresh daemon checks prev, then cur; cold checks cur. True if the pair fails.

    A fresh-session guard firing counts as a failure: the warm answer was wrong
    even when it happened to match cold. The guard runs in the background, so
    both checks wait for it to settle before the file changes or the verdict
    is read."""
    h = Harness(timeout)
    try:
        h.write(prev)
        h.run_cmd("check", True)
        h.wait_guard_idle()
        if not h.daemon_alive():
            return True, "daemon died on prev"
        h.write(cur)
        ok, why, da, co = compare(h, "check", strict)
        h.wait_guard_idle()
        if not ok:
            return True, why
        if h.guard_count() > 0:
            return True, "guard fired"
        return False, ""
    finally:
        h.close()


def cmd_replay(a):
    prev = open(a.prev).read()
    cur = open(a.cur).read()
    bad, why = replay_pair(prev, cur, a.timeout, a.strict)
    print(f"{'FAIL ' + why if bad else 'MATCH'} prev={a.prev} cur={a.cur}")
    return 1 if bad else 0


def shrink_lines(text, other, which, fails, budget):
    """Greedily delete line blocks from `text` while the pair still fails."""
    lines = text.splitlines(keepends=True)
    size = max(1, len(lines) // 2)
    while size >= 1 and budget[0] > 0:
        i = 0
        progressed = False
        while i < len(lines) and budget[0] > 0:
            cand = lines[:i] + lines[i + size:]
            if cand == lines:
                i += size
                continue
            budget[0] -= 1
            pair = ("".join(cand), other) if which == "prev" else (other, "".join(cand))
            if fails(*pair):
                lines = cand
                progressed = True
            else:
                i += size
        if not progressed:
            size //= 2
    return "".join(lines)


def cmd_shrink(a):
    prev = open(a.prev).read()
    cur = open(a.cur).read()
    bad, why = replay_pair(prev, cur, a.timeout)
    if not bad:
        print("pair does not fail; nothing to shrink")
        return 0
    print(f"shrinking (fails with: {why}); budget {a.budget} replays")
    budget = [a.budget]

    def fails(p, c):
        if budget[0] <= 0:
            return False
        bad, _ = replay_pair(p, c, a.timeout)
        return bad

    # A common case: prev only has to prime the session, so cur alone as prev works.
    if fails(cur, cur):
        prev = cur
    cur = shrink_lines(cur, prev, "cur", fails, budget)
    prev = shrink_lines(prev, cur, "prev", fails, budget)
    cur = shrink_lines(cur, prev, "cur", fails, budget)
    save_pair(a.out, "min", prev, cur)
    print(f"minimized: prev {len(prev)} bytes, cur {len(cur)} bytes "
          f"(replays left: {budget[0]})")
    print(f"wrote {a.out}/min-prev.rs and {a.out}/min-cur.rs")
    bad, why = replay_pair(prev, cur, a.timeout)
    print(f"final pair: {'FAIL ' + why if bad else 'MATCH (bad shrink!)'}")
    return 1 if bad else 2


def main():
    p = argparse.ArgumentParser(description="daemon vs cold random-edit fuzzer")
    sub = p.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("--edits", type=int, default=2000)
    r.add_argument("--seed", type=int, default=7)
    r.add_argument("--crate", default="small", help="small, realish, or a file path")
    r.add_argument("--modules", type=int, default=40, help="realish module count")
    r.add_argument("--out", default="/tmp/lust-fuzz-out")
    r.add_argument("--timeout", type=float, default=10)
    r.add_argument("--strict", action="store_true")
    r.add_argument("--stop-first", action="store_true")
    r.add_argument("--fail-on-guard", action="store_true")
    r.add_argument("--keep-work", action="store_true")
    r.add_argument("--record", default=None, help="dir to write every text as NNNN.rs")
    for name in ("replay", "shrink"):
        s = sub.add_parser(name)
        s.add_argument("--prev", required=True)
        s.add_argument("--cur", required=True)
        s.add_argument("--timeout", type=float, default=10)
        s.add_argument("--strict", action="store_true")
        if name == "shrink":
            s.add_argument("--out", default="/tmp/lust-fuzz-out")
            s.add_argument("--budget", type=int, default=300)
    a = p.parse_args()
    if not os.path.exists(LUST):
        print(f"setup error: {LUST} not found; build first (cargo build --release)")
        return 2
    return {"run": cmd_run, "replay": cmd_replay, "shrink": cmd_shrink}[a.cmd](a)


if __name__ == "__main__":
    sys.exit(main())
