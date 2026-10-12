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
#   fuzz.py run --edits 2000 --seed 7 --crate small|realish [--modules 40] [--strict]
#   fuzz.py replay --prev A.rs --cur B.rs
#   fuzz.py shrink --prev A.rs --cur B.rs --out DIR
# Exit status: 0 = clean, 1 = a failure was found, 2 = setup error.
import argparse, os, random, re, shutil, signal, subprocess, sys, tempfile, time
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
LUST = os.path.join(ROOT, "target/release/lust")

SMALL_CRATE = '''struct Point {
    x: i64,
    y: i64,
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

fn main() {
    let mut pts: Vec<Point> = Vec::new();
    pts.push(Point { x: 1, y: 2 });
    pts.push(Point { x: 3, y: 4 });
    pts[0].bump(5);
    let t = total(&pts);
    let c = classify(Shape::Pair(2, 3));
    let nums = vec![10, 20, 30];
    println!("{} {} {} {}", label(t), c, pick(&nums, 1), pts.len());
}
'''

SNIPPETS = ["/*", "*/", '"', "fn zz() {", "}", "#[derive(Debug)]\n", "\n\n", "pub ",
            "struct Qq {", "// note\n", "x", "123", "->", "impl Qq {", 'let q = "abc\n',
            "/* a\nb\nfn fake() {}\n*/\n", "#[derive(Clone)]\n\n", "fn", "(", "/*\n\n\n",
            'static S: &str = "a\nfn fake2() {}\nb";\n']
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
         "delete_bytes", "move_item", "insert_fn", "word_sub", "dup_lines",
         "join_line", "split_line", "swap_lines"],
        weights=[10, 10, 8, 14, 8, 6, 8, 6, 8, 5, 5, 5, 5])[0]
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
    if op == "word_sub":
        for a, bb in [("10", "2"), ("100", "7"), ("i64", "i32"), ("true", "false"), ("+", "-")]:
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


def crate_text(kind, modules):
    if kind == "small":
        return SMALL_CRATE
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
    rng = random.Random(a.seed)
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
            if it % 25 == 24 and da[0] == 0:
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
