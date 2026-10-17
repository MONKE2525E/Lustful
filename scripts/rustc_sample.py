#!/usr/bin/env python3
# rustc_sample.py: a cheap rule-zero oracle for fuzz lanes. A fuzz lane offers each program
# that lust accepts; this keeps a uniform sample (reservoir, own RNG, duplicates dropped) of
# at most N of them, then builds each with rustc at its default lint levels (a full build:
# `--emit=metadata` misses deny-by-default lints such as unconditional_panic). A rustc
# rejection is a failure: lust accepted a program that is not valid Rust. A rustc timeout is
# counted, never judged.
#   fuzz.py run --rustc-sample N   (Sample in-process)
#   rustc_sample.py N SEED OUTDIR FILE...   (parse-fuzz.sh: the files lust accepted)
# The CLI prints "rustc sample: <k> built, <r> rejected, <t> timeouts, of <a> accepted" and
# exits 1 when r > 0. Rejected programs are copied to OUTDIR as rustc-reject-<i>.rs.
import concurrent.futures, hashlib, os, random, shutil, subprocess, sys, tempfile

FLAGS = ["--edition", "2024", "--crate-type", "bin", "-C", "panic=abort", "-C", "overflow-checks=on", "-A", "warnings"]


class Sample:
    """Up to n distinct offered texts, chosen uniformly with a seeded RNG."""

    def __init__(self, n, seed):
        self.n, self.rng = n, random.Random(seed ^ 0x2C5C)
        self.seen, self.keep, self.hashes = 0, [], set()

    def offer(self, text):
        if self.n <= 0:
            return
        h = hashlib.sha256(text.encode() if isinstance(text, str) else text).digest()
        if h in self.hashes:
            return
        self.hashes.add(h)
        self.seen += 1
        if len(self.keep) < self.n:
            self.keep.append(text)
        else:
            j = self.rng.randrange(self.seen)
            if j < self.n:
                self.keep[j] = text

    def judge(self, out, timeout=120, jobs=8):
        """Builds the sample with rustc; prints one FAIL line per rejection and the summary.
        Returns the rejection count."""
        if self.n <= 0:
            return 0
        tmp = tempfile.mkdtemp(prefix="lust-rustc-sample-")

        def one(i):
            d = os.path.join(tmp, str(i))
            os.makedirs(d)
            src = os.path.join(d, "main.rs")
            text = self.keep[i]
            with open(src, "wb") as f:
                f.write(text.encode() if isinstance(text, str) else text)
            try:
                r = subprocess.run(["rustc", *FLAGS, "-o", os.path.join(d, "bin"), "main.rs"], cwd=d,
                                   capture_output=True, text=True, timeout=timeout)
            except subprocess.TimeoutExpired:
                return i, "timeout", ""
            if r.returncode == 0:
                return i, "ok", ""
            err = next((l for l in r.stderr.splitlines() if l.startswith("error")), r.stderr[:200])
            return i, "reject", err

        rejected = timeouts = 0
        try:
            with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
                for i, st, err in sorted(ex.map(one, range(len(self.keep)))):
                    if st == "timeout":
                        timeouts += 1
                    elif st == "reject":
                        rejected += 1
                        os.makedirs(out, exist_ok=True)
                        keep = os.path.join(out, f"rustc-reject-{rejected}.rs")
                        shutil.copy(os.path.join(tmp, str(i), "main.rs"), keep)
                        print(f"FAIL[rustc rejects a lust accept] {keep}: {err}", flush=True)
        finally:
            shutil.rmtree(tmp, ignore_errors=True)
        built = len(self.keep) - rejected - timeouts
        print(f"rustc sample: {built} built, {rejected} rejected, {timeouts} timeouts, of {self.seen} accepted",
              flush=True)
        return rejected


def main():
    n, seed, out, files = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4:]
    s = Sample(n, seed)
    for f in sorted(files):
        with open(f, "rb") as fh:
            s.offer(fh.read())
    return 1 if s.judge(out) else 0


if __name__ == "__main__":
    sys.exit(main())
