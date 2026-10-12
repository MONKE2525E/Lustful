#!/usr/bin/env bash
# Parser robustness fuzz: truncations and mutations of tests/pass files, plus random
# token soup. Every case runs under a 2 second timeout. A hang (timeout), a compiler
# panic (exit 101), or a signal death (exit > 128) is a failure; clean accepts and
# clean errors are both fine. Failing inputs are kept in a directory printed at the end.
# Usage: scripts/parse-fuzz.sh [cases] [seed]
set -uo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lust=$root/target/release/lust
cases=${1:-3000}
seed=${2:-1}
work=$(mktemp -d)
faildir=$(mktemp -d)
echo "parse-fuzz: $cases cases, seed $seed, work dir $work"

python3 - "$root" "$work" "$cases" "$seed" <<'PY'
import glob, os, random, sys
root, work, cases, seed = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
rng = random.Random(seed)
sources = [open(f, "rb").read() for f in sorted(glob.glob(os.path.join(root, "tests/pass/*.rs")))]
tokens = [b"fn", b"let", b"mut", b"struct", b"enum", b"impl", b"match", b"if", b"else",
          b"loop", b"while", b"for", b"in", b"return", b"break", b"pub", b"pub(",
          b"use", b"gen", b"r#gen", b"x", b"main", b"Vec", b"i64", b"self", b"Self",
          b"(", b")", b"{", b"}", b"[", b"]", b"<", b">", b">>", b";", b",", b":",
          b"::", b".", b"..", b"..=", b"->", b"=>", b"=", b"==", b"+", b"-", b"*",
          b"/", b"%", b"&", b"&&", b"|", b"||", b"!", b"#", b"#[derive(", b"?",
          b"$", b"@", b"_", b"0", b"128i8", b"0x", b"1e", b"1.5", b"'a", b"'\\n'",
          b"'", b'"s"', b'"unterminated', b"/*", b"*/", b"// c\n", b"println!",
          b"18446744073709551616u64", "🧀".encode()]
known = [b"(", b"", b"pub(", b"fn", b"{", b"'", b'"', b"/*", b"r#", b"r#self",
         b"fn main() { let x = ", b"####", b"<<<<", b"fn f(&mut self,,,,",
         b"struct S {", b"match x {", b"#[",
         b"fn main() { let x = " + b"(" * 5000 + b"1",
         b"fn main() { let x: i64 = 1" + b" + 1" * 5000 + b"; }",
         b"fn main() { let x: i64 = " + b"-" * 5000 + b"1; }"]

def write(i, data):
    with open(os.path.join(work, "case-%05d.rs" % i), "wb") as f:
        f.write(data)

for i in range(cases):
    if i < len(known):
        write(i, known[i])
        continue
    mode = i % 3
    src = rng.choice(sources)
    if mode == 0:  # truncation at a random byte offset
        write(i, src[: rng.randint(0, len(src))])
    elif mode == 1:  # random token soup
        n = rng.randint(1, 80)
        write(i, b" ".join(rng.choice(tokens) for _ in range(n)))
    else:  # a few random mutations of a real file
        data = bytearray(src)
        for _ in range(rng.randint(1, 5)):
            if not data:
                break
            op = rng.randint(0, 2)
            pos = rng.randint(0, len(data))
            if op == 0:
                end = min(len(data), pos + rng.randint(1, 60))
                del data[pos:end]
            elif op == 1:
                data[pos:pos] = rng.choice(tokens)
            else:
                end = min(len(data), pos + rng.randint(1, 60))
                data[pos:pos] = data[pos:end]
        write(i, bytes(data))
PY

# Run from the temp dir so no lust daemon for this repo answers instead of a cold check,
# and do not autostart a daemon for the temp dir either.
export LUST_BIN="$lust" FAILDIR="$faildir"
run_one() {
  f="$1"
  LUST_NO_DAEMON=1 timeout 2 "$LUST_BIN" check "$f" >/dev/null 2>&1
  code=$?
  if [ "$code" -eq 124 ] || [ "$code" -eq 101 ] || [ "$code" -gt 128 ]; then
    cp "$f" "$FAILDIR/"
    echo "BAD exit=$code $f"
  fi
}
export -f run_one
cd "$work" || exit 1
ls case-*.rs | xargs -P 8 -I{} bash -c 'run_one "$@"' _ {}

bad=$(find "$faildir" -name 'case-*.rs' | wc -l)
echo "parse-fuzz: $cases cases, $bad bad"
if [ "$bad" -ne 0 ]; then
  echo "failing inputs kept in $faildir"
  exit 1
fi
rm -rf "$work" "$faildir"
