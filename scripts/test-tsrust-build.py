#!/usr/bin/env python3
# Unit tests for the text transforms of scripts/tsrust_build.py: cfg(test) on, test attribute
# markers, `pub(crate)` insertion, dev-dependencies as dependencies.
# Usage: python3 scripts/test-tsrust-build.py   (exit 0 = pass)
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "bench/slices"))
import tsrust_build as tb  # noqa: E402

failures = []


def eq(name, got, want):
    if got != want:
        failures.append(f"{name}:\n  got  {got!r}\n  want {want!r}")


eq("cfg test", tb.cfg_on("#[cfg(test)]\nmod t;"), "#[cfg(all())]\nmod t;")
eq("cfg not test", tb.cfg_on("#[cfg(not(test))] fn a() {}"), "#[cfg(not(all()))] fn a() {}")
eq("cfg any", tb.cfg_on('#[cfg(any(test, feature = "test"))]'), '#[cfg(any(all(), feature = "test"))]')
eq("cfg_attr", tb.cfg_on("#[cfg_attr(test, derive(Debug))]"), "#[cfg_attr(all(), derive(Debug))]")
eq("cfg macro", tb.cfg_on("if cfg!(test) { tests() }"), "if cfg!(all()) { tests() }")
eq("not a cfg", tb.cfg_on("fn test() { test(); }"), "fn test() { test(); }")
eq("marks", tb.mark_attrs("    #[test]\n    #[should_panic(expected = \"x\")]\n    #[ignore]\n    fn a() {}"),
   '    #[doc = "lust-test"]\n    #[doc = "lust-should-panic"]\n    #[doc = "lust-ignore"]\n    fn a() {}')
eq("mark only at line start", tb.mark_attrs('let s = "#[test]";'), 'let s = "#[test]";')

with tempfile.TemporaryDirectory() as d:
    f = Path(d) / "a.rs"
    f.write_text("mod tests {\n    fn a() {}\n    const fn b() {}\n    pub fn c() {}\n#[cfg(all())] mod inner {}\n}\n")
    edits = {}
    for line, word, name in [(1, "mod", "tests"), (2, "fn", "a"), (3, "fn", "b"), (4, "fn", "c"), (5, "mod", "inner")]:
        tb.add_text(edits, str(f), line, word, name, "pub(crate) ")
    tb.apply_edits(edits)
    eq("vis edits", f.read_text(),
       "pub(crate) mod tests {\n    pub(crate) fn a() {}\n    pub(crate) const fn b() {}\n    pub fn c() {}\n#[cfg(all())] pub(crate) mod inner {}\n}\n")
    m = Path(d) / "Cargo.toml"
    m.write_text('[package]\nname = "p"\n\n[dependencies]\nx = "1"\n\n[dev-dependencies]\nx = "1"\ny = "2"\n')
    tb.manifests_with_dev_deps(Path(d))
    eq("dev deps", m.read_text(), '[package]\nname = "p"\n\n[dependencies]\ny = "2"\nx = "1"\n\n')

if failures:
    print("\n".join(failures))
    sys.exit(1)
print("test-tsrust-build: all passed")
