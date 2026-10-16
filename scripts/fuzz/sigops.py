# Signature-level edit ops for the edit fuzzer (sigedit PLAN, P1.1).
#
# Each op takes the crate's files (rel path -> text) and returns the
# states to visit in order, the last one being the files it started
# from, so a pulse leaves the main edit stream as it was:
#   sig_where      a `where` clause on a fn (true, false, or generic bound)
#   sig_param      a fn parameter added, or its type changed
#   sig_ret        a fn return type changed (or `-> ()` written out)
#   rpit_bound     a bound added to an `-> impl Trait` return type
#   derive_drop    one trait out of a `#[derive(..)]`
#   derive_add     one trait into a `#[derive(..)]`
#   alias_rename   `use a::f` becomes `use a::f as g` (uses follow), or a
#                  new `use crate::m::f as g` in another file
#   reexport_glob  `pub use crate::m::*;` in another module
#   rpit_chain     Sol's case: f's return type changes, an unchanged
#                  `g() -> impl Trait { f() }` hides it, a caller needs an
#                  auto trait from g()
#   const_closure  Sol's case: `static P: fn() -> u32 = make();` with
#                  `const fn make() -> fn() -> u32 { f }`, then a `where`
#                  clause on f
#   sig_generic    the header delta's own op (driver/kept_delta.rs takes
#                  only programs with user generics): a generic fn first,
#                  sometimes an RPIT user or a const closure of a fresh fn,
#                  then two header edits in a row, back, and the files
# `External` adds verdicts from rustc 1.99 and a pinned baseline lust for
# the op states (`--rustc`, `--baseline`): a state where the warm answer
# disagrees with rustc fails unless the baseline gives the same answer
# (a known gap, counted, not a failure); with no baseline, only a false
# accept fails.
import os, re, subprocess, tempfile

OPS = ["sig_where", "sig_param", "sig_ret", "rpit_bound", "derive_drop", "derive_add",
       "alias_rename", "reexport_glob", "rpit_chain", "const_closure", "sig_generic"]

# One-line fn headers: indent, head up to the name, generics, params,
# return type. A header that already has a `where` is left alone.
FN_HEAD = re.compile(r"^(?P<ind>[ \t]*)(?P<pre>(?:pub(?:\([\w:]+\))? )?(?:const )?(?:unsafe )?)fn (?P<name>\w+)"
                     r"(?P<gen><[^>{}]*>)?\((?P<params>[^()]*(?:\([^()]*\)[^()]*)*)\)"
                     r"(?: -> (?P<ret>[^{]+?))? \{$", re.M)
DERIVE = re.compile(r"#\[derive\(([^)]*)\)\]")
SINGLE_USE = re.compile(r"^(?P<ind>[ \t]*)(?P<vis>pub(?:\([\w:]+\))? )?use (?P<path>(?:crate|super|self)(?:::\w+)*)::(?P<name>[a-z_]\w*);$", re.M)
PUB_FN = re.compile(r"^pub fn (\w+)", re.M)
DERIVABLE = ["Clone", "Copy", "Debug", "PartialEq", "Eq", "Default", "Hash", "PartialOrd"]


def _heads(fs):
    return [(rel, m) for rel in sorted(fs) for m in FN_HEAD.finditer(fs[rel]) if m.group("name") != "main"]


def _swap(fs, rel, s, e, new):
    out = dict(fs)
    out[rel] = fs[rel][:s] + new + fs[rel][e:]
    return out


def _header(m, gen=None, params=None, ret=None, where=""):
    g = m.group("gen") if gen is None else gen
    p = m.group("params") if params is None else params
    r = m.group("ret") if ret is None else ret
    return f"{m.group('ind')}{m.group('pre')}fn {m.group('name')}{g or ''}({p}){' -> ' + r if r else ''}{where} {{"


def _mod_path(rel):
    """The module path of a file in a multi crate (`a/inner.rs` -> `crate::a::inner`)."""
    if rel in ("main.rs", "crate.rs", "lib.rs"):
        return "crate"
    parts = rel[:-3].split("/")
    if parts[-1] == "mod":
        parts = parts[:-1]
    return "crate::" + "::".join(parts)


def sig_where(rng, fs):
    heads = _heads(fs)
    if not heads:
        return []
    rel, m = rng.choice(heads)
    clauses = [" where u32: Copy", " where String: Copy", " where i64: Clone + Default"]
    params = re.findall(r"<\s*(\w+)", m.group("gen") or "")
    if params:
        clauses += [f" where {params[0]}: Clone", f" where {params[0]}: Default", f" where {params[0]}: Sized"]
    return [_swap(fs, rel, m.start(), m.end(), _header(m, where=rng.choice(clauses))), fs]


def sig_param(rng, fs):
    heads = _heads(fs)
    if not heads:
        return []
    rel, m = rng.choice(heads)
    p = m.group("params")
    typed = list(re.finditer(r"\b(i64|i32|u32|u64|usize)\b", p))
    if typed and rng.random() < 0.6:
        t = rng.choice(typed)
        new_t = rng.choice([x for x in ["i64", "i32", "u32", "u64"] if x != t.group(1)])
        params = p[:t.start()] + new_t + p[t.end():]
    else:
        params = (p + ", " if p.strip() else "") + "_sig: u8"
    return [_swap(fs, rel, m.start(), m.end(), _header(m, params=params)), fs]


def sig_ret(rng, fs):
    heads = _heads(fs)
    if not heads:
        return []
    rel, m = rng.choice(heads)
    r = m.group("ret")
    if r is None:
        ret = "()"
    elif r.startswith("impl "):
        ret = r + " + Sized"
    else:
        ret = rng.choice(["i32", "u64", "Option<" + r + ">", "()", "&'static str", r])
    return [_swap(fs, rel, m.start(), m.end(), _header(m, ret=ret)), fs]


def rpit_bound(rng, fs):
    sites = [(rel, m) for rel, m in _heads(fs) if (m.group("ret") or "").startswith("impl ")]
    if not sites:
        return []
    rel, m = rng.choice(sites)
    ret = m.group("ret") + rng.choice([" + Sized", " + Copy", " + Send", " + Sync", " + 'static", " + Clone"])
    return [_swap(fs, rel, m.start(), m.end(), _header(m, ret=ret)), fs]


def _derive_sites(fs):
    return [(rel, m) for rel in sorted(fs) for m in DERIVE.finditer(fs[rel])]


def derive_drop(rng, fs):
    sites = [(rel, m) for rel, m in _derive_sites(fs) if m.group(1).strip()]
    if not sites:
        return []
    rel, m = rng.choice(sites)
    names = [x.strip() for x in m.group(1).split(",") if x.strip()]
    names.remove(rng.choice(names))
    return [_swap(fs, rel, m.start(), m.end(), f"#[derive({', '.join(names)})]"), fs]


def derive_add(rng, fs):
    sites = _derive_sites(fs)
    if not sites:
        return []
    rel, m = rng.choice(sites)
    names = [x.strip() for x in m.group(1).split(",") if x.strip()]
    extra = [d for d in DERIVABLE if d not in names]
    if not extra:
        return []
    names.insert(rng.randrange(len(names) + 1), rng.choice(extra))
    return [_swap(fs, rel, m.start(), m.end(), f"#[derive({', '.join(names)})]"), fs]


def alias_rename(rng, fs):
    uses = [(rel, m) for rel in sorted(fs) for m in SINGLE_USE.finditer(fs[rel])]
    if uses and rng.random() < 0.7:
        rel, m = rng.choice(uses)
        name = m.group("name")
        alias = name + "_sig"
        text = fs[rel]
        rest = re.sub(rf"\b{name}\b(?=\s*[(!:<])", alias, text[m.end():])
        new = f"{m.group('ind')}{m.group('vis') or ''}use {m.group('path')}::{name} as {alias};"
        out = dict(fs)
        out[rel] = text[:m.start()] + new + rest
        return [out, fs]
    # A new alias of another file's pub fn (unused: a warning both ways).
    defs = [(rel, n) for rel in sorted(fs) for n in PUB_FN.findall(fs[rel])]
    if len(fs) < 2 or not defs:
        return []
    rel, name = rng.choice(defs)
    into = rng.choice([r for r in sorted(fs) if r != rel])
    line = f"#[allow(unused_imports)]\nuse {_mod_path(rel)}::{name} as {name}_alias;\n"
    out = dict(fs)
    out[into] = _after_inner_attrs(fs[into], line)
    return [out, fs]


def _after_inner_attrs(text, line):
    """`text` with `line` inserted after its inner attributes (`#![..]`)."""
    m = re.match(r"(?:\s*#!\[[^\]]*\]\s*\n)*", text)
    k = m.end() if m else 0
    return text[:k] + line + text[k:]


def reexport_glob(rng, fs):
    mods = [r for r in sorted(fs) if _mod_path(r) != "crate"]
    if not mods:
        return []
    src = rng.choice(mods)
    into = rng.choice([r for r in sorted(fs) if r != src])
    line = f"#[allow(unused_imports)]\npub use {_mod_path(src)}::*;\n"
    out = dict(fs)
    out[into] = _after_inner_attrs(fs[into], line)
    return [out, fs]


def _root(fs):
    for r in ("main.rs", "crate.rs"):
        if r in fs:
            return r
    return sorted(fs)[0]


def rpit_chain(rng, fs):
    """Sol's RPIT chain, appended to the root file with fresh names: A
    (passes), B (f's return type changes; the unchanged opaque users must
    see it), back to A, then the files as they were."""
    k = rng.randrange(10**6)
    auto = rng.choice(["Send", "Sync"])
    depth = rng.choice([1, 2])
    trait = rng.choice(["std::fmt::Debug", "Clone"])
    chain = f"fn zs{k}_g() -> impl {trait} {{ zs{k}_f() }}\n"
    top = f"zs{k}_g"
    if depth == 2:
        chain += f"fn zs{k}_h() -> impl {trait} {{ zs{k}_g() }}\n"
        top = f"zs{k}_h"
    def items(ret, val):
        return (f"\nfn zs{k}_f() -> {ret} {{ {val} }}\n{chain}"
                f"fn zs{k}_need<T: {auto}>(t: T) -> T {{ t }}\n"
                f"#[allow(dead_code)]\nfn zs{k}_use() {{ let _ = zs{k}_need({top}()); }}\n")
    root = _root(fs)
    a = dict(fs)
    a[root] = fs[root] + items("u32", "7")
    bad = rng.choice([("std::rc::Rc<u32>", "std::rc::Rc::new(7)"), ("std::cell::Cell<u32>", "std::cell::Cell::new(7)"),
                      ("u64", "7"), ("*const u8", "std::ptr::null()")])
    b = dict(fs)
    b[root] = fs[root] + items(*bad)
    return [a, b, a, fs]


def const_closure(rng, fs):
    """Sol's const-fn closure, appended to the root file: A (passes), B (a
    `where` clause on f, which make() names), back to A, then the files."""
    k = rng.randrange(10**6)
    def items(where_f, where_make):
        return (f"\nfn zc{k}_f() -> u32{where_f} {{ 5 }}\n"
                f"const fn zc{k}_make() -> fn() -> u32{where_make} {{ zc{k}_f }}\n"
                f"static ZC{k}_P: fn() -> u32 = zc{k}_make();\n"
                f"#[allow(dead_code)]\nfn zc{k}_use() -> u32 {{ let p = ZC{k}_P; p() }}\n")
    root = _root(fs)
    a = dict(fs)
    a[root] = fs[root] + items("", "")
    b = dict(fs)
    b[root] = fs[root] + rng.choice([items(" where u32: Copy", ""), items("", " where u32: Copy")])
    return [a, b, a, fs]


def sig_generic(rng, fs):
    """A: the files with a generic fn (and maybe a fresh fn `f` that an
    unchanged `-> impl Debug` body or a const fn names) at the end of the
    root file; then one header edit on A, a second on top of it, back to
    A, and the files. The edits pick `f` half the time when it exists."""
    k = rng.randrange(10**6)
    extra = rng.choice(["", "rpit", "const"])
    items = f"\n#[allow(dead_code)]\nfn zg{k}_id<T: Clone>(t: T) -> T {{ t.clone() }}\n"
    if extra == "rpit":
        auto = rng.choice(["Send", "Sync"])
        items += (f"fn zg{k}_f(x: u32) -> u32 {{\n    x\n}}\n"
                  f"fn zg{k}_g() -> impl std::fmt::Debug {{ zg{k}_f(1) }}\n"
                  f"fn zg{k}_need<T: {auto}>(t: T) -> T {{ t }}\n"
                  f"#[allow(dead_code)]\nfn zg{k}_use() {{ let _ = zg{k}_need(zg{k}_g()); }}\n")
    elif extra == "const":
        items += (f"fn zg{k}_f(x: u32) -> u32 {{\n    x\n}}\n"
                  f"const fn zg{k}_make() -> fn(u32) -> u32 {{ zg{k}_f }}\n"
                  f"static ZG{k}_P: fn(u32) -> u32 = zg{k}_make();\n"
                  f"#[allow(dead_code)]\nfn zg{k}_use() -> u32 {{ let p = ZG{k}_P; p(2) }}\n")
    root = _root(fs)
    a = dict(fs)
    a[root] = fs[root] + items

    def edit(cur):
        heads = _heads(cur)
        own = [(rel, m) for rel, m in heads if m.group("name") == f"zg{k}_f"]
        if own and rng.random() < 0.5:
            rel, m = own[0]
            new = rng.choice([_header(m, where=" where u32: Copy"), _header(m, where=" where String: Copy"),
                              _header(m, params="x: u64"), _header(m, ret="u64"), _header(m, params="x: u32, _y: u8")])
            return _swap(cur, rel, m.start(), m.end(), new)
        op = rng.choice([sig_where, sig_param, sig_ret])
        states = op(rng, cur)
        return states[0] if states else cur

    s1 = edit(a)
    s2 = edit(s1)
    return [a, s1, s2, a, fs]


def sig_states(rng, fs):
    """One op: (op name, states to visit). No state when it has no site."""
    op = rng.choice(OPS)
    return op, globals()[op](rng, fs)


class External:
    """rustc 1.99 and baseline lust verdicts for op states (see the top)."""

    def __init__(self, rustc, baseline):
        self.rustc = rustc
        self.baseline = baseline if baseline and os.access(baseline, os.X_OK) else None
        if baseline and not self.baseline:
            print(f"sigops: baseline {baseline} is not an executable file; judging without it", flush=True)
        self.counts = {"states": 0, "false_accept": 0, "false_reject": 0, "known_fa": 0, "known_fr": 0,
                       "rustc_timeout": 0}
        self.tmp = tempfile.mkdtemp(prefix="lust-sigops-")

    def on(self):
        return self.rustc

    def _rustc_ok(self, root):
        try:
            r = subprocess.run(["rustc", "--edition", "2024", "--crate-type", "bin", "--emit=metadata",
                                "-o", os.path.join(self.tmp, "x.rmeta"), root],
                               cwd=os.path.dirname(root), capture_output=True, text=True, timeout=60)
        except subprocess.TimeoutExpired:
            return None
        return r.returncode == 0

    def _base_ok(self, root, env):
        if not self.baseline:
            return None
        try:
            r = subprocess.run([self.baseline, "check", root], cwd=os.path.dirname(root), env=env,
                               capture_output=True, text=True, timeout=120)
        except subprocess.TimeoutExpired:
            return "hang"
        return r.returncode == 0

    def judge(self, root, warm_ok, cold_env):
        """None when the warm verdict stands; else why it fails."""
        if not self.rustc:
            return None
        self.counts["states"] += 1
        r = self._rustc_ok(root)
        if r is None:
            self.counts["rustc_timeout"] += 1
            return None
        if warm_ok == r:
            return None
        kind = "false_accept" if warm_ok else "false_reject"
        b = self._base_ok(root, cold_env)
        if b == warm_ok:
            self.counts["known_" + ("fa" if warm_ok else "fr")] += 1
            return None
        if b is None and not warm_ok:
            # No baseline: a false reject may be a known gap.
            self.counts["known_fr"] += 1
            return None
        self.counts[kind] += 1
        return f"new {kind} (rustc {'accepts' if r else 'rejects'}, baseline {b})"

    def summary(self):
        return "sigops: " + " ".join(f"{k}={v}" for k, v in self.counts.items())
