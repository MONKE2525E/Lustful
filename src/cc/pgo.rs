// Clang PGO for the release driver, per unit (rel-cache round 3).
//
// `LUST_PGO_GEN=1` builds an instrumented binary (`-fprofile-generate`; its runs write
// raw profiles where `LLVM_PROFILE_FILE` says). zig ships no profile runtime, so with a
// zig compiler that build uses `LUST_PGO_CC`, a clang of zig's LLVM major version, for
// the host (`gen_spec`; scripts/pgo-llvm.sh installs one). `LUST_PGO_USE=<file.profdata>`
// builds with a merged profile, which must come from the compiler's LLVM major. A profile must not change every object's cache key, so each
// unit compiles with a profile of only its own functions' records, and its key holds
// exactly that (`Mode::key_part`): a refreshed or pinned profile recompiles only the
// units whose own counts moved. The thresholds LLVM derives from a profile's summary
// (hot, cold, the working-set size) would then be per unit; flags pin them to the
// whole profile's instead (`pins`, in every key), rounded to a power of 2 so a retrain
// keeps them, and size optimization keys on the pinned cold count only
// (`-pgso-cold-code-only`). `LUST_PGO_BITS=<n>` keeps n significant bits of every
// count (0 = exact), so a retrain on the same inputs moves fewer records (2 bits: 89%
// of tsgo's units keep their records). `LUST_PROFDATA` names the llvm-profdata of the
// compiler's LLVM.
//
// Record names: an external function is its own name; a static one is
// `<file>;<name>` with the file as given to the compiler, so units compile from inside
// the work dir under content-derived names (`stable_name`). A unit owns the records of
// the definitions it prints (`defined_externs`). The runtime unit's helpers come from
// macros (`LUST_ABS(int8_t, i8)`), so the runtime unit also owns the `lust_*` records no
// unit visibly defines; any other record no unit defines is of a fn this build does not
// have (a profile from an older state) and goes to no unit.
use super::CcSpec;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The PGO mode of one release build.
pub enum Mode {
    Gen,
    Use(Pgo),
}

/// A loaded profile, split by unit.
pub struct Pgo {
    /// The text profile's header (the IR-level flag lines).
    head: String,
    /// Each unit's own records, sorted, by the file name the unit compiles as.
    own: HashMap<String, Vec<String>>,
    /// The flags that pin the summary thresholds to the whole profile's.
    pins: Vec<String>,
    records: usize,
    /// `lust_*` records no unit visibly defines (the runtime unit's macro-made helpers):
    /// the runtime unit owns them, or every unit when no unit includes system headers.
    unowned: usize,
    /// Other records no unit defines (fns this build does not have): in no profile.
    absent: usize,
    work: PathBuf,
}

impl Mode {
    /// The mode `LUST_PGO_GEN` / `LUST_PGO_USE` ask for, or None. `units` are (file name
    /// the unit compiles as, C text).
    pub fn from_env(spec: &CcSpec, work: &Path, units: &[(String, &str)]) -> Result<Option<Mode>, String> {
        if std::env::var_os("LUST_PGO_GEN").is_some_and(|v| v == "1") {
            return Ok(Some(Mode::Gen));
        }
        let Some(path) = std::env::var_os("LUST_PGO_USE") else { return Ok(None) };
        // The profile format and the fns' CFG hashes are those of one LLVM major.
        let cc = clang_major(&spec.cmd)?;
        let pd = run(Command::new(profdata()).arg("--version"))?;
        let pd = major_after(&pd, "LLVM version ")?;
        if pd != cc {
            return Err(format!("LUST_PROFDATA ({}) is LLVM {pd}, the compiler ({}) LLVM {cc}", profdata(), spec.cmd.join(" ")));
        }
        let bits = std::env::var("LUST_PGO_BITS").ok().and_then(|b| b.parse().ok()).unwrap_or(0);
        Pgo::load(Path::new(&path), bits, work, units).map(|p| Some(Mode::Use(p)))
    }

    /// Extra link flags: the profile runtime of an instrumented build.
    pub fn link_flags(&self) -> Vec<String> {
        match self {
            Mode::Gen => vec!["-fprofile-generate".into()],
            Mode::Use(_) => Vec::new(),
        }
    }

    /// The compile flags of the unit compiled as `file`. With a profile it first writes
    /// that unit's own profile into the work dir (a unit with no records gets none).
    pub fn unit_flags(&self, file: &str) -> Result<Vec<String>, String> {
        match self {
            Mode::Gen => Ok(vec!["-fprofile-generate".into()]),
            Mode::Use(p) => {
                let mut flags = p.pins.clone();
                if let Some(recs) = p.own.get(file).filter(|r| !r.is_empty()) {
                    let stem = file.strip_suffix(".c").unwrap_or(file);
                    let (txt, out) = (p.work.join(format!("{stem}.proftext")), p.work.join(format!("{stem}.profdata")));
                    std::fs::write(&txt, format!("{}{}\n\n", p.head, recs.join("\n\n"))).map_err(|e| format!("cannot write {}: {e}", txt.display()))?;
                    run(Command::new(profdata()).arg("merge").arg("-o").arg(&out).arg(&txt))?;
                    flags.push(format!("-fprofile-use={}", out.display()));
                }
                Ok(flags)
            }
        }
    }

    /// The profile part of the cache key of the unit compiled as `file` (`cc::unit_key`).
    pub fn key_part(&self, file: &str) -> String {
        match self {
            Mode::Gen => "gen".into(),
            Mode::Use(p) => {
                let own = p.own.get(file).map(|r| r.join("\n\n")).unwrap_or_default();
                digest(&[p.pins.join(" ").as_bytes(), own.as_bytes()])
            }
        }
    }

    /// For the build summary line.
    pub fn describe(&self) -> String {
        match self {
            Mode::Gen => "pgo instrumented".into(),
            Mode::Use(p) => format!("pgo {} records, {} runtime helpers, {} of fns not in this build", p.records, p.unowned, p.absent),
        }
    }
}

/// The compiler of an instrumented build for `spec`. zig ships no profile runtime, so for
/// zig `LUST_PGO_CC` names a clang of zig's LLVM major and that build targets the host,
/// where the training runs (the C is the release target's all the same). Any other
/// compiler must itself be a clang: the profiles are LLVM IR profiles.
pub fn gen_spec(spec: &CcSpec) -> Result<CcSpec, String> {
    let want = clang_major(&spec.cmd)?;
    if !super::is_zig(&spec.cmd[0]) {
        return Ok(spec.clone());
    }
    let words: Vec<String> = std::env::var("LUST_PGO_CC").unwrap_or_default().split_whitespace().map(str::to_string).collect();
    if words.is_empty() {
        return Err(format!(
            "an instrumented build (LUST_PGO_GEN=1) needs a profile runtime, and zig ships none: set LUST_PGO_CC to a clang of LLVM {want}, zig's version (scripts/pgo-llvm.sh installs one)"
        ));
    }
    let have = clang_major(&words)?;
    if have != want {
        return Err(format!("LUST_PGO_CC ({}) is LLVM {have}, zig cc LLVM {want}: its profile would not match", words.join(" ")));
    }
    Ok(CcSpec { triple: spec.triple.clone(), cxx: super::cxx_for(&words), cmd: words, statik: false, exe_suffix: spec.exe_suffix })
}

/// The LLVM major version of a clang command; an error for another compiler (gcc writes
/// its own profile format).
fn clang_major(cmd: &[String]) -> Result<u32, String> {
    let out = run(Command::new(&cmd[0]).args(&cmd[1..]).arg("--version"))?;
    let first = out.lines().next().unwrap_or("");
    if !first.contains("clang version ") {
        return Err(format!("PGO needs clang (LLVM IR profiles); `{}` says: {first}", cmd.join(" ")));
    }
    major_after(first, "clang version ")
}

/// The major version number after `marker` in `text` (`clang version 20.1.2 ...`).
fn major_after(text: &str, marker: &str) -> Result<u32, String> {
    text.split(marker)
        .nth(1)
        .and_then(|r| r.split(['.', ' ']).next())
        .and_then(|m| m.trim().parse().ok())
        .ok_or_else(|| format!("no version after `{}` in: {}", marker.trim(), text.lines().next().unwrap_or("")))
}

fn profdata() -> String {
    std::env::var("LUST_PROFDATA").unwrap_or_else(|_| "llvm-profdata".into())
}

fn run(cmd: &mut Command) -> Result<String, String> {
    let o = cmd.output().map_err(|e| format!("cannot run {:?}: {e}", cmd.get_program()))?;
    if !o.status.success() {
        return Err(format!("{:?} failed: {}", cmd.get_program(), String::from_utf8_lossy(&o.stderr)));
    }
    Ok(String::from_utf8_lossy(&o.stdout).into_owned())
}

fn digest(parts: &[&[u8]]) -> String {
    let (a, b) = crate::driver::cache::hash128(parts, 41);
    format!("{a:016x}{b:016x}")
}

impl Pgo {
    /// Reads `path` (an indexed profile), quantizes it to `bits`, pins the summary
    /// thresholds of the whole quantized profile, and splits the records by unit.
    fn load(path: &Path, bits: u32, work: &Path, units: &[(String, &str)]) -> Result<Pgo, String> {
        let text = run(Command::new(profdata()).args(["merge", "--text", "-o", "-"]).arg(path))?;
        let (head, mut records) = parse(&text);
        if bits > 0 {
            for r in records.values_mut() {
                *r = quantize(r, bits);
            }
        }
        std::fs::create_dir_all(work).map_err(|e| format!("cannot create {}: {e}", work.display()))?;
        let (txt, all) = (work.join("pgo-all.proftext"), work.join("pgo-all.profdata"));
        let mut names: Vec<&String> = records.keys().collect();
        names.sort();
        let body: Vec<&str> = names.iter().map(|n| records[*n].as_str()).collect();
        std::fs::write(&txt, format!("{head}{}\n\n", body.join("\n\n"))).map_err(|e| format!("cannot write {}: {e}", txt.display()))?;
        run(Command::new(profdata()).arg("merge").arg("-o").arg(&all).arg(&txt))?;
        let pins = pins(&run(Command::new(profdata()).args(["show", "--detailed-summary"]).arg(&all))?)?;
        let (own, unowned, absent) = split(&records, units);
        Ok(Pgo { head, own, pins, records: records.len(), unowned, absent, work: work.to_path_buf() })
    }
}

/// The records of each unit (by the file name it compiles as), sorted, and how many went
/// to the runtime unit for want of a visible definition and how many to no unit. A
/// static fn's record goes to its file, an external one to every unit that prints its
/// definition, else a `lust_*` one to the runtime unit (the one that includes system
/// headers; every unit when none does), else to none.
fn split(records: &HashMap<String, String>, units: &[(String, &str)]) -> (HashMap<String, Vec<String>>, usize, usize) {
    let mut owner: HashMap<&str, Vec<&str>> = HashMap::new();
    for (file, c) in units {
        for n in defined_externs(c) {
            owner.entry(n).or_default().push(file);
        }
    }
    let runtime: Vec<&str> = match units.iter().find(|(_, c)| c.contains("#include <")) {
        Some((file, _)) => vec![file],
        None => units.iter().map(|(f, _)| f.as_str()).collect(),
    };
    let mut own: HashMap<String, Vec<String>> = HashMap::new();
    let (mut unowned, mut absent) = (0, 0);
    for (name, r) in records {
        let files: Vec<&str> = match name.split_once(';') {
            Some((file, _)) => vec![file],
            None => match owner.get(name.as_str()) {
                Some(f) => f.clone(),
                None if name.starts_with("lust_") => {
                    unowned += 1;
                    runtime.clone()
                }
                None => {
                    absent += 1;
                    Vec::new()
                }
            },
        };
        for f in files {
            own.entry(f.to_string()).or_default().push(r.clone());
        }
    }
    for r in own.values_mut() {
        r.sort_unstable();
    }
    (own, unowned, absent)
}

/// An IR PGO text profile: the header (flag lines) and each record by name.
fn parse(text: &str) -> (String, HashMap<String, String>) {
    let mut head = String::new();
    let mut lines = text.lines().peekable();
    while let Some(l) = lines.peek() {
        if (l.starts_with('#') || l.starts_with(':')) && *l != "# Func Hash:" {
            head.push_str(l);
            head.push('\n');
            lines.next();
        } else {
            break;
        }
    }
    // A record starts with its name, which never begins with `#` or `:`.
    let mut records = HashMap::new();
    let mut cur: Vec<&str> = Vec::new();
    for l in lines.chain(std::iter::once("")) {
        if l.is_empty() {
            if let Some(name) = cur.first() {
                records.insert(name.to_string(), cur.join("\n"));
            }
            cur.clear();
        } else {
            cur.push(l);
        }
    }
    (head, records)
}

/// `r` with every counter and value-site count cut to `bits` significant bits.
fn quantize(r: &str, bits: u32) -> String {
    let q = |v: u64| if v < (1 << bits) { v } else { let s = 64 - v.leading_zeros() - bits; (v >> s) << s };
    let mut mode = "";
    let mut out: Vec<String> = Vec::new();
    for l in r.lines() {
        if l.starts_with('#') {
            mode = l;
            out.push(l.into());
        } else if mode == "# Counter Values:" && let Ok(v) = l.parse::<u64>() {
            out.push(q(v).to_string());
        } else if mode.contains("Value") && let Some((k, c)) = l.rsplit_once(':') && let Ok(v) = c.parse::<u64>() {
            out.push(format!("{k}:{}", q(v)));
        } else {
            out.push(l.into());
        }
    }
    out.join("\n")
}

/// The `-mllvm` flags that pin LLVM's summary thresholds (ProfileSummaryInfo) to those of
/// a whole profile (`llvm-profdata show --detailed-summary`): the hot and cold counts
/// (the 99% and 99.9999% cutoffs' minimum counts, rounded down to a power of 2), size
/// optimization by the cold count only, and the working-set flags (the hot cutoff's block
/// count against 12500 and 15000).
fn pins(show: &str) -> Result<Vec<String>, String> {
    let (mut hot, mut cold, mut blocks) = (None, None, 0u64);
    for l in show.lines() {
        // LLVM 18: "<n> blocks with count >= <min> account for <p> percentage of the total counts."
        // LLVM 20: "<n> blocks (<f>%) with count >= <min> account for <p>% of the total counts."
        let w: Vec<&str> = l.split_whitespace().collect();
        let at = |s: &str| w.iter().position(|x| *x == s);
        let (Some(ge), Some(f)) = (at(">="), at("for")) else { continue };
        if w.get(1) != Some(&"blocks") {
            continue;
        }
        let n = w[0].parse::<u64>().unwrap_or(0);
        let min = w.get(ge + 1).and_then(|m| m.parse::<u64>().ok()).unwrap_or(0);
        match w.get(f + 1).map(|p| p.trim_end_matches('%')) {
            Some("99") => (hot, blocks) = (Some(min), n),
            Some("99.9999") => cold = Some(min),
            _ => {}
        }
    }
    let (Some(hot), Some(cold)) = (hot, cold) else { return Err(format!("no detailed summary in llvm-profdata show output:\n{show}")) };
    let pow2 = |v: u64| if v == 0 { 0 } else { 1u64 << (63 - v.leading_zeros()) };
    let ws = |limit: u64| if blocks > limit { 0 } else { u32::MAX };
    Ok([
        format!("-profile-summary-hot-count={}", pow2(hot)),
        format!("-profile-summary-cold-count={}", pow2(cold)),
        "-pgso-cold-code-only=true".into(),
        format!("-profile-summary-huge-working-set-size-threshold={}", ws(15000)),
        format!("-profile-summary-large-working-set-size-threshold={}", ws(12500)),
    ]
    .into_iter()
    .flat_map(|f| ["-mllvm".to_string(), f])
    .collect())
}

/// The external functions unit `c` defines: an identifier that starts a column-0
/// declarator line and whose parameter list (over any number of lines) is followed by
/// a body. A prototype ends in `;` instead; a static function's record name carries
/// its file, so it is not listed.
pub fn defined_externs(c: &str) -> Vec<&str> {
    let b = c.as_bytes();
    let mut out = Vec::new();
    let mut at = 0;
    while at < b.len() {
        let end = c[at..].find('\n').map_or(b.len(), |k| at + k);
        let line = &c[at..end];
        let first = line.bytes().next().unwrap_or(b' ');
        let skip = ["static", "typedef", "struct", "union", "enum", "extern", "#"];
        if (first.is_ascii_alphabetic() || first == b'_') && !skip.iter().any(|s| line.starts_with(s)) {
            if let Some((name, open)) = declarator_name(line) {
                let mut depth = 0usize;
                let mut i = at + open;
                while i < b.len() {
                    match b[i] {
                        b'(' => depth += 1,
                        b')' => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                    i += 1;
                }
                if c.get(i + 1..).is_some_and(|rest| rest.trim_start().starts_with('{')) {
                    out.push(name);
                }
            }
        }
        at = end + 1;
    }
    out
}

/// The first identifier on `line` that is followed by `(` and is not an attribute or a
/// type operator, and the byte index of that `(`.
fn declarator_name(line: &str) -> Option<(&str, usize)> {
    let b = line.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i].is_ascii_alphabetic() || b[i] == b'_' {
            let s = i;
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            let id = &line[s..i];
            let mut j = i;
            while j < b.len() && b[j] == b' ' {
                j += 1;
            }
            if j < b.len() && b[j] == b'(' {
                if matches!(id, "__attribute__" | "__declspec" | "_Alignas" | "__typeof__" | "typeof" | "__asm__") {
                    // Skip the attribute's own parenthesized list.
                    let mut depth = 0usize;
                    while j < b.len() {
                        match b[j] {
                            b'(' => depth += 1,
                            b')' => {
                                depth -= 1;
                                if depth == 0 {
                                    break;
                                }
                            }
                            _ => {}
                        }
                        j += 1;
                    }
                    i = j + 1;
                    continue;
                }
                return Some((id, j));
            }
        } else {
            i += 1;
        }
    }
    None
}

/// A content-derived file name for a unit (the record names of its static functions
/// carry it): a hash of the external functions it defines, so it stays while its
/// member set does. None for a unit that defines none.
pub fn stable_name(c: &str) -> Option<String> {
    let mut ext = defined_externs(c);
    if ext.is_empty() {
        return None;
    }
    ext.sort_unstable();
    let (a, _) = crate::driver::cache::hash128(&[ext.join(",").as_bytes()], 43);
    Some(format!("x{a:016x}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn defined_externs_finds_definitions_not_prototypes() {
        let c = "int f(int a);\nint f(int a) {\n  return a;\n}\nstatic int g(void) { return 1; }\nRcI_A* tramp_1(O_A p1) { return 0; }\n__attribute__((noreturn)) void lust_die(const char *m,\n    int n)\n{\n}\nstruct S { int (*cb)(void); };\n  int h(void) {\n";
        assert_eq!(defined_externs(c), vec!["f", "tramp_1", "lust_die"]);
    }

    fn rec(n: &str, c: u64) -> String {
        format!("{n}\n# Func Hash:\n7\n# Num Counters:\n1\n# Counter Values:\n{c}")
    }

    /// A loaded profile of `records` (name, count) over `units`.
    fn split_mode(records: &[(&str, u64)], units: &[(&str, &str)]) -> Mode {
        let recs: HashMap<String, String> = records.iter().map(|(n, c)| (n.to_string(), rec(n, *c))).collect();
        let units: Vec<(String, &str)> = units.iter().map(|(f, c)| (f.to_string(), *c)).collect();
        let (own, unowned, absent) = split(&recs, &units);
        Mode::Use(Pgo { head: String::new(), own, pins: vec!["-mllvm".into(), "-x".into()], records: recs.len(), unowned, absent, work: PathBuf::new() })
    }

    #[test]
    fn a_unit_key_moves_only_with_its_own_records() {
        let units = [("u1.c", "int f(void) {\n}\nstatic int s(void) {\n}\n"), ("u2.c", "int g(void) {\n}\n"), ("u3.c", "#include <stdint.h>\nLUST_ABS(int8_t, i8)\n")];
        let mk = |f: u64, g: u64, s: u64, abs: u64| split_mode(&[("f", f), ("g", g), ("u1.c;s", s), ("lust_abs_i8", abs), ("f_gone", f + g)], &units);
        let base = mk(1, 2, 3, 4);
        assert_eq!(base.key_part("u2.c"), mk(9, 2, 9, 9).key_part("u2.c"), "others' records");
        assert_ne!(base.key_part("u2.c"), mk(1, 5, 3, 4).key_part("u2.c"), "own record");
        assert_ne!(base.key_part("u1.c"), mk(1, 2, 5, 4).key_part("u1.c"), "own static record");
        assert_ne!(base.key_part("u3.c"), mk(1, 2, 3, 5).key_part("u3.c"), "the runtime unit owns what no unit prints");
        assert_eq!(base.key_part("u1.c"), mk(1, 2, 3, 5).key_part("u1.c"));
        // `f_gone` (no unit defines it) moves no key, the runtime unit's included.
        let Mode::Use(p) = &base else { unreachable!() };
        assert_eq!((p.unowned, p.absent), (1, 1));
    }

    #[test]
    fn llvm_majors_from_version_lines() {
        let zig = "clang version 20.1.2 (https://github.com/ziglang/zig-bootstrap 7ef74e6)";
        assert_eq!(major_after(zig, "clang version "), Ok(20));
        assert_eq!(major_after("Ubuntu clang version 20.1.8 (++20250708)", "clang version "), Ok(20));
        assert_eq!(major_after("Ubuntu LLVM version 20.1.8\n  Optimized build.", "LLVM version "), Ok(20));
        assert_eq!(major_after("LLVM (http://llvm.org/):\n  LLVM version 18.1.3\n", "LLVM version "), Ok(18));
        assert!(major_after("gcc (Ubuntu 13.2.0) 13.2.0", "clang version ").is_err());
    }

    #[test]
    fn quantize_keeps_small_counts_and_cuts_low_bits() {
        let r = "f\n# Func Hash:\n12345\n# Num Counters:\n2\n# Counter Values:\n5\n1000\n# Num Value Kinds:\n1\n# ValueKind = IPVK_IndirectCallTarget:\n0\n# NumValueSites:\n1\n1\ng:1000";
        let q = quantize(r, 3);
        assert!(q.contains("# Func Hash:\n12345\n"), "the hash stays");
        assert!(q.contains("\n5\n896\n"), "{q}");
        assert!(q.ends_with("g:896"), "{q}");
    }

    #[test]
    fn pins_read_llvm_20_summaries() {
        let show = "Detailed summary:\n21764 blocks (0.63%) with count >= 32768 account for 99% of the total counts.\n129141 blocks (3.71%) with count >= 4 account for 99.9999% of the total counts.\n";
        let p = pins(show).unwrap();
        assert!(p.contains(&"-profile-summary-hot-count=32768".to_string()), "{p:?}");
        assert!(p.contains(&"-profile-summary-cold-count=4".to_string()), "{p:?}");
        assert!(p.contains(&"-profile-summary-huge-working-set-size-threshold=0".to_string()), "{p:?}");
    }

    #[test]
    fn pins_read_the_hot_and_cold_cutoffs() {
        let show = "Detailed summary:\n20000 blocks with count >= 40960 account for 99 percentage of the total counts.\n90000 blocks with count >= 10 account for 99.9999 percentage of the total counts.\n";
        let p = pins(show).unwrap();
        assert!(p.contains(&"-profile-summary-hot-count=32768".to_string()), "{p:?}");
        assert!(p.contains(&"-profile-summary-cold-count=8".to_string()), "{p:?}");
        assert!(p.contains(&"-profile-summary-huge-working-set-size-threshold=0".to_string()), "{p:?}");
    }
}
