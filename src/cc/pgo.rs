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
// the definitions it prints (`defined_externs`), and only those, so its key moves only
// with its own fns' records. A unit with `#include`s (the runtime, mimalloc) makes some
// fns with macros (`LUST_ABS(int8_t, i8)`), so its definitions come from its
// preprocessed text. A record no unit defines is of a fn this build does not have (a
// profile from an older state, or a `lust_*` fn only inline copies held) and goes to no
// unit.
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
    /// Each unit's own records, sorted, by the file name the unit compiles as.
    own: HashMap<String, Vec<String>>,
    /// The flags that pin the summary thresholds to the whole profile's.
    pins: Vec<String>,
    records: usize,
    /// Records of macro-made fns: only a preprocessed text shows their definition.
    helpers: usize,
    /// Other records no unit defines (fns this build does not have): in no profile.
    absent: usize,
    /// The quantized profile and pins came from the last build's work dir (`load`).
    kept: bool,
    /// The whole quantized profile (`pgo-all.profdata`) every unit with records compiles
    /// against, and its digest (the memo key).
    all: PathBuf,
    key: String,
}

impl Mode {
    /// The mode `LUST_PGO_GEN` / `LUST_PGO_USE` ask for, or None. `units` are (file name
    /// the unit compiles as, C text).
    pub fn from_env(spec: &CcSpec, work: &Path, units: &[(String, &str, Option<&[u8]>)]) -> Result<Option<Mode>, String> {
        if std::env::var_os("LUST_PGO_GEN").is_some_and(|v| v == "1") {
            return Ok(Some(Mode::Gen));
        }
        let Some(path) = std::env::var_os("LUST_PGO_USE") else { return Ok(None) };
        // The profile format and the fns' CFG hashes are those of one LLVM major.
        let cc = clang_major(&spec.cmd)?;
        let tool = run(Command::new(profdata()).arg("--version"))?;
        let pd = major_after(&tool, "LLVM version ")?;
        if pd != cc {
            return Err(format!("LUST_PROFDATA ({}) is LLVM {pd}, the compiler ({}) LLVM {cc}", profdata(), spec.cmd.join(" ")));
        }
        let bits = std::env::var("LUST_PGO_BITS").ok().and_then(|b| b.parse().ok()).unwrap_or(0);
        Pgo::load(Path::new(&path), bits, work, &tool, &unit_defs(units)).map(|p| Some(Mode::Use(p)))
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
        let nopre = no_preinline().then_some(["-mllvm".to_string(), "-disable-preinline".to_string()]).into_iter().flatten();
        match self {
            Mode::Gen => Ok(std::iter::once("-fprofile-generate".to_string()).chain(nopre).collect()),
            Mode::Use(p) => {
                let mut flags = p.pins.clone();
                flags.extend(nopre);
                // A unit with records reads the whole profile: clang takes only the records of
                // its module's fns, and the pins hold the summary to the whole profile's, so
                // the object is the one its own records would give, with no per-unit profile
                // to write and merge. Its key still holds only its own records (`key_part`).
                if p.own.get(file).is_some_and(|r| !r.is_empty()) {
                    flags.push(format!("-fprofile-use={}", p.all.display()));
                    // zig cc caches a compile by its source and args, not by this file: the
                    // profile's digest in the args keeps another profile at this path from
                    // getting the object of the last one.
                    flags.push(format!("-DLUST_PROFILE_DIGEST={}", p.key));
                }
                Ok(flags)
            }
        }
    }

    /// The profile part of the cache key of the unit compiled as `file` (`cc::unit_key`).
    pub fn key_part(&self, file: &str) -> String {
        let nopre = if no_preinline() { " nopre" } else { "" };
        match self {
            Mode::Gen => format!("gen{nopre} {STATIC_FILE}"),
            Mode::Use(p) => {
                let own = p.own.get(file).map(|r| r.join("\n\n")).unwrap_or_default();
                digest(&[p.pins.join(" ").as_bytes(), nopre.as_bytes(), STATIC_FILE.as_bytes(), own.as_bytes()])
            }
        }
    }

    /// For the build summary line.
    pub fn describe(&self) -> String {
        match self {
            Mode::Gen => "pgo instrumented".into(),
            Mode::Use(p) => format!("pgo {} records{}, {} runtime helpers, {} of fns not in this build", p.records, if p.kept { " (kept)" } else { "" }, p.helpers, p.absent),
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

/// The source file name every PGO unit compiles under (a C unit as `<work>/<unit>.d/lust.c`,
/// an LLVM unit by its IR's `source_filename`). PGO names an internal fn `<source name>;<fn>`;
/// the unit's own name hashes its members, so a merge that moved one fn would rename the
/// records of every static fn and helper in the unit. `split` owns these records by fn name.
pub(crate) const STATIC_FILE: &str = "lust.c";

/// `LUST_PGO_PREINLINE=0`: neither the instrumented nor the use build runs LLVM's PGO
/// pre-inliner. It inlines small callees before each fn's CFG hash is taken, so a caller's
/// record stops matching when a callee it inlined changes (a cross-unit copy, a merge that
/// edits the callee); without it a record follows its own fn only.
pub fn no_preinline() -> bool {
    std::env::var("LUST_PGO_PREINLINE").is_ok_and(|v| v == "0")
}

fn digest(parts: &[&[u8]]) -> String {
    let (a, b) = crate::driver::cache::hash128(parts, 41);
    format!("{a:016x}{b:016x}")
}

impl Pgo {
    /// Reads `path` (an indexed profile), quantizes it to `bits`, pins the summary
    /// thresholds of the whole quantized profile, and splits the records by unit. `tool` is
    /// the `llvm-profdata --version` text.
    fn load(path: &Path, bits: u32, work: &Path, tool: &str, defs: &UnitDefs) -> Result<Pgo, String> {
        std::fs::create_dir_all(work).map_err(|e| format!("cannot create {}: {e}", work.display()))?;
        let (txt, all, memo) = (work.join("pgo-all.proftext"), work.join("pgo-all.profdata"), work.join("pgo-all.memo"));
        // The quantized profile and its pins depend only on the profile, `bits` and the
        // tool: a warm build of the same ones (a pinned profile, every merge) reads them
        // back from the last build's work dir instead of running llvm-profdata three times
        // (~2.8 s for tsgo's). `memo` holds their digest and the pins, and is written last.
        let bytes = std::fs::read(path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        let key = digest(&[&bytes, &bits.to_le_bytes(), tool.as_bytes()]);
        let kept = std::fs::read_to_string(&memo)
            .ok()
            .and_then(|m| m.strip_prefix(&format!("{key}\n")).map(|pins| pins.split_whitespace().map(str::to_string).collect::<Vec<_>>()))
            .and_then(|pins| std::fs::read_to_string(&txt).ok().map(|t| (parse(&t), pins)));
        let hit = kept.is_some();
        let ((_, records), pins) = match kept {
            Some(k) => k,
            None => {
                let _ = std::fs::remove_file(&memo);
                let text = run(Command::new(profdata()).args(["merge", "--text", "-o", "-"]).arg(path))?;
                let (head, mut records) = parse(&text);
                if bits > 0 {
                    for r in records.values_mut() {
                        *r = quantize(r, bits);
                    }
                }
                let mut names: Vec<&String> = records.keys().collect();
                names.sort();
                let body: Vec<&str> = names.iter().map(|n| records[*n].as_str()).collect();
                std::fs::write(&txt, format!("{head}{}\n\n", body.join("\n\n"))).map_err(|e| format!("cannot write {}: {e}", txt.display()))?;
                run(Command::new(profdata()).arg("merge").arg("-o").arg(&all).arg(&txt))?;
                let pins = pins(&run(Command::new(profdata()).args(["show", "--detailed-summary"]).arg(&all))?)?;
                std::fs::write(&memo, format!("{key}\n{}\n", pins.join(" "))).map_err(|e| format!("cannot write {}: {e}", memo.display()))?;
                ((head, records), pins)
            }
        };
        if hit && !all.exists() {
            run(Command::new(profdata()).arg("merge").arg("-o").arg(&all).arg(&txt))?;
        }
        let (own, helpers, absent) = split(&records, defs);
        Ok(Pgo { own, pins, records: records.len(), helpers, absent, kept: hit, all, key })
    }
}

/// The external fns each unit defines, by the file name it compiles as, the names only a
/// preprocessed text shows (macro-made), and the static fns each unit defines.
struct UnitDefs {
    units: Vec<(String, Vec<String>)>,
    macro_made: std::collections::HashSet<String>,
    statics: Vec<(String, Vec<String>)>,
}

/// The definitions of each unit (`defined_externs`), on every thread: of its preprocessed
/// text when the caller has one (a unit with `#include`s; `cc::preprocessed`, else its text
/// as given), so the fns its macros make count as its own.
fn unit_defs(units: &[(String, &str, Option<&[u8]>)]) -> UnitDefs {
    let per: Vec<(String, Vec<String>, Vec<String>, Vec<String>)> = crate::pool::par_map(units, |(file, c, pre)| {
        let raw: std::collections::HashSet<&str> = defined_externs(c).into_iter().collect();
        let pre = pre.map(String::from_utf8_lossy);
        let names: Vec<String> = match &pre {
            Some(pre) => defined_externs(pre).into_iter().map(str::to_string).collect(),
            None => raw.iter().map(|n| n.to_string()).collect(),
        };
        let made = names.iter().filter(|n| !raw.contains(n.as_str())).cloned().collect();
        let statics = defined_statics(pre.as_deref().unwrap_or(c)).into_iter().map(str::to_string).collect();
        (file.clone(), names, made, statics)
    });
    let mut macro_made = std::collections::HashSet::new();
    let mut units = Vec::with_capacity(per.len());
    let mut statics = Vec::with_capacity(per.len());
    for (file, names, made, st) in per {
        macro_made.extend(made);
        statics.push((file.clone(), st));
        units.push((file, names));
    }
    UnitDefs { units, macro_made, statics }
}

/// The records of each unit (by the file name it compiles as), sorted, how many are of
/// macro-made fns, and how many external ones went to no unit. An external fn's record goes
/// to every unit that defines it, a static fn's (`STATIC_FILE;<fn>`) to every unit that
/// defines a static fn of that name; a static record of another file goes to that file.
fn split(records: &HashMap<String, String>, defs: &UnitDefs) -> (HashMap<String, Vec<String>>, usize, usize) {
    let mut owner: HashMap<&str, Vec<&str>> = HashMap::new();
    for (file, names) in &defs.units {
        for n in names {
            owner.entry(n).or_default().push(file);
        }
    }
    let mut static_owner: HashMap<&str, Vec<&str>> = HashMap::new();
    for (file, names) in &defs.statics {
        for n in names {
            static_owner.entry(n).or_default().push(file);
        }
    }
    let mut own: HashMap<String, Vec<String>> = HashMap::new();
    let (mut helpers, mut absent) = (0, 0);
    for (name, r) in records {
        let files: Vec<&str> = match name.split_once(';') {
            Some((STATIC_FILE, f)) => static_owner.get(f).cloned().unwrap_or_default(),
            Some((file, _)) => vec![file],
            None => match owner.get(name.as_str()) {
                Some(f) => {
                    helpers += defs.macro_made.contains(name) as usize;
                    f.clone()
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
    (own, helpers, absent)
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
/// a body. A prototype ends in `;` instead; a static function's record is owned by name
/// (`defined_statics`), so it is not listed.
pub fn defined_externs(c: &str) -> Vec<&str> {
    definitions(c, false)
}

/// The static functions `c` defines, as `defined_externs` finds the external ones.
pub fn defined_statics(c: &str) -> Vec<&str> {
    definitions(c, true)
}

fn definitions(c: &str, statics: bool) -> Vec<&str> {
    let b = c.as_bytes();
    let mut out = Vec::new();
    let mut at = 0;
    while at < b.len() {
        let end = c[at..].find('\n').map_or(b.len(), |k| at + k);
        let line = &c[at..end];
        let first = line.bytes().next().unwrap_or(b' ');
        let skip = ["static", "typedef", "struct", "union", "enum", "extern", "#"];
        let wanted = if statics { line.starts_with("static ") } else { !skip.iter().any(|s| line.starts_with(s)) };
        if (first.is_ascii_alphabetic() || first == b'_') && wanted {
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

    /// A loaded profile of `records` (name, count) over units that define `defs` (file,
    /// fn names; `macro_made` of them only a preprocessed text shows).
    fn split_mode(records: &[(&str, u64)], defs: &[(&str, &[&str])], macro_made: &[&str]) -> Mode {
        let recs: HashMap<String, String> = records.iter().map(|(n, c)| (n.to_string(), rec(n, *c))).collect();
        let defs = UnitDefs {
            units: defs.iter().map(|(f, ns)| (f.to_string(), ns.iter().map(|n| n.to_string()).collect())).collect(),
            macro_made: macro_made.iter().map(|n| n.to_string()).collect(),
            statics: Vec::new(),
        };
        let (own, helpers, absent) = split(&recs, &defs);
        Mode::Use(Pgo { own, pins: vec!["-mllvm".into(), "-x".into()], records: recs.len(), helpers, absent, kept: false, all: PathBuf::new(), key: String::new() })
    }

    /// A static fn's record (`STATIC_FILE;<fn>`) goes to every unit that defines a static fn
    /// of that name, whatever the unit is called: a merge that renames a unit keeps it.
    #[test]
    fn a_static_record_follows_its_fn_not_its_unit() {
        let recs: HashMap<String, String> =
            [("lust.c;lh_aa_0", 5), ("lust.c;lust_mix", 2), ("x1.c;old", 3)].iter().map(|(n, c)| (n.to_string(), rec(n, *c))).collect();
        let st = |f: &str, ns: &[&str]| (f.to_string(), ns.iter().map(|n| n.to_string()).collect::<Vec<_>>());
        let defs = UnitDefs { units: Vec::new(), macro_made: Default::default(), statics: vec![st("x9.ll", &["lh_aa_0", "lust_mix"]), st("x7.c", &["lust_mix"])] };
        let (own, _, absent) = split(&recs, &defs);
        assert_eq!(own["x9.ll"].len(), 2);
        assert!(own["x7.c"][0].starts_with("lust.c;lust_mix"));
        assert!(own["x1.c"][0].starts_with("x1.c;old"), "another file's static record stays with that file");
        assert_eq!(absent, 0);
        assert_eq!(defined_statics("static inline int lust_mix(int a) {\n}\nstatic int g;\nint f(void) {\n}\n"), vec!["lust_mix"]);
    }

    /// A unit's key moves only with the records of the fns it defines (the runtime unit's
    /// macro-made ones included), never with a record no unit defines: the runtime unit
    /// keeps its key when another unit's inline copy of a `lust_*` fn comes or goes.
    #[test]
    fn a_unit_key_moves_only_with_its_own_records() {
        let with_copy: [(&str, &[&str]); 3] = [("u1.c", &["f", "lust_copy"]), ("u2.c", &["g"]), ("u3.c", &["lust_abs_i8"])];
        let without: [(&str, &[&str]); 3] = [("u1.c", &["f"]), ("u2.c", &["g"]), ("u3.c", &["lust_abs_i8"])];
        let mk = |defs: &[(&str, &[&str])], f: u64, g: u64, s: u64, abs: u64| {
            split_mode(&[("f", f), ("g", g), ("u1.c;s", s), ("lust_abs_i8", abs), ("lust_copy", 7), ("f_gone", f + g)], defs, &["lust_abs_i8"])
        };
        let base = mk(&with_copy, 1, 2, 3, 4);
        assert_eq!(base.key_part("u2.c"), mk(&with_copy, 9, 2, 9, 9).key_part("u2.c"), "others' records");
        assert_ne!(base.key_part("u2.c"), mk(&with_copy, 1, 5, 3, 4).key_part("u2.c"), "own record");
        assert_ne!(base.key_part("u1.c"), mk(&with_copy, 1, 2, 5, 4).key_part("u1.c"), "own static record");
        assert_ne!(base.key_part("u3.c"), mk(&with_copy, 1, 2, 3, 5).key_part("u3.c"), "own macro-made record");
        assert_eq!(base.key_part("u1.c"), mk(&with_copy, 1, 2, 3, 5).key_part("u1.c"));
        assert_eq!(base.key_part("u3.c"), mk(&without, 1, 2, 3, 4).key_part("u3.c"), "an inline copy elsewhere comes or goes");
        // `f_gone` and, with no copy left, `lust_copy` (no unit defines them) go to no unit.
        let Mode::Use(p) = &mk(&without, 1, 2, 3, 4) else { unreachable!() };
        assert_eq!((p.helpers, p.absent), (1, 2));
    }

    /// A unit with `#include`s is read through the preprocessor: the fns its macros make
    /// are its own.
    #[test]
    fn macro_made_fns_belong_to_their_unit() {
        let Ok(spec) = super::super::spec_for(crate::protocol::host_triple()) else { return };
        let c = "#include <stddef.h>\n#define MK(n) int lust_##n(void) { return 0; }\nMK(a)\nint visible(void) {\n  return 1;\n}\n";
        let pre = super::super::preprocessed(c, &spec.cmd, &super::super::cflags(false), false);
        let d = unit_defs(&[("u2.c".to_string(), c, pre.as_deref())]);
        let mut names = d.units[0].1.clone();
        names.sort();
        assert_eq!(names, vec!["lust_a", "visible"]);
        assert_eq!(d.macro_made, ["lust_a".to_string()].into_iter().collect());
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
