// cfg evaluation and stripping (docs/ARCH.md section 1.6).
//
// The cfg environment is a fixed set per crate session: target values from a
// small built-in table, per-unit features, and the profile flags. Predicates
// arrive as the raw token trees an attribute stored (`#[cfg(...)]` contents,
// or a Cargo dependency's target string re-lexed by cargo.rs). Evaluation is
// total: a known name with an unknown value is false, an unknown *name* is
// error L0520, because silently dropping a module would change the program.
use crate::ast::{Attr, AttrInput};
use crate::diag::{Diag, Span};
use crate::intern::Interner;
use crate::lexer::{Tok, TokenTree};
use crate::protocol::ProfileFlags;
use std::collections::BTreeSet;

/// Every cfg name lust knows (the rustc well-known list of section 1.6, plus
/// `feature`). Any other name in a predicate is L0520. `lust_dev` is known
/// only for shipped crates; in user code it takes the unknown-name error.
pub const KNOWN_CFG_NAMES: &[&str] = &[
    "all", "any", "not", "feature", "target_arch", "target_os", "target_vendor", "target_family", "target_env", "target_abi",
    "target_endian", "target_pointer_width", "target_has_atomic", "target_has_atomic_equal_alignment", "target_feature",
    "target_thread_local", "unix", "windows", "panic", "overflow_checks", "debug_assertions", "test", "docsrs", "fuzzing",
    "miri", "target_has_atomic_load_store", "target_os_version", "target_abi_version",
];

/// One crate session's cfg environment. Flags are names that are on
/// (`unix`); pairs are `name = "value"` facts (`target_os = "linux"`). A pair
/// name may repeat (`target_family`, `target_feature`, `target_has_atomic`).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct CfgEnv {
    pub flags: BTreeSet<String>,
    pub pairs: Vec<(String, String)>,
    pub features: BTreeSet<String>,
    /// Custom cfg names declared by build-script output (recorded by
    /// `lust port prepare`). They are known names; their values here are
    /// flags or pairs like the rest.
    pub custom_names: BTreeSet<String>,
    /// True only while a shipped std or adapter crate resolves: `lust_dev`
    /// is then a known, true flag (section 1.6).
    pub allow_lust_dev: bool,
}

impl CfgEnv {
    /// The environment for one target triple (empty means the host), one
    /// per-unit feature set, the test-crate flag, and the profile. Tier 1
    /// targets and `wasm32-wasip1` (classification only) are in the table;
    /// another triple gets the parts its name proves (arch, pointer width
    /// for `wasm32`/`64` suffix arches) and nothing else, never a guess at
    /// a value that would change code silently beyond what the name says.
    pub fn new(triple: &str, features: &[String], test: bool, profile: ProfileFlags) -> CfgEnv {
        let triple = if triple.is_empty() { crate::protocol::host_triple() } else { triple };
        let mut env = CfgEnv { features: features.iter().cloned().collect(), ..Default::default() };
        let parts: Vec<&str> = triple.split('-').collect();
        let arch = parts.first().copied().unwrap_or("");
        env.pair("target_arch", arch);
        env.pair("target_endian", if matches!(arch, "s390x" | "powerpc" | "powerpc64" | "sparc64" | "mips" | "mips64") { "big" } else { "little" });
        env.pair("target_pointer_width", if arch.contains("64") || arch == "wasm64" { "64" } else { "32" });
        // vendor-os[-env[-abi]] after the arch, when the triple has them.
        // Two-part triples (`wasm32-wasip1`) carry the os in the vendor
        // slot; rustc reports vendor "unknown" for them.
        let (vendor_os, env_abi_at) = if parts.len() == 2 {
            (Some(("unknown", parts[1])), 2usize)
        } else {
            (parts.get(1).zip(parts.get(2)).map(|(&v, &o)| (v, o)), 3usize)
        };
        if let Some((vendor, os)) = vendor_os {
            env.pair("target_vendor", vendor);
            let (os_name, family) = match os {
                "darwin" => ("macos", "unix"),
                "windows" => ("windows", "windows"),
                "wasip1" | "wasip2" | "wasi" => ("wasi", "wasm"),
                "emscripten" => ("emscripten", "unix"),
                other => (other, "unix"),
            };
            env.pair("target_os", os_name);
            env.pair("target_family", family);
            if family == "unix" {
                env.flags.insert("unix".into());
            }
            if family == "windows" {
                env.flags.insert("windows".into());
            }
            let env_part = parts.get(env_abi_at).copied().unwrap_or("");
            // `gnu`/`msvc`/`musl` may carry an ABI suffix (`gnueabi`); keep the
            // written value, and the abi as its own pair only when a 5th part
            // exists (for example `x86_64-pc-windows-msvc` has empty abi).
            env.pair("target_env", env_part);
            env.pair("target_abi", parts.get(env_abi_at + 1).copied().unwrap_or(""));
        }
        // Atomics: the tier-1 table. Widths up to the pointer width, plus
        // 64 on x86_64/aarch64 (both are 64-bit pointer targets here).
        if arch != "wasm32" {
            for w in ["8", "16", "32", "64", "ptr"] {
                env.pair("target_has_atomic", w);
                env.pair("target_has_atomic_load_store", w);
                env.pair("target_has_atomic_equal_alignment", w);
            }
        }
        if arch == "x86_64" {
            for f in ["fxsr", "sse", "sse2"] {
                env.pair("target_feature", f);
            }
        }
        if !arch.starts_with("wasm") {
            env.flags.insert("target_thread_local".into());
        }
        env.pair("panic", if profile.panic_abort { "abort" } else { "unwind" });
        if profile.overflow_checks {
            env.flags.insert("overflow_checks".into());
        }
        if profile.debug_assertions {
            env.flags.insert("debug_assertions".into());
        }
        if test {
            env.flags.insert("test".into());
        }
        env
    }

    fn pair(&mut self, name: &str, value: &str) {
        self.pairs.push((name.to_string(), value.to_string()));
    }

    /// True when `name` may appear in a predicate at all (section 1.6).
    pub fn knows(&self, name: &str) -> bool {
        KNOWN_CFG_NAMES.contains(&name)
            || self.custom_names.contains(name)
            || (self.allow_lust_dev && name == "lust_dev")
            || self.pairs.iter().any(|(n, _)| n == name)
    }

    /// The fingerprint input of this environment: every flag, pair, and
    /// feature in sorted order. Session keys and cache keys hash this text.
    pub fn describe(&self) -> String {
        let mut parts: Vec<String> = self.flags.iter().cloned().collect();
        let mut pairs: Vec<String> = self.pairs.iter().map(|(n, v)| format!("{n}={v}")).collect();
        pairs.sort();
        parts.extend(pairs);
        parts.extend(self.features.iter().map(|f| format!("feature={f}")));
        parts.join(" ")
    }

    /// Evaluates one predicate from its token trees. String tokens index
    /// `strings` (the owning AST's string table). A syntax shape outside
    /// the cfg grammar is L0001; an unknown name is L0520.
    pub fn eval(&self, trees: &[TokenTree], strings: &[String], interner: &Interner, span: Span) -> Result<bool, Diag> {
        let mut pos = 0;
        let v = self.pred(trees, &mut pos, strings, interner, span)?;
        if pos != trees.len() {
            return Err(Diag::new("L0001", span, "malformed `#[cfg]` predicate", "Write `#[cfg(name)]`, `#[cfg(name = \"value\")]`, or `all`/`any`/`not` combinations."));
        }
        Ok(v)
    }

    fn pred(&self, trees: &[TokenTree], pos: &mut usize, strings: &[String], interner: &Interner, span: Span) -> Result<bool, Diag> {
        let name_of = |trees: &[TokenTree], at: usize| -> Option<(String, Span)> {
            match trees.get(at) {
                Some(TokenTree::Token(t)) => match t.tok {
                    Tok::Ident(s) => Some((interner.get(s).to_string(), t.span)),
                    Tok::True => Some(("true".into(), t.span)),
                    Tok::False => Some(("false".into(), t.span)),
                    _ => None,
                },
                _ => None,
            }
        };
        let Some((name, name_span)) = name_of(trees, *pos) else {
            return Err(Diag::new("L0001", span, "malformed `#[cfg]` predicate", "Write `#[cfg(name)]`, `#[cfg(name = \"value\")]`, or `all`/`any`/`not` combinations."));
        };
        *pos += 1;
        // Combinators: `all(...)`, `any(...)`, `not(...)`.
        if matches!(name.as_str(), "all" | "any" | "not") {
            let Some(TokenTree::Delim(_, inner, _)) = trees.get(*pos) else {
                return Err(Diag::new("L0001", name_span, format!("`{name}` in a cfg predicate needs `(...)`"), "Write `all(a, b)`, `any(a, b)`, or `not(a)`."));
            };
            let inner = inner.clone();
            *pos += 1;
            let mut values = Vec::new();
            let mut ip = 0;
            while ip < inner.len() {
                values.push(self.pred(&inner, &mut ip, strings, interner, span)?);
                if matches!(inner.get(ip), Some(TokenTree::Token(t)) if t.tok == Tok::Comma) {
                    ip += 1;
                }
            }
            return Ok(match name.as_str() {
                "all" => values.iter().all(|v| *v),
                "any" => values.iter().any(|v| *v),
                _ => values.len() == 1 && !values[0],
            });
        }
        // `name = "value"` form.
        if matches!(trees.get(*pos), Some(TokenTree::Token(t)) if t.tok == Tok::Eq) {
            let value = match trees.get(*pos + 1) {
                Some(TokenTree::Token(t)) => match t.tok {
                    Tok::Str(i) => strings.get(i as usize).cloned().unwrap_or_default(),
                    Tok::Ident(s) => interner.get(s).to_string(),
                    _ => String::new(),
                },
                _ => String::new(),
            };
            *pos += 2;
            if name == "feature" {
                return Ok(self.features.contains(&value));
            }
            if !self.knows(&name) {
                return Err(unknown_cfg(&name, name_span));
            }
            return Ok(self.pairs.iter().any(|(n, v)| *n == name && *v == value));
        }
        // Bare `name` form.
        match name.as_str() {
            "true" => Ok(true),
            "false" => Ok(false),
            _ if !self.knows(&name) => Err(unknown_cfg(&name, name_span)),
            _ => Ok(self.flags.contains(&name) || (self.allow_lust_dev && name == "lust_dev")),
        }
    }
}

/// The L0520 diagnostic for a cfg name lust does not know.
fn unknown_cfg(name: &str, span: Span) -> Diag {
    Diag::new(
        "L0520",
        span,
        format!("unknown cfg name `{name}`"),
        "Declare the cfg in build script output (`cargo::rustc-cfg`), or remove it. Lust knows the standard target, feature, and profile cfg names.",
    )
}

/// True when an attribute list stays in the program: every `#[cfg(...)]`
/// holds. `#[cfg_attr(...)]` does not gate the item; see `expand_cfg_attr`.
pub fn attrs_enabled(env: &CfgEnv, attrs: &[Attr], strings: &[String], interner: &Interner) -> Result<bool, Diag> {
    for a in attrs {
        if a.path.len() == 1 && interner.get(a.path[0].name) == "cfg"
            && let AttrInput::List(_, trees) = &a.input
            && !env.eval(trees, strings, interner, a.span)?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Rewrites `#[cfg_attr(pred, attr...)]` entries in an attribute list: a
/// true predicate splices the inner attributes in, a false one drops the
/// entry. Inner attributes are rebuilt from their token trees in the two
/// written forms (`name`, `name(...)`, `name = lit`); anything else keeps
/// its raw trees under a `List` input so later readers see the tokens.
pub fn expand_cfg_attr(env: &CfgEnv, attrs: &mut Vec<Attr>, strings: &[String], interner: &Interner) -> Result<(), Diag> {
    let mut out = Vec::with_capacity(attrs.len());
    for a in attrs.drain(..) {
        let is_cfg_attr = a.path.len() == 1 && interner.get(a.path[0].name) == "cfg_attr";
        if !is_cfg_attr {
            out.push(a);
            continue;
        }
        let AttrInput::List(_, trees) = &a.input else {
            out.push(a);
            continue;
        };
        // The predicate is the trees up to the first top-level comma.
        let comma = trees.iter().position(|t| matches!(t, TokenTree::Token(tok) if tok.tok == Tok::Comma));
        let Some(comma) = comma else {
            return Err(Diag::new("L0001", a.span, "malformed `#[cfg_attr]`", "Write `#[cfg_attr(predicate, attribute)]`."));
        };
        if !env.eval(&trees[..comma], strings, interner, a.span)? {
            continue;
        }
        // Split the rest into attributes at top-level commas. Each piece is
        // a path with an optional `(...)` or `= lit` tail.
        let mut start = comma + 1;
        while start < trees.len() {
            let mut end = start;
            while end < trees.len() && !matches!(&trees[end], TokenTree::Token(t) if t.tok == Tok::Comma) {
                end += 1;
            }
            if end > start {
                out.push(attr_from_trees(&trees[start..end], a.span, a.style));
            }
            start = end + 1;
        }
    }
    *attrs = out;
    Ok(())
}

/// One attribute rebuilt from cfg_attr token trees.
fn attr_from_trees(trees: &[TokenTree], span: Span, style: crate::ast::AttrStyle) -> Attr {
    let mut path = Vec::new();
    let mut i = 0;
    while let Some(TokenTree::Token(t)) = trees.get(i) {
        match t.tok {
            Tok::Ident(s) => {
                path.push(crate::ast::PathSeg::plain(s));
                i += 1;
                if matches!(trees.get(i), Some(TokenTree::Token(t2)) if t2.tok == Tok::PathSep) {
                    i += 1;
                } else {
                    break;
                }
            }
            _ => break,
        }
    }
    let input = match trees.get(i) {
        Some(TokenTree::Delim(d, inner, _)) => AttrInput::List(*d, inner.clone()),
        Some(_) => AttrInput::List(crate::lexer::Delim::Bracket, trees[i..].to_vec()),
        None => AttrInput::None,
    };
    Attr { style, path, input, span }
}

/// Evaluates raw predicate trees from the scan outline (a `mod` declaration's
/// cfg), where the string table is the lexed file's.
pub fn outline_enabled(env: &CfgEnv, cfgs: &[Vec<TokenTree>], strings: &[String], interner: &Interner, span: Span) -> Result<bool, Diag> {
    for trees in cfgs {
        if !env.eval(trees, strings, interner, span)? {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::FileId;
    use crate::lexer;

    /// Lexes `#[cfg(<pred>)]` and evaluates the predicate trees.
    fn eval_pred(env: &CfgEnv, pred: &str) -> Result<bool, Diag> {
        let interner = Interner::default();
        let src = format!("#[cfg({pred})]\nfn f() {{}}");
        let lexed = lexer::lex(&src, FileId(0), 0, &interner).unwrap();
        let o = crate::scan::outline(&lexed, &interner);
        let _ = o;
        // Reuse the outline's cfg capture path through a mod decl instead.
        let src = format!("#[cfg({pred})]\nmod m;");
        let lexed = lexer::lex(&src, FileId(0), 0, &interner).unwrap();
        let o = crate::scan::outline(&lexed, &interner);
        outline_enabled(env, &o.mods[0].cfg, &lexed.strings, &interner, Span::default())
    }

    #[test]
    fn target_table_and_predicates() {
        let env = CfgEnv::new("x86_64-unknown-linux-gnu", &["beta".into()], false, ProfileFlags::DEV);
        assert!(eval_pred(&env, "unix").unwrap());
        assert!(!eval_pred(&env, "windows").unwrap());
        assert!(eval_pred(&env, "target_os = \"linux\"").unwrap());
        assert!(eval_pred(&env, "target_vendor = \"unknown\"").unwrap());
        assert!(eval_pred(&env, "target_pointer_width = \"64\"").unwrap());
        assert!(eval_pred(&env, "target_has_atomic = \"64\"").unwrap());
        assert!(eval_pred(&env, "feature = \"beta\"").unwrap());
        assert!(!eval_pred(&env, "feature = \"alpha\"").unwrap());
        assert!(eval_pred(&env, "all(unix, not(windows))").unwrap());
        assert!(eval_pred(&env, "any(windows, target_arch = \"x86_64\")").unwrap());
        assert!(eval_pred(&env, "debug_assertions").unwrap());
        assert!(!eval_pred(&env, "test").unwrap());
        let mac = CfgEnv::new("aarch64-apple-darwin", &[], true, ProfileFlags::DEV);
        assert!(eval_pred(&mac, "target_os = \"macos\"").unwrap());
        assert!(eval_pred(&mac, "target_vendor = \"apple\"").unwrap());
        assert!(eval_pred(&mac, "test").unwrap());
        let wasi = CfgEnv::new("wasm32-wasip1", &[], false, ProfileFlags::DEV);
        assert!(eval_pred(&wasi, "target_os = \"wasi\"").unwrap());
        assert!(!eval_pred(&wasi, "target_thread_local").unwrap());
    }

    #[test]
    fn unknown_cfg_name_is_l0520() {
        let env = CfgEnv::new("", &[], false, ProfileFlags::DEV);
        let e = eval_pred(&env, "frobnicate").unwrap_err();
        assert_eq!(e.code, "L0520");
        // `lust_dev` is unknown in user code, true in shipped crates.
        assert_eq!(eval_pred(&env, "lust_dev").unwrap_err().code, "L0520");
        let mut shipped = env.clone();
        shipped.allow_lust_dev = true;
        assert!(eval_pred(&shipped, "lust_dev").unwrap());
    }
}
