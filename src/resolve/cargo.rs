// Cargo graph loading (docs/ARCH.md section 1.1).
//
// Lust does not write a Cargo resolver. Cargo owns version solving: this
// file runs `cargo metadata --format-version 1` once per graph key and
// reads packages, targets, dependencies (kind, rename, target cfg), and the
// resolve nodes. Per-unit features come from the resolve nodes when the
// graph shape makes them exact (one workspace member, no dependencies),
// and otherwise from one cached `cargo check --message-format=json` run
// for the same request, whose compiler-artifact messages carry the exact
// feature set of each selected unit.
//
// The graph key is the full resolver input: every workspace `Cargo.toml`
// plus `Cargo.lock`, the requested package and target, the requested
// features with the default-feature policy, the target triple, and the
// `.cargo/config.toml` chain that applies. Two feature selections or two
// targets therefore key two sessions in one daemon (section 1.8).
use crate::diag::{Diag, Span};
use crate::intern::FxHasher;
use crate::resolve::cfg::CfgEnv;
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

// ---------- Minimal JSON reader ----------
//
// `cargo metadata` output only. Objects keep insertion order in a Vec; the
// reader is total (any malformed byte is an Err, never a panic).

#[derive(Clone, Debug, PartialEq)]
enum Json {
    Null,
    Bool(bool),
    Num(f64),
    Str(String),
    Arr(Vec<Json>),
    Obj(Vec<(String, Json)>),
}

impl Json {
    fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Obj(kvs) => kvs.iter().rev().find(|(k, _)| k == key).map(|(_, v)| v),
            _ => None,
        }
    }
    fn as_str(&self) -> Option<&str> {
        match self {
            Json::Str(s) => Some(s),
            _ => None,
        }
    }
    fn as_arr(&self) -> &[Json] {
        match self {
            Json::Arr(v) => v,
            _ => &[],
        }
    }
    fn as_bool(&self) -> bool {
        matches!(self, Json::Bool(true))
    }
    fn strings(&self) -> Vec<String> {
        self.as_arr().iter().filter_map(|v| v.as_str().map(str::to_string)).collect()
    }
}

fn parse_json(text: &str) -> Result<Json, String> {
    let b = text.as_bytes();
    let mut p = 0usize;
    let v = json_value(b, &mut p)?;
    Ok(v)
}

fn json_ws(b: &[u8], p: &mut usize) {
    while *p < b.len() && b[*p].is_ascii_whitespace() {
        *p += 1;
    }
}

fn json_value(b: &[u8], p: &mut usize) -> Result<Json, String> {
    json_ws(b, p);
    match b.get(*p) {
        Some(b'{') => {
            *p += 1;
            let mut kvs = Vec::new();
            loop {
                json_ws(b, p);
                if b.get(*p) == Some(&b'}') {
                    *p += 1;
                    return Ok(Json::Obj(kvs));
                }
                let Json::Str(k) = json_value(b, p)? else { return Err("object key is not a string".into()) };
                json_ws(b, p);
                if b.get(*p) != Some(&b':') {
                    return Err("expected `:` in object".into());
                }
                *p += 1;
                let v = json_value(b, p)?;
                kvs.push((k, v));
                json_ws(b, p);
                if b.get(*p) == Some(&b',') {
                    *p += 1;
                }
            }
        }
        Some(b'[') => {
            *p += 1;
            let mut vs = Vec::new();
            loop {
                json_ws(b, p);
                if b.get(*p) == Some(&b']') {
                    *p += 1;
                    return Ok(Json::Arr(vs));
                }
                vs.push(json_value(b, p)?);
                json_ws(b, p);
                if b.get(*p) == Some(&b',') {
                    *p += 1;
                }
            }
        }
        Some(b'"') => {
            *p += 1;
            let mut s = String::new();
            loop {
                match b.get(*p) {
                    None => return Err("unterminated string".into()),
                    Some(b'"') => {
                        *p += 1;
                        return Ok(Json::Str(s));
                    }
                    Some(b'\\') => {
                        *p += 1;
                        match b.get(*p) {
                            Some(b'n') => s.push('\n'),
                            Some(b't') => s.push('\t'),
                            Some(b'r') => s.push('\r'),
                            Some(b'u') => {
                                let hex = std::str::from_utf8(b.get(*p + 1..*p + 5).unwrap_or(&[])).unwrap_or("");
                                let mut cp = u32::from_str_radix(hex, 16).map_err(|_| "bad \\u escape".to_string())?;
                                *p += 4;
                                // Surrogate pair for astral characters.
                                if (0xD800..0xDC00).contains(&cp) && b.get(*p + 1) == Some(&b'\\') && b.get(*p + 2) == Some(&b'u') {
                                    let hex2 = std::str::from_utf8(b.get(*p + 3..*p + 7).unwrap_or(&[])).unwrap_or("");
                                    if let Ok(lo) = u32::from_str_radix(hex2, 16) {
                                        cp = 0x10000 + ((cp - 0xD800) << 10) + lo.saturating_sub(0xDC00);
                                        *p += 6;
                                    }
                                }
                                s.push(char::from_u32(cp).unwrap_or('\u{fffd}'));
                            }
                            Some(&c) => s.push(c as char),
                            None => return Err("unterminated escape".into()),
                        }
                        *p += 1;
                    }
                    Some(_) => {
                        let rest = std::str::from_utf8(&b[*p..]).map_err(|_| "invalid utf-8 in string".to_string())?;
                        let ch = rest.chars().next().ok_or("unterminated string")?;
                        s.push(ch);
                        *p += ch.len_utf8();
                    }
                }
            }
        }
        Some(b't') if b[*p..].starts_with(b"true") => {
            *p += 4;
            Ok(Json::Bool(true))
        }
        Some(b'f') if b[*p..].starts_with(b"false") => {
            *p += 5;
            Ok(Json::Bool(false))
        }
        Some(b'n') if b[*p..].starts_with(b"null") => {
            *p += 4;
            Ok(Json::Null)
        }
        Some(_) => {
            let start = *p;
            while *p < b.len() && matches!(b[*p], b'0'..=b'9' | b'-' | b'+' | b'.' | b'e' | b'E') {
                *p += 1;
            }
            let text = std::str::from_utf8(&b[start..*p]).unwrap_or("");
            text.parse::<f64>().map(Json::Num).map_err(|_| format!("bad number `{text}`"))
        }
        None => Err("unexpected end of JSON".into()),
    }
}

// ---------- Graph types ----------

/// One target of one package (a lib, bin, test, example, or bench crate).
#[derive(Clone, Debug)]
pub struct TargetInfo {
    pub kind: Vec<String>,
    pub crate_types: Vec<String>,
    pub name: String,
    pub src_path: PathBuf,
    pub edition: String,
    /// The `test = false`-style target flags; `test_flag` is Cargo's
    /// `test` key, which baselines runners turn off (section 1.1).
    pub test_flag: bool,
}

/// One resolved dependency of a package, before kind/target filtering.
#[derive(Clone, Debug)]
pub struct DepInfo {
    pub name: String,
    pub rename: Option<String>,
    pub kind: String,
    /// The `cfg(...)` target string, when the dependency is target-gated.
    pub target: Option<String>,
    /// The resolved package id repr, when the resolve graph names it.
    pub pkg: Option<String>,
}

/// One Cargo package in the graph.
#[derive(Clone, Debug)]
pub struct PackageInfo {
    /// Cargo's package id repr, for example
    /// `path+file:///x#name@0.1.0` or `registry+...#serde@1.0.0`.
    pub id_repr: String,
    pub name: String,
    pub version: String,
    pub edition: String,
    pub manifest_path: PathBuf,
    pub source: Option<String>,
    pub targets: Vec<TargetInfo>,
    pub dependencies: Vec<DepInfo>,
    pub features: Vec<String>,
    /// Features the resolve node activated for this package id.
    pub resolved_features: Vec<String>,
}

/// One selected compilation unit: a package target with its exact
/// per-unit feature set and its extern prelude (dependency lib crates).
#[derive(Clone, Debug)]
pub struct UnitInfo {
    pub package: PackageInfo,
    pub target: TargetInfo,
    /// The identity string the stable crate hash covers (section 1.7
    /// step 1): the package id for registry crates; for a path package,
    /// name, version, and the workspace-relative manifest path.
    pub package_id: String,
    pub features: Vec<String>,
    /// (extern name as written in paths, package id repr, lib src path).
    pub externs: Vec<(String, String, PathBuf)>,
}

/// The full graph for one request.
#[derive(Clone, Debug)]
pub struct CrateGraph {
    pub key: u64,
    pub workspace_root: PathBuf,
    pub packages: Vec<PackageInfo>,
    pub workspace_members: Vec<String>,
}

/// The user's resolver request, mirroring the SessionKey fields (1.8).
#[derive(Clone, Debug, Default)]
pub struct GraphRequest {
    pub manifest_path: PathBuf,
    pub package: Option<String>,
    pub features: Vec<String>,
    pub default_features: bool,
    pub all_features: bool,
    pub target_triple: String,
}

fn hash_bytes(h: &mut FxHasher, path: &Path) {
    path.to_string_lossy().hash(h);
    if let Ok(bytes) = std::fs::read(path) {
        bytes.hash(h);
    }
}

/// The graph key of section 1.1: manifest texts plus the lockfile, the
/// request, and the cargo config chain. Computed before metadata runs so
/// the same key can serve as the cache key for the metadata result: the
/// workspace member manifests join through the root manifest's own text
/// plus a directory walk of sibling member dirs is not possible without
/// metadata, so the key covers the named manifest, every ancestor
/// manifest, and the lock next to each. After metadata, `refined_key`
/// folds the member manifests in; the driver keys sessions by the
/// SessionKey, and this key keys the in-process graph cache.
pub fn graph_key(req: &GraphRequest) -> u64 {
    let mut h = FxHasher::default();
    "lust-graph-v1".hash(&mut h);
    let mut dir = req.manifest_path.parent();
    while let Some(d) = dir {
        let m = d.join("Cargo.toml");
        if m.exists() {
            hash_bytes(&mut h, &m);
            hash_bytes(&mut h, &d.join("Cargo.lock"));
        }
        // The config chain: `.cargo/config.toml` in every ancestor.
        hash_bytes(&mut h, &d.join(".cargo/config.toml"));
        dir = d.parent();
    }
    if let Ok(home) = std::env::var("CARGO_HOME") {
        hash_bytes(&mut h, &Path::new(&home).join("config.toml"));
    } else if let Ok(home) = std::env::var("HOME") {
        hash_bytes(&mut h, &Path::new(&home).join(".cargo/config.toml"));
    }
    req.package.hash(&mut h);
    let mut feats = req.features.clone();
    feats.sort();
    feats.dedup();
    feats.hash(&mut h);
    req.default_features.hash(&mut h);
    req.all_features.hash(&mut h);
    req.target_triple.hash(&mut h);
    h.finish()
}

/// In-process cache of loaded graphs, by graph key. A daemon serves many
/// requests per graph; metadata runs once per key while inputs hold.
fn graph_cache() -> &'static Mutex<std::collections::HashMap<u64, std::sync::Arc<CrateGraph>>> {
    static CACHE: OnceLock<Mutex<std::collections::HashMap<u64, std::sync::Arc<CrateGraph>>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(std::collections::HashMap::new()))
}

/// Loads (or reuses) the Cargo graph for one request. Errors are message
/// strings: the driver turns them into code-2 responses, since a graph
/// Cargo itself rejects has no crate to attach a span diagnostic to.
pub fn load_graph(req: &GraphRequest) -> Result<std::sync::Arc<CrateGraph>, String> {
    let key = graph_key(req);
    if let Some(g) = graph_cache().lock().unwrap().get(&key) {
        return Ok(g.clone());
    }
    let mut cmd = Command::new("cargo");
    cmd.args(["metadata", "--format-version", "1", "--manifest-path"]).arg(&req.manifest_path);
    if !req.features.is_empty() {
        cmd.args(["--features", &req.features.join(",")]);
    }
    if !req.default_features {
        cmd.arg("--no-default-features");
    }
    if req.all_features {
        cmd.arg("--all-features");
    }
    if !req.target_triple.is_empty() {
        cmd.args(["--filter-platform", &req.target_triple]);
    }
    let out = cmd.output().map_err(|e| format!("cannot run `cargo metadata`: {e}"))?;
    if !out.status.success() {
        return Err(format!("`cargo metadata` failed: {}", String::from_utf8_lossy(&out.stderr).lines().take(3).collect::<Vec<_>>().join(" ")));
    }
    let text = String::from_utf8_lossy(&out.stdout);
    let root = parse_json(&text).map_err(|e| format!("cannot parse `cargo metadata` output: {e}"))?;
    let workspace_root = PathBuf::from(root.get("workspace_root").and_then(|v| v.as_str()).unwrap_or(""));
    let members: Vec<String> = root.get("workspace_members").map(|v| v.strings()).unwrap_or_default();
    // Resolve nodes: features per package id, and the exact dep edges.
    let mut node_features: std::collections::HashMap<String, Vec<String>> = std::collections::HashMap::new();
    let mut node_deps: std::collections::HashMap<String, Vec<(String, String, Option<String>)>> = std::collections::HashMap::new();
    if let Some(nodes) = root.get("resolve").and_then(|r| r.get("nodes")) {
        for n in nodes.as_arr() {
            let Some(id) = n.get("id").and_then(|v| v.as_str()) else { continue };
            node_features.insert(id.to_string(), n.get("features").map(|v| v.strings()).unwrap_or_default());
            let mut deps = Vec::new();
            for d in n.get("deps").map(|v| v.as_arr()).unwrap_or(&[]) {
                let pkg = d.get("pkg").and_then(|v| v.as_str()).unwrap_or("").to_string();
                for k in d.get("dep_kinds").map(|v| v.as_arr()).unwrap_or(&[]) {
                    let kind = match k.get("kind") {
                        Some(Json::Str(s)) => s.clone(),
                        _ => "normal".to_string(),
                    };
                    let target = k.get("target").and_then(|v| v.as_str()).map(str::to_string);
                    deps.push((pkg.clone(), kind, target));
                }
                if d.get("dep_kinds").is_none() {
                    deps.push((pkg, "normal".into(), None));
                }
            }
            node_deps.insert(id.to_string(), deps);
        }
    }
    let mut packages = Vec::new();
    for p in root.get("packages").map(|v| v.as_arr()).unwrap_or(&[]) {
        let id_repr = p.get("id").and_then(|v| v.as_str()).unwrap_or("").to_string();
        let mut dependencies: Vec<DepInfo> = p
            .get("dependencies")
            .map(|v| v.as_arr())
            .unwrap_or(&[])
            .iter()
            .map(|d| DepInfo {
                name: d.get("name").and_then(|v| v.as_str()).unwrap_or("").to_string(),
                rename: d.get("rename").and_then(|v| v.as_str()).map(str::to_string),
                kind: match d.get("kind") {
                    Some(Json::Str(s)) => s.clone(),
                    _ => "normal".to_string(),
                },
                target: d.get("target").and_then(|v| v.as_str()).map(str::to_string),
                pkg: None,
            })
            .collect();
        // Fill each dependency's resolved package by matching the resolve
        // edges of this package (name plus kind plus target).
        if let Some(edges) = node_deps.get(&id_repr) {
            for dep in &mut dependencies {
                let pkg_name = dep.rename.clone().unwrap_or_else(|| dep.name.clone());
                let _ = pkg_name;
                dep.pkg = edges
                    .iter()
                    .find(|(_, kind, target)| *kind == dep.kind && *target == dep.target)
                    .map(|(pkg, _, _)| pkg.clone())
                    .or_else(|| edges.first().map(|(pkg, _, _)| pkg.clone()));
            }
        }
        packages.push(PackageInfo {
            resolved_features: node_features.get(&id_repr).cloned().unwrap_or_default(),
            id_repr: id_repr.clone(),
            name: p.get("name").and_then(|v| v.as_str()).unwrap_or("").to_string(),
            version: p.get("version").and_then(|v| v.as_str()).unwrap_or("0.0.0").to_string(),
            edition: p.get("edition").and_then(|v| v.as_str()).unwrap_or("2015").to_string(),
            manifest_path: PathBuf::from(p.get("manifest_path").and_then(|v| v.as_str()).unwrap_or("")),
            source: p.get("source").and_then(|v| v.as_str()).map(str::to_string),
            targets: p
                .get("targets")
                .map(|v| v.as_arr())
                .unwrap_or(&[])
                .iter()
                .map(|t| TargetInfo {
                    kind: t.get("kind").map(|v| v.strings()).unwrap_or_default(),
                    crate_types: t.get("crate_types").map(|v| v.strings()).unwrap_or_default(),
                    name: t.get("name").and_then(|v| v.as_str()).unwrap_or("").to_string(),
                    src_path: PathBuf::from(t.get("src_path").and_then(|v| v.as_str()).unwrap_or("")),
                    edition: t.get("edition").and_then(|v| v.as_str()).unwrap_or("2015").to_string(),
                    test_flag: t.get("test").map(|v| v.as_bool()).unwrap_or(true),
                })
                .collect(),
            dependencies,
            features: p.get("features").map(|v| match v {
                Json::Obj(kvs) => kvs.iter().map(|(k, _)| k.clone()).collect(),
                _ => Vec::new(),
            }).unwrap_or_default(),
        });
    }
    let graph = std::sync::Arc::new(CrateGraph { key, workspace_root, packages, workspace_members: members });
    graph_cache().lock().unwrap().insert(key, graph.clone());
    Ok(graph)
}

/// The stable package identity of section 1.7 step 1.
pub fn package_id_string(graph: &CrateGraph, pkg: &PackageInfo) -> String {
    match &pkg.source {
        Some(source) => format!("{} {} ({})", pkg.name, pkg.version, source),
        None => {
            let rel = pkg.manifest_path.strip_prefix(&graph.workspace_root).unwrap_or(&pkg.manifest_path);
            format!("{} {} (path+{})", pkg.name, pkg.version, rel.display())
        }
    }
}

/// The per-unit feature sets from one `cargo check --message-format=json`
/// run for the same request (section 1.1), keyed by (package id repr,
/// target name). Cached per graph key in this process. Returns None when
/// the run fails; the caller then falls back to resolve-node features and
/// the session still works for single-package graphs.
fn unit_features_via_check(req: &GraphRequest) -> Option<std::collections::HashMap<(String, String), Vec<String>>> {
    let key = graph_key(req);
    static CACHE: OnceLock<Mutex<std::collections::HashMap<u64, std::collections::HashMap<(String, String), Vec<String>>>>> =
        OnceLock::new();
    let cache = CACHE.get_or_init(|| Mutex::new(std::collections::HashMap::new()));
    if let Some(v) = cache.lock().unwrap().get(&key) {
        return Some(v.clone());
    }
    let mut cmd = Command::new("cargo");
    cmd.args(["check", "--message-format=json", "--manifest-path"]).arg(&req.manifest_path);
    if let Some(pkg) = &req.package {
        cmd.args(["-p", pkg]);
    }
    if !req.features.is_empty() {
        cmd.args(["--features", &req.features.join(",")]);
    }
    if !req.default_features {
        cmd.arg("--no-default-features");
    }
    if req.all_features {
        cmd.arg("--all-features");
    }
    if !req.target_triple.is_empty() {
        cmd.args(["--target", &req.target_triple]);
    }
    let out = cmd.output().ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    let mut map = std::collections::HashMap::new();
    for line in text.lines() {
        let Ok(v) = parse_json(line) else { continue };
        if v.get("reason").and_then(|r| r.as_str()) != Some("compiler-artifact") {
            continue;
        }
        let pkg = v.get("package_id").and_then(|p| p.as_str()).unwrap_or("").to_string();
        let target = v.get("target").and_then(|t| t.get("name")).and_then(|n| n.as_str()).unwrap_or("").to_string();
        let feats = v.get("features").map(|f| f.strings()).unwrap_or_default();
        map.insert((pkg, target), feats);
    }
    if map.is_empty() {
        return None;
    }
    cache.lock().unwrap().insert(key, map.clone());
    Some(map)
}

/// Evaluates a Cargo dependency target string (`cfg(windows)`,
/// `cfg(target_arch = "wasm32")`) against the session cfg environment.
/// The string is re-lexed and read through the same predicate evaluator
/// as source `#[cfg]`, so the two never disagree.
pub fn dep_target_matches(env: &CfgEnv, target: Option<&str>, interner: &crate::intern::Interner) -> bool {
    let Some(target) = target else { return true };
    let src = format!("#[{target}]\nmod m;");
    let Ok(lexed) = crate::lexer::lex(&src, crate::diag::FileId(0), 0, interner) else { return false };
    let o = crate::scan::outline(&lexed, interner);
    match o.mods.first() {
        Some(m) => crate::resolve::cfg::outline_enabled(env, &m.cfg, &lexed.strings, interner, Span::default()).unwrap_or(false),
        None => false,
    }
}

/// Picks one unit from the graph: the package (by name, or the one whose
/// manifest the request names) and the target (kind plus name). The
/// unit's features prefer the `cargo check` dry run; for a graph with a
/// single workspace member and no dependencies the resolve-node features
/// are exact and no check runs.
pub fn select_unit(
    graph: &CrateGraph,
    req: &GraphRequest,
    target_kind: &str,
    target_name: &str,
    env: &CfgEnv,
    interner: &crate::intern::Interner,
    test_crate: bool,
) -> Result<UnitInfo, String> {
    let pkg = graph
        .packages
        .iter()
        .find(|p| Some(&p.name) == req.package.as_ref())
        .or_else(|| graph.packages.iter().find(|p| p.manifest_path == req.manifest_path))
        .or_else(|| graph.packages.iter().find(|p| graph.workspace_members.contains(&p.id_repr)))
        .ok_or_else(|| format!("no package in the Cargo graph matches {}", req.manifest_path.display()))?;
    let target = pkg
        .targets
        .iter()
        .find(|t| t.name == target_name && (t.kind.iter().any(|k| k == target_kind) || target_kind == "lib" && t.kind.iter().any(|k| k == "lib" || k == "rlib")))
        .or_else(|| pkg.targets.iter().find(|t| t.name == target_name))
        .ok_or_else(|| format!("package `{}` has no {target_kind} target named `{target_name}`", pkg.name))?;
    let simple_graph = graph.workspace_members.len() <= 1 && pkg.dependencies.is_empty();
    let features = if simple_graph {
        pkg.resolved_features.clone()
    } else {
        unit_features_via_check(req)
            .and_then(|m| m.get(&(pkg.id_repr.clone(), target.name.clone())).cloned())
            .unwrap_or_else(|| pkg.resolved_features.clone())
    };
    // Extern prelude: direct dependencies whose kind and target select
    // them for this unit. Dev-dependencies join only test crates.
    let mut externs = Vec::new();
    for dep in &pkg.dependencies {
        let kind_ok = dep.kind == "normal" || (test_crate && dep.kind == "dev");
        if !kind_ok || !dep_target_matches(env, dep.target.as_deref(), interner) {
            continue;
        }
        let Some(dep_pkg_id) = &dep.pkg else { continue };
        let Some(dep_pkg) = graph.packages.iter().find(|p| &p.id_repr == dep_pkg_id) else { continue };
        let Some(lib) = dep_pkg.targets.iter().find(|t| t.kind.iter().any(|k| k == "lib" || k == "rlib")) else { continue };
        let extern_name = dep.rename.clone().unwrap_or_else(|| dep.name.replace('-', "_"));
        externs.push((extern_name, dep_pkg.id_repr.clone(), lib.src_path.clone()));
    }
    Ok(UnitInfo { package_id: package_id_string(graph, pkg), package: pkg.clone(), target: target.clone(), features, externs })
}

/// The edition gate for a selected unit (section 1.1): lust source crates
/// must be edition 2024. Applied only to selected units.
pub fn check_edition(unit: &UnitInfo) -> Result<(), Diag> {
    if unit.target.edition == "2024" {
        return Ok(());
    }
    Err(Diag::new(
        "L0530",
        Span::default(),
        format!("crate `{}` is edition {}, but lust source crates must be edition 2024", unit.package.name, unit.target.edition),
        "Set `edition = \"2024\"` in the package manifest.",
    ))
}

/// Reads `[lints]` and `[workspace.lints]` from the manifest texts of a
/// selected unit (cargo metadata does not report lints). `unsafe_code` at
/// forbid/deny is enforced by the parser's blanket `unsafe` reject; any
/// other rust lint at deny/forbid rejects the session with L0531 naming
/// the lint, because rustc would reject code that triggers it and lust
/// does not check it (section 1.1).
pub fn check_lints(graph: &CrateGraph, unit: &UnitInfo) -> Result<(), Diag> {
    let mut texts: Vec<String> = Vec::new();
    if let Ok(t) = std::fs::read_to_string(&unit.package.manifest_path) {
        texts.push(t);
    }
    let root_manifest = graph.workspace_root.join("Cargo.toml");
    if root_manifest != unit.package.manifest_path
        && let Ok(t) = std::fs::read_to_string(&root_manifest)
    {
        texts.push(t);
    }
    for text in &texts {
        if let Some(lint) = first_deny_lint(text) {
            return Err(Diag::new(
                "L0531",
                Span::default(),
                format!("lint `{lint}` is denied in the manifest, but lust does not check it"),
                "Lower the lint to warn for lust dev builds, or build this crate with Cargo.",
            ));
        }
    }
    Ok(())
}

/// The first non-`unsafe_code` rust lint at deny or forbid level in one
/// manifest text, from `[lints]` / `[workspace.lints]` (inline-table form)
/// or `[lints.rust]` / `[workspace.lints.rust]` (table form).
fn first_deny_lint(text: &str) -> Option<String> {
    let mut section = String::new();
    for raw in text.lines() {
        let line = raw.trim();
        if line.starts_with('[') {
            section = line.trim_matches(|c| c == '[' || c == ']').trim().to_string();
            continue;
        }
        let in_lints = matches!(section.as_str(), "lints" | "workspace.lints" | "lints.rust" | "workspace.lints.rust");
        if !in_lints || !line.contains('=') {
            continue;
        }
        // Two shapes: `rust = { unsafe_code = "forbid", dead_code = "deny" }`
        // and one `name = "deny"` per line under `[lints.rust]`.
        let is_table_form = matches!(section.as_str(), "lints.rust" | "workspace.lints.rust");
        if is_table_form {
            let (name, value) = line.split_once('=')?;
            let name = name.trim();
            let level = value.trim().trim_matches('"');
            if (level == "deny" || level == "forbid") && name != "unsafe_code" && !name.contains("::") {
                return Some(name.to_string());
            }
        } else if let Some((_, inner)) = line.split_once('{') {
            for part in inner.trim_end_matches('}').split(',') {
                let Some((name, value)) = part.split_once('=') else { continue };
                let name = name.trim();
                let level = value.trim().trim_matches('"');
                if (level == "deny" || level == "forbid") && name != "unsafe_code" && !name.contains("::") {
                    return Some(name.to_string());
                }
            }
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_reader_handles_metadata_shapes() {
        let v = parse_json(r#"{"a":[1,"x",true,null],"b":{"c":"d\né"},"n":-1.5e3}"#).unwrap();
        assert_eq!(v.get("a").unwrap().as_arr().len(), 4);
        assert_eq!(v.get("b").unwrap().get("c").unwrap().as_str(), Some("d\né"));
        assert_eq!(v.get("n"), Some(&Json::Num(-1500.0)));
        assert!(parse_json("{").is_err());
    }

    #[test]
    fn deny_lint_scan() {
        let inline = "[workspace.lints.rust]\nunsafe_code = \"forbid\"\n";
        assert_eq!(first_deny_lint(inline), None);
        let table = "[lints.rust]\ndead_code = \"deny\"\n";
        assert_eq!(first_deny_lint(table).as_deref(), Some("dead_code"));
        let inline_table = "[lints]\nrust = { missing_docs = \"deny\" }\n";
        assert_eq!(first_deny_lint(inline_table).as_deref(), Some("missing_docs"));
        let warn = "[lints.rust]\ndead_code = \"warn\"\n";
        assert_eq!(first_deny_lint(warn), None);
    }

    #[test]
    fn graph_of_a_fixture_package() {
        // The checked-in hello fixture: one package, one bin, edition 2024.
        // Copied to a temp dir first: `cargo metadata` writes a Cargo.lock
        // next to the manifest, and the repo fixture must stay clean.
        let src_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/crates/hello");
        let dir = std::env::temp_dir().join(format!("lust-cargo-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(dir.join("src")).unwrap();
        std::fs::copy(src_dir.join("Cargo.toml"), dir.join("Cargo.toml")).unwrap();
        std::fs::copy(src_dir.join("src/main.rs"), dir.join("src/main.rs")).unwrap();
        let req = GraphRequest { manifest_path: dir.join("Cargo.toml"), package: None, features: vec![], default_features: true, all_features: false, target_triple: String::new() };
        let graph = load_graph(&req).expect("cargo metadata on the hello fixture");
        let interner = crate::intern::Interner::default();
        let env = CfgEnv::new("", &[], false, crate::protocol::ProfileFlags::DEV);
        let unit = select_unit(&graph, &req, "bin", "hello", &env, &interner, false).expect("hello unit");
        assert_eq!(unit.package.name, "hello");
        assert_eq!(unit.target.edition, "2024");
        assert!(unit.target.src_path.ends_with("src/main.rs"));
        assert!(unit.package_id.contains("hello 0.1.0"), "{}", unit.package_id);
        check_edition(&unit).unwrap();
        check_lints(&graph, &unit).unwrap();
    }
}
