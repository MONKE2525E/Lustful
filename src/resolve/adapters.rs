// Adapter crates (docs/ARCH.md sections 1.1 and 3.6): lust-owned crates in
// `library/deps/<package>/` with the public API of one registry package
// version. The resolver swaps one in by the resolved package (never by a
// source spelling) when all of these hold:
//
// - the package name has a lust adapter crate (`src/lib.rs` exists),
// - the adapter manifest pins the same upstream version as the lockfile,
// - the manifest's adapter format is this compiler's `ADAPTER_FORMAT`,
// - every feature Cargo enabled on the unit is one the adapter implements.
//
// Anything else is an L0508 reason that names the crate and the mismatch,
// never a silent swap. The manifest is `library/deps/<package>/Cargo.toml`:
//
//   [package]
//   name = "memchr"
//   version = "2.8.2"                    # the exact upstream version
//   [package.metadata.lust]
//   adapter = 1                          # ADAPTER_FORMAT
//   features = ["alloc", "default", "std"]
//   exact-layout = ["memchr::Memchr"]    # optional, see below
//
// `exact-layout` lists the adapter types (by source path) whose size,
// align, and niches equal upstream's. Every other adapter type answers
// no layout query (`size_of`, `align_of`, `offset_of!`, `size_of_val`):
// check rejects with L0652 instead of printing a size the real crate does
// not have.
//
// The parser reads only this TOML subset: table headers, and `key = value`
// lines where the value is a string, an integer, or a one-line array of
// strings.

use std::path::PathBuf;

/// The adapter manifest format this compiler reads. An adapter tree built
/// for another format (a stale `LUST_LIBRARY`) is a mismatch, not a guess.
pub const ADAPTER_FORMAT: u32 = 1;

/// Registry packages that have (or will have) a lust adapter crate. A name
/// here with no `library/deps/<name>/src/lib.rs` is "no adapter yet".
pub const ADAPTER_PACKAGES: &[&str] = &[
    "log",
    "serde_json",
    "rustc-hash",
    "indexmap",
    "smallvec",
    "memchr",
    "bumpalo",
    "xxhash-rust",
    "ryu-js",
    "num-bigint",
    "num-traits",
    "tikv-jemallocator",
    "tikv-jemalloc-ctl",
    "rustix",
    "nix",
    "signal-hook",
    "flate2",
    "same-file",
    "name-to-handle-at",
    "jiff",
];

/// Whether the validated source adapter needs the original Cargo edges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AdapterDependencies {
    Upstream,
    Replaced,
}

// Audited complete source replacements, not a build-script allowlist.
// Entries still require registry identity and manifest/unit validation.
const COMPLETE_SOURCE_ADAPTERS: &[(&str, &str)] = &[("serde_json", "1.0.151")];

/// One adapter crate, read from its manifest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Adapter {
    /// The lib root, `library/deps/<package>/src/lib.rs`.
    pub root: PathBuf,
    /// The exact upstream version the adapter matches.
    pub upstream: String,
    /// Upstream features the adapter implements (including `default`).
    pub features: Vec<String>,
    /// Types whose layout equals upstream's (source paths).
    pub exact_layout: Vec<String>,
    pub dependencies: AdapterDependencies,
}

/// The library tree: `$LUST_LIBRARY` when set (the section 3.8 override
/// for std and adapter authors), else the release package's copy, else the
/// build-time `library/`.
pub fn library_root() -> PathBuf {
    match std::env::var_os("LUST_LIBRARY") {
        Some(d) if !d.is_empty() => PathBuf::from(d),
        _ => match crate::tcc::install_dir() {
            Some(d) => d.join("library"),
            None => PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("library"),
        },
    }
}

/// Reads the adapter for registry package `package`. `Ok(None)` means the
/// package has no adapter crate yet; `Err` means a broken adapter manifest
/// (an installation error, reported through L0508 with its reason).
pub fn load(package: &str) -> Result<Option<Adapter>, String> {
    let dir = library_root().join("deps").join(package);
    let root = dir.join("src/lib.rs");
    if !root.is_file() {
        return Ok(None);
    }
    let path = dir.join("Cargo.toml");
    let text = std::fs::read_to_string(&path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    parse_manifest(&text, package, root).map(Some).map_err(|e| format!("{}: {e}", path.display()))
}

/// The shared classification boundary for graph admission and source loading.
/// Path packages remain ordinary source, regardless of their package name.
pub fn classify(package: &str, version: &str, source: Option<&str>, features: &[String]) -> Result<Option<Adapter>, String> {
    let Some(source) = source else { return Ok(None) };
    if !ADAPTER_PACKAGES.contains(&package) { return Ok(None); }
    let mut a = load(package)
        .map_err(|e| format!("the lust adapter for `{package}` is broken: {e}"))?
        .ok_or_else(|| format!("dependency crate `{package}` has no lust adapter yet"))?;
    check_unit(&a, package, version, features)?;
    if source.starts_with("registry+") && COMPLETE_SOURCE_ADAPTERS.contains(&(package, version)) {
        a.dependencies = AdapterDependencies::Replaced;
    }
    Ok(Some(a))
}

/// Queries only complete replacement candidates during strict discovery.
/// Other adapters keep their existing host checks and L0508 timing.
pub fn replaces_upstream(package: &str, version: &str, source: Option<&str>, features: &[String]) -> Result<bool, String> {
    if !source.is_some_and(|s| s.starts_with("registry+"))
        || !COMPLETE_SOURCE_ADAPTERS.iter().any(|(name, _)| *name == package)
    { return Ok(false); }
    Ok(classify(package, version, source, features)?.is_some_and(|a| a.dependencies == AdapterDependencies::Replaced))
}

/// Checks one resolved dependency unit against its adapter. Returns the
/// L0508 reason when the adapter cannot stand in for it.
pub fn check_unit(a: &Adapter, package: &str, version: &str, features: &[String]) -> Result<(), String> {
    if version != a.upstream {
        return Err(format!("dependency crate `{package}` {version} has no matching lust adapter (the adapter matches {})", a.upstream));
    }
    if let Some(f) = features.iter().find(|f| !a.features.contains(f)) {
        return Err(format!("the lust adapter for `{package}` {version} does not implement feature `{f}`"));
    }
    Ok(())
}

fn parse_manifest(text: &str, package: &str, root: PathBuf) -> Result<Adapter, String> {
    let mut table = String::new();
    let (mut name, mut version, mut format) = (None, None, None);
    let (mut features, mut exact_layout) = (None, Vec::new());
    for (i, raw) in text.lines().enumerate() {
        let line = strip_comment(raw).trim();
        if line.is_empty() {
            continue;
        }
        let at = |e: String| format!("line {}: {e}", i + 1);
        if let Some(h) = line.strip_prefix('[') {
            table = h.strip_suffix(']').ok_or_else(|| at("bad table header".into()))?.trim().to_string();
            continue;
        }
        let (key, value) = line.split_once('=').ok_or_else(|| at("expected `key = value`".into()))?;
        let (key, value) = (key.trim(), value.trim());
        match (table.as_str(), key) {
            ("package", "name") => name = Some(string(value).map_err(at)?),
            ("package", "version") => version = Some(string(value).map_err(at)?),
            ("package.metadata.lust", "adapter") => format = Some(value.parse::<u32>().map_err(|e| at(format!("adapter: {e}")))?),
            ("package.metadata.lust", "features") => features = Some(strings(value).map_err(at)?),
            ("package.metadata.lust", "exact-layout") => exact_layout = strings(value).map_err(at)?,
            ("package.metadata.lust", k) => return Err(at(format!("unknown key `{k}`"))),
            _ => {}
        }
    }
    if name.as_deref() != Some(package) {
        return Err(format!("package name is {name:?}, want \"{package}\""));
    }
    match format {
        Some(ADAPTER_FORMAT) => {}
        Some(f) => return Err(format!("adapter format {f}, but this lust reads format {ADAPTER_FORMAT}")),
        None => return Err("no `adapter` key in [package.metadata.lust]".into()),
    }
    Ok(Adapter {
        root,
        upstream: version.ok_or("no package version")?,
        features: features.ok_or("no `features` key in [package.metadata.lust]")?,
        exact_layout,
        dependencies: AdapterDependencies::Upstream,
    })
}

/// The line without a `#` comment (no `#` appears inside our strings).
fn strip_comment(line: &str) -> &str {
    line.split_once('#').map_or(line, |(code, _)| code)
}

fn string(v: &str) -> Result<String, String> {
    v.strip_prefix('"').and_then(|s| s.strip_suffix('"')).map(str::to_string).ok_or_else(|| format!("expected a string, got `{v}`"))
}

fn strings(v: &str) -> Result<Vec<String>, String> {
    let inner = v.strip_prefix('[').and_then(|s| s.strip_suffix(']')).ok_or_else(|| format!("expected a one-line array, got `{v}`"))?;
    inner.split(',').map(str::trim).filter(|s| !s.is_empty()).map(string).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const GOOD: &str = r#"
# A comment line.
[package]
name = "memchr"
version = "2.8.2" # upstream
edition = "2024"

[package.metadata.lust]
adapter = 1
features = ["alloc", "default", "std"]
exact-layout = ["memchr::Memchr"]
"#;

    #[test]
    fn json_replacement_requires_registry_version_and_feature_validation() {
        let registry = Some("registry+https://github.com/rust-lang/crates.io-index");
        for features in [vec![], vec!["default".into(), "std".into()], vec!["alloc".into()]] {
            let a = classify("serde_json", "1.0.151", registry, &features).unwrap().unwrap();
            assert_eq!(a.dependencies, AdapterDependencies::Replaced);
            assert!(a.exact_layout.is_empty());
        }
        assert!(classify("serde_json", "1.0.151", None, &["raw_value".into()]).unwrap().is_none());
        let git = classify("serde_json", "1.0.151", Some("git+https://example.invalid/json"), &[]).unwrap().unwrap();
        assert_eq!(git.dependencies, AdapterDependencies::Upstream);
        for version in ["1.0.150", "1.0.152", "1.0.151+other"] {
            assert!(classify("serde_json", version, registry, &[]).unwrap_err().contains(version));
        }
        for feature in ["raw_value", "preserve_order", "arbitrary_precision", "float_roundtrip", "unbounded_depth", "unknown"] {
            assert!(classify("serde_json", "1.0.151", registry, &[feature.into()]).unwrap_err().contains(feature));
        }
    }

    #[test]
    fn manifest_reads_the_subset() {
        let a = parse_manifest(GOOD, "memchr", PathBuf::from("lib.rs")).unwrap();
        assert_eq!(a.upstream, "2.8.2");
        assert_eq!(a.features, ["alloc", "default", "std"]);
        assert_eq!(a.exact_layout, ["memchr::Memchr"]);
    }

    #[test]
    fn manifest_mismatches_are_errors() {
        let wrong_format = GOOD.replace("adapter = 1", "adapter = 2");
        assert!(parse_manifest(&wrong_format, "memchr", PathBuf::new()).unwrap_err().contains("format 2"));
        assert!(parse_manifest(GOOD, "indexmap", PathBuf::new()).unwrap_err().contains("package name"));
        let typo = GOOD.replace("exact-layout", "exact_layout");
        assert!(parse_manifest(&typo, "memchr", PathBuf::new()).unwrap_err().contains("unknown key"));
    }

    #[test]
    fn unit_check_names_the_mismatch() {
        let a = parse_manifest(GOOD, "memchr", PathBuf::new()).unwrap();
        assert!(check_unit(&a, "memchr", "2.8.2", &["std".into(), "default".into()]).is_ok());
        let v = check_unit(&a, "memchr", "2.8.3", &[]).unwrap_err();
        assert!(v.contains("2.8.3") && v.contains("matches 2.8.2"), "{v}");
        let f = check_unit(&a, "memchr", "2.8.2", &["logging".into()]).unwrap_err();
        assert!(f.contains("feature `logging`"), "{f}");
    }
}
