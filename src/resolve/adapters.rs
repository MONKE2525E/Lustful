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

use std::path::{Path, PathBuf};

use crate::ty::lang::ShippedCrate;

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
    /// Explicit privilege from validated classification, never a source name.
    pub shipped: Option<ShippedCrate>,
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
/// Ordinary path packages are handled separately by `classify_path`; names
/// alone never identify a trusted source adapter.
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
    a.shipped = shipped_identity(&a, package, version, source);
    Ok(Some(a))
}

/// Path source is privileged only when Cargo points at the exact installed
/// serde_json adapter, including its package directory. Both comparisons
/// resolve symlinks and `..`; missing paths fail closed. LUST_LIBRARY is the
/// installation override, as for core/std, not dependency-controlled metadata.
pub fn classify_path(
    package: &str,
    version: &str,
    root: &Path,
    manifest_dir: &Path,
    features: &[String],
) -> Result<Option<Adapter>, String> {
    if package != "serde_json" {
        return Ok(None);
    }
    let dir = library_root().join("deps/serde_json");
    if !same_canonical_path(root, &dir.join("src/lib.rs"))
        || !same_canonical_path(manifest_dir, &dir)
    {
        return Ok(None);
    }
    // Load the trusted manifest, not a manifest selected by a crate name or
    // supplied path. This validates name, adapter format and feature metadata.
    let mut a = load(package)
        .map_err(|e| format!("the lust adapter for `{package}` is broken: {e}"))?
        .ok_or_else(|| format!("dependency crate `{package}` has no lust adapter yet"))?;
    check_unit(&a, package, version, features)?;
    if version != "1.0.151" {
        return Err(format!("the shipped serde_json intrinsic requires version 1.0.151, got {version}"));
    }
    a.shipped = Some(ShippedCrate::SerdeJson);
    // Preserve Cargo's existing path edges; only registry complete replacements
    // are eligible for host-discovery edge pruning.
    Ok(Some(a))
}

fn same_canonical_path(a: &Path, b: &Path) -> bool {
    match (a.canonicalize(), b.canonicalize()) {
        (Ok(a), Ok(b)) => a == b,
        _ => false,
    }
}

/// Called only after manifest/unit validation of a compiler-selected adapter.
fn shipped_identity(a: &Adapter, package: &str, version: &str, source: &str) -> Option<ShippedCrate> {
    if !same_canonical_path(&a.root, &library_root().join("deps").join(package).join("src/lib.rs")) {
        return None;
    }
    if package == "serde_json" {
        return (version == "1.0.151" && a.upstream == "1.0.151" && source.starts_with("registry+"))
            .then_some(ShippedCrate::SerdeJson);
    }
    // Preserve existing adapters' identities (including git-backed units):
    // classification has already selected and validated shipped source.
    let name = package.replace('-', "_");
    ShippedCrate::ALL.iter().copied().find(|k| k.name() == name)
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
        shipped: None,
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
            assert_eq!(a.shipped, Some(ShippedCrate::SerdeJson));
            assert!(a.exact_layout.is_empty());
        }
        assert!(classify("serde_json", "1.0.151", None, &["raw_value".into()]).unwrap().is_none());
        let git = classify("serde_json", "1.0.151", Some("git+https://example.invalid/json"), &[]).unwrap().unwrap();
        assert_eq!(git.dependencies, AdapterDependencies::Upstream);
        assert_eq!(git.shipped, None);
        for version in ["1.0.150", "1.0.152", "1.0.151+other"] {
            assert!(classify("serde_json", version, registry, &[]).unwrap_err().contains(version));
        }
        for feature in ["raw_value", "preserve_order", "arbitrary_precision", "float_roundtrip", "unbounded_depth", "unknown"] {
            assert!(classify("serde_json", "1.0.151", registry, &[feature.into()]).unwrap_err().contains(feature));
        }
    }

    #[test]
    fn json_privilege_requires_the_pinned_shipped_adapter() {
        let registry = "registry+https://github.com/rust-lang/crates.io-index";
        let mut a = load("serde_json").unwrap().unwrap();
        assert_eq!(a.shipped, None, "loading alone is not validation");
        assert_eq!(shipped_identity(&a, "serde_json", "1.0.151", registry), Some(ShippedCrate::SerdeJson));
        assert_eq!(shipped_identity(&a, "serde_json", "1.0.152", registry), None);
        a.upstream = "1.0.152".into();
        assert_eq!(shipped_identity(&a, "serde_json", "1.0.151", registry), None);
        a.upstream = "1.0.151".into();
        a.root = PathBuf::from("/untrusted/serde_json/src/lib.rs");
        assert_eq!(shipped_identity(&a, "serde_json", "1.0.151", registry), None);
        assert!(classify("json_fmt_f64", "1.0.151", Some(registry), &[]).unwrap().is_none());
    }

    #[test]
    fn copied_json_package_does_not_get_intrinsic_privilege() {
        let trusted = library_root().join("deps/serde_json");
        let unique = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let copy = std::env::temp_dir().join(format!("lust-json-identity-{}-{unique}", std::process::id()));
        std::fs::create_dir_all(copy.join("src")).unwrap();
        std::fs::copy(trusted.join("Cargo.toml"), copy.join("Cargo.toml")).unwrap();
        std::fs::copy(trusted.join("src/lib.rs"), copy.join("src/lib.rs")).unwrap();
        let result = classify_path("serde_json", "1.0.151", &copy.join("src/lib.rs"), &copy, &[]);
        std::fs::remove_dir_all(&copy).unwrap();
        assert!(result.unwrap().is_none(), "identical package names, metadata and root text do not establish trust");
    }

    #[test]
    fn json_path_identity_requires_exact_trusted_root_and_manifest() {
        let dir = library_root().join("deps/serde_json").canonicalize().unwrap();
        let root = dir.join("src/lib.rs");
        for features in [vec![], vec!["default".into(), "std".into()], vec!["alloc".into()]] {
            let a = classify_path("serde_json", "1.0.151", &root, &dir, &features).unwrap().unwrap();
            assert_eq!(a.shipped, Some(ShippedCrate::SerdeJson));
            assert_eq!(a.dependencies, AdapterDependencies::Upstream);
            assert!(a.exact_layout.is_empty());
        }
        // Equivalent canonical paths are the same trusted source, not a copy.
        let equivalent = dir.join("src/../src/lib.rs");
        assert!(classify_path("serde_json", "1.0.151", &equivalent, &dir, &[]).unwrap().is_some());
        assert!(classify_path("fake_json", "1.0.151", &root, &dir, &[]).unwrap().is_none());
        assert!(classify_path("serde_json", "1.0.151", &root, &dir.join("src"), &[]).unwrap().is_none());
        // Existing wrong roots exercise canonical comparison, not just ENOENT.
        assert!(classify_path("serde_json", "1.0.151", &dir.join("src/number.rs"), &dir, &[]).unwrap().is_none());
        let fake = library_root().join("deps/memchr");
        assert!(classify_path("serde_json", "1.0.151", &fake.join("src/lib.rs"), &fake, &[]).unwrap().is_none());
        assert!(classify_path("serde_json", "1.0.151", Path::new("/nonexistent/serde_json/src/lib.rs"), &dir, &[]).unwrap().is_none());
        for version in ["1.0.150", "1.0.152", "1.0.151+other"] {
            assert!(classify_path("serde_json", version, &root, &dir, &[]).unwrap_err().contains(version));
        }
        for feature in ["raw_value", "preserve_order", "arbitrary_precision", "float_roundtrip", "unbounded_depth", "unknown"] {
            assert!(classify_path("serde_json", "1.0.151", &root, &dir, &[feature.into()]).unwrap_err().contains(feature));
        }
        // No other path crate gains new shipped behavior in this change.
        assert!(classify_path("memchr", "2.8.2", &fake.join("src/lib.rs"), &fake, &[]).unwrap().is_none());
    }

    #[test]
    fn json_manifest_validation_precedes_identity() {
        let text = std::fs::read_to_string(library_root().join("deps/serde_json/Cargo.toml")).unwrap();
        let root = library_root().join("deps/serde_json/src/lib.rs");
        for bad in [text.replace("adapter = 1", "adapter = 2"), text.replace("name = \"serde_json\"", "name = \"fake_json\"")] {
            assert!(parse_manifest(&bad, "serde_json", root.clone()).is_err());
        }
        let a = parse_manifest(&text, "serde_json", root).unwrap();
        assert_eq!(a.shipped, None, "the manifest constructor cannot grant identity");
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
