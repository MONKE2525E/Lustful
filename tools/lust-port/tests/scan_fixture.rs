//! End-to-end scan of a tiny fixture crate built in a temp directory.
//! Covers module walking (`mod`, `#[path]`), cfg scope labels, an
//! undecidable cfg, an unparseable file, the coverage curve, and the
//! dependency decision table.

use std::path::PathBuf;
use std::process::Command;

fn write(root: &PathBuf, rel: &str, text: &str) {
    let p = root.join(rel);
    std::fs::create_dir_all(p.parent().unwrap()).unwrap();
    std::fs::write(p, text).unwrap();
}

fn fixture(name: &str) -> PathBuf {
    // One directory per test: cargo runs tests in parallel threads in
    // one process, so the pid alone is not unique.
    let root = std::env::temp_dir().join(format!("lust-port-test-{}-{name}", std::process::id()));
    let _ = std::fs::remove_dir_all(&root);
    write(
        &root,
        "Cargo.toml",
        "[package]\nname = \"fixture1\"\nversion = \"0.1.0\"\nedition = \"2024\"\n\n[dependencies]\nindexmap = \"2\"\n",
    );
    write(
        &root,
        "src/lib.rs",
        "pub mod sub;\n#[path = \"elsewhere.rs\"]\npub mod elsewhere;\n#[cfg(windows)]\npub mod win_only;\n#[cfg(feature = \"x\")]\npub mod feat;\npub mod broken;\n#[cfg(test)]\npub mod tests_only;\npub fn f() -> usize { let m: std::collections::HashMap<i32, i32> = std::collections::HashMap::new(); m.len() }\npub fn h(cb: for<'a> fn(&'a i32) -> i32) -> i32 { cb(&1) }\n",
    );
    write(&root, "src/sub/mod.rs", "pub fn h() -> Box<dyn Fn(i32) -> i32> { Box::new(|x| x) }\n");
    write(&root, "src/elsewhere.rs", "pub const N: usize = 1;\n");
    write(&root, "src/win_only.rs", "pub fn w() { let _m: std::collections::HashMap<i32, i32> = std::collections::HashMap::new(); }\n");
    write(&root, "src/feat.rs", "pub fn q() {}\n");
    write(&root, "src/tests_only.rs", "pub fn t() { let _m: std::collections::HashMap<i32, i32> = std::collections::HashMap::new(); }\n");
    write(&root, "src/broken.rs", "pub fn broken( {\n");
    root
}

fn scan_json(root: &PathBuf) -> serde_json::Value {
    let out = Command::new(env!("CARGO_BIN_EXE_lust-port"))
        .args(["scan", "--manifest-path", root.join("Cargo.toml").to_str().unwrap(), "--target", "x86_64-unknown-linux-gnu", "--json"])
        .output()
        .unwrap();
    assert!(out.status.success(), "scan failed: {}", String::from_utf8_lossy(&out.stderr));
    serde_json::from_slice(&out.stdout).unwrap()
}

#[test]
fn scan_reports_gaps_and_survives_bad_files() {
    let root = fixture("gaps");
    let v = scan_json(&root);

    // All 7 files are found by walking mods, including #[path].
    let files: Vec<&str> = v["files"].as_array().unwrap().iter().map(|f| f["file"].as_str().unwrap()).collect();
    for want in ["src/lib.rs", "src/sub/mod.rs", "src/elsewhere.rs", "src/win_only.rs", "src/feat.rs", "src/tests_only.rs", "src/broken.rs"]
    {
        assert!(files.contains(&want), "missing {want} in {files:?}");
    }

    // The unparseable file is recorded and the scan still finished.
    assert_eq!(v["totals"]["parse_errors"], 1);
    assert_eq!(v["parse_errors"][0]["file"], "src/broken.rs");

    // feature="x" cannot be decided from the triple.
    let und: Vec<&str> = v["undecidable_cfg"].as_array().unwrap().iter().map(|x| x.as_str().unwrap()).collect();
    assert!(und.iter().any(|u| u.contains("feature")), "undecidable: {und:?}");

    let findings = v["findings"].as_array().unwrap();
    let has = |feature: &str, file: &str, scope: &str| {
        findings.iter().any(|f| f["feature"] == feature && f["file"] == file && f["scope"] == scope)
    };
    assert!(has("std.hashmap", "src/lib.rs", "active"));
    assert!(has("std.hashmap", "src/win_only.rs", "target-specific"));
    assert!(has("std.hashmap", "src/tests_only.rs", "test-only"));
    // Box<dyn Fn> in sub/mod.rs is supported today (dyn.fn and
    // dyn.boxed are supported rows), so it makes no finding.
    assert!(!has("dyn.fn", "src/sub/mod.rs", "active"));
    assert!(!has("dyn.boxed", "src/sub/mod.rs", "active"));
    assert!(has("lifetimes.hrtb", "src/lib.rs", "active"));

    // Every finding carries a byte range inside its file and a snippet.
    for f in findings {
        let text = std::fs::read_to_string(root.join(f["file"].as_str().unwrap())).unwrap();
        let (s, e) = (f["byte_start"].as_u64().unwrap() as usize, f["byte_end"].as_u64().unwrap() as usize);
        assert!(s <= e && e <= text.len(), "bad range {f}");
        assert!(f["line"].as_u64().unwrap() >= 1);
        assert!(!f["fix_class"].as_str().unwrap().is_empty());
    }

    // Findings are grouped by root cause.
    let causes: Vec<&str> = v["root_causes"].as_array().unwrap().iter().map(|g| g["root_cause"].as_str().unwrap()).collect();
    assert!(causes.contains(&"std-runtime"), "causes: {causes:?}");
    assert!(causes.contains(&"lifetimes"));

    // feat.rs (empty fn), elsewhere.rs (a const), and sub/mod.rs
    // (Box<dyn Fn>) compile now; lib.rs needs milestone 6 for its
    // for<'a> fn.
    let feat = v["files"].as_array().unwrap().iter().find(|f| f["file"] == "src/feat.rs").unwrap();
    assert!(feat["missing_features"].as_array().unwrap().is_empty(), "{feat}");
    assert_eq!(v["coverage"]["supported_today_files"], 3);
    let today = &v["coverage"]["by_plan_milestone"][0];
    let m6 = &v["coverage"]["by_plan_milestone"][3];
    assert_eq!(today["id"], "0");
    assert_eq!(m6["id"], "6");
    assert!(m6["files"].as_u64().unwrap() > today["files"].as_u64().unwrap());
    // The broken file blocks every milestone.
    let m8 = v["coverage"]["by_plan_milestone"].as_array().unwrap().last().unwrap();
    assert!(m8["files"].as_u64().unwrap() < v["coverage"]["total_files"].as_u64().unwrap());

    // The dependency report uses the decision table.
    let deps = v["dependencies"].as_array().unwrap();
    let indexmap = deps.iter().find(|d| d["name"] == "indexmap").expect("indexmap dep");
    assert_eq!(indexmap["decision"], "builtin-adapter");
    assert_eq!(indexmap["milestone"], 5);
}

#[test]
fn human_output_groups_findings() {
    let root = fixture("human");
    let out = Command::new(env!("CARGO_BIN_EXE_lust-port"))
        .args(["scan", "--manifest-path", root.join("Cargo.toml").to_str().unwrap(), "--target", "x86_64-unknown-linux-gnu"])
        .output()
        .unwrap();
    assert!(out.status.success());
    let text = String::from_utf8_lossy(&out.stdout);
    assert!(text.contains("Gaps by root cause"), "{text}");
    assert!(text.contains("std.hashmap"));
    // Grouped, not one line per finding: only 2 samples per feature.
    let map_samples = text.matches("std.hashmap").count();
    assert!(map_samples <= 3, "too many hashmap lines: {map_samples}");
}

#[test]
fn unknown_package_is_an_error() {
    let root = fixture("human");
    let out = Command::new(env!("CARGO_BIN_EXE_lust-port"))
        .args(["scan", "--manifest-path", root.join("Cargo.toml").to_str().unwrap(), "-p", "nope"])
        .output()
        .unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8_lossy(&out.stderr).contains("not found"));
}
