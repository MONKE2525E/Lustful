// Build-script refresh checks (docs/ARCH.md section 1.1). Lust does not
// compile `build.rs`; Cargo runs it, and the driver reads the recorded
// output. A record is valid only while its recorded inputs hold: the
// build script source, every `rerun-if-changed` file, and every
// `rerun-if-env-changed` value. `refresh` re-checks the inputs per
// session (hashes only, no Cargo run while they hold) and re-runs the
// script through Cargo when one changed. The outputs hash covers
// `cargo::rustc-cfg`, `cargo::rustc-env`, and the contents of OUT_DIR
// files; it enters the daemon's per-session refresh key and the cold
// disk cache key, so a build script change can never serve output
// resolved under the old one. Code that consumes the outputs (env!,
// OUT_DIR includes) lands with W-MACRO and W-RESOLVE; until then lust
// rejects such code, and this module keeps the routing honest.
use crate::intern::{FxHasher, FxMap};
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};

/// Build script stdout directives the driver records. Cargo accepts
/// both `cargo:key=value` and `cargo::key=value`; other lines are the
/// script's own diagnostics and are ignored here, as Cargo ignores
/// them for build purposes.
#[derive(Default, Debug, PartialEq, Eq)]
pub struct BuildOutput {
    pub rerun_if_changed: Vec<String>,
    pub rerun_if_env_changed: Vec<String>,
    pub rustc_cfg: Vec<String>,
    pub rustc_env: Vec<(String, String)>,
}

/// Parses build script stdout into `BuildOutput`.
pub fn parse_output(text: &str) -> BuildOutput {
    let mut out = BuildOutput::default();
    for line in text.lines() {
        let Some(rest) = line.strip_prefix("cargo:") else { continue };
        let rest = rest.strip_prefix(':').unwrap_or(rest);
        let Some((key, value)) = rest.split_once('=') else { continue };
        match key {
            "rerun-if-changed" => out.rerun_if_changed.push(value.to_string()),
            "rerun-if-env-changed" => out.rerun_if_env_changed.push(value.to_string()),
            "rustc-cfg" => out.rustc_cfg.push(value.to_string()),
            "rustc-env" => {
                let (k, v) = value.split_once('=').unwrap_or((value, ""));
                out.rustc_env.push((k.to_string(), v.to_string()));
            }
            _ => {}
        }
    }
    out
}

/// One recorded build-script run: input hashes to re-check, plus the
/// output hash consumers key on. Stored as text lines in the disk cache
/// dir (magic `LBS1`); W-DRIVER owns the form and changes it only by
/// bumping the magic, never by migrating an old record.
pub struct Record {
    pub script: PathBuf,
    pub script_hash: u64,
    pub inputs: Vec<(PathBuf, u64)>,
    pub env_inputs: Vec<(String, Option<String>)>,
    pub output_hash: u64,
}

fn hash_parts(parts: &[&[u8]]) -> u64 {
    let mut h = FxHasher::default();
    "buildscript-v1".hash(&mut h);
    for p in parts {
        (p.len() as u64).hash(&mut h);
        p.hash(&mut h);
    }
    h.finish()
}

/// Hashes recorded outputs the way consumers key on them: cfgs, env
/// pairs, and OUT_DIR file contents (names and bytes, sorted).
fn output_hash(out: &BuildOutput, out_dir: Option<&Path>) -> u64 {
    let mut parts: Vec<Vec<u8>> = vec![b"cfg".to_vec()];
    let mut cfgs = out.rustc_cfg.clone();
    cfgs.sort();
    parts.extend(cfgs.iter().map(|c| c.as_bytes().to_vec()));
    parts.push(b"env".to_vec());
    let mut envs = out.rustc_env.clone();
    envs.sort();
    parts.extend(envs.iter().map(|(k, v)| format!("{k}={v}").into_bytes()));
    if let Some(dir) = out_dir {
        let mut files: Vec<PathBuf> = Vec::new();
        let mut stack = vec![dir.to_path_buf()];
        while let Some(d) = stack.pop() {
            if let Ok(rd) = std::fs::read_dir(&d) {
                for e in rd.flatten() {
                    let p = e.path();
                    if p.is_dir() {
                        stack.push(p);
                    } else {
                        files.push(p);
                    }
                }
            }
        }
        files.sort();
        for f in files {
            parts.push(f.to_string_lossy().as_bytes().to_vec());
            parts.push(std::fs::read(&f).unwrap_or_default());
        }
    }
    let refs: Vec<&[u8]> = parts.iter().map(|v| &v[..]).collect();
    hash_parts(&refs)
}

/// The record file for one manifest dir inside the cache dir.
fn record_path(cache_dir: &Path, manifest_dir: &Path) -> PathBuf {
    let h = hash_parts(&[manifest_dir.to_string_lossy().as_bytes()]);
    cache_dir.join(format!("buildscript-{h:016x}.txt"))
}

/// File contents hash for rerun-if inputs; a missing file hashes as a
/// fixed sentinel, so creating or deleting the file changes the hash.
fn file_hash(path: &Path) -> u64 {
    match std::fs::read(path) {
        Ok(bytes) => hash_parts(&[&bytes]),
        Err(_) => hash_parts(&[b"<missing>"]),
    }
}

impl Record {
    /// Serializes the record. Paths are lossy text; a record that
    /// fails to read back is a miss, never a wrong answer.
    fn encode(&self) -> Vec<u8> {
        let mut s = String::from("LBS1\n");
        s.push_str(&format!("script {} {}\n", self.script_hash, self.script.to_string_lossy()));
        for (p, h) in &self.inputs {
            s.push_str(&format!("input {h} {}\n", p.to_string_lossy()));
        }
        for (k, v) in &self.env_inputs {
            // No value token at all means the var was unset;
            // an empty value is a real, different state.
            match v {
                Some(v) => s.push_str(&format!("env {k} {v}\n")),
                None => s.push_str(&format!("env {k}\n")),
            }
        }
        s.push_str(&format!("output {}\n", self.output_hash));
        s.into_bytes()
    }

    /// Reads bytes written by `encode`. None on any malformed line.
    fn decode(text: &str) -> Option<Record> {
        let mut lines = text.lines();
        if lines.next()? != "LBS1" {
            return None;
        }
        let (mut script, mut script_hash, mut output_hash) = (None, 0u64, None);
        let (mut inputs, mut env_inputs) = (Vec::new(), Vec::new());
        for line in lines {
            let mut it = line.splitn(3, ' ');
            match it.next()? {
                "script" => {
                    script_hash = it.next()?.parse().ok()?;
                    script = Some(PathBuf::from(it.next()?));
                }
                "input" => inputs.push((PathBuf::from(it.nth(1)?), line.split(' ').nth(1)?.parse().ok()?)),
                "env" => {
                    let k = it.next()?.to_string();
                    env_inputs.push((k, it.next().map(str::to_string)));
                }
                "output" => output_hash = Some(it.next()?.parse().ok()?),
                _ => return None,
            }
        }
        Some(Record { script: script?, script_hash, inputs, env_inputs, output_hash: output_hash? })
    }

    /// True while every recorded input still holds: the script source
    /// hash, each `rerun-if-changed` file hash, and each
    /// `rerun-if-env-changed` value.
    fn inputs_still_hold(&self) -> bool {
        file_hash(&self.script) == self.script_hash
            && self.inputs.iter().all(|(p, h)| file_hash(p) == *h)
            && self.env_inputs.iter().all(|(k, v)| std::env::var(k).ok().as_deref() == v.as_deref())
    }
}

/// The build script for one manifest dir: `build = "..."` in the
/// `[package]` table when present (`false` means none), else the
/// conventional `build.rs`. A plain line scan, like protocol's manifest
/// reads; W-RESOLVE replaces it with Cargo metadata.
pub fn build_script_for(manifest_dir: &Path) -> Option<PathBuf> {
    if let Ok(text) = std::fs::read_to_string(manifest_dir.join("Cargo.toml")) {
        let mut in_package = false;
        for raw in text.lines() {
            let line = raw.trim();
            if line.starts_with('[') {
                in_package = line.trim_matches(|c| c == '[' || c == ']') == "package";
                continue;
            }
            if in_package && line.starts_with("build") {
                let value = line.split('=').nth(1)?.trim();
                if value == "false" {
                    return None;
                }
                let path = value.trim_matches(|c| c == '"' || c == '\'');
                let p = manifest_dir.join(path);
                return p.exists().then_some(p);
            }
        }
    }
    let p = manifest_dir.join("build.rs");
    p.exists().then_some(p)
}

/// What a refresh check found. `hash` is what session routing and cache
/// keys mix in; it is 0 when the crate has no build script.
pub enum Refresh {
    /// No build script, or no manifest dir to look in.
    None,
    /// Recorded inputs still hold; no Cargo run happened.
    Fresh { hash: u64 },
    /// The script re-ran through Cargo and the record was rewritten.
    Reran { hash: u64 },
    /// Inputs changed but the Cargo re-run failed. The caller logs it;
    /// the hash is over the failure text so each distinct failure state
    /// still separates sessions from the last good record.
    Failed { hash: u64, error: String },
}

impl Refresh {
    pub fn hash(&self) -> u64 {
        match self {
            Refresh::None => 0,
            Refresh::Fresh { hash } | Refresh::Reran { hash } | Refresh::Failed { hash, .. } => *hash,
        }
    }
}

/// Re-checks the build script of `manifest_dir` against its record in
/// `cache_dir`, re-running it through Cargo when stale. The fresh path
/// only hashes the recorded inputs (the script plus its
/// `rerun-if-changed` files), so a per-request check stays cheap. When
/// a script declares no `rerun-if-changed`, Cargo's default (any
/// package file change) is approximated by the manifest bytes, which
/// the graph key already covers.
pub fn refresh(manifest_dir: &Path, cache_dir: &Path) -> Refresh {
    let Some(script) = build_script_for(manifest_dir) else { return Refresh::None };
    let path = record_path(cache_dir, manifest_dir);
    let stored = std::fs::read_to_string(&path).ok().and_then(|t| Record::decode(&t));
    if let Some(rec) = &stored
        && rec.script == script
        && rec.inputs_still_hold()
    {
        return Refresh::Fresh { hash: rec.output_hash };
    }
    match run_through_cargo(manifest_dir, &script) {
        Ok(rec) => {
            let hash = rec.output_hash;
            let _ = std::fs::create_dir_all(cache_dir);
            let tmp = path.with_extension(format!("tmp{}", std::process::id()));
            if std::fs::write(&tmp, rec.encode()).is_ok() && std::fs::rename(&tmp, &path).is_err() {
                let _ = std::fs::remove_file(&tmp);
            }
            Refresh::Reran { hash }
        }
        Err(e) => Refresh::Failed { hash: hash_parts(&[b"failed", e.as_bytes()]), error: e },
    }
}

/// Runs the build script through Cargo and builds a fresh record.
/// `cargo check` already runs build scripts; its JSON messages name
/// the OUT_DIR, and the script's stdout sits in the sibling `output`
/// file Cargo keeps next to it.
fn run_through_cargo(manifest_dir: &Path, script: &Path) -> Result<Record, String> {
    let out = std::process::Command::new("cargo")
        .args(["check", "--offline", "--message-format=json"])
        .current_dir(manifest_dir)
        .env("CARGO_TERM_COLOR", "never")
        .output()
        .map_err(|e| format!("cannot run cargo: {e}"))?;
    if !out.status.success() {
        return Err(format!("cargo check failed: {}", String::from_utf8_lossy(&out.stderr).lines().take(3).collect::<Vec<_>>().join(" ")));
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    let mut out_dir: Option<PathBuf> = None;
    for line in stdout.lines() {
        if line.contains("\"build-script-executed\"") {
            // The message is one JSON object per line; pull the two
            // string fields this record needs without a JSON parser.
            let field = |name: &str| -> Option<String> {
                let at = line.find(&format!("\"{name}\":\""))? + name.len() + 3;
                let rest = &line[at..];
                let mut s = String::new();
                let mut chars = rest.chars();
                while let Some(c) = chars.next() {
                    match c {
                        '"' => return Some(s),
                        '\\' => s.push(chars.next()?),
                        _ => s.push(c),
                    }
                }
                None
            };
            if let Some(d) = field("out_dir") {
                out_dir = Some(PathBuf::from(d));
            }
        }
    }
    let Some(out_dir_path) = out_dir else {
        return Err("cargo check ran no build script for this manifest".to_string());
    };
    let output_file = out_dir_path.parent().map(|p| p.join("output"));
    let text = output_file.as_deref().and_then(|p| std::fs::read_to_string(p).ok()).unwrap_or_default();
    let parsed = parse_output(&text);
    let inputs: Vec<(PathBuf, u64)> = parsed
        .rerun_if_changed
        .iter()
        .map(|p| {
            let ap = if Path::new(p).is_absolute() { PathBuf::from(p) } else { manifest_dir.join(p) };
            let h = file_hash(&ap);
            (ap, h)
        })
        .collect();
    let env_inputs: Vec<(String, Option<String>)> =
        parsed.rerun_if_env_changed.iter().map(|k| (k.clone(), std::env::var(k).ok())).collect();
    Ok(Record {
        output_hash: output_hash(&parsed, Some(&out_dir_path)),
        script: script.to_path_buf(),
        script_hash: file_hash(script),
        inputs,
        env_inputs,
    })
}

/// Per-manifest record cache for one daemon: hashes by manifest dir, so
/// a second crate in the same workspace frame does not re-hash files
/// the first one just checked in the same instant. Kept minimal: the
/// daemon constructs a fresh check per request anyway; this exists so
/// `refresh` results can be shared by the cold-cache key path.
pub fn refresh_hash(manifest_dir: &Path, cache_dir: &Path, memo: &mut FxMap<PathBuf, u64>) -> u64 {
    if let Some(h) = memo.get(manifest_dir) {
        return *h;
    }
    let h = refresh(manifest_dir, cache_dir).hash();
    memo.insert(manifest_dir.to_path_buf(), h);
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Both directive spellings parse, and unrecorded keys are ignored.
    #[test]
    fn output_directives_parse() {
        let out = parse_output(
            "cargo::rerun-if-changed=build.rs\ncargo:rerun-if-changed=data.txt\n\
             cargo::rerun-if-env-changed=GOOS\ncargo::rustc-cfg=wasm_pack\n\
             cargo:rustc-env=GREETING=hi there\ncargo:warning=ignored\nnoise\n",
        );
        assert_eq!(out.rerun_if_changed, ["build.rs", "data.txt"]);
        assert_eq!(out.rerun_if_env_changed, ["GOOS"]);
        assert_eq!(out.rustc_cfg, ["wasm_pack"]);
        assert_eq!(out.rustc_env, [("GREETING".to_string(), "hi there".to_string())]);
    }

    /// A record round-trips, holds while its input files are unchanged,
    /// and goes stale the moment one changes (the refresh decision that
    /// matters; no Cargo run in this test).
    #[test]
    fn record_holds_until_an_input_changes() {
        let dir = std::env::temp_dir().join(format!("lust-buildscript-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let script = dir.join("build.rs");
        let data = dir.join("data.txt");
        std::fs::write(&script, "fn main() {}").unwrap();
        std::fs::write(&data, "v1").unwrap();
        let rec = Record {
            script: script.clone(),
            script_hash: file_hash(&script),
            inputs: vec![(data.clone(), file_hash(&data))],
            env_inputs: vec![("LUST_BS_TEST_ENV".into(), None)],
            output_hash: 42,
        };
        let back = Record::decode(&String::from_utf8(rec.encode()).unwrap()).unwrap();
        assert_eq!((back.script_hash, back.output_hash), (rec.script_hash, 42));
        assert!(back.inputs_still_hold(), "unchanged inputs hold");
        std::fs::write(&data, "v2").unwrap();
        assert!(!back.inputs_still_hold(), "edited rerun-if-changed file is stale");
        assert!(Record::decode("junk").is_none());
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// `build = false` and a custom `build = "gen.rs"` both win over the
    /// conventional build.rs.
    #[test]
    fn manifest_build_setting_wins() {
        let dir = std::env::temp_dir().join(format!("lust-buildscript-find-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("build.rs"), "fn main() {}").unwrap();
        std::fs::write(dir.join("Cargo.toml"), "[package]\nname = \"x\"\nbuild = false\n").unwrap();
        assert_eq!(build_script_for(&dir), None, "build = false");
        std::fs::write(dir.join("gen.rs"), "fn main() {}").unwrap();
        std::fs::write(dir.join("Cargo.toml"), "[package]\nname = \"x\"\nbuild = \"gen.rs\"\n").unwrap();
        assert_eq!(build_script_for(&dir), Some(dir.join("gen.rs")), "custom build path");
        std::fs::write(dir.join("Cargo.toml"), "[package]\nname = \"x\"\n").unwrap();
        assert_eq!(build_script_for(&dir), Some(dir.join("build.rs")), "conventional");
        let _ = std::fs::remove_dir_all(&dir);
    }
}
