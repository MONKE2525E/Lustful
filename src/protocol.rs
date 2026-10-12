// Command-line parsing and the daemon wire protocol. Shared by the thin `lust` client and the
// `lust-core` compiler, so the client stays small and starts fast.
//
// Wire format. Request: one line of tab-separated fields:
//   cmd  file  out  json  timings  debug  emit_c  max_errors
// The last field is optional on decode so an older client still works.
// Response: "<code> <stdout len> <stderr len>\n" followed by the two byte strings.
// Both binaries include this module and each uses only part of it.
#![allow(dead_code)]

use std::io::{BufRead, BufReader, Read, Write};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Cmd {
    Check,
    Build,
}

pub struct Request {
    pub cmd: Cmd,
    pub file: PathBuf,
    pub out: PathBuf,
    pub json: bool,
    pub timings: bool,
    pub debug: bool,
    pub emit_c: Option<PathBuf>,
    /// Cap on shown diagnostics (0 means no cap). See `diag::render`.
    pub max_errors: usize,
    /// For `lust run`: the program's arguments (without argv[0]), so a one-shot compile can
    /// run a small program in memory instead of building a file. The daemon wire format does
    /// not carry this (decode sets None): a daemon build still writes the executable and the
    /// client runs it.
    pub run_args: Option<Vec<String>>,
    /// For `lust test`: the file gets a generated `main`, so a missing user `main` is not
    /// an error. The daemon wire format does not carry this (decode sets false): `lust
    /// test` compiles in its own process.
    pub harness: bool,
}

#[derive(Default)]
pub struct Response {
    pub stdout: String,
    pub stderr: String,
    pub code: i32,
    /// The program already ran in memory; `code` is its exit code. Do not run `out` again.
    pub ran: bool,
}

pub enum Invocation {
    Daemon,
    /// `run` is a build, then the client runs the program with `args`.
    Compile {
        req: Request,
        run: bool,
        args: Vec<String>,
    },
    /// `lust build --release` / `--profile <name>`: hand the file to Cargo or rustc.
    /// Handled in the client process; never sent to the daemon.
    Release {
        file: PathBuf,
        out: Option<PathBuf>,
        profile: Option<String>,
        debug: bool,
    },
    /// `lust check --rustc`: run the real rustc as an oracle. Never sent to the daemon.
    RustcCheck {
        file: PathBuf,
    },
}

pub const USAGE: &str = "usage: lust <check|build|run> <file.rs> [--json] [--max-errors N] [--timings] [-o out] [-g] [--emit-c prefix] [-- args]\n       lust build <file.rs> --release | --profile <name> [-o out]\n       lust check <file.rs> --rustc\n       lust test <file.rs> [filter] [--json] [--timeout SECONDS] [--max-errors N]\n       lust explain <L####>\n       lust capabilities [--json]\n       lust daemon";

/// Parses the command line (without the program name). Paths become absolute.
pub fn parse_args(args: &[String]) -> Option<Invocation> {
    let mut it = args.iter();
    let cmd = it.next()?;
    if cmd == "daemon" {
        return Some(Invocation::Daemon);
    }
    if !["check", "build", "run"].contains(&cmd.as_str()) {
        return None;
    }
    let mut file = PathBuf::new();
    let (mut out, mut json, mut timings, mut debug, mut emit_c, mut run_args) = (None, false, false, false, None, Vec::new());
    let (mut release, mut profile, mut rustc) = (false, None, false);
    let mut max_errors = 20usize;
    while let Some(a) = it.next() {
        match a.as_str() {
            "--json" => json = true,
            "--timings" => timings = true,
            "-g" => debug = true,
            "-o" => out = Some(PathBuf::from(it.next()?)),
            "--emit-c" => emit_c = Some(PathBuf::from(it.next()?)),
            "--release" => release = true,
            "--profile" => profile = Some(it.next()?.clone()),
            "--rustc" => rustc = true,
            "--max-errors" => max_errors = it.next()?.parse().ok()?,
            _ if a.starts_with("--max-errors=") => max_errors = a["--max-errors=".len()..].parse().ok()?,
            "--" => run_args = it.by_ref().cloned().collect(),
            _ if file.as_os_str().is_empty() => file = a.into(),
            _ => return None,
        }
    }
    if file.as_os_str().is_empty() {
        return None;
    }
    let abs = |p: &Path| std::path::absolute(p).unwrap_or_else(|_| p.to_path_buf());
    // Release and the rustc oracle are build/check-only, with no extra lust flags.
    if rustc {
        if cmd != "check" || release || profile.is_some() || !run_args.is_empty() {
            return None;
        }
        return Some(Invocation::RustcCheck { file: abs(&file) });
    }
    if release || profile.is_some() {
        if cmd != "build" || !run_args.is_empty() || emit_c.is_some() {
            return None;
        }
        if release && profile.is_none() {
            profile = Some("release".into());
        }
        return Some(Invocation::Release { file: abs(&file), out: out.map(|p| abs(&p)), profile, debug });
    }
    let out = out.unwrap_or_else(|| PathBuf::from(file.file_stem().unwrap_or_default()));
    let run = cmd == "run";
    let req = Request {
        cmd: if cmd == "check" { Cmd::Check } else { Cmd::Build },
        file: abs(&file),
        out: abs(&out),
        json,
        timings,
        debug,
        emit_c: emit_c.map(|p| abs(&p)),
        max_errors,
        run_args: if run { Some(run_args.clone()) } else { None },
        harness: false,
    };
    Some(Invocation::Compile { req, run, args: run_args })
}

/// The daemon socket for the current directory. The name holds the compiler build hash, so a rebuilt
/// `lust` never talks to a daemon from an older build (that daemon exits on its idle timeout).
pub fn socket_path() -> PathBuf {
    std::env::var_os("LUST_DAEMON_SOCKET")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(format!(".lust-daemon-{}.sock", &env!("LUST_BUILD_HASH")[..8])))
}

pub fn encode(r: &Request) -> String {
    let b = |x: bool| if x { "1" } else { "0" };
    let cmd = if r.cmd == Cmd::Check { "check" } else { "build" };
    let emit = r.emit_c.as_ref().map(|p| p.display().to_string()).unwrap_or_default();
    format!("{cmd}\t{}\t{}\t{}\t{}\t{}\t{emit}\t{}\n", r.file.display(), r.out.display(), b(r.json), b(r.timings), b(r.debug), r.max_errors)
}

pub fn decode(line: &str) -> Option<Request> {
    let f: Vec<&str> = line.trim_end_matches('\n').split('\t').collect();
    if f.len() != 7 && f.len() != 8 {
        return None;
    }
    Some(Request {
        cmd: if f[0] == "check" { Cmd::Check } else { Cmd::Build },
        file: f[1].into(),
        out: f[2].into(),
        json: f[3] == "1",
        timings: f[4] == "1",
        debug: f[5] == "1",
        emit_c: if f[6].is_empty() { None } else { Some(f[6].into()) },
        max_errors: if f.len() == 8 { f[7].parse().ok()? } else { 20 },
        run_args: None,
        harness: false,
    })
}

pub fn write_response(w: &mut impl Write, r: &Response) -> std::io::Result<()> {
    write!(w, "{} {} {}\n{}{}", r.code, r.stdout.len(), r.stderr.len(), r.stdout, r.stderr)
}

/// Sends a request to a running daemon. None if no daemon answers.
pub fn request(sock: &Path, req: &Request) -> Option<Response> {
    let mut conn = UnixStream::connect(sock).ok()?;
    conn.write_all(encode(req).as_bytes()).ok()?;
    let mut reader = BufReader::new(conn);
    let mut head = String::new();
    reader.read_line(&mut head).ok()?;
    let nums: Vec<usize> = head.split_whitespace().filter_map(|x| x.parse().ok()).collect();
    if nums.len() != 3 {
        return None;
    }
    let mut out = vec![0; nums[1]];
    let mut err = vec![0; nums[2]];
    reader.read_exact(&mut out).ok()?;
    reader.read_exact(&mut err).ok()?;
    Some(Response {
        code: nums[0] as i32,
        stdout: String::from_utf8_lossy(&out).into_owned(),
        stderr: String::from_utf8_lossy(&err).into_owned(),
        ran: false,
    })
}

/// Prints a response. For `run`, runs the program after a successful build. Never returns.
pub fn finish(resp: Response, run: bool, out: &Path, args: &[String]) -> ! {
    print!("{}", resp.stdout);
    eprint!("{}", resp.stderr);
    let _ = std::io::stdout().flush();
    let _ = std::io::stderr().flush();
    if resp.ran || resp.code != 0 || !run {
        std::process::exit(resp.code);
    }
    let status = std::process::Command::new(out).args(args).status().expect("cannot run the program");
    std::process::exit(status.code().unwrap_or(134));
}

// ---------------------------------------------------------------------------
// Release builds and the rustc oracle. lust owns the dev loop; Cargo or rustc
// builds the shipped binary from the same source (rule zero). Output streams
// through this process. These paths never use the daemon or the disk cache.

/// Runs a child with this process's stdin/stdout/stderr. Exits with its code.
fn run_streamed(tool: &str, cmd: &mut std::process::Command) -> std::process::ExitStatus {
    match cmd.status() {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot run {tool}: {e}");
            std::process::exit(2);
        }
    }
}

/// Exits with a child status: its code, or 1 when a signal killed it.
fn exit_with(status: std::process::ExitStatus) -> ! {
    std::process::exit(status.code().unwrap_or(1));
}

/// The bits of a Cargo.toml that bin selection needs.
struct Manifest {
    dir: PathBuf,
    path: PathBuf,
    package: Option<String>,
    /// (bin name, path as written) per `[[bin]]` table.
    bins: Vec<(String, Option<String>)>,
}

/// A TOML string value after `key =`: quoted text (up to the closing quote, so a
/// trailing comment is dropped), else the bare token.
fn toml_value(line: &str) -> Option<String> {
    let v = line.split_once('=')?.1.trim();
    if let Some(rest) = v.strip_prefix(['"', '\'']) {
        let quote = v.as_bytes()[0] as char;
        return Some(rest.split(quote).next()?.to_string());
    }
    Some(v.trim_end_matches(|c: char| c == ',' || c.is_whitespace()).to_string())
}

/// Reads package name and `[[bin]]` tables from manifest text. Section-gated on purpose:
/// a `name` in `[dependencies]` or a profile table must never match.
fn parse_manifest(text: &str) -> (Option<String>, Vec<(String, Option<String>)>) {
    let mut package = None;
    let mut bins: Vec<(String, Option<String>)> = Vec::new();
    let mut section = "";
    for raw in text.lines() {
        let line = raw.trim();
        if line.starts_with('[') {
            section = line.trim_matches(|c| c == '[' || c == ']');
            if section == "bin" && line.starts_with("[[") {
                bins.push((String::new(), None));
            }
            continue;
        }
        let key = line.split('=').next().unwrap_or("").trim();
        match (section, key) {
            ("package", "name") if package.is_none() => package = toml_value(line),
            ("bin", "name") => {
                if let (Some(last), Some(v)) = (bins.last_mut(), toml_value(line)) {
                    last.0 = v;
                }
            }
            ("bin", "path") => {
                if let (Some(last), Some(v)) = (bins.last_mut(), toml_value(line)) {
                    last.1 = Some(v);
                }
            }
            _ => {}
        }
    }
    (package, bins)
}

/// The nearest Cargo.toml at or above the file's directory, if one exists.
fn find_manifest(file: &Path) -> Option<Manifest> {
    let mut dir = file.parent();
    while let Some(d) = dir {
        let path = d.join("Cargo.toml");
        if let Ok(text) = std::fs::read_to_string(&path) {
            let (package, bins) = parse_manifest(&text);
            return Some(Manifest { dir: d.to_path_buf(), path, package, bins });
        }
        dir = d.parent();
    }
    None
}

/// Which `--bin` a file selects inside its package. Cargo conventions first
/// (`src/bin/<name>.rs`, `src/bin/<name>/main.rs`), then `[[bin]] path`, then
/// `src/main.rs` as the package bin. A library or module file selects no bin:
/// the whole package builds.
fn selected_bin(m: &Manifest, file: &Path) -> Option<String> {
    let rel = file.strip_prefix(&m.dir).ok()?;
    let parts: Vec<String> = rel.components().map(|c| c.as_os_str().to_string_lossy().into_owned()).collect();
    if parts.len() == 3 && parts[0] == "src" && parts[1] == "bin" {
        return parts[2].strip_suffix(".rs").map(str::to_string);
    }
    if parts.len() == 4 && parts[0] == "src" && parts[1] == "bin" && parts[3] == "main.rs" {
        return Some(parts[2].clone());
    }
    let rel_str = rel.to_string_lossy().replace('\\', "/");
    if let Some((name, _)) = m.bins.iter().find(|(_, p)| p.as_deref() == Some(rel_str.as_str())) {
        return Some(name.clone());
    }
    if rel_str == "src/main.rs" {
        // An explicit [[bin]] for it won above. Else it is the package bin.
        return m.package.clone();
    }
    None
}

/// The target directory a manifest builds into, from `cargo metadata`.
/// Only used after a successful build when `-o` needs the artifact path.
fn cargo_target_dir(manifest: &Path) -> Option<PathBuf> {
    let out = std::process::Command::new("cargo")
        .args(["metadata", "--format-version", "1", "--no-deps", "--manifest-path"])
        .arg(manifest)
        .output()
        .ok()?;
    let text = String::from_utf8_lossy(&out.stdout);
    let at = text.find("\"target_directory\":\"")? + "\"target_directory\":\"".len();
    let end = text[at..].find('"')? + at;
    Some(PathBuf::from(text[at..end].replace("\\\\", "\\")))
}

/// `lust build --release` / `--profile <name>`. With a Cargo.toml above the file, Cargo
/// builds it with the file's package and bin selection. Without one, rustc builds the
/// single file with the release oracle flags from DESIGN.md. Never returns.
pub fn run_release(file: &Path, out: Option<&Path>, profile: Option<&str>, debug: bool) -> ! {
    let profile = profile.unwrap_or("release");
    let dev = profile == "dev";
    if let Some(m) = find_manifest(file) {
        let bin = selected_bin(&m, file);
        let mut args: Vec<std::ffi::OsString> = vec!["build".into(), "--manifest-path".into(), m.path.clone().into_os_string()];
        match profile {
            "release" => args.push("--release".into()),
            "dev" => {}
            name => args.extend(["--profile".into(), name.into()]),
        }
        if let Some(pkg) = &m.package {
            args.extend(["-p".into(), pkg.into()]);
        }
        if let Some(bin) = &bin {
            args.extend(["--bin".into(), bin.into()]);
        }
        eprintln!("lust: release build via cargo: cargo {}", args.iter().map(|a| a.to_string_lossy()).collect::<Vec<_>>().join(" "));
        let status = run_streamed("cargo", std::process::Command::new("cargo").args(&args));
        if !status.success() {
            exit_with(status);
        }
        // Cargo has no stable -o. Copy the artifact when the caller asked for one.
        if let Some(out) = out {
            let name = bin.as_ref().or(m.package.as_ref());
            let artifact = name.and_then(|n| cargo_target_dir(&m.path).map(|t| t.join(if dev { "debug" } else { profile }).join(n)));
            match artifact {
                Some(a) if a.exists() => {
                    if let Err(e) = std::fs::copy(&a, out) {
                        eprintln!("error: cannot copy {} to {}: {e}", a.display(), out.display());
                        std::process::exit(2);
                    }
                    eprintln!("lust: built with cargo: {} (copied to {})", a.display(), out.display());
                }
                _ => {
                    eprintln!("error: cargo built the package, but no binary artifact was found to copy to {}", out.display());
                    std::process::exit(2);
                }
            }
        } else {
            eprintln!("lust: built with cargo (profile {profile})");
        }
        std::process::exit(0);
    }
    // No Cargo.toml: rustc on the single file, with DESIGN.md's release oracle flags.
    let fallback = PathBuf::from(file.file_stem().unwrap_or_default());
    let out: &Path = out.unwrap_or(&fallback);
    let mut cmd = std::process::Command::new("rustc");
    cmd.args(["--edition", "2024", "-C", "panic=abort", "-A", "unconditional_panic"]);
    if dev {
        cmd.args(["-C", "overflow-checks=on"]);
    } else {
        cmd.args(["-O", "-C", "overflow-checks=off"]);
    }
    if debug {
        cmd.arg("-g");
    }
    cmd.arg("-o").arg(out).arg(file);
    eprintln!(
        "lust: release build via rustc: rustc --edition 2024 {} -o {} {}",
        if dev { "(dev flags)" } else { "-O" },
        out.display(),
        file.display()
    );
    let status = run_streamed("rustc", &mut cmd);
    if status.success() {
        eprintln!("lust: built with rustc: {}", out.display());
    }
    exit_with(status);
}

/// `lust check --rustc`: the real rustc check (metadata only, no binary) with the dev
/// oracle flags from DESIGN.md. A second opinion for agents. Never returns.
pub fn run_rustc_check(file: &Path) -> ! {
    let meta = std::env::temp_dir().join(format!("lust-rustc-check-{}.rmeta", std::process::id()));
    eprintln!("lust: checking with rustc (oracle): rustc --edition 2024 --emit=metadata {}", file.display());
    let status = run_streamed(
        "rustc",
        std::process::Command::new("rustc")
            .args([
                "--edition",
                "2024",
                "-C",
                "panic=abort",
                "-C",
                "overflow-checks=on",
                "-A",
                "unconditional_panic",
                "--emit=metadata",
                "-o",
            ])
            .arg(&meta)
            .arg(file),
    );
    let _ = std::fs::remove_file(&meta);
    exit_with(status);
}

// ---------------------------------------------------------------------------
// Daemon startup shared by the client (autostart) and the daemon (single
// instance, idle exit). The lock file sits next to the socket and holds the
// daemon's pid. The daemon holds an flock on it for its whole life.

/// The lock file for a daemon socket: `<socket>.lock`.
pub fn daemon_lock_path(sock: &Path) -> PathBuf {
    let mut s = sock.as_os_str().to_owned();
    s.push(".lock");
    PathBuf::from(s)
}

/// How long a daemon may sit idle before it exits. `LUST_DAEMON_IDLE` is seconds,
/// or seconds with an `s`, `m`, or `h` suffix. Default 30 minutes. 0 means never.
pub fn daemon_idle() -> Option<std::time::Duration> {
    let raw = std::env::var("LUST_DAEMON_IDLE").unwrap_or_else(|_| "1800".into());
    let (num, mul) = match raw.chars().last() {
        Some('m') => (&raw[..raw.len() - 1], 60),
        Some('h') => (&raw[..raw.len() - 1], 3600),
        Some('s') => (&raw[..raw.len() - 1], 1),
        _ => (raw.as_str(), 1),
    };
    match num.trim().parse::<u64>() {
        Ok(0) => None,
        Ok(n) => Some(std::time::Duration::from_secs(n * mul)),
        Err(_) => Some(std::time::Duration::from_secs(1800)),
    }
}
