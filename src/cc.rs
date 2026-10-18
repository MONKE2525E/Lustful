// The external C compiler backend (`lust build --release --target ...`):
// one lust front-end run per target cfg, then every emitted C unit compiles
// in parallel with `zig cc` (or clang/cc where that reaches the target) and
// links into the release binary. tcc stays the dev backend; this path runs
// only for `Request::cc` builds, which the daemon never serves.
//
// Flags are rel-opt's release set (round 1 report): optimized, with the
// aliasing and wrapping rules the emitted C relies on, plus -fexceptions
// and -lunwind so a unit set built for zero-cost unwinding (rel-opt round
// 2) links unchanged. `LUST_CC` replaces the compiler command (for example
// `LUST_CC="clang-18"` on a box with no zig, for host-reachable targets).
//
// Objects go through the disk cache: `unit_key` below is the one seam a
// smarter object cache (rel-cache) takes over. Its inputs are the C text,
// the compiler identity, the flag string, and the Rust target triple; an
// object is a function of those alone.
use std::path::{Path, PathBuf};
use std::process::Command;

/// One target's compiler setup: the command words, the flags every unit
/// gets, and how the link differs from a host link.
#[derive(Clone, Debug)]
pub struct CcSpec {
    /// The Rust triple as the user named it (the front end's cfg target).
    pub triple: String,
    /// Compiler command words, for example ["zig", "cc", "-target", "aarch64-linux-musl"].
    pub cmd: Vec<String>,
    /// Static link (musl release binaries, as ts-rust ships them).
    pub statik: bool,
    /// File name suffix of the output (".exe" on Windows triples).
    pub exe_suffix: &'static str,
}

/// The zig target spelling of a Rust triple. The front end keeps the Rust
/// cfg (a windows-msvc triple checks as msvc); only the C compiler and
/// linker see gnu, which is all zig ships libraries for.
pub fn zig_target(triple: &str) -> Option<&'static str> {
    Some(match triple {
        "x86_64-unknown-linux-gnu" => "x86_64-linux-gnu",
        "x86_64-unknown-linux-musl" => "x86_64-linux-musl",
        "aarch64-unknown-linux-gnu" => "aarch64-linux-gnu",
        "aarch64-unknown-linux-musl" => "aarch64-linux-musl",
        "aarch64-apple-darwin" => "aarch64-macos",
        "x86_64-apple-darwin" => "x86_64-macos",
        "x86_64-pc-windows-msvc" | "x86_64-pc-windows-gnu" => "x86_64-windows-gnu",
        "aarch64-pc-windows-msvc" => "aarch64-windows-gnu",
        _ => return None,
    })
}

/// True when `prog` is an executable on PATH.
fn on_path(prog: &str) -> bool {
    if prog.contains('/') {
        return Path::new(prog).exists();
    }
    std::env::var_os("PATH").is_some_and(|p| std::env::split_paths(&p).any(|d| d.join(prog).exists()))
}

/// The compiler spec for one Rust triple. `LUST_CC` (words split on
/// spaces) wins; a zig command gets `-target` appended when it does not
/// carry one. Without it: zig when present, else the host `cc` for a
/// triple this host already is (same arch and OS), else an error that
/// names the fix.
pub fn spec_for(triple: &str) -> Result<CcSpec, String> {
    let zt = zig_target(triple).ok_or_else(|| format!("no C compiler target for `{triple}`"))?;
    let statik = triple.ends_with("-musl");
    let exe_suffix = if triple.contains("windows") { ".exe" } else { "" };
    if let Ok(cc) = std::env::var("LUST_CC") {
        let mut cmd: Vec<String> = cc.split_whitespace().map(str::to_string).collect();
        if cmd.is_empty() {
            return Err("LUST_CC is empty".into());
        }
        let is_zig = Path::new(&cmd[0]).file_stem().is_some_and(|s| s == "zig");
        if is_zig && !cmd.iter().any(|a| a == "-target") {
            if cmd.len() == 1 {
                cmd.push("cc".into());
            }
            cmd.extend(["-target".into(), zt.into()]);
        }
        return Ok(CcSpec { triple: triple.into(), cmd, statik, exe_suffix });
    }
    if on_path("zig") {
        return Ok(CcSpec {
            triple: triple.into(),
            cmd: vec!["zig".into(), "cc".into(), "-target".into(), zt.into()],
            statik,
            exe_suffix,
        });
    }
    let (arch, os) = (triple.split('-').next().unwrap_or(""), triple);
    let host_like = arch == std::env::consts::ARCH
        && ((os.contains("linux") && std::env::consts::OS == "linux") || (os.contains("darwin") && std::env::consts::OS == "macos"));
    if host_like && on_path("cc") {
        // A host clang/gcc reaches this target as far as this driver
        // checks (same arch and OS; a musl static link still needs the
        // musl toolchain, which the link error will name).
        return Ok(CcSpec { triple: triple.into(), cmd: vec!["cc".into()], statik, exe_suffix });
    }
    Err(format!(
        "no C compiler for target `{triple}`: install zig (zig cc cross-compiles it) or set LUST_CC to a cross compiler command"
    ))
}

/// The C flags of every unit, one string so the cache key and the command
/// line can never disagree.
pub fn cflags(debug: bool) -> String {
    // -fsigned-char pins plain C char signed on every target (aarch64
    // defaults to unsigned): generated code keeps Rust bytes in
    // uint8_t and chars in uint32_t, so nothing should depend on it,
    // and after this flag nothing can (it also matches MSVC where the
    // windows-gnu build would otherwise differ on arm64).
    let base = "-O2 -std=gnu11 -w -fsigned-char -fno-strict-aliasing -fwrapv -fno-delete-null-pointer-checks -fexceptions -fno-asynchronous-unwind-tables";
    if debug { format!("{base} -g") } else { base.into() }
}

/// The link-time extras for one spec: libm for the float methods, the
/// unwinder for zig targets (its libc has none linked by default on musl
/// and windows-gnu), static where the spec asks, and a strip for release
/// size unless debug info was asked for.
fn ldflags(spec: &CcSpec, debug: bool) -> Vec<String> {
    let mut v: Vec<String> = Vec::new();
    if spec.statik {
        v.push("-static".into());
    }
    if !debug {
        v.push("-s".into());
    } else {
        v.push("-g".into());
    }
    if spec.cmd.first().is_some_and(|c| Path::new(c).file_stem().is_some_and(|s| s == "zig")) {
        v.push("-lunwind".into());
    }
    if !spec.triple.contains("windows") {
        v.push("-pthread".into());
    }
    v.push("-lm".into());
    v
}

/// The compiler identity for keys: the command, its `--version` first line,
/// and the size and modification time of the binary it resolves to (an
/// in-place toolchain update moves the key). Computed once per process.
fn compiler_id(cmd: &[String]) -> String {
    static ID: std::sync::OnceLock<std::sync::Mutex<std::collections::HashMap<Vec<String>, String>>> = std::sync::OnceLock::new();
    // One spec per process in practice (one lust-core per target); a map
    // keeps a second spec honest anyway.
    let map = ID.get_or_init(Default::default);
    if let Some(id) = map.lock().unwrap_or_else(|e| e.into_inner()).get(cmd).cloned() {
        return id;
    }
    let ver = Command::new(&cmd[0])
        .args(&cmd[1..])
        .arg("--version")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).lines().next().unwrap_or("").to_string())
        .unwrap_or_default();
    let bin = std::env::var_os("PATH")
        .and_then(|path| std::env::split_paths(&path).map(|d| d.join(&cmd[0])).find(|p| p.is_file()))
        .unwrap_or_else(|| PathBuf::from(&cmd[0]));
    let stamp = std::fs::metadata(std::fs::canonicalize(&bin).unwrap_or(bin))
        .map(|m| format!("{} {:?}", m.len(), m.modified().ok()))
        .unwrap_or_default();
    let id = format!("{} | {ver} | {stamp}", cmd.join(" "));
    map.lock().unwrap_or_else(|e| e.into_inner()).insert(cmd.to_vec(), id.clone());
    id
}

/// The disk cache key of one unit's object under this backend: the C text,
/// the compiler, the flags, the target, and `profile`, the digest of the PGO
/// data this unit's object depends on (see `Pgo::unit_digest`). A unit that
/// includes system headers (the runtime unit) keys on its preprocessed text
/// instead, so a header or sysroot change moves its key; the other units
/// include nothing.
pub fn unit_key(c_text: &str, spec: &CcSpec, debug: bool, profile: Option<&str>) -> String {
    let id = compiler_id(&spec.cmd);
    let flags = cflags(debug);
    let pre = c_text.contains("#include <").then(|| preprocessed(c_text, spec, &flags)).flatten();
    let text = pre.as_deref().unwrap_or(c_text.as_bytes());
    let (a, b) = crate::driver::cache::hash128(
        &[b"cc-v2", spec.triple.as_bytes(), id.as_bytes(), flags.as_bytes(), &[debug as u8], profile.unwrap_or("").as_bytes(), text],
        37,
    );
    format!("{a:016x}{b:016x}")
}

/// `c_text` after the preprocessor of `spec` with `flags`, or None when it
/// cannot run (the key then holds the raw text, and a failed compile reports
/// the real error).
fn preprocessed(c_text: &str, spec: &CcSpec, flags: &str) -> Option<Vec<u8>> {
    use std::io::Write as _;
    let mut cmd = Command::new(&spec.cmd[0]);
    cmd.args(&spec.cmd[1..]).args(flags.split_whitespace()).args(["-E", "-P", "-x", "c", "-", "-o", "-"]);
    let mut child = cmd.stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::null()).spawn().ok()?;
    let mut stdin = child.stdin.take()?;
    let text = c_text.to_string();
    let writer = std::thread::spawn(move || stdin.write_all(text.as_bytes()));
    let out = child.wait_with_output().ok()?;
    writer.join().ok()?.ok()?;
    out.status.success().then_some(out.stdout)
}

/// Compiles every unit and links `out`. `units` are (name, C text) pairs in
/// link order; `work` is a scratch dir for C files and objects the caller
/// owns. Returns a one-line summary, or the compiler's error text.
pub fn build(
    units: &[(String, String)],
    spec: &CcSpec,
    out: &Path,
    debug: bool,
    cache: Option<&crate::driver::cache::Cache>,
    work: &Path,
) -> Result<String, String> {
    std::fs::create_dir_all(work).map_err(|e| format!("cannot create {}: {e}", work.display()))?;
    let flags: Vec<String> = cflags(debug).split_whitespace().map(str::to_string).collect();
    // Largest units first, bounded workers: the tcc driver's shape
    // (src/tcc.rs), for the same reason (the tail is short units).
    let mut order: Vec<usize> = (0..units.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(units[i].1.len()));
    let objs: Vec<PathBuf> = units.iter().map(|(name, _)| work.join(format!("{name}.o"))).collect();
    let keys: Vec<Option<String>> = units.iter().map(|(_, c)| cache.map(|_| unit_key(c, spec, debug, None))).collect();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let errors = std::sync::Mutex::new(String::new());
    let hits = std::sync::atomic::AtomicUsize::new(0);
    let limit = crate::pool::threads().max(1).min(units.len().max(1));
    std::thread::scope(|scope| {
        for _ in 0..limit {
            scope.spawn(|| loop {
                let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(&i) = order.get(k) else { return };
                let (name, c) = &units[i];
                let obj = &objs[i];
                if let (Some(cache), Some(key)) = (cache, &keys[i])
                    && cache.unit_object(key, obj)
                {
                    hits.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    continue;
                }
                let src = work.join(format!("{name}.c"));
                let fail = |msg: String| errors.lock().unwrap_or_else(|e| e.into_inner()).push_str(&msg);
                if let Err(e) = std::fs::write(&src, c) {
                    fail(format!("cannot write {}: {e}\n", src.display()));
                    continue;
                }
                let mut cmd = Command::new(&spec.cmd[0]);
                cmd.args(&spec.cmd[1..]).args(&flags).arg("-c").arg(&src).arg("-o").arg(obj);
                match cmd.output() {
                    Ok(o) if o.status.success() => {
                        if let (Some(cache), Some(key)) = (cache, &keys[i]) {
                            cache.store_unit_object(key, obj);
                        }
                    }
                    Ok(o) => {
                        let mut msg = format!("--- unit {name} ({})\n", o.status);
                        msg.push_str(&String::from_utf8_lossy(&o.stderr));
                        fail(msg);
                    }
                    Err(e) => fail(format!("cannot run {}: {e}\n", spec.cmd.join(" "))),
                }
            });
        }
    });
    let errors = errors.into_inner().unwrap_or_else(|e| e.into_inner());
    if !errors.is_empty() {
        return Err(format!("the C compiler failed for target {}:\n{errors}", spec.triple));
    }
    let mut cmd = Command::new(&spec.cmd[0]);
    cmd.args(&spec.cmd[1..]).args(ldflags(spec, debug)).args(&objs).arg("-o").arg(out);
    match cmd.output() {
        Ok(o) if o.status.success() => Ok(format!(
            "{} units ({} from cache), linked {}",
            units.len(),
            hits.load(std::sync::atomic::Ordering::Relaxed),
            out.display()
        )),
        Ok(o) => Err(format!("link failed for target {} ({})\n{}", spec.triple, o.status, String::from_utf8_lossy(&o.stderr))),
        Err(e) => Err(format!("cannot run {}: {e}", spec.cmd.join(" "))),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn zig_targets_cover_the_release_triples() {
        assert_eq!(super::zig_target("aarch64-unknown-linux-musl"), Some("aarch64-linux-musl"));
        assert_eq!(super::zig_target("x86_64-pc-windows-msvc"), Some("x86_64-windows-gnu"));
        assert_eq!(super::zig_target("aarch64-apple-darwin"), Some("aarch64-macos"));
        assert_eq!(super::zig_target("riscv64gc-unknown-linux-gnu"), None);
    }

    #[test]
    fn unit_key_moves_with_every_input() {
        let spec = |triple: &str, cmd: &str| super::CcSpec {
            triple: triple.into(),
            cmd: cmd.split_whitespace().map(str::to_string).collect(),
            statik: false,
            exe_suffix: "",
        };
        let base = super::unit_key("int f(void);", &spec("aarch64-unknown-linux-musl", "zig cc"), false, None);
        assert_ne!(base, super::unit_key("int g(void);", &spec("aarch64-unknown-linux-musl", "zig cc"), false, None), "C text");
        assert_ne!(base, super::unit_key("int f(void);", &spec("x86_64-unknown-linux-musl", "zig cc"), false, None), "target");
        assert_ne!(base, super::unit_key("int f(void);", &spec("aarch64-unknown-linux-musl", "zig cc"), true, None), "debug");
        assert_ne!(base, super::unit_key("int f(void);", &spec("aarch64-unknown-linux-musl", "clang"), false, None), "compiler");
        assert_ne!(base, super::unit_key("int f(void);", &spec("aarch64-unknown-linux-musl", "zig cc"), false, Some("p1")), "profile");
    }
}
