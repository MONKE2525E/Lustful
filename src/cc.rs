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
// A build with unwind tables has one C++ unit (a name ending in `.cc`, the
// throw and the catch of src/runtime/unwind.cc): the C++ driver of the same
// compiler (`CcSpec::cxx`) compiles it and links the binary, which brings
// in the C++ runtime and personality.
//
// Objects go through the disk cache: `unit_key` below is the one seam a
// smarter object cache (rel-cache) takes over. Its inputs are the C text,
// the compiler identity, the flag string, the Rust target triple, and with
// PGO (`cc/pgo.rs`) the unit's own part of the profile; an object is a
// function of those alone.
use std::path::{Path, PathBuf};
use std::process::Command;

mod pgo;
mod rtinl;

/// One target's compiler setup: the command words, the flags every unit
/// gets, and how the link differs from a host link.
#[derive(Clone, Debug)]
pub struct CcSpec {
    /// The Rust triple as the user named it (the front end's cfg target).
    pub triple: String,
    /// Compiler command words, for example ["zig", "cc", "-target", "aarch64-linux-musl"].
    pub cmd: Vec<String>,
    /// The C++ driver of the same compiler (`cxx_for`), for a `.cc` unit and its link.
    pub cxx: Vec<String>,
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

/// True when `prog` names zig (`zig`, `/opt/zig/zig`).
fn is_zig(prog: &str) -> bool {
    Path::new(prog).file_stem().is_some_and(|s| s == "zig")
}

/// The C++ driver that goes with a C compiler command: `zig cc` -> `zig c++`,
/// `clang[-N]` -> `clang++[-N]`, `[prefix-]gcc[-N]` -> `[prefix-]g++[-N]`, `cc` ->
/// `c++`; other names stay (they must take C++ themselves). `LUST_CXX` (words)
/// replaces it.
fn cxx_for(cmd: &[String]) -> Vec<String> {
    if let Ok(cxx) = std::env::var("LUST_CXX") {
        let words: Vec<String> = cxx.split_whitespace().map(str::to_string).collect();
        if !words.is_empty() {
            return words;
        }
    }
    let mut v = cmd.to_vec();
    if v.first().is_some_and(|c| is_zig(c)) {
        if let Some(w) = v.iter_mut().find(|w| *w == "cc") {
            *w = "c++".into();
        }
        return v;
    }
    let Some(first) = v.first_mut() else { return v };
    let path = Path::new(first.as_str());
    let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("").to_string();
    let cxx = if name.contains("++") {
        name
    } else if let Some(i) = name.rfind("clang") {
        format!("{}clang++{}", &name[..i], &name[i + 5..])
    } else if let Some(i) = name.rfind("gcc") {
        format!("{}g++{}", &name[..i], &name[i + 3..])
    } else if name == "cc" {
        "c++".into()
    } else {
        name
    };
    *first = path.with_file_name(cxx).to_string_lossy().into_owned();
    v
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
        if is_zig(&cmd[0]) && !cmd.iter().any(|a| a == "-target") {
            if cmd.len() == 1 {
                cmd.push("cc".into());
            }
            cmd.extend(["-target".into(), zt.into()]);
        }
        let cxx = cxx_for(&cmd);
        return Ok(CcSpec { triple: triple.into(), cmd, cxx, statik, exe_suffix });
    }
    if on_path("zig") {
        let cmd: Vec<String> = vec!["zig".into(), "cc".into(), "-target".into(), zt.into()];
        let cxx = cxx_for(&cmd);
        return Ok(CcSpec { triple: triple.into(), cmd, cxx, statik, exe_suffix });
    }
    let (arch, os) = (triple.split('-').next().unwrap_or(""), triple);
    let host_like = arch == std::env::consts::ARCH
        && ((os.contains("linux") && std::env::consts::OS == "linux") || (os.contains("darwin") && std::env::consts::OS == "macos"));
    if host_like && on_path("cc") {
        // A host clang/gcc reaches this target as far as this driver
        // checks (same arch and OS; a musl static link still needs the
        // musl toolchain, which the link error will name).
        let cmd = vec!["cc".to_string()];
        let cxx = cxx_for(&cmd);
        return Ok(CcSpec { triple: triple.into(), cmd, cxx, statik, exe_suffix });
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
    // -fomit-frame-pointer: zig cc keeps a frame pointer in every fn
    // (7% of a release tsgo's instructions); nothing walks them, as
    // unwinding reads .eh_frame. Targets whose ABI needs one keep it.
    let base = "-O2 -std=gnu11 -w -fsigned-char -fno-strict-aliasing -fwrapv -fno-delete-null-pointer-checks -fexceptions -fno-asynchronous-unwind-tables -fomit-frame-pointer";
    if debug { format!("{base} -g") } else { base.into() }
}

/// mimalloc as one C unit that replaces malloc and free (`MI_MALLOC_OVERRIDE`): the
/// allocator of musl release builds, whose own malloc ran tsgo 3.2x slower. Allocation
/// strategy is not observable. `MI_BUILD_RELEASE`: without it (or NDEBUG) mimalloc builds
/// its debug mode, with asserts on every call and warnings on stderr when memory runs out
/// (rustc's binary prints only its own message). None when the build had no mimalloc
/// source (build.rs).
pub fn mimalloc_unit() -> Option<String> {
    let src = include_str!(concat!(env!("OUT_DIR"), "/mimalloc.c"));
    (!src.is_empty()).then(|| format!("#define MI_MALLOC_OVERRIDE 1\n#define MI_BUILD_RELEASE 1\n{src}"))
}

/// Vector memcpy, memmove, memcmp, bcmp and memchr as one C unit for musl targets
/// (src/runtime/memfast.c): musl's and zig's forms are byte or word loops, which a release
/// tsgo spent 2.3 G instructions in on the TypeORM check. The results are libc's.
pub fn memfast_unit() -> String {
    include_str!("runtime/memfast.c").to_string()
}

/// The flags of a `.cc` unit (the runtime's throw and catch).
pub fn cxxflags(debug: bool) -> String {
    let base = "-O2 -w -fexceptions -fomit-frame-pointer";
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
    if spec.cmd.first().is_some_and(|c| is_zig(c)) {
        v.push("-lunwind".into());
    }
    if !spec.triple.contains("windows") {
        v.push("-pthread".into());
    }
    v.push("-lm".into());
    // Extra link flags, for measurement (for example section GC or hot/cold text grouping).
    if let Ok(extra) = std::env::var("LUST_RELEASE_LDFLAGS") {
        v.extend(extra.split_whitespace().map(str::to_string));
    }
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

/// The disk cache key of one unit's object under this backend: the C (or,
/// `cxx`, C++) text, the compiler, the flags, the target, and `profile`, the
/// digest of the PGO data this unit's object depends on (see
/// `pgo::Mode::key_part`). A unit that includes system headers (the runtime
/// unit, the C++ unit) keys on its preprocessed text instead, so a header or
/// sysroot change moves its key; the other units include nothing.
pub fn unit_key(c_text: &str, spec: &CcSpec, debug: bool, profile: Option<&str>, cxx: bool) -> String {
    let (words, flags) = if cxx { (&spec.cxx, cxxflags(debug)) } else { (&spec.cmd, cflags(debug)) };
    let id = compiler_id(words);
    let pre = c_text.contains("#include <").then(|| preprocessed(c_text, words, &flags, cxx)).flatten();
    let text = pre.as_deref().unwrap_or(c_text.as_bytes());
    let (a, b) = crate::driver::cache::hash128(
        &[b"cc-v2", spec.triple.as_bytes(), id.as_bytes(), flags.as_bytes(), &[debug as u8, cxx as u8], profile.unwrap_or("").as_bytes(), text],
        37,
    );
    format!("{a:016x}{b:016x}")
}

/// A command that runs the C compiler (or links through it). gcc 7+, clang 16+ and zig cc
/// take `__DATE__` and `__TIME__` from `SOURCE_DATE_EPOCH`, fixed here unless the caller
/// set it: mimalloc's unit prints them, so its object, and its key (the preprocessed text,
/// `unit_key`), changed every second and a release binary with the build time.
fn cc_command(prog: impl AsRef<std::ffi::OsStr>) -> Command {
    let mut cmd = Command::new(prog);
    if std::env::var_os("SOURCE_DATE_EPOCH").is_none() {
        cmd.env("SOURCE_DATE_EPOCH", "0");
    }
    cmd
}

/// `c_text` (C++ text with `cxx`) after the preprocessor of the compiler
/// `words` with `flags`, or None when it cannot run (the key then holds the
/// raw text, and a failed compile reports the real error).
fn preprocessed(c_text: &str, words: &[String], flags: &str, cxx: bool) -> Option<Vec<u8>> {
    use std::io::Write as _;
    let mut cmd = cc_command(&words[0]);
    cmd.args(&words[1..]).args(flags.split_whitespace()).args(["-E", "-P", "-x", if cxx { "c++" } else { "c" }, "-", "-o", "-"]);
    let mut child = cmd.stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).stderr(std::process::Stdio::null()).spawn().ok()?;
    let mut stdin = child.stdin.take()?;
    let text = c_text.to_string();
    let writer = std::thread::spawn(move || stdin.write_all(text.as_bytes()));
    let out = child.wait_with_output().ok()?;
    writer.join().ok()?.ok()?;
    out.status.success().then_some(out.stdout)
}

/// The flags of an LLVM unit's own compile (its IR plus its C half's bitcode).
/// `LUST_LL_OPT` replaces the optimization level (default -O2; for measurement).
pub fn llflags(debug: bool) -> String {
    let opt = std::env::var("LUST_LL_OPT").unwrap_or_else(|_| "-O2".into());
    let base = format!("{opt} -w -fexceptions");
    if debug { format!("{base} -g") } else { base }
}

/// Compiles one LLVM backend unit into `obj`: the C unit `src` and the helpers' C `hc` to
/// bitcode with the C flags (no LLVM passes yet), then the IR `ll` with both linked in, so
/// the optimizer sees one module (cgen/ll.rs: the C helpers inline into the LLVM fns). The
/// helpers link as builtin bitcode: only what the IR names, internalized, so the copies
/// left after inlining are dropped instead of compiled. `pgo`: the unit's PGO flags
/// (`pgo::Mode::unit_flags`) for that last step, which then runs inside `src`'s dir on the
/// IR's bare file name, as the profile names the module's static fns by it. `rt_inl`: the
/// runtime's inlinable copy (`compile_runtime_ir`), linked as builtin bitcode too.
#[allow(clippy::too_many_arguments)]
fn compile_pair(spec: &CcSpec, cflags: &[String], debug: bool, src: &Path, ll: &str, hc: &str, obj: &Path, pgo: Option<&[String]>, rt_inl: Option<&Path>) -> Result<(), String> {
    let bc = src.with_extension("c.bc");
    let ll_path = src.with_extension("ll");
    let hc_path = src.with_extension("hc.c");
    let hbc = src.with_extension("hc.bc");
    std::fs::write(&ll_path, ll).map_err(|e| format!("cannot write {}: {e}\n", ll_path.display()))?;
    std::fs::write(&hc_path, hc).map_err(|e| format!("cannot write {}: {e}\n", hc_path.display()))?;
    let run = |cmd: &mut Command| -> Result<(), String> {
        match cmd.output() {
            Ok(o) if o.status.success() => Ok(()),
            Ok(o) => Err(format!("({})\n{}", o.status, String::from_utf8_lossy(&o.stderr))),
            Err(e) => Err(format!("cannot run {}: {e}\n", spec.cmd.join(" "))),
        }
    };
    let words = &spec.cmd;
    // No `noundef` on C values: the C halves pass aggregates' bits as integers
    // (cgen/ll.rs `Pass::Bits`, `Pass::Pair`), which may hold uninitialized bytes.
    let to_bc = |from: &Path, to: &Path| {
        run(cc_command(&words[0])
            .args(&words[1..])
            .args(cflags)
            .args(["-emit-llvm", "-Xclang", "-disable-llvm-passes", "-Xclang", "-no-enable-noundef-analysis", "-c"])
            .arg(from)
            .arg("-o")
            .arg(to))
    };
    to_bc(src, &bc)?;
    to_bc(&hc_path, &hbc)?;
    // A relative compiler path must not resolve against the work dir (PGO compiles there).
    let prog = if words[0].contains('/') { std::fs::canonicalize(&words[0]).unwrap_or_else(|_| PathBuf::from(&words[0])) } else { PathBuf::from(&words[0]) };
    let mut cmd = cc_command(prog);
    cmd.args(&words[1..]).args(llflags(debug).split_whitespace()).arg("-c");
    match (pgo, ll_path.parent(), ll_path.file_name()) {
        (Some(flags), Some(dir), Some(file)) => cmd.args(flags).current_dir(dir).arg(file),
        _ => cmd.arg(&ll_path),
    };
    let abs = |p: &Path| std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf());
    cmd.args(["-Xclang", "-mlink-bitcode-file", "-Xclang"]).arg(abs(&bc)).args(["-Xclang", "-mlink-builtin-bitcode", "-Xclang"]).arg(abs(&hbc));
    if let Some(rt) = rt_inl {
        cmd.args(["-Xclang", "-mlink-builtin-bitcode", "-Xclang"]).arg(abs(rt));
    }
    run(cmd.arg("-o").arg(obj))
}

/// Compiles the runtime unit `src` through LLVM IR (`rtinl.rs`): the C to IR with the full
/// pipeline (and the unit's profile: `pgo`, then inside `src`'s dir), `rtinl::split`, its
/// object `obj` from the IR with every internal symbol exported (no IR passes again), and
/// `inl`, the bitcode of the copy the LLVM units inline from (fns of at most `max`
/// instructions).
fn compile_runtime_ir(spec: &CcSpec, cflags: &[String], src: &Path, obj: &Path, inl: &Path, max: usize, pgo: Option<&[String]>) -> Result<(), String> {
    let words = &spec.cmd;
    let prog = if words[0].contains('/') { std::fs::canonicalize(&words[0]).unwrap_or_else(|_| PathBuf::from(&words[0])) } else { PathBuf::from(&words[0]) };
    let run = |extra: &[&str], input: &Path, out: &Path, pgo: Option<&[String]>| -> Result<(), String> {
        let mut cmd = Command::new(&prog);
        cmd.args(&words[1..]).args(cflags).args(extra);
        match (pgo, input.parent(), input.file_name()) {
            (Some(flags), Some(dir), Some(file)) => cmd.args(flags).current_dir(dir).arg(file),
            _ => cmd.arg(input),
        };
        match cmd.arg("-o").arg(out).output() {
            Ok(o) if o.status.success() => Ok(()),
            Ok(o) => Err(format!("({})\n{}", o.status, String::from_utf8_lossy(&o.stderr))),
            Err(e) => Err(format!("cannot run {}: {e}\n", words.join(" "))),
        }
    };
    let (ir, obj_ll, inl_ll) = (src.with_extension("rt.ll"), src.with_extension("obj.ll"), src.with_extension("inl.ll"));
    let ir = std::fs::canonicalize(src.parent().unwrap_or(Path::new("."))).map(|d| d.join(ir.file_name().unwrap_or_default())).unwrap_or(ir);
    run(&["-S", "-emit-llvm"], src, &ir, pgo)?;
    let text = std::fs::read_to_string(&ir).map_err(|e| format!("cannot read {}: {e}\n", ir.display()))?;
    let parts = rtinl::split(&text, max);
    std::fs::write(&obj_ll, parts.obj).map_err(|e| format!("cannot write {}: {e}\n", obj_ll.display()))?;
    std::fs::write(&inl_ll, parts.inl).map_err(|e| format!("cannot write {}: {e}\n", inl_ll.display()))?;
    run(&["-Xclang", "-disable-llvm-passes", "-c"], &obj_ll, obj, None)?;
    run(&["-emit-llvm", "-Xclang", "-disable-llvm-passes", "-c"], &inl_ll, inl, None)
}

/// What the PGO split (`pgo::defined_externs`, `pgo::stable_name`) reads for an LLVM unit:
/// its C half, then a C definition line for each external fn its IR defines (its own and
/// the `available_externally` copies, whose bodies the profile annotates too).
fn ll_profile_text(c: &str, ll: &str) -> String {
    let mut out = c.to_string();
    for line in ll.lines().filter(|l| l.starts_with("define ") && !l.starts_with("define internal ") && !l.starts_with("define private ")) {
        if let Some(at) = line.find(" @")
            && let Some(len) = line[at + 2..].find('(')
        {
            out.push_str(&format!("\nvoid {}(void) {{\n}}\n", &line[at + 2..at + 2 + len]));
        }
    }
    out
}

/// Compiles every unit and links `out`. `units` are (name, C text) pairs in
/// link order (a name ending in `.cc` is C++ text, for `spec.cxx`); `work`
/// is a scratch dir for C files and objects the caller owns. Returns a
/// one-line summary, or the compiler's error text.
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
    let cxx_flags: Vec<String> = cxxflags(debug).split_whitespace().map(str::to_string).collect();
    let is_cxx = |name: &str| name.ends_with(".cc");
    // The LLVM backend (cgen/ll.rs): a unit `u<N>.ll` is the LLVM IR of the C unit `u<N>`, and
    // `u<N>.hc` the C of its helpers; the three compile as one module into `u<N>.o`
    // (`compile_pair`) and key on all three texts. For PGO such a unit is `<name>.ll`: the
    // profile names the combined module's static fns by the IR's file name.
    let ll_of: std::collections::HashMap<&str, &str> =
        units.iter().filter_map(|(name, text)| name.strip_suffix(".ll").map(|stem| (stem, text.as_str()))).collect();
    let hc_of: std::collections::HashMap<&str, &str> =
        units.iter().filter_map(|(name, text)| name.strip_suffix(".hc").map(|stem| (stem, text.as_str()))).collect();
    let units: Vec<&(String, String)> = units.iter().filter(|(name, _)| !name.ends_with(".ll") && !name.ends_with(".hc")).collect();
    // PGO (`pgo.rs`): the C units compile from inside `work` under content-derived
    // names, as the profile names their static functions by file, and each key holds
    // that unit's own part of the profile. The C++ unit is not profiled.
    let pgo_on = std::env::var_os("LUST_PGO_GEN").is_some() || std::env::var_os("LUST_PGO_USE").is_some();
    let work = &if pgo_on { std::fs::canonicalize(work).map_err(|e| format!("cannot resolve {}: {e}", work.display()))? } else { work.to_path_buf() };
    let ll_texts: Vec<Option<String>> =
        units.iter().map(|(name, c)| ll_of.get(name.as_str()).filter(|_| pgo_on).map(|ll| ll_profile_text(c, ll))).collect();
    let names: Vec<String> = units
        .iter()
        .zip(&ll_texts)
        .map(|((name, c), llt)| if pgo_on && !is_cxx(name) { pgo::stable_name(llt.as_deref().unwrap_or(c)).unwrap_or_else(|| name.clone()) } else { name.clone() })
        .collect();
    // The LLVM units by their PGO names (`ll_of` and `hc_of` stay by unit name).
    let is_ll: Vec<bool> = units.iter().map(|(name, _)| ll_of.contains_key(name.as_str())).collect();
    let pfile = |i: usize| if is_ll[i] { format!("{}.ll", names[i]) } else { format!("{}.c", names[i]) };
    let files: Vec<(String, &str)> =
        (0..units.len()).filter(|&i| !is_cxx(&names[i])).map(|i| (pfile(i), ll_texts[i].as_deref().unwrap_or(&units[i].1))).collect();
    let pgo = pgo::Mode::from_env(spec, work, &files)?;
    let pgo_of = |i: usize| pgo.as_ref().filter(|_| !is_cxx(&names[i]));
    // An instrumented build needs a compiler with a profile runtime (`pgo::gen_spec`).
    let gen_spec = if matches!(pgo, Some(pgo::Mode::Gen)) { Some(pgo::gen_spec(spec)?) } else { None };
    let spec = gen_spec.as_ref().unwrap_or(spec);
    // Largest units first, bounded workers: the tcc driver's shape
    // (src/tcc.rs), for the same reason (the tail is short units).
    let mut order: Vec<usize> = (0..units.len()).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(units[i].1.len() + ll_of.get(units[i].0.as_str()).map_or(0, |l| l.len())));
    let objs: Vec<PathBuf> = names.iter().map(|name| work.join(format!("{name}.o"))).collect();
    let hits = std::sync::atomic::AtomicUsize::new(0);
    // `LUST_LL_RTINL=<max instructions>` (0 or unset: off): with LLVM units, the runtime unit
    // compiles through IR first (`compile_runtime_ir`) and every LLVM unit links the
    // runtime's fns of at most that size as inlinable IR (not in an instrumented build,
    // whose counters must stay the runtime's). LLVM unit keys hold that copy's digest.
    // Off by default: a PGO build lost half its fns' profile with it (the training build has
    // no runtime IR, and the PGO pre-inliner inlines runtime fns before it hashes CFGs).
    let rt_max: usize = std::env::var("LUST_LL_RTINL").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let rt = (rt_max > 0 && !ll_of.is_empty() && !matches!(pgo, Some(pgo::Mode::Gen)))
        .then(|| units.iter().position(|(_, c)| c.starts_with("#define LUST_IMPL 1\n")))
        .flatten();
    let rt_inl = work.join("runtime.inl.bc");
    let rt_digest = match rt {
        Some(r) => {
            let part = pgo_of(r).map(|m| m.key_part(&pfile(r)));
            let key = cache.map(|_| unit_key(&format!("{}\n/* rtinl {rt_max} */", units[r].1), spec, debug, part.as_deref(), false));
            let cached = matches!((cache, &key), (Some(c), Some(k)) if c.unit_object(k, &objs[r]) && c.unit_object(&format!("{k}-inl"), &rt_inl));
            if cached {
                hits.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            } else {
                let src = work.join(format!("{}.c", names[r]));
                std::fs::write(&src, &units[r].1).map_err(|e| format!("cannot write {}: {e}", src.display()))?;
                let pf = pgo_of(r).map(|m| m.unit_flags(&pfile(r))).transpose()?;
                compile_runtime_ir(spec, &flags, &src, &objs[r], &rt_inl, rt_max, pf.as_deref())
                    .map_err(|e| format!("the C compiler failed for target {} (runtime IR):\n{e}", spec.triple))?;
                if let (Some(c), Some(k)) = (cache, &key) {
                    c.store_unit_object(k, &objs[r]);
                    c.store_unit_object(&format!("{k}-inl"), &rt_inl);
                }
            }
            let bytes = std::fs::read(&rt_inl).map_err(|e| format!("cannot read {}: {e}", rt_inl.display()))?;
            let (a, b) = crate::driver::cache::hash128(&[&bytes], 47);
            format!("{a:016x}{b:016x}")
        }
        None => String::new(),
    };
    let keys: Vec<Option<String>> = units
        .iter()
        .enumerate()
        .map(|(i, (unit, c))| {
            let part = pgo_of(i).map(|m| m.key_part(&pfile(i)));
            cache.map(|_| match ll_of.get(unit.as_str()) {
                Some(ll) => {
                    let hc = hc_of.get(unit.as_str()).copied().unwrap_or("");
                    unit_key(&format!("{c}\n/* llvm-v2 {} */\n{ll}\n/* helpers */\n{hc}\n/* rtinl {rt_digest} */", llflags(debug)), spec, debug, part.as_deref(), false)
                }
                None => unit_key(c, spec, debug, part.as_deref(), is_cxx(&names[i])),
            })
        })
        .collect();
    let next = std::sync::atomic::AtomicUsize::new(0);
    let errors = std::sync::Mutex::new(String::new());
    let limit = crate::pool::threads().max(1).min(units.len().max(1));
    let t_compile = std::time::Instant::now();
    std::thread::scope(|scope| {
        for _ in 0..limit {
            scope.spawn(|| loop {
                let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some(&i) = order.get(k) else { return };
                if Some(i) == rt {
                    continue;
                }
                let (name, c) = (&names[i], &units[i].1);
                let obj = &objs[i];
                if let (Some(cache), Some(key)) = (cache, &keys[i])
                    && cache.unit_object(key, obj)
                {
                    hits.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    continue;
                }
                let cxx = is_cxx(name);
                let src = if cxx { work.join(name) } else { work.join(format!("{name}.c")) };
                let fail = |msg: String| errors.lock().unwrap_or_else(|e| e.into_inner()).push_str(&msg);
                if let Err(e) = std::fs::write(&src, c) {
                    fail(format!("cannot write {}: {e}\n", src.display()));
                    continue;
                }
                if let Some(ll) = ll_of.get(units[i].0.as_str()) {
                    let pf = match pgo_of(i).map(|m| m.unit_flags(&pfile(i))).transpose() {
                        Ok(pf) => pf,
                        Err(e) => {
                            fail(format!("--- unit {name}: {e}\n"));
                            continue;
                        }
                    };
                    match compile_pair(spec, &flags, debug, &src, ll, hc_of.get(units[i].0.as_str()).copied().unwrap_or(""), obj, pf.as_deref(), rt.map(|_| rt_inl.as_path())) {
                        Ok(()) => {
                            if let (Some(cache), Some(key)) = (cache, &keys[i]) {
                                cache.store_unit_object(key, obj);
                            }
                        }
                        Err(e) => fail(format!("--- unit {name} (LLVM)\n{e}")),
                    }
                    continue;
                }
                let (words, unit_flags) = if cxx { (&spec.cxx, &cxx_flags) } else { (&spec.cmd, &flags) };
                // A relative compiler path must not resolve against `work` (PGO compiles there).
                let prog = if words[0].contains('/') { std::fs::canonicalize(&words[0]).unwrap_or_else(|_| PathBuf::from(&words[0])) } else { PathBuf::from(&words[0]) };
                let mut cmd = cc_command(prog);
                cmd.args(&words[1..]).args(unit_flags).arg("-o").arg(obj);
                match pgo_of(i).map(|m| m.unit_flags(&pfile(i))) {
                    Some(Ok(pf)) => {
                        cmd.args(pf).current_dir(work).arg("-c").arg(format!("{name}.c"));
                    }
                    Some(Err(e)) => {
                        fail(format!("--- unit {name}: {e}\n"));
                        continue;
                    }
                    None => {
                        cmd.arg("-c").arg(&src);
                    }
                }
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
                    Err(e) => fail(format!("cannot run {}: {e}\n", words.join(" "))),
                }
            });
        }
    });
    let errors = errors.into_inner().unwrap_or_else(|e| e.into_inner());
    if !errors.is_empty() {
        return Err(format!("the C compiler failed for target {}:\n{errors}", spec.triple));
    }
    let compile_s = t_compile.elapsed().as_secs_f64();
    let t_link = std::time::Instant::now();
    // A build with a C++ unit links with the C++ driver (its runtime and personality).
    let link = if units.iter().any(|(name, _)| is_cxx(name)) { &spec.cxx } else { &spec.cmd };
    let mut cmd = cc_command(&link[0]);
    cmd.args(&link[1..]).args(ldflags(spec, debug)).args(pgo.as_ref().map(pgo::Mode::link_flags).unwrap_or_default()).args(&objs).arg("-o").arg(out);
    match cmd.output() {
        Ok(o) if o.status.success() => Ok(format!(
            "{} units ({} from cache, clang {:.2}s, link {:.2}s{}), linked {}",
            units.len(),
            hits.load(std::sync::atomic::Ordering::Relaxed),
            compile_s,
            t_link.elapsed().as_secs_f64(),
            pgo.as_ref().map(|m| format!(", {}", m.describe())).unwrap_or_default(),
            out.display()
        )),
        Ok(o) => Err(format!("link failed for target {} ({})\n{}", spec.triple, o.status, String::from_utf8_lossy(&o.stderr))),
        Err(e) => Err(format!("cannot run {}: {e}", link.join(" "))),
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn an_llvm_unit_owns_the_records_of_its_ir_fns_and_copies() {
        let c = "void f_aa(void) {\n}\n";
        let ll = "define void @fl_aa(ptr %p) uwtable {\nentry:\n  ret void\n}\ndefine available_externally i64 @fl_bb() {\nentry:\n  ret i64 0\n}\ndefine internal void @k() {\nentry:\n  ret void\n}\n";
        let text = super::ll_profile_text(c, ll);
        assert_eq!(super::pgo::defined_externs(&text), vec!["f_aa", "fl_aa", "fl_bb"]);
    }

    #[test]
    fn zig_targets_cover_the_release_triples() {
        assert_eq!(super::zig_target("aarch64-unknown-linux-musl"), Some("aarch64-linux-musl"));
        assert_eq!(super::zig_target("x86_64-pc-windows-msvc"), Some("x86_64-windows-gnu"));
        assert_eq!(super::zig_target("aarch64-apple-darwin"), Some("aarch64-macos"));
        assert_eq!(super::zig_target("riscv64gc-unknown-linux-gnu"), None);
    }

    #[test]
    fn cxx_driver_matches_the_c_driver() {
        let words = |s: &str| s.split_whitespace().map(str::to_string).collect::<Vec<String>>();
        assert_eq!(super::cxx_for(&words("zig cc -target x86_64-linux-musl")), words("zig c++ -target x86_64-linux-musl"));
        assert_eq!(super::cxx_for(&words("/usr/bin/clang-18")), words("/usr/bin/clang++-18"));
        assert_eq!(super::cxx_for(&words("x86_64-linux-musl-gcc")), words("x86_64-linux-musl-g++"));
        assert_eq!(super::cxx_for(&words("cc")), words("c++"));
        assert_eq!(super::cxx_for(&words("clang++")), words("clang++"));
    }

    /// The key text of a unit with `#include`s is its preprocessed text: `__DATE__` and
    /// `__TIME__` in it must not be the clock's, or the unit misses the cache every second.
    #[test]
    fn the_preprocessor_sees_a_fixed_build_time() {
        let Ok(spec) = super::spec_for(crate::protocol::host_triple()) else { return };
        if std::env::var_os("SOURCE_DATE_EPOCH").is_some() {
            return;
        }
        let text = "#include <stddef.h>\nconst char *built = __DATE__ \" \" __TIME__;\n";
        let pre = super::preprocessed(text, &spec.cmd, &super::cflags(false), false).expect("the host C compiler preprocesses");
        let pre = String::from_utf8_lossy(&pre);
        assert!(pre.contains("\"Jan  1 1970\" \" \" \"00:00:00\""), "{pre}");
    }

    #[test]
    fn unit_key_moves_with_every_input() {
        let spec = |triple: &str, cmd: &str| {
            let cmd: Vec<String> = cmd.split_whitespace().map(str::to_string).collect();
            super::CcSpec { triple: triple.into(), cxx: super::cxx_for(&cmd), cmd, statik: false, exe_suffix: "" }
        };
        let key = |text: &str, triple: &str, cmd: &str, debug: bool, profile: Option<&str>, cxx: bool| super::unit_key(text, &spec(triple, cmd), debug, profile, cxx);
        let base = key("int f(void);", "aarch64-unknown-linux-musl", "zig cc", false, None, false);
        assert_ne!(base, key("int g(void);", "aarch64-unknown-linux-musl", "zig cc", false, None, false), "C text");
        assert_ne!(base, key("int f(void);", "x86_64-unknown-linux-musl", "zig cc", false, None, false), "target");
        assert_ne!(base, key("int f(void);", "aarch64-unknown-linux-musl", "zig cc", true, None, false), "debug");
        assert_ne!(base, key("int f(void);", "aarch64-unknown-linux-musl", "clang", false, None, false), "compiler");
        assert_ne!(base, key("int f(void);", "aarch64-unknown-linux-musl", "zig cc", false, Some("p1"), false), "profile");
        assert_ne!(base, key("int f(void);", "aarch64-unknown-linux-musl", "zig cc", false, None, true), "C++");
    }
}
