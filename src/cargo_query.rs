//! Cargo's read-only compiler queries. This entry cannot compile a host unit.
use crate::protocol::ProfileFlags;
use crate::resolve::cfg::CfgEnv;

const MODE: &str = "LUST_CARGO_QUERY";

/// Cargo sets no command prefix on RUSTC, so metadata children select this
/// restricted entry through an environment variable owned by this command.
pub fn dispatch(args: &[String]) -> Option<i32> {
    if std::env::var(MODE).as_deref() != Ok("1") { return None; }
    let result = query(args);
    Some(match result {
        Ok((out, err)) => { print!("{out}"); eprint!("{err}"); 0 }
        Err(error) => { eprintln!("error: Lust Cargo query refused: {error}"); 2 }
    })
}

fn query(args: &[String]) -> Result<(String, String), String> {
    if args == ["-vV"] {
        return Ok((format!("lust {}\nbinary: lust\ncommit-hash: unknown\nlust-build: {}\ncommit-date: unknown\nhost: {}\nrelease: {}\n",
            env!("CARGO_PKG_VERSION"), env!("LUST_BUILD_HASH"), crate::protocol::host_triple(), env!("CARGO_PKG_VERSION")), String::new()));
    }
    let reject = || "only Cargo's target-information query is supported; no source compilation, host preparation, or compiler flags are accepted".to_string();
    let mut name = None;
    let mut target = crate::protocol::host_triple().to_string();
    let mut kinds = Vec::new();
    let mut prints = Vec::new();
    let mut stdin = false;
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "-" if !stdin => stdin = true,
            "--crate-name" if name.is_none() => name = Some(iter.next().ok_or_else(reject)?.clone()),
            "--target" => target = iter.next().ok_or_else(reject)?.clone(),
            "--crate-type" => kinds.push(iter.next().ok_or_else(reject)?.as_str()),
            "-Wwarnings" => {},
            p if p.starts_with("--print=") => prints.push(&p[8..]),
            _ => return Err(reject()),
        }
    }
    let name = name.ok_or_else(reject)?;
    if !stdin || name != "___" || kinds.is_empty()
        || prints != ["file-names", "sysroot", "split-debuginfo", "crate-name", "cfg"]
        || target != "x86_64-unknown-linux-gnu" || target != crate::protocol::host_triple()
    { return Err(reject()); }
    let mut out = String::new();
    let mut err = String::new();
    for kind in kinds {
        match kind {
            "bin" => out.push_str(&format!("{name}\n")),
            // Lust's internal libraries are source units, not Cargo rlibs or
            // exported native libraries. Cargo recognizes these diagnostics
            // and consumes no filename for the unsupported crate type.
            "rlib" | "dylib" | "cdylib" | "staticlib" | "proc-macro" =>
                err.push_str(&format!("warning: unsupported crate type `{kind}` for Lust\n")),
            _ => return Err(reject()),
        }
    }
    let exe = std::env::current_exe().map_err(|e| e.to_string())?;
    let root = exe.parent().ok_or_else(reject)?.to_str().ok_or_else(reject)?;
    // Sources are embedded in the compiler, so its installation directory is
    // the query root. No rustc sysroot or precompiled Rust library is used.
    out.push_str(&format!("{root}\noff\n{name}\n"));
    let cfg = CfgEnv::new(&target, &[], false, ProfileFlags::DEV_UNWIND);
    for flag in cfg.flags { out.push_str(&format!("{flag}\n")); }
    for (key, value) in cfg.pairs { out.push_str(&format!("{key}=\"{value}\"\n")); }
    Ok((out, err))
}

/// Resolve a graph only. Cargo may fetch sources according to its network
/// flags, but any attempt to use this compiler for an artifact is rejected.
pub fn metadata(args: &[String]) -> i32 {
    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        let valid = match arg.as_str() {
            "--manifest-path" | "--features" | "--filter-platform" => iter.next().is_some(),
            "--format-version" => iter.next().map(String::as_str) == Some("1"),
            "--locked" | "--offline" | "--frozen" | "--no-default-features" | "--all-features" | "--no-deps" => true,
            _ => false,
        };
        if !valid { eprintln!("error: unsupported Lust metadata argument `{arg}`"); return 2; }
    }
    let exe = match std::env::current_exe() {
        Ok(exe) => exe,
        Err(error) => { eprintln!("error: cannot locate Lust compiler: {error}"); return 2; }
    };
    let mut command = std::process::Command::new("cargo");
    command.arg("metadata");
    if !args.iter().any(|a| a == "--format-version") { command.args(["--format-version", "1"]); }
    match command.args(args).env(MODE, "1").env("RUSTC", exe).env("CARGO_CACHE_RUSTC_INFO", "0")
        .env("RUSTC_WRAPPER", "").env("RUSTC_WORKSPACE_WRAPPER", "").status() {
        Ok(status) => status.code().unwrap_or(2),
        Err(error) => { eprintln!("error: cannot run Cargo metadata: {error}"); 2 }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn args() -> Vec<String> {
        "- --crate-name ___ --print=file-names --crate-type bin --crate-type rlib --crate-type dylib --crate-type cdylib --crate-type staticlib --crate-type proc-macro --print=sysroot --print=split-debuginfo --print=crate-name --print=cfg -Wwarnings"
            .split_whitespace().map(str::to_string).collect()
    }
    #[test]
    fn identity_is_lust() {
        let (out, err) = query(&["-vV".into()]).unwrap();
        assert!(out.starts_with("lust "));
        assert!(out.contains("binary: lust\n"));
        assert!(!out.contains("rustc"));
        assert!(err.is_empty());
    }
    #[test]
    fn target_query_uses_compiler_cfg() {
        if crate::protocol::host_triple() != "x86_64-unknown-linux-gnu" { return; }
        let (out, err) = query(&args()).unwrap();
        let lines: Vec<_> = out.lines().collect();
        assert_eq!(lines[0], "___");
        assert_eq!(lines[2..4], ["off", "___"]);
        let cfg = CfgEnv::new(crate::protocol::host_triple(), &[], false, ProfileFlags::DEV_UNWIND);
        let expected: Vec<_> = cfg.flags.into_iter().chain(cfg.pairs.into_iter().map(|(k,v)| format!("{k}=\"{v}\""))).collect();
        assert_eq!(lines[4..], expected);
        assert_eq!(err.lines().count(), 5);
    }
    #[test]
    fn compilation_and_unknown_queries_are_rejected() {
        for extra in ["-Copt-level=3", "--emit=metadata", "input.rs", "-o", "--print=target-list", "--target=wasm32-wasip1"] {
            let mut a = args(); a.push(extra.into());
            assert!(query(&a).is_err(), "{extra}");
        }
        assert!(query(&["input.rs".into()]).is_err());
        let mut a = args(); a.extend(["--target".into(), "aarch64-unknown-linux-gnu".into()]);
        assert!(query(&a).is_err());
    }
}
