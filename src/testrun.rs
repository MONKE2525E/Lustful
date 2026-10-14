// `lust test <file.rs> [filter]`: finds `#[test]` functions, builds one test binary, and runs
// each test in its own child process with a timeout. Lust builds with panic=abort, so a panicking
// test kills its child only, never the run.
//
// The test binary is the user file plus a generated `main` that dispatches on
// `std::env::args().count()`: the runner passes i+1 dummy arguments to run test i. With no extra
// arguments the binary runs every test in order. A user `main` is renamed in place (same byte
// length, so every span still matches the user file); `rustc --test` ignores `main` the same way.
//
// Exit status follows cargo test: 0 when every selected test passes, 101 when the build fails or
// any test fails or times out, 2 for bad arguments or an unreadable file. A skipped or filtered
// test is never reported as a pass; it is counted in `filtered_out`.
use crate::ast::{ItemKind, TyExpr};
use crate::diag::{self, Diag, FileId, SourceMap};
use crate::driver::{self, Cmd, Request, SessionKey};
use crate::intern::{Interner, Known};
use crate::{lexer, parser};
use std::io::Read;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

const USAGE: &str = "usage: lust test <file.rs> [filter] [--json] [--list] [--timeout SECONDS] [--max-errors N]";

struct Opts {
    file: PathBuf,
    filter: Option<String>,
    json: bool,
    list: bool,
    timeout: Duration,
    max_errors: usize,
}

/// Parses `lust test` arguments (without the word `test`).
fn parse_opts(args: &[String]) -> Result<Opts, String> {
    let (mut file, mut filter, mut json, mut list) = (None, None, false, false);
    let (mut timeout, mut max_errors) = (Duration::from_secs(10), diag::DEFAULT_MAX_ERRORS);
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--json" => json = true,
            "--list" => list = true,
            "--timeout" => timeout = parse_secs(it.next().ok_or(USAGE)?)?,
            "--max-errors" => max_errors = it.next().and_then(|v| v.parse().ok()).ok_or(USAGE)?,
            _ if a.starts_with("--timeout=") => timeout = parse_secs(&a["--timeout=".len()..].to_string())?,
            _ if a.starts_with("--max-errors=") => max_errors = a["--max-errors=".len()..].parse().map_err(|_| USAGE.to_string())?,
            _ if a.starts_with("--") => return Err(USAGE.into()),
            _ if file.is_none() => file = Some(PathBuf::from(a)),
            _ if filter.is_none() => filter = Some(a.clone()),
            _ => return Err(USAGE.into()),
        }
    }
    Ok(Opts { file: file.ok_or(USAGE)?, filter, json, list, timeout, max_errors })
}

fn parse_secs(s: &String) -> Result<Duration, String> {
    let v: f64 = s.parse().map_err(|_| USAGE.to_string())?;
    if v <= 0.0 {
        return Err(USAGE.into());
    }
    Ok(Duration::from_secs_f64(v))
}

/// One test case result.
struct Outcome {
    name: String,
    status: &'static str, // "pass", "fail", or "timeout"
    duration_ms: f64,
    exit_code: Option<i32>,
    stdout: String,
    stderr: String,
}

/// Runs the binary once for test `index`, capturing output and enforcing the timeout.
fn run_one(bin: &PathBuf, index: usize, name: &str, timeout: Duration) -> Outcome {
    let start = Instant::now();
    let mut cmd = Command::new(bin);
    cmd.args(std::iter::repeat_n("x", index + 1)).stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = match cmd.spawn() {
        Ok(c) => c,
        Err(e) => {
            return Outcome {
                name: name.into(),
                status: "fail",
                duration_ms: millis(start),
                exit_code: None,
                stdout: String::new(),
                stderr: format!("cannot run the test binary: {e}"),
            };
        }
    };
    let mut out_pipe = child.stdout.take().expect("piped");
    let mut err_pipe = child.stderr.take().expect("piped");
    let out_thread = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = out_pipe.read_to_end(&mut buf);
        buf
    });
    let err_thread = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = err_pipe.read_to_end(&mut buf);
        buf
    });
    let (status, timed_out) = loop {
        match child.try_wait() {
            Ok(Some(s)) => break (Some(s), false),
            Ok(None) if start.elapsed() < timeout => std::thread::sleep(Duration::from_millis(2)),
            Ok(None) => {
                let _ = child.kill();
                break (child.wait().ok(), true);
            }
            Err(_) => break (child.wait().ok(), false),
        }
    };
    let stdout = String::from_utf8_lossy(&out_thread.join().unwrap_or_default()).into_owned();
    let stderr = String::from_utf8_lossy(&err_thread.join().unwrap_or_default()).into_owned();
    let exit_code = status.and_then(|s| s.code());
    let status = if timed_out {
        "timeout"
    } else if exit_code == Some(0) {
        "pass"
    } else {
        "fail"
    };
    Outcome { name: name.into(), status, duration_ms: millis(start), exit_code, stdout, stderr }
}

fn millis(start: Instant) -> f64 {
    start.elapsed().as_secs_f64() * 1000.0
}

/// The JSON summary record printed last in `--json` mode.
fn summary_json(file: &str, hash: &str, build: &str, outcomes: &[Outcome], filtered_out: usize, start: Instant) -> String {
    let count = |s: &str| outcomes.iter().filter(|o| o.status == s).count();
    format!(
        "{{\"schema\":{},\"kind\":\"summary\",\"file\":{},\"source_hash\":{},\"build\":\"{}\",\"total\":{},\"passed\":{},\"failed\":{},\"timed_out\":{},\"filtered_out\":{},\"duration_ms\":{:.3}}}",
        diag::SCHEMA,
        diag::json_str(file),
        diag::json_str(hash),
        build,
        outcomes.len(),
        count("pass"),
        count("fail"),
        count("timeout"),
        filtered_out,
        millis(start)
    )
}

/// Entry point for `lust test`. Returns the process exit code.
pub fn run(args: &[String]) -> i32 {
    let opts = match parse_opts(args) {
        Ok(o) => o,
        Err(u) => {
            eprintln!("{u}");
            return 2;
        }
    };
    let start = Instant::now();
    let abs = |p: &PathBuf| std::path::absolute(p).unwrap_or_else(|_| p.clone());
    let file = abs(&opts.file);
    let path = file.to_string_lossy().into_owned();
    let src = match std::fs::read_to_string(&file) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return 2;
        }
    };
    let hash = diag::source_hash(&src);
    // Prints rendered diagnostics in the right stream for the mode, plus the JSON summary.
    let fail_build = |text: String, filtered_out: usize| -> i32 {
        if opts.json {
            print!("{text}");
            println!("{}", summary_json(&path, &hash, "failed", &[], filtered_out, start));
        } else {
            eprint!("{text}");
        }
        101
    };

    // Parse once to find the tests, their names, and the user's `main` (if any). This
    // one-shot parse has its own source map with the user file as file 0.
    let mut map = SourceMap::default();
    map.add_file(&path, &src);
    let interner = Interner::default();
    let known = Known::new(&interner);
    let lexed = match lexer::lex(&src, FileId(0), 0, &interner).and_then(|l| {
        let ctx = crate::expand::ExpandCtx::for_file(&interner, &known, std::path::Path::new(&path), &src, true);
        crate::expand::expand_lexed(l, &ctx)
    }) {
        Ok(l) => l,
        Err(d) => return fail_build(diag::render(&mut [d], &map, &src, opts.json, opts.max_errors), 0),
    };
    let ast = match parser::parse(&lexed, &interner, &known) {
        Ok(a) => a,
        Err(d) => return fail_build(diag::render(&mut [d], &map, &src, opts.json, opts.max_errors), 0),
    };
    let mut tests: Vec<String> = Vec::new();
    let mut fn_names: Vec<String> = Vec::new();
    let mut main_span = None;
    let mut bad: Vec<Diag> = Vec::new();
    for item in &ast.items {
        match &item.kind {
            ItemKind::Fn(def) => {
                let name = interner.get(def.name).to_string();
                if name == "main" {
                    main_span = Some(def.name_span);
                }
                fn_names.push(name.clone());
                if def.is_test {
                    let ret_ok = def.ret.is_none_or(|t| matches!(ast.ty(t), TyExpr::Unit));
                    if def.self_param.is_some() || !def.params.is_empty() || !ret_ok {
                        bad.push(Diag::new(
                            "L0110",
                            def.name_span,
                            format!("test function `{name}` must take no arguments and return `()`"),
                            format!("Change the signature to `fn {name}() {{ ... }}`."),
                        ));
                    } else {
                        tests.push(name);
                    }
                }
            }
            ItemKind::Impl(imp) => {
                for def in &imp.fns {
                    if def.is_test {
                        bad.push(diag::unsupported(def.name_span, "#[test] functions inside impl blocks"));
                    }
                }
            }
            _ => {}
        }
    }
    if !bad.is_empty() {
        return fail_build(diag::render(&mut bad, &map, &src, opts.json, opts.max_errors), 0);
    }
    let selected: Vec<String> = match &opts.filter {
        Some(f) => tests.iter().filter(|n| n.contains(f.as_str())).cloned().collect(),
        None => tests.clone(),
    };
    let filtered_out = tests.len() - selected.len();
    if opts.list {
        if opts.json {
            let names: Vec<String> = selected.iter().map(|n| diag::json_str(n)).collect();
            println!(
                "{{\"schema\":{},\"kind\":\"list\",\"file\":{},\"source_hash\":{},\"tests\":[{}],\"filtered_out\":{}}}",
                diag::SCHEMA,
                diag::json_str(&path),
                diag::json_str(&hash),
                names.join(","),
                filtered_out
            );
        } else {
            for n in &selected {
                println!("{n}: test");
            }
            println!("\n{} tests", selected.len());
        }
        return 0;
    }

    // Check the user file as written first, so diagnostics name the real file and hash.
    // One session per crate root: the user file as a test crate, then the
    // generated harness file as its own bin crate (driver sessions are keyed
    // by crate, so the harness build below gets a fresh session).
    let dir = std::env::temp_dir().join(format!("lust-test-{}", std::process::id()));
    let mut session = driver::Session::new(dir.join("obj"), false, SessionKey::synthetic(&file, true));
    let req = |cmd: Cmd, file: PathBuf, out: PathBuf| Request {
        cmd,
        session: SessionKey::synthetic(&file, cmd == Cmd::Check),
        file,
        out,
        json: opts.json,
        timings: false,
        debug: false,
        emit_c: None,
        max_errors: opts.max_errors,
        run_args: None,
        // The check below runs on the user file before the generated `main` is added.
        harness: cmd == Cmd::Check,
        client: Default::default(),
    };
    let check = driver::compile(&req(Cmd::Check, file.clone(), dir.join("testbin")), &mut session);
    if check.code != 0 {
        let _ = std::fs::remove_dir_all(&dir);
        // In JSON mode the driver puts diagnostics on stdout already; keep its split.
        print!("{}", check.stdout);
        eprint!("{}", check.stderr);
        if opts.json {
            println!("{}", summary_json(&path, &hash, "failed", &[], filtered_out, start));
        }
        return 101;
    }

    // Build the harness: user source (with `main` renamed) plus a generated dispatching `main`.
    let mut harness = src.clone();
    if let Some(span) = main_span {
        let replacement = ["zain", "yain", "xain", "wain", "vain", "qain"]
            .iter()
            .find(|c| !fn_names.iter().any(|n| n == *c))
            .expect("no free name for the user main");
        harness.replace_range(span.lo as usize..span.hi as usize, replacement);
    }
    harness.push_str("\nfn main() {\n    let n = std::env::args().count();\n    if n == 1 {\n");
    for t in &selected {
        harness.push_str(&format!("        {t}();\n"));
    }
    for (i, t) in selected.iter().enumerate() {
        harness.push_str(&format!("    }} else if n == {} {{\n        {t}();\n", i + 2));
    }
    harness.push_str("    }\n}\n");
    if let Err(e) = std::fs::create_dir_all(&dir).and_then(|_| std::fs::write(dir.join("harness.rs"), &harness)) {
        eprintln!("error: cannot write the test harness: {e}");
        let _ = std::fs::remove_dir_all(&dir);
        return 101;
    }
    let harness_path = abs(&dir.join("harness.rs"));
    let bin = dir.join("testbin");
    let mut session = driver::Session::new(dir.join("obj-harness"), false, SessionKey::synthetic(&harness_path, false));
    let build = driver::compile(&req(Cmd::Build, harness_path.clone(), bin.clone()), &mut session);
    if build.code != 0 {
        // Spans match the user file byte for byte; only the file name differs.
        let fix = |s: &str| s.replace(&harness_path.to_string_lossy().into_owned(), &path);
        let _ = std::fs::remove_dir_all(session.obj_dir());
        print!("{}", fix(&build.stdout));
        eprint!("{}", fix(&build.stderr));
        if opts.json {
            println!("{}", summary_json(&path, &hash, "failed", &[], filtered_out, start));
        }
        let _ = std::fs::remove_dir_all(&dir);
        return 101;
    }

    // Run each selected test in its own child process.
    if !opts.json {
        println!("running {} tests", selected.len());
    }
    let mut outcomes: Vec<Outcome> = Vec::new();
    for (i, name) in selected.iter().enumerate() {
        let mut o = run_one(&bin, i, name, opts.timeout);
        // Panic messages name the harness file; its lines match the user file, so rename it back.
        o.stderr = o.stderr.replace(&harness_path.to_string_lossy().into_owned(), &path);
        o.stdout = o.stdout.replace(&harness_path.to_string_lossy().into_owned(), &path);
        if opts.json {
            println!(
                "{{\"schema\":{},\"kind\":\"test\",\"name\":{},\"status\":\"{}\",\"duration_ms\":{:.3},\"exit_code\":{},\"stdout\":{},\"stderr\":{}}}",
                diag::SCHEMA,
                diag::json_str(&o.name),
                o.status,
                o.duration_ms,
                o.exit_code.map_or("null".into(), |c| c.to_string()),
                diag::json_str(&o.stdout),
                diag::json_str(&o.stderr)
            );
        } else {
            let word = match o.status {
                "pass" => "ok",
                "timeout" => "TIMEOUT",
                _ => "FAILED",
            };
            println!("test {} ... {} ({:.1}ms)", o.name, word, o.duration_ms);
        }
        outcomes.push(o);
    }
    let failed = outcomes.iter().filter(|o| o.status != "pass").count();
    if opts.json {
        println!("{}", summary_json(&path, &hash, "ok", &outcomes, filtered_out, start));
    } else {
        if failed > 0 {
            println!("\nfailures:");
            for o in outcomes.iter().filter(|o| o.status != "pass") {
                println!("---- {} ({}) ----", o.name, o.status);
                if !o.stdout.is_empty() {
                    println!("stdout:\n{}", o.stdout);
                }
                if !o.stderr.is_empty() {
                    println!("stderr:\n{}", o.stderr);
                }
            }
        }
        let passed = outcomes.len() - failed;
        let timed_out = outcomes.iter().filter(|o| o.status == "timeout").count();
        println!(
            "\ntest result: {}. {} passed; {} failed; {} timed out; {} filtered out",
            if failed == 0 { "ok" } else { "FAILED" },
            passed,
            failed - timed_out,
            timed_out,
            filtered_out
        );
    }
    let _ = std::fs::remove_dir_all(session.obj_dir());
    let _ = std::fs::remove_dir_all(&dir);
    if failed == 0 { 0 } else { 101 }
}
