// lust-core: the lust compiler (see DESIGN.md). Usually started by the `lust` client.
//
//   lust-core check|build|run <file.rs> ...   compile cold, in this process
//   lust-core daemon                          serve warm, incremental compiles for this directory
//   lust-core test <file.rs> ...              run #[test] functions, one child process each
//   lust-core explain <L####>                 long-form help for one diagnostic code
//   lust-core capabilities [--json]           what the supported subset contains
/// AST v2 keeps shapes for syntax whose parsers land later (docs/ARCH.md S3b),
/// so many nodes are defined before anything reads them.
#[allow(dead_code)]
mod ast;
mod borrowck;
mod capabilities;
mod cgen;
mod check;
mod daemon;
mod def;
mod diag;
mod driver;
mod explain;
mod intern;
mod ir;
mod lexer;
mod lower;
mod parser;
mod protocol;
mod scan;
mod tcc;
mod testrun;
mod ty;

use protocol::Invocation;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Deletes a one-shot session's object directory. A serial walk costs 3 to 6 ms on a cold
/// build (one unlink per object and C file), so many files are unlinked in parallel. The
/// final remove_dir_all handles subdirectories and anything the parallel pass missed.
fn remove_obj_dir(dir: &std::path::Path) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        let files: Vec<std::path::PathBuf> = rd.filter_map(|e| e.ok().map(|e| e.path())).filter(|p| p.is_file()).collect();
        if files.len() > 16 {
            let n = 8usize;
            std::thread::scope(|s| {
                for k in 0..n {
                    let files = &files;
                    s.spawn(move || {
                        for f in files.iter().skip(k).step_by(n) {
                            let _ = std::fs::remove_file(f);
                        }
                    });
                }
            });
        }
    }
    let _ = std::fs::remove_dir_all(dir);
}

fn main() {
    tcc::use_mimalloc();
    let args: Vec<String> = std::env::args().skip(1).collect();
    // Agent-kit commands run in this process; they never go through the daemon.
    match args.first().map(String::as_str) {
        Some("test") => std::process::exit(testrun::run(&args[1..])),
        Some("explain") => std::process::exit(explain::run(&args[1..])),
        Some("capabilities") => std::process::exit(capabilities::run(&args[1..])),
        _ => {}
    }
    match protocol::parse_args(&args) {
        Some(Invocation::Daemon) => daemon::serve(&protocol::socket_path()),
        // The `lust` client handles these itself; direct `lust-core` calls work too.
        Some(Invocation::Release { file, out, profile, debug }) => protocol::run_release(&file, out.as_deref(), profile.as_deref(), debug),
        Some(Invocation::RustcCheck { file }) => protocol::run_rustc_check(&file),
        Some(Invocation::Compile { req, run, args }) => {
            // Whole-request disk cache (cold runs only; the daemon path keeps its own
            // in-memory state). `--emit-c` writes side files, so it always compiles. A `run`
            // request is also never cached: its response can be the program's own output and
            // exit code (an in-memory run writes no executable), not a build result.
            let start = std::time::Instant::now();
            let cache = if req.emit_c.is_none() && req.run_args.is_none() { driver::cache::Cache::open(&req.file) } else { None };
            let src = cache.as_ref().and_then(|_| std::fs::read(&req.file).ok());
            if let (Some(cache), Some(src)) = (&cache, &src)
                && let Some(resp) = cache.lookup(&req, src, start)
            {
                protocol::finish(resp, run, &req.out, &args);
            }
            let dir = std::env::temp_dir().join(format!("lust-{}", std::process::id()));
            let mut session = driver::Session::new(dir, false, req.session.clone());
            let resp = driver::compile(&req, &mut session);
            remove_obj_dir(session.obj_dir());
            if let (Some(cache), Some(src)) = (&cache, &src) {
                cache.store(&req, src, &resp);
            }
            // This process exits inside `finish`. Leak the session instead of freeing it:
            // dropping millions of small allocations (many made on worker threads) costs
            // about 10 ms on a 31k-line crate, and the OS reclaims the memory for free.
            // The daemon path never reaches this code, so it still frees normally.
            std::mem::forget(session);
            protocol::finish(resp, run, &req.out, &args);
        }
        None => {
            eprintln!("{}", protocol::USAGE);
            std::process::exit(2);
        }
    }
}
