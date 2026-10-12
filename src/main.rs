// lust-core: the lust compiler (see DESIGN.md). Usually started by the `lust` client.
//
//   lust-core check|build|run <file.rs> ...   compile cold, in this process
//   lust-core daemon                          serve warm, incremental compiles for this directory
mod ast;
mod borrowck;
mod cache;
mod cgen;
mod check;
mod collect;
mod daemon;
mod diag;
mod driver;
mod intern;
mod ir;
mod lexer;
mod lower;
mod parser;
mod protocol;
mod scan;
mod tcc;
mod types;

use protocol::Invocation;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    tcc::use_mimalloc();
    let args: Vec<String> = std::env::args().skip(1).collect();
    match protocol::parse_args(&args) {
        Some(Invocation::Daemon) => daemon::serve(&protocol::socket_path()),
        // The `lust` client handles these itself; direct `lust-core` calls work too.
        Some(Invocation::Release { file, out, profile, debug }) => protocol::run_release(&file, out.as_deref(), profile.as_deref(), debug),
        Some(Invocation::RustcCheck { file }) => protocol::run_rustc_check(&file),
        Some(Invocation::Compile { req, run, args }) => {
            // Whole-request disk cache (cold runs only; the daemon path keeps its own
            // in-memory state). `--emit-c` writes side files, so it always compiles.
            let start = std::time::Instant::now();
            let cache = if req.emit_c.is_none() { cache::Cache::open(&req.file) } else { None };
            let src = cache.as_ref().and_then(|_| std::fs::read(&req.file).ok());
            if let (Some(cache), Some(src)) = (&cache, &src)
                && let Some(resp) = cache.lookup(&req, src, start)
            {
                protocol::finish(resp, run, &req.out, &args);
            }
            let dir = std::env::temp_dir().join(format!("lust-{}", std::process::id()));
            let mut session = driver::Session::new(dir, false);
            let resp = driver::compile(&req, &mut session);
            let _ = std::fs::remove_dir_all(session.obj_dir());
            if let (Some(cache), Some(src)) = (&cache, &src) {
                cache.store(&req, src, &resp);
            }
            protocol::finish(resp, run, &req.out, &args);
        }
        None => {
            eprintln!("{}", protocol::USAGE);
            std::process::exit(2);
        }
    }
}
