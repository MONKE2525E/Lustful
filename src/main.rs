// lust-core: the lust compiler (see DESIGN.md). Usually started by the `lust` client.
//
//   lust-core check|build|run <file.rs> ...   compile cold, in this process
//   lust-core daemon                          serve warm, incremental compiles for this directory
//   lust-core test <file.rs> ...              run #[test] functions, one child process each
//   lust-core explain <L####>                 long-form help for one diagnostic code
//   lust-core expand <file.rs>                print the file's expanded token stream
//   lust-core capabilities [--json]           what the supported subset contains
/// AST v2 keeps shapes for syntax whose parsers land later (docs/ARCH.md S3b),
/// so many nodes are defined before anything reads them.
#[allow(dead_code)]
mod ast;
mod borrowck;
mod capabilities;
mod cgen;
mod check;
mod colwidth;
mod daemon;
mod def;
mod diag;
mod driver;
mod expand;
mod explain;
mod intern;
mod ir;
mod lexer;
mod lower;
#[allow(dead_code)] // Instance discovery is called from collect and the driver as W-TRAITS-CORE lands in increments.
mod mono;
mod parser;
mod pool;
mod protocol;
#[allow(dead_code)] // Wired into the driver by the worklist increment.
mod resolve;
mod scan;
mod stdload;
mod stdmods;
mod tcc;
mod testrun;
#[allow(dead_code)] // See `mod mono`.
mod traits;
mod ty;

use protocol::Invocation;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

/// Deletes a one-shot session's object directory. A serial walk costs 3 to 6 ms on a cold
/// build (one unlink per object and C file), so many files are unlinked in parallel on the
/// thread pool. The final remove_dir_all handles subdirectories and anything the parallel
/// pass missed.
fn remove_obj_dir(dir: &std::path::Path) {
    if let Ok(rd) = std::fs::read_dir(dir) {
        let files: Vec<std::path::PathBuf> = rd.filter_map(|e| e.ok().map(|e| e.path())).filter(|p| p.is_file()).collect();
        if files.len() > 16 {
            pool::par_map(&files, |f| {
                let _ = std::fs::remove_file(f);
            });
        }
    }
    let _ = std::fs::remove_dir_all(dir);
}

/// Raises the main thread's stack limit toward `pool::STACK_SIZE` (best
/// effort, capped by the hard limit), so the thread the compiler runs
/// on holds deep expressions the parser accepts. The main thread keeps
/// running the compile because an in-memory `lust run` forks, and a
/// fork is only sound from a lone thread (see src/tcc.rs). On Linux the
/// main stack grows on demand up to the soft limit at fault time, so
/// raising it here, before any deep work, is enough.
#[cfg(unix)]
fn raise_stack_limit() {
    #[repr(C)]
    struct Rlimit {
        cur: u64,
        max: u64,
    }
    unsafe extern "C" {
        fn getrlimit(resource: i32, rlim: *mut Rlimit) -> i32;
        fn setrlimit(resource: i32, rlim: *const Rlimit) -> i32;
    }
    const RLIMIT_STACK: i32 = 3;
    let mut rl = Rlimit { cur: 0, max: 0 };
    // SAFETY: `rl` is a valid out pointer for the call.
    if unsafe { getrlimit(RLIMIT_STACK, &mut rl) } != 0 {
        return;
    }
    let want = (pool::STACK_SIZE as u64).min(rl.max).max(rl.cur);
    if want > rl.cur {
        rl.cur = want;
        // SAFETY: `rl` names a limit no higher than the hard limit read above.
        unsafe { setrlimit(RLIMIT_STACK, &rl) };
    }
}

/// The root file size from which a one-shot compile keeps transparent
/// huge pages in its serial phases (see `main`). On boat, realish40
/// (940 KB) and plain1600 (1.2 MB) gain from them there, realish20
/// (470 KB) is even, and fmt40 (54 KB) and a trivial program lose.
const BIG_FILE: u64 = 256 << 10;

fn main() {
    // Cargo runs lust-core as its RUSTC_WRAPPER during the feature probe.
    if let Some(code) = resolve::probe::wrapper_main() {
        std::process::exit(code);
    }
    #[cfg(unix)]
    raise_stack_limit();
    tcc::use_mimalloc();
    let args: Vec<String> = std::env::args().skip(1).collect();
    // Agent-kit commands run in this process; they never go through the daemon.
    match args.first().map(String::as_str) {
        Some("test") => std::process::exit(testrun::run(&args[1..])),
        Some("explain") => std::process::exit(explain::run(&args[1..])),
        Some("capabilities") => std::process::exit(capabilities::run(&args[1..])),
        Some("expand") => std::process::exit(expand::run_expand(&args[1..])),
        _ => {}
    }
    match protocol::parse_args(&args) {
        Some(Invocation::Daemon) => daemon::serve(&protocol::socket_path()),
        // The `lust` client handles these itself; direct `lust-core` calls work too.
        Some(Invocation::Release { file, out, profile, debug, net }) => {
            protocol::run_release(&file, out.as_deref(), profile.as_deref(), debug, net)
        }
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
            // Transparent huge pages cost a 2 MB zeroing per first touch. Pool
            // threads touch memory sparsely, so parallel phases always run
            // without them. A big file's serial phases (collect over every
            // item) touch memory densely and gain from them; a small program
            // touches little and loses, so it runs without them throughout,
            // with them on again before `finish` runs the program.
            let small = std::fs::metadata(&req.file).map_or(true, |m| m.len() < BIG_FILE);
            if small {
                tcc::set_huge_pages(false);
            } else {
                pool::small_pages_in_parallel();
            }
            let dir = std::env::temp_dir().join(format!("lust-{}", std::process::id()));
            let mut session = driver::Session::new(dir, false, req.session.clone());
            // A panicking compile must not leave its temp dir behind:
            // clean up, then let the panic run its normal course.
            let compiled = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| driver::compile(&req, &mut session)));
            let resp = match compiled {
                Ok(resp) => resp,
                Err(payload) => {
                    remove_obj_dir(session.obj_dir());
                    std::panic::resume_unwind(payload);
                }
            };
            remove_obj_dir(session.obj_dir());
            if small {
                tcc::set_huge_pages(true);
            }
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
