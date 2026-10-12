// `lust`: the thin command-line client. If a daemon serves this directory, it sends the request
// there (a warm, incremental compile). Otherwise it hands the command to `lust-core`, the compiler.
// It has no custom allocator and few dependencies, so it starts in about a millisecond.
//
//   lust check <file.rs> [--json] [--timings]
//   lust build <file.rs> [-o <out>] [-g] [--emit-c <prefix>] [--timings]
//   lust run   <file.rs> [-- <args>...]
//   lust daemon            serve warm, incremental compiles for this directory
#[path = "protocol.rs"]
mod protocol;

use protocol::Invocation;
use std::os::unix::process::CommandExt;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if let Some(Invocation::Compile { req, run, args: run_args }) = protocol::parse_args(&args)
        && let Some(resp) = protocol::request(&protocol::socket_path(), &req)
    {
        protocol::finish(resp, run, &req.out, &run_args);
    }
    // No daemon (or a daemon command, or bad arguments): let the compiler handle it.
    let core = std::env::current_exe().map(|p| p.with_file_name("lust-core")).unwrap_or_else(|_| "lust-core".into());
    let err = std::process::Command::new(&core).args(&args).exec();
    eprintln!("error: cannot run {}: {err}", core.display());
    std::process::exit(2);
}
