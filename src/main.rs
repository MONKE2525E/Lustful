// lust-core: the lust compiler (see DESIGN.md). Usually started by the `lust` client.
//
//   lust-core check|build|run <file.rs> ...   compile cold, in this process
//   lust-core daemon                          serve warm, incremental compiles for this directory
mod ast;
mod borrowck;
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
        Some(Invocation::Compile { req, run, args }) => {
            let dir = std::env::temp_dir().join(format!("lust-{}", std::process::id()));
            let mut session = driver::Session::new(dir, false);
            let resp = driver::compile(&req, &mut session);
            let _ = std::fs::remove_dir_all(session.obj_dir());
            protocol::finish(resp, run, &req.out, &args);
        }
        None => {
            eprintln!("{}", protocol::USAGE);
            std::process::exit(2);
        }
    }
}
