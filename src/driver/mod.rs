// The driver: session state (session.rs), the whole-request disk cache (cache.rs),
// and the compile pipeline (compile.rs). Callers use the re-exports below, so the
// public paths (`driver::Session`, `driver::compile`, `driver::cache::Cache`) stay
// stable when items move between these files.
pub(crate) mod ast_hash;
mod ir_cache;
pub mod buildscript;
pub mod cache;
mod compile;
mod const_reach;
pub(crate) mod kept_delta;
pub(crate) mod laps;
mod item_oracle;
mod item_outline;
pub(crate) mod gen_reuse;
pub mod graph;
mod patch;
mod sig_nodes;
mod span_shift;
mod session;

pub use crate::protocol::{Cmd, Request, Response, SessionKey};
pub use compile::{release_bases, sweep_bases};

/// Compiles one request in `session` (`compile::compile`). Under the
/// patch oracle (`item_oracle.rs`) a patched check request then compares
/// its answer with a one-shot compile.
pub fn compile(req: &Request, session: &mut Session) -> Response {
    let resp = compile::compile(req, session);
    if item_oracle::on() {
        item_oracle::compare_response(req, session, &resp);
    }
    resp
}
pub use session::Session;
