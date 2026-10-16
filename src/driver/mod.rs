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
mod kept_delta;
pub(crate) mod gen_reuse;
pub mod graph;
mod patch;
mod sig_nodes;
mod span_shift;
mod session;

pub use crate::protocol::{Cmd, Request, Response, SessionKey};
pub use compile::{compile, release_bases, sweep_bases};
pub use session::Session;
