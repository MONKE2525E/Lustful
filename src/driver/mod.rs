// The driver: session state (session.rs), the whole-request disk cache (cache.rs),
// and the compile pipeline (compile.rs). Callers use the re-exports below, so the
// public paths (`driver::Session`, `driver::compile`, `driver::cache::Cache`) stay
// stable when items move between these files.
pub mod cache;
mod compile;
mod session;

pub use crate::protocol::{Cmd, Request, Response};
pub use compile::compile;
pub use session::Session;
