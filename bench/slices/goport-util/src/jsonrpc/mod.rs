//! Go package `internal/jsonrpc`.

pub mod baseproto;
pub mod jsonrpc;

pub use baseproto::*;
pub use jsonrpc::*;

/// Glob import for jsonrpc files: `use crate::jsonrpc::prelude::*;`.
pub mod prelude {
    pub use super::{baseproto::*, jsonrpc::*};
    pub use crate::prelude::*;
}
