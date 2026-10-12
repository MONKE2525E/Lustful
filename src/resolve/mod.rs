// Name resolution: the crate graph, the module tree, the import worklist,
// cfg stripping, and the outline worklist driver (docs/ARCH.md sections 1
// and 6.1). W-RESOLVE owns this directory and src/scan.rs.
pub mod cargo;
pub mod cfg;
pub mod modules;
