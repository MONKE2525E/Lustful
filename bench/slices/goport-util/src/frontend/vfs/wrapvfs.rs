//! Go: internal/vfs/wrapvfs/wrapvfs.go

use crate::frontend::prelude::*;
use std::time::SystemTime;

// Go: wrapvfs.go:9 Replacements
// PORT: nil Go funcs are `None`. `time.Time` is `Option<SystemTime>`
// (`None` is the Go zero time), as in the `Fs` trait.

// Go: wrapvfs.go:23 Wrap
// PORT: the Go package function `wrapvfs.Wrap` is `wrapvfs_wrap`.

// Go: wrapvfs.go:30 wrappedFS

