// `rustix::path`: the argument trait of the path-taking calls.
// Upstream `Arg` hands the backend a C string; the adapter hands
// the sysx shims the path bytes (the C side adds the NUL). The
// fs calls reject a path with an interior NUL with EINVAL
// before the syscall, as upstream's C string conversion does.

use std::ffi::{OsStr, OsString};
use std::path::{Path, PathBuf};

/// A path argument.
pub trait Arg {
    /// The path bytes (no terminator; the shim adds it).
    fn as_path_bytes(&self) -> Vec<u8>;
}

impl Arg for &str {
    fn as_path_bytes(&self) -> Vec<u8> {
        self.as_bytes().to_vec()
    }
}

impl Arg for String {
    fn as_path_bytes(&self) -> Vec<u8> {
        self.as_bytes().to_vec()
    }
}

impl Arg for &String {
    fn as_path_bytes(&self) -> Vec<u8> {
        self.as_bytes().to_vec()
    }
}

impl Arg for &OsStr {
    fn as_path_bytes(&self) -> Vec<u8> {
        self.as_encoded_bytes().to_vec()
    }
}

impl Arg for &OsString {
    fn as_path_bytes(&self) -> Vec<u8> {
        self.as_encoded_bytes().to_vec()
    }
}

impl Arg for &Path {
    fn as_path_bytes(&self) -> Vec<u8> {
        self.as_os_str().as_encoded_bytes().to_vec()
    }
}

impl Arg for &PathBuf {
    fn as_path_bytes(&self) -> Vec<u8> {
        self.as_os_str().as_encoded_bytes().to_vec()
    }
}

impl Arg for PathBuf {
    fn as_path_bytes(&self) -> Vec<u8> {
        self.as_os_str().as_encoded_bytes().to_vec()
    }
}
