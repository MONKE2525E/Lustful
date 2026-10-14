// `core::intrinsics`: the private intrinsic signatures (docs/ARCH.md
// section 3.2).
//
// The machine-checked registry is `INTRINSICS` in src/ty/lang.rs: name,
// signature, C symbol, and the shipped crates that may call each row.
// This file is the author-facing mirror for std writers. Only shipped
// crates may name these paths; a user crate that tries gets L0642.
//
// Implemented (callable from std source, or from the named adapter):
//
//     pub fn exit(code: i32) -> !;
//     pub fn xxh3_64(input: &[u8], seed: u64) -> u64;          // xxhash-rust
//     pub fn xxh3_128(input: &[u8], seed: u64) -> u128;        // xxhash-rust
//     pub fn ryu_js_fmt_f64(out: &mut String, value: f64);     // ryu-js
//
// The std platform crate (library/std/src/platform.rs, W-SHIM; C in
// src/runtime/sys.c):
//
//     pub fn sys_write_std(fd: i32, buf: &[u8]) -> i64;         // n or -errno
//     pub fn sys_flush_std(fd: i32) -> i32;                     // 0 or errno
//     pub fn sys_os_error_text(code: i32, out: &mut String);
//     pub fn sys_fmt_arguments_bytes(args: fmt::Arguments) -> Vec<u8>;
//
// Every other row of the section 3.2 table is registered with its
// signature and privilege list, but has no body yet: a privileged call
// rejects with L0640 until W-STD lands the wrapper and the runtime hook.
// Declarations gain real foreign-fn form when the checker learns foreign
// fns (section 3.7); until then this module holds no items on purpose,
// so the file still parses as ordinary lust source.
