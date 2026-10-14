// expect: L0522
// Valid Rust; lust does not support a user global allocator, so the
// attribute stays a clean reject rather than a silent accept.
#[global_allocator]
static A: std::alloc::System = std::alloc::System;

fn main() {
    println!("x");
}
