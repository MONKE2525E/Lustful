// expect: L0110
// Valid Rust: a deref coercion of two steps (ManuallyDrop, then String) is not supported yet.
use std::mem::ManuallyDrop;
fn main() {
    let m = ManuallyDrop::new(String::from("hi"));
    let s: &str = &m;
    println!("{s}");
}
