// expect: L0104
// Valid Rust: the unsafe ManuallyDrop::take operation is not implemented.
use std::mem::ManuallyDrop;
fn main() {
    let mut m = ManuallyDrop::new(String::from("x"));
    let s = unsafe { ManuallyDrop::take(&mut m) };
    println!("{s}");
}
