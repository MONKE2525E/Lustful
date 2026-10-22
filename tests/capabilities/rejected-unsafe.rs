// capability: rejected: unsafe Rust functions and foreign calls outside unsafe blocks
// expect: L0404

unsafe fn value() -> i32 { 1 }
fn main() { println!("{}", unsafe { value() }); }
