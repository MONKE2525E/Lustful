// expect: L0641
// Valid Rust: a Weak of a slice is not built yet.
use std::rc::{Rc, Weak};
fn main() {
    let s = Rc::new([1u8, 2, 3]);
    let w: Weak<[u8; 3]> = Rc::downgrade(&s);
    let d: Weak<[u8]> = w;
    println!("{}", d.upgrade().map_or(0, |x| x.len()));
}
