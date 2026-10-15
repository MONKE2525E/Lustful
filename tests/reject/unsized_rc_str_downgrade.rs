// expect: L0641
// Valid Rust: `Rc::downgrade` of an `Rc<str>` gives a `Weak<str>`; lust's `Weak` is a thin pointer, so it rejects (w-unsized).
use std::rc::Rc;
fn main() { let a: Rc<str> = Rc::from("x"); let w = Rc::downgrade(&a); println!("{:?}", w.upgrade()); }
