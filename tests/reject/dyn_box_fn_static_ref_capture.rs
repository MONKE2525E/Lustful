// expect: L0705
// Valid Rust: the closure captures a `&'static str`, so the `'static` box holds. lust erases reference regions and cannot prove it (W-BORROW: check the object lifetime at the unsizing).
fn mk(s: &'static str) -> Box<dyn Fn() -> usize> { Box::new(move || s.len()) }
fn main() { println!("{}", mk("abcd")()); }
