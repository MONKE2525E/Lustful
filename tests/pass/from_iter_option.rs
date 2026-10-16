// expect: L0640
// Valid Rust; lust has no build for `FromIterator` into `Option` yet, as `collect` into it has none.
fn main() { let v: Option<Vec<u32>> = Option::from_iter([Some(1), Some(2)]); println!("{:?}", v); }
