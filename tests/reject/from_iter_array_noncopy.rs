// expect: L0640
// Valid Rust; iterating an array of non-`Copy` elements by value is not built yet, as for `collect`.
fn main() { let v: Vec<Vec<u32>> = Vec::from_iter([vec![1], vec![2]]); println!("{:?}", v); }
