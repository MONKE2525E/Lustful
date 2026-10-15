// expect: L0640
// Valid Rust; a source known only by an `IntoIterator` bound converts in neither `from_iter` nor `extend` yet.
fn from_src<S: IntoIterator<Item = u32>>(s: S) -> Vec<u32> { Vec::from_iter(s) }
fn main() { println!("{:?}", from_src([3, 4])); }
