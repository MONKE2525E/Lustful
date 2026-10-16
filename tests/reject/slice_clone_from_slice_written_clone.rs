// expect: L0640
// Valid Rust: core's clone_from_slice on a Copy type with a written Clone runs
// that Clone per element; lust's glue does not call such impls.
#[derive(Copy, Debug)]
struct W(u8);
impl Clone for W { fn clone(&self) -> W { *self } }
fn main() { let mut a = [W(1), W(2)]; a.clone_from_slice(&[W(3), W(4)]); println!("{:?}", a); }
