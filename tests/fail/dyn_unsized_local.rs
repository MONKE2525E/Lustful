// expect: L0305
// ARCH 2.8, rustc E0277: `*d` is unsized and cannot be moved into a local.
trait Tr { fn m(&self) -> u8; }
struct S;
impl Tr for S { fn m(&self) -> u8 { 1 } }
fn main() { let s = S; let d: &dyn Tr = &s; let _x = *d; }
