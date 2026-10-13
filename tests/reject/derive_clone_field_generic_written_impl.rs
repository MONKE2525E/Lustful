// expect: L0112
// Valid Rust: a field type whose Clone impl is generic (G<T>) needs an
// instance of that impl the derived clone glue cannot call yet.
struct G<T>(T);
impl<T: Clone> Clone for G<T> { fn clone(&self) -> G<T> { G(self.0.clone()) } }
#[derive(Clone)]
struct S { g: G<u8> }
fn main() { let s = S { g: G(1) }; let _t = s.clone(); println!("ok"); }
