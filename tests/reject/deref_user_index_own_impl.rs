// expect: L0113
// Valid Rust: `w[0]` uses W's own `Index` impl (prints 3 3), not its
// `Deref` to the Vec. `[]` through a user `Index` impl is not supported
// yet, so a type with one must not index through its Deref instead.
use std::ops::{Deref, Index};
struct W(Vec<u32>);
impl Deref for W {
    type Target = Vec<u32>;
    fn deref(&self) -> &Vec<u32> {
        &self.0
    }
}
impl Index<usize> for W {
    type Output = u32;
    fn index(&self, i: usize) -> &u32 {
        &self.0[self.0.len() - 1 - i]
    }
}
fn main() {
    let w = W(vec![1, 2, 3]);
    println!("{} {}", w[0], w.len());
}
