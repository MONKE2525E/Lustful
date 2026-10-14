// expect: L0104
// A user Deref type: Rust accepts; lust has no Deref impls in its
// Option source yet.
use std::ops::Deref;
struct W(String);
impl Deref for W {
    type Target = String;
    fn deref(&self) -> &String {
        &self.0
    }
}
fn main() {
    let o = Some(W(String::from("x")));
    println!("{:?}", o.as_deref());
}
