// expect: L0104
// Valid Rust: method calls through Cow's Deref (autoderef) are not
// supported yet.
use std::borrow::Cow;

fn main() {
    let c: Cow<str> = Cow::Borrowed("ab");
    println!("{}", c.len());
}
