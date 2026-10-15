// expect: L0640
// Valid Rust: Clone::clone_from on a Cow reuses the Owned buffer.
// Lust has no clone_from on any type yet.
use std::borrow::Cow;

fn main() {
    let mut a: Cow<str> = Cow::Owned("long string here".to_string());
    let b: Cow<str> = Cow::Borrowed("b");
    a.clone_from(&b);
    println!("{}", a);
}
