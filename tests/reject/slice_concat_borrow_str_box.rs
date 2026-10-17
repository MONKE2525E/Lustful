// expect: L0640
// Valid Rust: `Box<str>: Borrow<str>`, so `[Box<str>]::concat` is core's
// join. Lust builds it only over String and `&str` elements.
fn main() {
    let b: Vec<Box<str>> = vec!["a".into(), "b".into()];
    println!("{} {}", b.concat(), b.join("-"));
}
