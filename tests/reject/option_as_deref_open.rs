// expect: L0610
// Valid Rust: rustc fixes the payload type later; lust picks among its
// per-type `as_deref` impls at the call, so an open payload rejects.
fn main() {
    let mut x = None;
    let n = x.as_deref().is_some();
    x = Some(String::from("a"));
    println!("{} {:?}", n, x);
}
