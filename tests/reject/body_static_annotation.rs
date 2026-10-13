// expect: L0203
// Valid Rust: lust does not keep regions of body annotations yet (W-BORROW).
fn main() {
    let s: &'static str = "hi";
    println!("{}", s);
}
