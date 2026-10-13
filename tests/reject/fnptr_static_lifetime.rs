// expect: L0203
// Valid Rust: lust does not track lifetimes in fn pointer types yet (W-BORROW).
fn apply(f: fn(&'static str) -> usize) -> usize {
    f("abc")
}

fn len(s: &str) -> usize {
    s.len()
}

fn main() {
    println!("{}", apply(len));
}
