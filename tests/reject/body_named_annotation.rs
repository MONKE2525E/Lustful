// expect: L0203
// Valid Rust: lust does not keep regions of body annotations yet (W-BORROW).
fn first<'a>(x: &'a [i32]) -> i32 {
    let y: &'a i32 = &x[0];
    *y
}

fn main() {
    println!("{}", first(&[3, 4]));
}
