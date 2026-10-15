// expect: L0104
// rustc E0599: `i32` does not implement `Deref`.
fn main() {
    let x: Option<i32> = None;
    println!("{:?}", x.as_deref());
}
