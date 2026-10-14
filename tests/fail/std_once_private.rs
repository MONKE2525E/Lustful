// expect: L0510
// rustc E0616: the cell's storage is private.
use std::sync::OnceLock;
fn main() {
    let o: OnceLock<i32> = OnceLock::new();
    println!("{:?}", o.inner);
}
