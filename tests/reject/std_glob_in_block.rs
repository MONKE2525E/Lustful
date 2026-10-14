// expect: L0505
// A block's std glob shadows the crate-root `min` (rustc prints 1); lust
// rejects the name, since it cannot list a std module's names.
fn min(a: i32, b: i32) -> i32 { a * 100 + b }
fn main() {
    use std::cmp::*;
    println!("{}", min(1, 2));
}
