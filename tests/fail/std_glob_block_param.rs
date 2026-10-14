// expect: L0505
// rustc E0308: the block's std glob brings `min` (a fn) over the parameter.
fn f(min: i32) -> i32 {
    use std::cmp::*;
    min
}
fn main() { println!("{}", f(5)); }
