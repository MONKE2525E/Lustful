// expect: L0306
// Valid Rust: rustc promotes `&|n| n - 1` (a closure with no captures) to a `'static` constant. lust does not promote closures yet (W-BORROW).
fn main() {
    let g = |n: i32| n * 2;
    let fs: Vec<&dyn Fn(i32) -> i32> = vec![&g, &|n| n - 1];
    println!("{}", fs.iter().map(|f| f(5)).sum::<i32>());
}
