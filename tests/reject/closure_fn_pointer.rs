// expect: L0820
fn main() {
    let f: fn(i32) -> i32 = |x| x + 1;
    println!("{}", f(1));
}
