// expect: L0621
fn main() {
    let x: <i64 as std::ops::Add>::Output = 3;
    println!("{}", x);
}
