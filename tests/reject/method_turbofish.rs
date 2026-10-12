// expect: L0104
fn main() {
    let n: i64 = "42".parse::<i64>().unwrap();
    println!("{}", n);
}
