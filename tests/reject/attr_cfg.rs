// expect: L0522
#[cfg(unix)]
fn one() -> i64 {
    1
}

fn main() {
    println!("{}", one());
}
