// expect: L0522
#[cfg_attr(unix, allow(dead_code))]
fn one() -> i64 {
    1
}

fn main() {
    println!("{}", one());
}
