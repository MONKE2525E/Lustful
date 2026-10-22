// expect: L0522
#[link(name = "m")]
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() {}
