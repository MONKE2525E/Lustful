// expect: L0404
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() { println!("{}", abs(-17)); }
