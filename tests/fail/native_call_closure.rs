// expect: L0404
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() { let f = || abs(-17); unsafe { println!("{}", f()); } }
