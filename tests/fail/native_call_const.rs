// expect: L0630
unsafe extern "C" { fn abs(value: i32) -> i32; }
const N: i32 = unsafe { abs(-17) };
fn main() { println!("{N}"); }
