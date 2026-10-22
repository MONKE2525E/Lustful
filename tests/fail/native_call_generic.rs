// expect: L0107
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() { unsafe { abs::<i32>(-1); } }
