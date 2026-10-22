// expect: L0404
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() { unsafe { abs(-1); } abs(-2); }
