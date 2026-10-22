// expect: L0110
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() { unsafe { abs(1u64); } }
