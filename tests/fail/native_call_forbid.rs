// expect: L0531
#![forbid(unsafe_code)]
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() { unsafe { abs(-1); } }
