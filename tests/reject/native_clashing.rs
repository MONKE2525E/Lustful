// expect: L0810
mod a { unsafe extern "C" { pub fn abs(value: i32) -> i32; } }
mod b { unsafe extern "C" { pub fn abs(value: u64) -> i32; } }
fn main() {}
