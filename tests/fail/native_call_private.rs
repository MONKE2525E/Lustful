// expect: L0510
mod m { unsafe extern "C" { fn abs(value: i32) -> i32; } }
fn main() { unsafe { m::abs(-1); } }
