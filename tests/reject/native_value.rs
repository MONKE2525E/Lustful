// expect: L0810
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() { let _function = abs; }
