// expect: L0810
unsafe extern "C" { fn unsupported(value: *const fn(i32) -> i32); }
fn main() {}
