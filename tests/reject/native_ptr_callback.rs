// expect: L0602
unsafe extern "C" { fn unsupported(value: *const extern "C" fn(i32) -> i32); }
fn main() {}
