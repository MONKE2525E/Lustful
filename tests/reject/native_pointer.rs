// expect: L0810
unsafe extern "C" { fn native_nested(value: *const *const u8) -> usize; }
fn main() {}
