// expect: L0810
unsafe extern "C" { fn unsupported(value: *const &'static u8); }
fn main() {}
