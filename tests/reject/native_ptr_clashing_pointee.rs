// expect: L0810
// rustc accepts these unused declarations with a clash warning.
mod a { unsafe extern "C" { pub fn same_pointer(value: *const i8); } }
mod b { unsafe extern "C" { pub fn same_pointer(value: *const u8); } }
fn main() {}
