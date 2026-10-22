// expect: L0110
unsafe extern "C" { fn strlen(text: *const i8) -> usize; }
fn main() { unsafe { strlen(0usize); } }
