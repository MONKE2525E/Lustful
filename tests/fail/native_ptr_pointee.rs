// expect: L0110
unsafe extern "C" { fn strlen(text: *const i8) -> usize; }
fn main() { let n = 0i32; unsafe { strlen(&n); } }
