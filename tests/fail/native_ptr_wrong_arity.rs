// expect: L0105
unsafe extern "C" { fn strlen(text: *const i8) -> usize; }
fn main() { unsafe { strlen(); } }
