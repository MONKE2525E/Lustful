// expect: L0404
unsafe extern "C" { fn strlen(text: *const i8) -> usize; }
fn main() { let text = b"x\0"; strlen(text.as_ptr().cast::<i8>()); }
