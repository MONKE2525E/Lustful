// expect: L0630
unsafe extern "C" { fn strlen(text: *const i8) -> usize; }
const N: usize = unsafe { strlen(b"x\0".as_ptr().cast::<i8>()) };
fn main() { println!("{N}"); }
