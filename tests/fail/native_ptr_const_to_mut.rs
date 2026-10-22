// expect: L0110
unsafe extern "C" { fn gethostname(text: *mut i8, len: usize) -> i32; }
fn main() { let n = [0i8; 256]; unsafe { gethostname(n.as_ptr(), n.len()); } }
