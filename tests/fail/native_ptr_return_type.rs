// expect: L0110
unsafe extern "C" { fn strchr(text: *const i8, ch: i32) -> *mut i8; }
fn wrapper(text: *const i8) -> *mut i32 { unsafe { strchr(text, 0) } }
fn main() {}
