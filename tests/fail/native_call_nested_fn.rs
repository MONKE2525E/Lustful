// expect: L0404
unsafe extern "C" { fn abs(value: i32) -> i32; }
fn main() { unsafe { fn nested() -> i32 { abs(-1) } println!("{}", nested()); } }
