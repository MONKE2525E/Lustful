// expect: L0810
#[repr(C)]
struct Record { value: i32 }
unsafe extern "C" { fn unsupported(value: *const Record); }
fn main() {}
