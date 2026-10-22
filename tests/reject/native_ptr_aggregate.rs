// expect: L0810
#[repr(C)]
struct Record { ptr: *const u8, len: usize }
unsafe extern "C" { fn unsupported(value: Record); }
fn main() {}
