// expect: L0810
trait Marker {}
unsafe extern "C" { fn unsupported(value: *const dyn Marker); }
fn main() {}
