// expect: L0701
// Valid Rust (ARCH 2.8 shape) that lust rejects until dyn
// support lands: a trait object type in a signature.
trait T {
    fn v(&self) -> u8;
}
fn f(_x: &dyn T) {}
fn main() {
    println!("x");
}
