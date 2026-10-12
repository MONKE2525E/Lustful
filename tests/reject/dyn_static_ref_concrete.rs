// expect: L0705
// ARCH 2.8: `dyn Tr + 'static` over a type that holds a reference. The
// reference is 'static here, so rustc accepts; lust erases lifetimes in
// types and cannot prove it, so it rejects instead of guessing.
trait Tr {
    fn get(&self) -> u8;
}
impl Tr for &u8 {
    fn get(&self) -> u8 {
        **self
    }
}
static X: u8 = 5;
fn keep(d: &(dyn Tr + 'static)) -> u8 {
    d.get()
}
fn main() {
    let r: &'static u8 = &X;
    println!("{}", keep(&r));
}
