// expect: L0614
// A generic fn named by a qualified path as a value is not supported yet.
struct W<T>(T);
impl<T> W<T> {
    fn get() -> u8 {
        4
    }
}
fn main() {
    let f = <W<u16>>::get;
    println!("{}", f());
}
