// expect: L0643
// Valid Rust: `s.as_mut_str()` is String's inherent method, which rustc
// picks over the user trait's method of that name. lust does not model
// `String::as_mut_str` yet, so it rejects the call rather than call the
// trait. `Mut::as_mut_str(&mut s)` names the trait.
trait Mut {
    fn as_mut_str(&mut self) -> u8;
}
impl Mut for String {
    fn as_mut_str(&mut self) -> u8 {
        3
    }
}
fn main() {
    let mut s = String::from("ab");
    println!("{:?}", s.as_mut_str());
    println!("{}", Mut::as_mut_str(&mut s));
}
