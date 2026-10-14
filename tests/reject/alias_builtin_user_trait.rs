// expect: L0104
// Valid Rust: `V4::mk()` calls the user trait's `mk` for `Vec<u8>`.
// lust takes only std traits on a type-relative path through an alias of
// a builtin type: std may have an inherent fn of that name lust does not
// model, which rustc would pick first. `<V4 as Mk>::mk()` names the trait.
trait Mk {
    fn mk() -> Self;
}
impl Mk for Vec<u8> {
    fn mk() -> Self {
        vec![1]
    }
}
type V4 = Vec<u8>;
fn main() {
    println!("{:?}", V4::mk());
}
