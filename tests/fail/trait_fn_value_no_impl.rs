// expect: L0104
// rustc E0277: S does not implement Tr.
trait Tr { fn mk() -> u8; }
struct S;
struct T;
impl Tr for T { fn mk() -> u8 { 1 } }
fn main() { let f = <S as Tr>::mk; println!("{}", f()); }
