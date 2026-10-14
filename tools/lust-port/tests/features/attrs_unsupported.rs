// feature: attrs.unsupported
// form: the non_exhaustive attribute
#[non_exhaustive]
struct Opts { level: i32 }
fn main() { println!("{}", Opts { level: 1 }.level); }
