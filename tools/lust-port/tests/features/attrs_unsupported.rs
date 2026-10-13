// feature: attrs.unsupported
// form: track_caller and non_exhaustive attributes
#[track_caller]
fn here() -> u32 { std::panic::Location::caller().line() }
#[non_exhaustive]
struct Opts { level: i32 }
fn main() { println!("{} {}", here() > 0, Opts { level: 1 }.level); }
