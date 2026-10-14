// feature: std.other
// form: a std path with no precise rule yet, std::panic::Location
fn main() {
    let l = std::panic::Location::caller();
    println!("{}", l.line());
}
