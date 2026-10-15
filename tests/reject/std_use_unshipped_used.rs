// expect: L0102
// The import of a std type lust does not model is accepted, but a use
// of the name rejects.
use std::backtrace::Backtrace;

fn main() {
    let b: Option<Backtrace> = None;
    println!("{}", b.is_none());
}
