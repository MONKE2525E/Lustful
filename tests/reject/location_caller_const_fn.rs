// expect: L0631
// Valid Rust: `Location::caller()` is itself a const fn. Lust does
// not model it as one, so a user const fn calling it rejects
// (fx-attrs; the runtime form works).
use std::panic::Location;

const fn here() -> &'static Location<'static> {
    Location::caller()
}

fn main() {
    println!("{}", here().line());
}
