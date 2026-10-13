// expect: L0102
// lust does not follow a std glob through a `pub use` glob yet.
mod a {
    pub use std::cell::*;
}
use a::*;
fn main() {
    let c = Cell::new(3);
    println!("{}", c.get());
}
