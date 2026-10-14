// expect: L0702
// Valid Rust. A `dyn Error` object needs its std supertraits in a
// vtable, which lust does not build yet (dyn.std). The trait
// itself, impls, and bounds work (W-STD-C phase 2).
use std::error::Error;
use std::fmt;
#[derive(Debug)]
struct Boom;
impl fmt::Display for Boom {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "boom") }
}
impl Error for Boom {}
fn show(e: &dyn Error) { println!("{e}"); }
fn main() { show(&Boom); }
