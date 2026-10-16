// expect: L0509
// Valid Rust: rustc keeps the public binding of `Square` here. The same item comes
// through a public and a private glob, and in other shapes rustc's answer depends
// on its import order, so lust rejects the class (subset rule, L0509).
mod shapes {
    pub struct Square;
    impl Square {
        pub fn sides() -> u32 {
            4
        }
    }
}

mod prelude {
    pub use crate::shapes::*;
}

mod geometry {
    pub use crate::shapes::*;
    use crate::prelude::*;
}

fn main() {
    println!("{}", geometry::Square::sides());
}
