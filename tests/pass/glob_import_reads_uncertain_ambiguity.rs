// `c` gets `x` from a private glob of `i1` first, and later `i2::x`
// through `h1`, which reads `h2`'s explicit import of `h0::x`. rustc's
// ambiguity in `c` keeps the private glob's visibility, so `h0`'s glob
// of `c` does not see it and `h2`'s import of `h0::x` is `i2::x`.
mod h0 {
    pub use crate::i2::*;
    pub use self::c::*;
    pub mod c {
        pub use crate::h1::*;
        #[allow(unused_imports)]
        use crate::i1::*;
        pub fn cf() -> u32 {
            5
        }
    }
}
mod h1 {
    pub use crate::h2::*;
}
mod h2 {
    pub use crate::h0::x;
}
mod i1 {
    pub fn x() -> u32 {
        10
    }
}
mod i2 {
    pub fn x() -> u32 {
        20
    }
}
fn main() {
    println!("{} {}", h0::c::cf(), h2::x());
}
