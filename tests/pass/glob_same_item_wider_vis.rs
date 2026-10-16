// The same item through a private glob and then a `pub(crate)` glob:
// the binding takes the wider visibility, so `h2::X` is visible from
// the crate root.
mod i3 {
    pub struct X {}
    impl X {
        pub fn v() -> u32 {
            3
        }
    }
}
mod h0 {
    pub(crate) use crate::i3::X;
}
mod h2 {
    use crate::i3::*;
    pub use crate::h0::*;
}
fn main() {
    println!("{}", crate::h2::X::v());
}
