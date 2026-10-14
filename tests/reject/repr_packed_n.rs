// expect: L0652
// Valid Rust; only packed and packed(1) are in the layout grammar.
#[repr(packed(2))]
struct S {
    a: u8,
    b: u32,
}

fn main() {
    println!("{}", std::mem::size_of::<S>());
}
