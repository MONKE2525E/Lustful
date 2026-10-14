// expect: L0112
// `PhantomData`'s Debug prints `type_name::<T>()`, which lust lacks yet.
use std::marker::PhantomData;
fn main() {
    let p: PhantomData<u8> = PhantomData;
    println!("{:?}", p);
}
