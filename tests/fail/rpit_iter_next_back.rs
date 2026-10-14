// expect: L0104
// rustc E0599: `next_back` is not a method of an `impl Iterator` value.
fn evens() -> impl Iterator<Item = u32> {
    vec![2u32, 4].into_iter()
}
fn main() {
    let mut it = evens();
    println!("{:?}", it.next_back());
}
