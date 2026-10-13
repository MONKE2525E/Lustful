// expect: L0110
// Box<[T]> works, but lust has no Box<[T; N]> to Box<[T]> coercion yet.
fn main() {
    let b: Box<[i32]> = Box::new([1, 2, 3]);
    println!("{:?}", b);
}
