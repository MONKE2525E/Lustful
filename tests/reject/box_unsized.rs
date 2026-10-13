// expect: L0641
fn main() {
    let b: Box<[i32]> = Box::new([1, 2, 3]);
    println!("{:?}", b);
}
