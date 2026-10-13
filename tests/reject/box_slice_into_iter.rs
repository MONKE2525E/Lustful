// expect: L0640
fn main() {
    let b: Box<[i32]> = vec![1, 2].into_boxed_slice();
    let v: Vec<i32> = b.into_iter().collect();
    println!("{:?}", v);
}
