// expect: L0640
fn main() {
    let v = vec![1, 2, 3, 4];
    let mut it = v.iter();
    let r = &mut it;
    let two: Vec<&i32> = r.take(2).collect();
    println!("{:?} {:?}", two, it.next());
}
