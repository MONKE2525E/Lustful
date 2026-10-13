// expect: L0640
fn main() {
    let v = vec![vec![1, 2], vec![3]];
    let f: Vec<i32> = v.iter().flat_map(|x| x.iter().copied()).collect();
    println!("{:?}", f);
}
