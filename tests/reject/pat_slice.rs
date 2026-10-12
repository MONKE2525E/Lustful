// expect: L0820
fn main() {
    let v = vec![1, 2, 3];
    match v.as_slice() {
        [first, ..] => println!("{}", first),
        [] => println!("empty"),
    }
}
