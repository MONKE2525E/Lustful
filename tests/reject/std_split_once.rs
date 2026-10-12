// expect: L0104
fn main() {
    let s = "a b";
    println!("{}", s.split_once(' ').unwrap().0);
}
