// expect: L0820
fn main() {
    let s = "a b";
    println!("{}", s.split_once(' ').unwrap().0);
}
