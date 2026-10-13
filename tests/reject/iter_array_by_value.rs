// expect: L0640
fn main() {
    let a = [String::from("x"), String::from("y")];
    for s in a.into_iter().rev() {
        println!("{}", s);
    }
}
