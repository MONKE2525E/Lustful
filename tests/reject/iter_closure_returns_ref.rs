// expect: L0820
fn main() {
    let v = vec![String::from("a")];
    let s: Vec<&str> = v.iter().map(|s| s.as_str()).collect();
    println!("{:?}", s);
}
