// expect: L0640
// Valid Rust: array::IntoIter of non-Copy elements (each element needs
// its own drop state, which lust does not track yet).
fn main() {
    let v: Vec<String> = [String::from("a"), String::from("b")].into_iter().collect();
    println!("{:?}", v);
}
