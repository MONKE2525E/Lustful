// expect: L0113
// Rust 2024 iterates a boxed slice by value; lust does not yet.
fn main() {
    let b: Box<[String]> = vec![String::from("a")].into_boxed_slice();
    for x in b {
        println!("{}", x);
    }
}
