// expect: L0303
fn main() {
    let mut text = String::from("hello");
    let chars = text.chars();
    let remaining = chars.as_str();
    text.clear();
    println!("{}", remaining);
}
