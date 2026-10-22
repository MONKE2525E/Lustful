// expect: L0311
fn main() {
    let text = String::from("hello");
    let chars = text.chars();
    let remaining = chars.as_str();
    drop(text);
    println!("{}", remaining);
}
