// expect: L0307
fn remaining<'a>() -> &'a str {
    let text = String::from("hello");
    text.chars().as_str()
}
fn main() { println!("{}", remaining()); }
