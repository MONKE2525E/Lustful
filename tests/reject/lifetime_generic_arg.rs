// expect: L0203
fn main() {
    let s: std::borrow::Cow<'static, str> = std::borrow::Cow::Borrowed("hi");
    println!("{}", s);
}
