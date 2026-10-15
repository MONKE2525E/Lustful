// expect: L0110
// rustc E0277: an integer is not a str Pattern.
fn main() {
    println!("{}", "abc".contains(98));
}
