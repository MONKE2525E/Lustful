// expect: L9001
// Std fns and Option/Result constructors as values have no value
// form yet. Each must report, not compile with an error type.
fn main() {
    let f = String::from;
    let s: String = f("x");
    let g = Box::new;
    let b = g(1u8);
    let h = Option::Some;
    println!("{} {} {:?}", s, b, h(2u8));
}
