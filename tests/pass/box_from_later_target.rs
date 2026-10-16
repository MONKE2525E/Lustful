// `Box::from(x)` whose target a later coercion fixes, as rustc infers it
// (ts-rust ls/sourcedefinition.rs:657 `Box::leak(Box::from(&*text))`).
use std::rc::Rc;
fn take_rc(r: Rc<str>) -> usize {
    r.len()
}
fn main() {
    let text = String::from("héllo");
    let a: &'static str = Box::leak(Box::from(&*text));
    let s: &str = &text[1..];
    let b: &'static str = match s.len() {
        0 => "empty",
        _ => Box::leak(Box::from(s)),
    };
    let v = vec![1u8, 2, 3];
    let c: &'static mut [u8] = Box::leak(Box::from(&v[..]));
    c[0] = 9;
    let r = Rc::from(text.as_str());
    let mut boxes: Vec<Box<str>> = Vec::new();
    boxes.push(Box::from(s));
    println!("{a} {b} {:?} {} {:?}", c, take_rc(r), boxes);
}
