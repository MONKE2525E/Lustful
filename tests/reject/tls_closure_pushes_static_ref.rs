// expect: L0733
// A 'static borrow captured by a `with_borrow_mut` closure and stored in
// the value: valid, but lust's closure regions do not see that the
// captured borrow is 'static yet (W-BORROW).
use std::cell::RefCell;
thread_local! {
    static V: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}
fn add(x: &'static str) {
    V.with_borrow_mut(|v| v.push(x));
}
fn main() {
    add("a");
    V.with_borrow(|v| println!("{:?}", v));
}
