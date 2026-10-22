use serde_json::json;
struct Key<'a> { trace: &'a std::cell::RefCell<String> }
impl<'a> From<Key<'a>> for String {
    fn from(k: Key<'a>) -> String {
        k.trace.borrow_mut().push_str("into;");
        String::from("dup")
    }
}
fn key(trace: &std::cell::RefCell<String>) -> Key<'_> {
    trace.borrow_mut().push_str("key;");
    Key { trace }
}
fn value(trace: &std::cell::RefCell<String>, n: i32) -> i32 {
    trace.borrow_mut().push_str("value;");
    n
}
fn sum(a: i32, b: i32) -> i32 { a + b }
fn main() {
    let trace = std::cell::RefCell::new(String::new());
    let values = [5, 6];
    let v = json!({
        (key(&trace)): value(&trace, 1),
        (key(&trace)): value(&trace, 2),
        "expr": [sum(1, 2), values[1], 2 + 3, ({ let x = 7; x + 1 }),],
        "array": [value(&trace, 3), value(&trace, 4)],
    });
    assert_eq!(&*trace.borrow(), "key;into;value;key;into;value;value;value;");
    println!("{}", serde_json::to_string(&v).unwrap());
    println!("{}", trace.borrow());
}
