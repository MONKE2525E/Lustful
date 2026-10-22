use serde_json as renamed;
use renamed::json;
struct Map;
struct Value;
fn to_value() {}
macro_rules! json_internal { ($($tt:tt)*) => { compile_error!("caller helper used") }; }
fn main() {
    let _ = (Map, Value);
    to_value();
    let v = json!({"a": [null, 1, {"b": true}],});
    let w = renamed::json!({"a": [null, 1, {"b": true}],});
    assert_eq!(v, w);
    println!("{}", renamed::to_string(&v).unwrap());
}
