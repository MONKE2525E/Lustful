use serde_json::Value;

fn owned() -> Value {
    let input = r#"{"x":"owned","dup":1,"dup":2,"float":-0.0}"#.to_string();
    serde_json::from_str(&input).unwrap()
}
fn main() {
    let value = owned();
    println!("{:?} {:?} {:?}", value.get("x").and_then(Value::as_str),
        value.get("dup").and_then(Value::as_u64), value.get("missing"));
    let zero = value.get("float").unwrap();
    println!("{} {} {} {:016x}", zero.is_f64(), zero.is_i64(), zero.is_u64(),
        zero.as_f64().unwrap().to_bits());
    println!("{}", serde_json::to_string(&value).unwrap());
    for text in ["null", "false", "1", "\"x\"", "[]"] {
        let parsed: Value = serde_json::from_slice(text.as_bytes()).unwrap();
        println!("{:?}", parsed.get("x"));
    }
    let parsed: Value = serde_json::from_str("[0, -0, 1.0, 9007199254740993.0]").unwrap();
    for number in parsed.as_array().unwrap() {
        println!("{} {} {} {:?} {:?} {:016x}", number.is_i64(), number.is_u64(),
            number.is_f64(), number.as_i64(), number.as_u64(), number.as_f64().unwrap().to_bits());
    }
    println!("{}", serde_json::to_string(&parsed).unwrap());
}
