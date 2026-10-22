use serde_json::{json, Value};
fn main() {
    let owned = String::from("owned");
    for v in [json!(null), json!(false), json!(true), json!(""), json!("borrowed"), json!(owned)] {
        println!("{} {:?} {:?} {:?}", serde_json::to_string(&v).unwrap(),
            v.as_null(), v.as_bool(), v.as_str());
    }
    assert_eq!(owned, "owned");
    let v: Value = Default::default();
    assert_eq!(v, json!(null));
    assert_eq!(serde_json::to_value(String::from("move")).unwrap(), json!("move"));
    println!("{}", serde_json::to_string::<str>("unsized").unwrap());
    println!("{:?}", serde_json::to_string(&true).unwrap());
}
