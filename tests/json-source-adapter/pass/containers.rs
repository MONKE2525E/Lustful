use serde_json::{json, Value};
fn main() {
    let defaults = ["ControlLeft", "MetaLeft"];
    let empty: [&str; 0] = [];
    let many = ["x"; 32];
    let slice: &[&str] = &defaults;
    let nested = vec![Some(vec![defaults]), None, Some(vec![defaults])];
    println!("{}", serde_json::to_string(&json!({"keys": defaults, "ok": true, "extra": null})).unwrap());
    println!("{}", serde_json::to_string(&json!(["ControlLeft", "AltLeft"])).unwrap());
    for v in [
        json!(empty), json!(["x"]), json!(defaults), json!(many),
        json!(slice), json!(&&&slice), json!([defaults, defaults]), json!(nested),
        json!(None::<Vec<[&str; 2]>>),
    ] {
        println!("{}", serde_json::to_string(&v).unwrap());
    }
    println!("{}", serde_json::to_string::<[&str]>(slice).unwrap());
    assert_eq!(defaults[0], "ControlLeft");
    let mut v = json!({"a": [null, true, {"z": 4}]});
    let original = v.clone();
    v.as_object_mut().unwrap().get_mut("a").unwrap().as_array_mut().unwrap().push(json!("new"));
    assert_ne!(original, v);
    println!("{}", serde_json::to_string(&original).unwrap());
    println!("{}", serde_json::to_string(&v).unwrap());
    let mut deep = Value::Null;
    for _ in 0..24 { deep = Value::Array(vec![deep]); }
    for _ in 0..16 {
        let copy = serde_json::to_value(&deep).unwrap();
        assert_eq!(copy, deep);
    }
    println!("{}", serde_json::to_string(&deep).unwrap());
}
