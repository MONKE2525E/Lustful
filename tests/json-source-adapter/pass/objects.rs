use serde_json::{json, Map, Value};
fn main() {
    let mut m = Map::new();
    assert!(m.is_empty());
    assert_eq!(m.insert("z".into(), json!(1)), None);
    assert_eq!(m.insert("a".into(), json!(2)), None);
    assert_eq!(m.insert("z".into(), json!(3)), Some(json!(1)));
    assert_eq!(m.len(), 2);
    assert!(m.get("missing").is_none());
    assert!(m.get_mut("missing").is_none());
    *m.get_mut("a").unwrap() = json!([null, false,]);
    for (k, v) in m.iter() { println!("{}={}", k, serde_json::to_string(v).unwrap()); }
    println!("{}", serde_json::to_string(&json!(m)).unwrap());
    println!("{:?}\n{:#?}", m, m);
    println!("{}", serde_json::to_string(&json!({
        "z": 0, "é": 1, "": 2, "a": 3, "😀": 4, "a": 5, "\n": 6,
    })).unwrap());
    let variants = [json!(null), json!(true), json!(1), json!("s"), json!([]), json!({})];
    for mut v in variants {
        println!("{} {} {} {} {} {} {:?} {:?} {:?} {:?} {:?} {} {}",
            v.is_null(), v.is_boolean(), v.is_number(), v.is_string(), v.is_array(), v.is_object(),
            v.as_null(), v.as_bool(), v.as_str(), v.as_i64(), v.as_u64(),
            v.as_array().is_some(), v.as_object().is_some());
        println!("{} {}", v.as_array_mut().is_some(), v.as_object_mut().is_some());
        println!("{:?}\n{:#?}", v, v);
    }
    let m: Map<String, Value> = Default::default();
    assert!(m.is_empty());
}
