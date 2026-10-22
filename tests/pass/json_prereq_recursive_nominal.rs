// Recursive layout/drop and nominal wrapper, deliberately without derives.
use std::collections::BTreeMap;
struct JsonPrereqMap<K, V> { inner: BTreeMap<K, V> }
enum JsonPrereqValue {
    Null,
    Text(String),
    Array(Vec<JsonPrereqValue>),
    Object(JsonPrereqMap<String, JsonPrereqValue>),
}
fn json_prereq_weight(value: &JsonPrereqValue) -> usize {
    match value {
        JsonPrereqValue::Null => 1,
        JsonPrereqValue::Text(s) => s.len(),
        JsonPrereqValue::Array(a) => a.iter().map(json_prereq_weight).sum(),
        JsonPrereqValue::Object(m) =>
            m.inner.iter().map(|(k, v)| k.len() + json_prereq_weight(v)).sum(),
    }
}
fn main() {
    for _ in 0..16 {
        let mut value = JsonPrereqValue::Text(String::from("leaf"));
        for _ in 0..24 {
            let mut inner = BTreeMap::new();
            inner.insert(String::from("k"), value);
            value = JsonPrereqValue::Array(vec![
                JsonPrereqValue::Null, JsonPrereqValue::Object(JsonPrereqMap { inner }),
            ]);
        }
        assert_eq!(json_prereq_weight(&value), 52);
        // Drop each complete tree before the next iteration.
    }
    let mut inner = BTreeMap::new();
    inner.insert(String::from("z"), JsonPrereqValue::Null);
    inner.insert(String::from("a"), JsonPrereqValue::Text(String::from("old")));
    let mut map = JsonPrereqMap { inner };
    match map.inner.insert(String::from("a"), JsonPrereqValue::Null) {
        Some(JsonPrereqValue::Text(s)) => assert_eq!(s, "old"),
        _ => panic!("replacement lost"),
    }
    match map.inner.get_mut("z").unwrap() {
        slot => *slot = JsonPrereqValue::Text(String::from("new")),
    }
    match map.inner.get("z").unwrap() {
        JsonPrereqValue::Text(s) => assert_eq!(s, "new"),
        _ => panic!("borrowed lookup lost"),
    }
    let mut keys = String::new();
    for (key, _) in map.inner.iter() { keys.push_str(key); }
    assert_eq!(keys, "az");
    println!("json_prereq_recursive_nominal ok");
}
