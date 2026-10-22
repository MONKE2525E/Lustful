use std::collections::BTreeMap;
struct JsonPrereqMap<K, V> { inner: BTreeMap<K, V> }
#[derive(Clone, PartialEq)]
enum JsonPrereqValue {
    Null,
    Text(String),
    Array(Vec<JsonPrereqValue>),
    Object(JsonPrereqMap<String, JsonPrereqValue>),
}
// Specialized wrapper impls deliberately feed back into the enum derives.
impl Clone for JsonPrereqMap<String, JsonPrereqValue> {
    fn clone(&self) -> Self { Self { inner: self.inner.clone() } }
}
impl PartialEq for JsonPrereqMap<String, JsonPrereqValue> {
    fn eq(&self, other: &Self) -> bool { self.inner == other.inner }
}
fn main() {
    for _ in 0..8 {
        let mut value = JsonPrereqValue::Text(String::from("leaf"));
        for _ in 0..16 {
            let mut inner = BTreeMap::new();
            inner.insert(String::from("child"), value);
            value = JsonPrereqValue::Array(vec![
                JsonPrereqValue::Null, JsonPrereqValue::Object(JsonPrereqMap { inner }),
            ]);
        }
        let mut copy = value.clone();
        assert!(value == copy);
        match &mut copy {
            JsonPrereqValue::Array(items) => match &mut items[1] {
                JsonPrereqValue::Object(map) => {
                    *map.inner.get_mut("child").unwrap() =
                        JsonPrereqValue::Text(String::from("changed"));
                }
                _ => panic!("object missing"),
            },
            _ => panic!("array missing"),
        }
        assert!(value != copy);
        assert!(value == value.clone());
    }
    println!("json_prereq_recursive_derive ok");
}
