use serde_json::json;
fn main() {
    let s = String::from("text");
    let a = vec![s.clone(), String::from("tail")];
    let value = json!({"inside": a});
    let refs = &&s;
    let v = json!([s, a, value, refs, String::from("temporary")]);
    assert_eq!(s, "text");
    assert_eq!(a.len(), 2);
    assert!(value.is_object());
    println!("{}", serde_json::to_string(&v).unwrap());
    println!("{} {} {}", s, a[1], serde_json::to_string(&value).unwrap());
    let owned_key = String::from("consumed");
    let keyed = json!({(owned_key): s});
    println!("{}", serde_json::to_string(&keyed).unwrap());
}
