use serde_json::json;
fn main() {
    let defaults = ["ControlLeft", "MetaLeft"];
    let v = json!({"keys": defaults, "ok": true, "extra": null});
    assert_eq!(defaults[0], "ControlLeft");
    assert_eq!(v.as_object().unwrap().get("ok").unwrap().as_bool(), Some(true));
    println!("{}", serde_json::to_string(&v).unwrap());
}
