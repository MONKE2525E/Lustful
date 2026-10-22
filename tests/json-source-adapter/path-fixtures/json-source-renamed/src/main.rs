use renamed_json::{json, Value};
fn main() {
    let defaults = ["ControlLeft", "MetaLeft"];
    let value: Value = json!({"keys": defaults, "ok": true, "extra": null});
    assert_eq!(defaults[0], "ControlLeft");
    assert_eq!(value, renamed_json::json!({"keys": defaults, "ok": true, "extra": null}));
    println!("{}", renamed_json::to_string(&value).unwrap());
}
