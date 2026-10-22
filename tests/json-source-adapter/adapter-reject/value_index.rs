fn main() { let v = serde_json::json!({"a":1}); let _ = &v["a"]; }
