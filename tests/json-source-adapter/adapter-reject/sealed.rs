struct Local;
impl serde_json::JsonInput for Local {
    fn __json_value(&self) -> serde_json::Value { serde_json::Value::Null }
}
fn main() { let _ = serde_json::to_value(Local); }
