use serde_json::json;
fn main() {
    let mut controls = String::new();
    for n in 0..32 { controls.push(char::from_u32(n).unwrap()); }
    let samples = [
        controls, String::from("\"/\\\u{7f}\r\n\0x"),
        String::from("é漢😀e\u{301}\u{2028}\u{2029}"),
    ];
    for text in &samples {
        println!("{}", serde_json::to_string(text).unwrap());
        println!("{}", serde_json::to_string(&json!({(text): text})).unwrap());
    }
}
