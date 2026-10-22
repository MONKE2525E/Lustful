// Isolated char iteration / UTF-8 / control-escape mechanism.
fn json_prereq_escape(input: &str) -> String {
    let hex = b"0123456789abcdef";
    let mut out = String::new();
    out.push('"');
    for ch in input.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{0008}' => out.push_str("\\b"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\u{000c}' => out.push_str("\\f"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 32 => {
                let n = c as usize;
                out.push_str("\\u00");
                out.push(hex[n >> 4] as char);
                out.push(hex[n & 15] as char);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
fn main() {
    let mut controls = String::new();
    for n in 0u8..32 { controls.push(n as char); }
    let expected = concat!(
        "\"\\u0000\\u0001\\u0002\\u0003\\u0004\\u0005\\u0006\\u0007",
        "\\b\\t\\n\\u000b\\f\\r\\u000e\\u000f",
        "\\u0010\\u0011\\u0012\\u0013\\u0014\\u0015\\u0016\\u0017",
        "\\u0018\\u0019\\u001a\\u001b\\u001c\\u001d\\u001e\\u001f\""
    );
    assert_eq!(json_prereq_escape(&controls), expected);
    assert_eq!(json_prereq_escape(""), "\"\"");
    assert_eq!(json_prereq_escape("\"/\\\r\n\0"), "\"\\\"/\\\\\\r\\n\\u0000\"");
    let unicode = "é😀e\u{0301}\u{2028}\u{2029}\u{007f}";
    let escaped = json_prereq_escape(unicode);
    assert_eq!(escaped, format!("\"{}\"", unicode));
    assert_eq!(escaped.as_bytes().len(), unicode.as_bytes().len() + 2);
    println!("json_prereq_control_escape ok");
}
