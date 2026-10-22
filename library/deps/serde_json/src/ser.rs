use crate::Value;

pub(crate) fn write_value(value: &Value, out: &mut String) {
    match value {
        Value::Null => out.push_str("null"),
        Value::Bool(v) => out.push_str(if *v { "true" } else { "false" }),
        Value::Number(v) => v.write_json(out),
        Value::String(v) => write_string(v, out),
        Value::Array(v) => {
            out.push('[');
            let mut first = true;
            for item in v {
                if !first { out.push(','); }
                first = false;
                write_value(item, out);
            }
            out.push(']');
        }
        Value::Object(v) => {
            out.push('{');
            let mut first = true;
            for (key, value) in v.iter() {
                if !first { out.push(','); }
                first = false;
                write_string(key, out);
                out.push(':');
                write_value(value, out);
            }
            out.push('}');
        }
    }
}

fn write_string(value: &str, out: &mut String) {
    out.push('"');
    for c in value.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{08}' => out.push_str("\\b"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\u{0c}' => out.push_str("\\f"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => {
                const HEX: &[u8] = b"0123456789abcdef";
                let n = c as usize;
                out.push_str("\\u00");
                out.push(HEX[n >> 4] as char);
                out.push(HEX[n & 15] as char);
            }
            c => out.push(c),
        }
    }
    out.push('"');
}
