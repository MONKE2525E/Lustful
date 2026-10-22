fn observe(label: &str, bytes: &[u8]) {
    match serde_json::from_slice::<serde_json::Value>(bytes) {
        Ok(value) => println!("{}\tOK\t{}\t{:?}", label, serde_json::to_string(&value).unwrap(), value),
        Err(error) => println!("{}\tERR\t{}\t{}\t{}", label, error, error.line(), error.column()),
    }
}
fn main() {
    let cases: &[(&str, &[u8])] = &[
        ("null", b"null"), ("bools", b"[true,false,null]"),
        ("spaces", b" \r\n\t {\"x\": [1,2]} \n"),
        ("empty", b""), ("spaces-only", b" \n\t"),
        ("short-null", b"nul"), ("bad-null", b"nulx"), ("null-tail", b"nullx"),
        ("short-true", b"tru"), ("bad-true", b"trux"), ("short-false", b"fals"),
        ("empty-array", b"[]"), ("empty-object", b"{}"),
        ("missing-array-end", b"["), ("array-space", b"[ \n"),
        ("array-comma", b"[,]"), ("array-trailing-comma", b"[1,]"),
        ("array-missing-comma", b"[1 2]"), ("array-missing-end", b"[1"),
        ("array-wrong-end", b"[1}"), ("array-double-comma", b"[1,,2]"),
        ("object-key-eof", b"{"), ("object-key-number", b"{1:2}"),
        ("object-key-bool", b"{true:2}"), ("object-key-single", b"{'x':1}"),
        ("object-colon-eof", b"{\"x\""), ("object-missing-colon", b"{\"x\" 1}"),
        ("object-value-eof", b"{\"x\":"), ("object-missing-value", b"{\"x\":}"),
        ("object-end-eof", b"{\"x\":1"), ("object-wrong-end", b"{\"x\":1]"),
        ("object-missing-comma", b"{\"x\":1 \"y\":2}"),
        ("object-trailing-comma", b"{\"x\":1,}"),
        ("duplicate-key", b"{\"x\":1,\"x\":2}"),
        ("sorted-key", b"{\"z\":1,\"a\":2,\"m\":3}"),
        ("empty-string", b"\"\""), ("string-eof", b"\"abc"),
        ("string-backslash-eof", b"\"abc\\"), ("string-invalid-escape", b"\"\\x\""),
        ("string-escapes", b"\"\\\"\\\\\\/\\b\\f\\n\\r\\t\""),
        ("string-control", b"\"a\x01b\""), ("string-nul", b"\"\x00\""),
        ("string-newline", b"\"a\nb\""), ("unicode-short", b"\"\\u12\""),
        ("unicode-badhex", b"\"\\u12gx\""), ("unicode-nul", b"\"\\u0000\""),
        ("unicode-bmp", b"\"\\u00e9\\u2028\""),
        ("surrogate-pair", b"\"\\ud83d\\ude80\""),
        ("surrogate-high", b"\"\\ud800\""), ("surrogate-low", b"\"\\udc00\""),
        ("surrogate-wrong", b"\"\\ud800\\u0041\""),
        ("surrogate-tail-eof", b"\"\\ud800\\u"),
        ("utf8-valid", b"\"\xc3\xa9\xf0\x9f\x9a\x80\""),
        ("utf8-invalid", b"\"\xff\""), ("utf8-truncated", b"\"\xe2\x82\""),
        ("utf8-overlong", b"\"\xc0\x80\""), ("utf8-surrogate", b"\"\xed\xa0\x80\""),
        ("utf8-too-large", b"\"\xf4\x90\x80\x80\""),
        ("utf8-outside", b"\xff"), ("bom", b"\xef\xbb\xbfnull"),
        ("comment", b"/*x*/null"), ("vertical-space", b"\x0bnull"),
        ("multiple", b"null false"), ("multi-line-error", b"[\n 1,\n x]"),
        ("cr-line-error", b"[\r 1,\r x]"),
        ("escaped-duplicate", b"{\"a\":1,\"\\u0061\":2}"),
    ];
    for (label, bytes) in cases { observe(label, bytes); }
    for depth in [126_usize,127,128,129] {
        let mut text = String::new();
        for _ in 0..depth { text.push('['); }
        text.push('0');
        for _ in 0..depth { text.push(']'); }
        observe(&format!("array-depth-{}", depth), text.as_bytes());
        let mut text = String::new();
        for _ in 0..depth { text.push_str("{\"x\":"); }
        text.push('0');
        for _ in 0..depth { text.push('}'); }
        observe(&format!("object-depth-{}", depth), text.as_bytes());
    }
}
