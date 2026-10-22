fn main() {
    for text in ["", "[", "{", "\"", "n", "[1,", "{\"x\":", "\"\\q\"", "01", "1e309", "[1,]", "{1:2}", "null false", "[\n x]"] {
        let error = serde_json::from_str::<serde_json::Value>(text).unwrap_err();
        println!("{:?}\t{:?}\t{}\t{:?}\t{}:{}\t{} {} {} {}", text, error, error,
            error.classify(), error.line(), error.column(), error.is_io(), error.is_syntax(), error.is_data(), error.is_eof());
    }
}
