// expect: L0640
// Valid Rust: a lookup by str through a written Borrow impl.
use std::borrow::Borrow;
use std::collections::HashMap;

#[derive(Hash, PartialEq, Eq, Debug)]
struct K(String);

impl Borrow<str> for K {
    fn borrow(&self) -> &str {
        &self.0
    }
}

fn main() {
    let mut m = HashMap::new();
    m.insert(K("a".to_string()), 1);
    println!("{:?}", m.get("a"));
}
