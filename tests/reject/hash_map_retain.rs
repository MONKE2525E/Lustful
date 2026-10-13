// expect: L0640
// Valid Rust: map retain (closure over each element) is not ported yet.
use std::collections::HashMap;

fn main() {
    let mut m: HashMap<u32, u32> = HashMap::new();
    m.insert(1, 2);
    m.retain(|k, _| *k > 1);
    println!("{}", m.len());
}
