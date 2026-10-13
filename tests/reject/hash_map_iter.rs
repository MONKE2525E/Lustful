// expect: L0640
// Valid Rust: map iteration is not ported yet.
use std::collections::HashMap;

fn main() {
    let mut m: HashMap<u32, u32> = HashMap::new();
    m.insert(1, 2);
    for (k, v) in m.iter() {
        println!("{} {}", k, v);
    }
}
