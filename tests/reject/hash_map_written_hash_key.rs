// expect: L0640
// Valid Rust: a key with a written Hash impl. The hash glue hashes by
// structure only, so lust rejects it.
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

#[derive(PartialEq, Eq, Debug)]
struct K(u32);

impl Hash for K {
    fn hash<H: Hasher>(&self, h: &mut H) {
        h.write_u32(self.0 / 2);
    }
}

fn main() {
    let mut m = HashMap::new();
    m.insert(K(1), 1);
    println!("{:?}", m.get(&K(0)));
}
