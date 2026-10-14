// expect: L0640
// Valid Rust: a map key with a generic written Hash impl. The hash glue
// calls written impls of non-generic impls only, so lust rejects it.
use std::collections::HashMap;
use std::hash::{Hash, Hasher};

#[derive(PartialEq, Eq)]
struct W<T>(T, u8);

impl<T: Hash> Hash for W<T> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.0.hash(h);
    }
}

fn main() {
    let mut m = HashMap::new();
    m.insert(W(1u32, 0), "a");
    println!("{:?}", m.get(&W(1u32, 9)));
}
