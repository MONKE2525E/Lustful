// expect: L0640
// Valid Rust: hash_one of a type with a written Hash impl (the hash glue
// hashes by structure, so lust does not run written impls there yet).
use std::hash::{BuildHasher, Hash, Hasher, RandomState};
struct K(u8);
impl Hash for K {
    fn hash<H: Hasher>(&self, state: &mut H) {
        state.write_u8(self.0 + 1);
    }
}
fn main() {
    let s = RandomState::new();
    println!("{}", s.hash_one(K(1)) == s.hash_one(K(1)));
}
