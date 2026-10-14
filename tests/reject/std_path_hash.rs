// expect: L0641
// Path hashes by components in std; lust has no user Hasher bound yet,
// so Path and PathBuf are not Hash.
use std::collections::HashMap;
use std::path::PathBuf;
fn main() {
    let mut s: HashMap<PathBuf, u8> = HashMap::new();
    s.insert("a".into(), 1);
    println!("{}", s.len());
}
