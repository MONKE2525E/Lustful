// expect: L0113
// `map[&k]` needs user `Index` impls, which lust lacks yet.
use std::collections::BTreeMap;
fn main() {
    let mut m = BTreeMap::new();
    m.insert(1, "a");
    println!("{}", m[&1]);
}
