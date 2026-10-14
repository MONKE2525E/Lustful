// expect: L0640
// `collect` into a std source collection needs collect into user
// `FromIterator` types; `BTreeMap::from_iter(iter)` works today.
use std::collections::BTreeMap;
fn main() {
    let m: BTreeMap<u8, u8> = vec![(1, 2)].into_iter().collect();
    println!("{:?}", m);
}
