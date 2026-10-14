// expect: L0612
// `VecDeque` has no `FromIterator` in lust std yet (its capacity after
// `collect` follows std's spec rules). rustc accepts this.
use std::collections::VecDeque;
fn main() {
    let s: VecDeque<u8> = vec![1u8].into_iter().collect();
    println!("{}", s.len());
}
