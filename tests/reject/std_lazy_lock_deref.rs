// expect: L0104
// `*lazy` and method calls through `Deref` on user and std source types
// wait for user Deref support (W-CHECK-G2).
use std::sync::LazyLock;
fn main() {
    let l = LazyLock::new(|| vec![1, 2, 3]);
    println!("{}", l.len());
}
