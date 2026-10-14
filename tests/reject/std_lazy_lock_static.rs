// expect: L0630
// A `static LazyLock` needs a fn pointer in a static initializer, which
// the const evaluator lacks yet.
use std::sync::LazyLock;
static T: LazyLock<Vec<i32>> = LazyLock::new(|| vec![1, 2, 3]);
fn main() {
    println!("{}", LazyLock::force(&T).len());
}
