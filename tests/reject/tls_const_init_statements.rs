// expect: L0631
// A `const { .. }` initializer with statements is valid Rust; lust hands
// such a block to the bounded const evaluator whole, which does not run
// std's const constructors (`Cell::new`) yet.
use std::cell::Cell;
thread_local! {
    static S: Cell<u32> = const {
        let x = 2;
        Cell::new(x * 3)
    };
}
fn main() {
    println!("{}", S.get());
}
