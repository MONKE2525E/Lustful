// expect: L0640
// A `const { .. }` initializer with statements is valid Rust; lust checks
// one-expression const initializers only.
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
