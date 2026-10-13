// expect: L0112
// A user type named `Cell` makes `Cell::get` its own fn, which rustc calls
// here; lust takes std fn paths only as `with` callables.
use std::cell::Cell as StdCell;
struct Cell(u8);
impl Cell {
    fn get(c: &StdCell<u8>) -> u8 {
        c.get() + 100
    }
}
thread_local! {
    static N: StdCell<u8> = const { StdCell::new(1) };
}
fn main() {
    println!("{}", N.with(Cell::get));
    let _ = Cell(0).0;
}
