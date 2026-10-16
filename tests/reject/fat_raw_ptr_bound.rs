// expect: L0641
// A raw pointer to a dyn value kept in a binding: lust builds fat raw
// pointers only for an operand read at once (cast, addr, addr_eq, eq).
use std::rc::Rc;
trait Host {}
struct H;
impl Host for H {}
fn main() {
    let a: Rc<dyn Host> = Rc::new(H);
    let p = Rc::as_ptr(&a);
    println!("{}", std::mem::size_of_val(&p));
}
