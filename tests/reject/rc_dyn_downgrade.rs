// expect: L0641
// A Weak is a thin pointer in lust: no Weak<dyn Trait> yet.
use std::rc::Rc;

trait Show {
    fn show(&self) -> u8;
}

struct A(u8);

impl Show for A {
    fn show(&self) -> u8 {
        self.0
    }
}

fn main() {
    let r: Rc<dyn Show> = Rc::new(A(1));
    let w = Rc::downgrade(&r);
    println!("{}", w.upgrade().is_some());
}
