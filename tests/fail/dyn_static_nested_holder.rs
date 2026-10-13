// expect: L0705
// rustc: lifetime may not live long enough. A user Adt arg used to reach tcc as two structs.
trait T { fn read(&self) -> u32; }
struct S { n: u32 }
impl T for S { fn read(&self) -> u32 { self.n } }
struct H<X> { x: X }
fn bad(x: H<&dyn T>) -> H<&(dyn T + 'static)> { x }
fn main() {}
