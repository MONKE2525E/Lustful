// ARCH 2.8: the trait's own object type may appear in argument
// and return positions. Those name the erased trait, not Self,
// so the trait stays dyn compatible. From the probe dyn2.rs,
// made executable.
trait T {
    fn f(&self, x: &dyn T) -> u8;
    fn g(&self) -> Box<dyn T>;
    fn v(&self) -> u8;
}
struct S(u8);
impl T for S {
    fn f(&self, x: &dyn T) -> u8 {
        self.0 + x.v()
    }
    fn g(&self) -> Box<dyn T> {
        Box::new(S(self.0 + 1))
    }
    fn v(&self) -> u8 {
        self.0
    }
}
fn use_object(obj: &dyn T) -> u8 {
    obj.f(obj.g().as_ref())
}
fn main() {
    println!("{}", use_object(&S(10)));
}
