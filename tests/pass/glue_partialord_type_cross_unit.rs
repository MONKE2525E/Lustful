// Regression, PartialOrd form of glue_display_type_cross_unit.rs: the cmp_
// glue in main's unit calls a user partial_cmp in a later unit and names
// Option<Ordering>, which the unit must declare itself.
fn main() {
    println!("{}", V(1) < V(2));
}
fn f0() {}
fn f1() {}
fn f2() {}
fn f3() {}
fn f4() {}
fn f5() {}
fn f6() {}
fn f7() {}
fn f8() {}
fn f9() {}
fn f10() {}
fn f11() {}
fn f12() {}
fn f13() {}
fn f14() {}
fn f15() {}
fn f16() {}
fn f17() {}
fn f18() {}
fn f19() {}
fn f20() {}
fn f21() {}
fn f22() {}
fn f23() {}
fn f24() {}
fn f25() {}
fn f26() {}
fn f27() {}
fn f28() {}
fn f29() {}
fn f30() {}
fn f31() {}
fn f32() {}
fn f33() {}
fn f34() {}
fn f35() {}
fn f36() {}
fn f37() {}
fn f38() {}
fn f39() {}
fn f40() {}
fn f41() {}
fn f42() {}
fn f43() {}
fn f44() {}
fn f45() {}
fn f46() {}
fn f47() {}
fn f48() {}
fn f49() {}
fn f50() {}
fn f51() {}
fn f52() {}
fn f53() {}
fn f54() {}
fn f55() {}
fn f56() {}
fn f57() {}
fn f58() {}
fn f59() {}
fn f60() {}
fn f61() {}
fn f62() {}
fn f63() {}
#[derive(PartialEq)]
struct V(u8);
impl PartialOrd for V {
    fn partial_cmp(&self, o: &V) -> Option<std::cmp::Ordering> { self.0.partial_cmp(&o.0) }
}
