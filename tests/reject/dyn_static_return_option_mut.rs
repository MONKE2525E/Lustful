// expect: L0705
// Valid Rust: `Some(d)` is a coercion site, so the object lifetime shortens. lust rejects a 'static use in a body whose return type holds `&mut dyn T` under `Option`.
trait T { fn read(&self) -> u32; }
struct S { n: u32 }
impl T for S { fn read(&self) -> u32 { self.n } }
impl dyn T { fn more_mut(&mut self) -> u32 { self.read() + 2 } }
fn f(x: &mut S) -> Option<&mut dyn T> { let d: &mut dyn T = x; d.more_mut(); Some(d) }
fn main() { let mut s = S { n: 1 }; println!("{}", f(&mut s).unwrap().read()); }
