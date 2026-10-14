// expect: L0306
// Valid Rust: an impl whose own where-clause names a lifetime trait
// (`impl<'a, T: Tr<'a>> Tr<'a> for Wrap<T>`) is replayed conservatively as
// `'static` (no recursive replay yet), so a free inner impl still rejects.
trait Tr<'a> { fn put(&mut self, x: &'a u8); }
struct Count(usize);
impl<'a> Tr<'a> for Count { fn put(&mut self, _x: &'a u8) { self.0 += 1; } }
struct Wrap<T>(T);
impl<'a, T: Tr<'a>> Tr<'a> for Wrap<T> { fn put(&mut self, x: &'a u8) { self.0.put(x); } }
fn feed<'d, V: Tr<'d>>(w: &mut V, x: &'d u8) { w.put(x); }
fn main() { let mut w = Wrap(Count(0)); let l = 5u8; feed(&mut w, &l); println!("{}", (w.0).0); }
