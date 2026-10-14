// A generic alias as a value path prefix: args fresh or written.
struct S<T>(T);
impl<T: Copy> S<T> {
    fn make(t: T) -> Self {
        S(t)
    }
    fn get(&self) -> T {
        self.0
    }
}
enum E<T> {
    A(T),
    B,
}
#[derive(Default)]
struct D<K, V> {
    k: Vec<K>,
    v: Vec<V>,
}
type A<T> = S<T>;
type EA<T> = E<T>;
type FD<K> = D<K, u8>;
fn main() {
    let a = A::make(5u8);
    let b = A::<i64>::make(-2);
    let e = EA::A(3u16);
    let f: EA<u8> = EA::B;
    let d: FD<u32> = FD::default();
    let g = FD::<u16>::default();
    let n = match (e, f) {
        (E::A(x), E::B) => x,
        _ => 0,
    };
    println!("{} {} {} {} {}", a.get(), b.get(), n, d.k.len() + d.v.len(), g.k.len());
}
