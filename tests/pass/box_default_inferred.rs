// Box::default() with an inferred T (ts-rust ast/store.rs:3316 Box::leak(Box::default())).
#[derive(Default, Debug)]
struct S { a: u8, v: Vec<u8> }
fn get(o: Option<&'static mut S>) -> &'static mut S { o.unwrap_or_else(|| Box::leak(Box::default())) }
fn main() {
    let b: Box<S> = Box::default();
    let c = Box::<u32>::default();
    let s = get(None);
    s.a = 3;
    println!("{:?} {} {:?}", b, c, s);
}
