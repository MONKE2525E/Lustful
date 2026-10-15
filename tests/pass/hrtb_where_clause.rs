fn f<T>(x: T) -> usize where for<'a> &'a T: IntoIterator { (&x).into_iter().count() }
fn main() { println!("{}", f(vec![1u8, 2])); }
