// expect: L0203
// Valid Rust: a higher-ranked where clause on a type (`for<'a> &'a T:
// IntoIterator`) is not supported yet (W-BORROW3).
fn count<T>(t: &T) -> usize where for<'a> &'a T: IntoIterator { t.into_iter().count() }
fn main() { println!("{}", count(&vec![1, 2])); }
