// expect: L0641
// A fn item as dedup_by's callable: valid Rust, lust takes closures only here.
fn same(a: &mut i32, b: &mut i32) -> bool { a == b }
fn main() { let mut v = vec![1, 1, 2]; v.dedup_by(same); println!("{v:?}"); }
