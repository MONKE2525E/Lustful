// expect: L0702
// Valid Rust: a `&dyn Fn` as `Iterator::map`'s callable. lust's adapter
// expansion calls closures, fn items, and fn pointers only.
fn main() { let r: &dyn Fn(i32) -> i32 = &|x| x + 1; let v: Vec<i32> = vec![1, 2].into_iter().map(r).collect(); println!("{:?}", v); }
