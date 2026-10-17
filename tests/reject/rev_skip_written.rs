// expect: L0641
// Valid Rust: `Skip<slice::Iter<u8>>` is double-ended (its inner iterator is exact-size and
// double-ended). lust keeps `Skip` forward-only, so a written `Rev` over it is a reject.
fn f(x: std::iter::Rev<std::iter::Skip<std::slice::Iter<'static, u8>>>) -> usize {
    x.count()
}
fn main() {
    let v: &'static [u8] = &[1, 2, 3];
    println!("{}", f(v.iter().skip(1).rev()));
}
