// expect: L0104
// rustc E0599: `RangeInclusive` is not an `ExactSizeIterator`
// (its length can overflow `usize`), so it has no `len` method.
fn main() {
    let mut it = 2..=5;
    it.next();
    println!("{}", it.len());
}
