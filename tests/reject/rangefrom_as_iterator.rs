// expect: L0104
// RangeFrom is a RangeBounds value here, not yet an iterator
// (std's Step-based iterator over the open range is not modeled).
fn main() {
    let c: Vec<usize> = (1usize..).take(3).collect();
    println!("{c:?}");
}
