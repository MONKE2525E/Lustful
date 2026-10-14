// expect: L0104
// Option::as_slice is stable (1.75) but not in lust's std source yet.
fn main() {
    let a = Some(3);
    println!("{:?}", a.as_slice());
}
