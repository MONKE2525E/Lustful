// expect: L0104
// Vec::splice waits: its replacement iterator is consumed lazily
// when the Splice drops, which the builtin iterator expansion
// cannot do yet.
fn main() {
    let mut v = vec![1, 2, 3];
    let r: Vec<i32> = v.splice(1..2, [9]).collect();
    println!("{r:?} {v:?}");
}
