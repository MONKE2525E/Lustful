// expect: L0820
// The closure's reference cannot leave `with` (rustc: lifetime may not
// live long enough); lust rejects reference-returning closures.
thread_local! {
    static S: Vec<i32> = Vec::new();
}
fn main() {
    let r: &Vec<i32> = S.with(|v| v);
    println!("{}", r.len());
}
