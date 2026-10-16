// expect: L0203
// rustc E0597: `&n as R` needs `n` to live for `'static`. lust cannot keep the alias's
// `'static` in a cast target, so it rejects as it does a written `&'static` there.
type R = &'static u32;
fn main() {
    let n = 5u32;
    let x = &n as R;
    println!("{}", x);
}
