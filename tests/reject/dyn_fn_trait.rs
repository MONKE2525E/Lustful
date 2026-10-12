// expect: L0702
// ARCH 2.8: `dyn Fn` comes with closures; a std trait has no vtable yet.
fn apply(f: &dyn Fn(u8) -> u8) -> u8 {
    f(2)
}
fn double(x: u8) -> u8 {
    x * 2
}
fn main() {
    println!("{}", apply(&double));
}
