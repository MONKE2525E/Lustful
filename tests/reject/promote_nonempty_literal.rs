// expect: L0307
// Valid Rust: rustc promotes `&[1, 2]` to `'static`; lust promotes only
// `&[]` and `&mut []` so far (no static storage for other constants yet).
fn f() -> &'static [u8] {
    &[1, 2]
}
fn main() {
    println!("{}", f().len());
}
