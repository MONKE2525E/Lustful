// expect: L0602
// A raw pointer to an unsized pointee is a fat pointer in Rust;
// lust's raw pointers are thin addresses, so the type rejects.
fn main() {
    let s = "hi";
    let p: *const str = s;
    println!("{}", !p.is_null());
}
