// expect: L0110
// Valid Rust: a constructor coerces to a fn pointer. Lust has no
// pointer form for constructors yet (user or builtin).
fn main() {
    let f: fn(u32) -> Option<u32> = Some;
    println!("{:?}", f(1));
}
