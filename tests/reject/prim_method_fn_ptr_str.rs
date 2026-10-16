// expect: L0110
// Valid Rust (prints 2): a `str` builtin method as a fn pointer. Only an
// integer type's builtin methods have a codegen fn yet (their panic site is
// known: core's `int_impl!` line).
fn main() {
    let f: fn(&str) -> usize = str::len;
    println!("{}", f("ab"));
}
