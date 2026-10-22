// expect: L0531
// Native calls enable unsafe syntax; lint scopes are not implemented yet.
#![forbid(unsafe_code)]

fn main() {
    println!("hi");
}
