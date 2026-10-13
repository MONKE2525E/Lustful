// expect: L0203
// Valid Rust: `T: 'a` bounds on named lifetimes are not supported yet (W-BORROW).
fn keep<'a, T: 'a>(r: &'a T) -> &'a T {
    r
}

fn main() {
    let x = 5;
    println!("{}", keep(&x));
}
