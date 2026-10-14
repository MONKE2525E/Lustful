// expect: L0702
// Valid Rust: `Some` at a generic `F: Fn(T) -> R` bound with a borrowed
// input. Borrowck does not relate a fn item's signature at such a bound
// yet, so a builtin item with a borrowing input there is a reject.
fn keep<T, R, F: Fn(T) -> R>(f: F, x: T) -> R {
    f(x)
}
fn main() {
    let data = vec![1u8, 2];
    let o = keep(Some, &data[0]);
    println!("{:?}", o);
}
