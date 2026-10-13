// expect: L0820
// An impl inside a fn body is valid Rust. Lust rejects type items in
// bodies on purpose. Regression (fuzz realish seed 1, iters 358/477):
// the token scan counts the nested method, the Ast fn list does not,
// and slot_update indexed past the Ast list and panicked.
struct S;
fn outer() {
fn inner() {
}
impl S {
    fn m(&self) {
    }
}
}
fn main() { outer(); }
