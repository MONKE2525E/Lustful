// expect: L0630
// rustc E0277: `String: Copy` does not hold. The const evaluator has no
// trait solver, so a bounded generic const fn call is outside it.
struct W<T>(Option<T>);
impl<T: Copy> W<T> {
    const fn mk() -> W<T> {
        W(None)
    }
}
static S: W<String> = W::mk();
fn main() {
    println!("{}", S.0.is_none());
}
