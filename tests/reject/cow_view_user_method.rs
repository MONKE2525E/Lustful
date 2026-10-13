// expect: L0640
// Valid Rust: a user trait method of `str` called on a Cow<str> through
// its Deref (lust resolves only B's builtin methods through the view).
use std::borrow::Cow;

trait Twice {
    fn twice(&self) -> usize;
}
impl Twice for str {
    fn twice(&self) -> usize {
        self.len() * 2
    }
}

fn main() {
    let c: Cow<str> = Cow::Borrowed("ab");
    println!("{}", c.twice());
}
