// expect: L0203
// Valid Rust: lifetime params on traits are not supported yet (W-BORROW).
trait Source<'a> {
    fn get(&self) -> &'a str;
}

struct S;

impl Source<'static> for S {
    fn get(&self) -> &'static str {
        "s"
    }
}

fn main() {
    println!("{}", S.get());
}
