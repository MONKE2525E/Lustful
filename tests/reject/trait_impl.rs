// expect: L0614
struct S;

impl std::fmt::Display for S {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "S")
    }
}

fn main() {
    println!("{}", S);
}
