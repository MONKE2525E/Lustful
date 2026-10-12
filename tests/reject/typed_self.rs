// expect: L0721
struct S;

impl S {
    fn get(self: Box<Self>) -> i64 {
        1
    }
}

fn main() {
    let b = Box::new(S);
    println!("{}", b.get());
}
