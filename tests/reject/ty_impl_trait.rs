// expect: L0112
fn show(x: impl std::fmt::Display) {
    println!("{}", x);
}

fn main() {
    show(3);
}
