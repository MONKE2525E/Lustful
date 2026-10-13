// expect: L0701
fn show(x: &dyn std::fmt::Display) {
    println!("{}", x);
}

fn main() {
    show(&3);
}
