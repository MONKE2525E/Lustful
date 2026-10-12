// expect: L0702
fn show(x: &dyn std::fmt::Display) {
    println!("{}", x);
}

fn main() {
    show(&3);
}
