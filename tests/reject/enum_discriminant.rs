// expect: L0632
enum E {
    A = 1,
    B,
}

fn main() {
    let _e = E::A;
    println!("hi");
}
