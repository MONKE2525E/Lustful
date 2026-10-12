// expect: L0820
fn main() {
    let v = 3;
    let f = || v + 1;
    println!("{}", f());
}
