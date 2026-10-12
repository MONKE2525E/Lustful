// expect: L0820
fn main() {
    let Some(x) = Some(3) else {
        return;
    };
    println!("{}", x);
}
