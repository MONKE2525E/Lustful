// expect: L0820
fn main() {
    let x = 'a: {
        break 'a 3;
    };
    println!("{}", x);
}
