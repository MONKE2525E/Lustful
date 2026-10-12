// expect: L0820
fn main() {
    fn inner() -> i64 {
        1
    }
    println!("{}", inner());
}
