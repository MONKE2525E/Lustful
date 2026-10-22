unsafe extern "C" {
    fn srand(seed: u32);
    fn rand() -> i32;
    fn umask(mask: u32) -> u32;
}
fn combine(a: i32, b: i32, c: i32) -> (i32, i32, i32) { (a, b, c) }
fn seed() { unsafe { srand(91) } }
fn main() {
    seed();
    let expected = unsafe { (rand(), rand(), rand()) };
    seed();
    let actual = unsafe { combine(rand(), rand(), rand()) };
    assert_eq!(actual, expected);
    unsafe {
        let previous = umask(0o077);
        assert_eq!(umask(previous), 0o077);
    }
    println!("{actual:?}");
}
