// expect: L0702
// Valid Rust (prints `7`): a thread's function as a `Box<dyn FnOnce>`.
// lust's thread start calls closures, fn items, and fn pointers only.
fn start<H>(mut c: impl FnMut(std::thread::Builder, Box<dyn FnOnce() -> i32 + Send>) -> std::io::Result<H>) -> H {
    c(std::thread::Builder::new(), Box::new(|| 7)).unwrap()
}
fn main() {
    let h = start(std::thread::Builder::spawn);
    println!("{}", h.join().unwrap());
}
