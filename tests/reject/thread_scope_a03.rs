// expect: L0733
use std::thread;
fn main() {
    let v = vec![5, 6];
    let r = thread::scope(|s| s.spawn(|| &v[0]).join().unwrap());
    println!("{}", r);
}
