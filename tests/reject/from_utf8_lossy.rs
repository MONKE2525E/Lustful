// expect: L0640
fn main() {
    let v = vec![104, 0xff];
    println!("{}", String::from_utf8_lossy(&v));
}
