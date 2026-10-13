// panic: split index should be <= len
fn main() {
    let mut v = vec![1, 2, 3];
    println!("before");
    let _t = v.split_off(9);
    println!("unreachable");
}
