// panic: byte index out of bounds
fn main() {
    let mut s = "héllo".to_string();
    println!("pre");
    s.insert(9, 'x');
    println!("post");
}
