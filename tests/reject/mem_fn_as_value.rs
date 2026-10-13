// expect: L9001
fn main() {
    let f = std::mem::drop::<String>;
    f(String::from("x"));
    println!("ok");
}
