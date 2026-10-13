// expect: L0820
fn main() {
    let s = String::from("borrowed");
    let get = || &s;
    println!("{}", get());
}
