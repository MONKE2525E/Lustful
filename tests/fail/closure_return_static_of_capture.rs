// expect: L0733
// rustc: the closure returns a borrow of its capture as `&'static str`.

fn main() {
    let local = String::from("l");
    let get = || -> &'static str { local.as_str() };
    println!("{}", get());
}
