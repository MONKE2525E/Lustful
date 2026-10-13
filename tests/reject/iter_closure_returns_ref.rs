// expect: L0733
// rustc accepts: `map`'s closure argument is free (the iterator's items);
// lust treats closure arguments as higher-ranked, so returning a borrow of
// one is L0733.
fn main() {
    let v = vec![String::from("a")];
    let s: Vec<&str> = v.iter().map(|s| s.as_str()).collect();
    println!("{:?}", s);
}
