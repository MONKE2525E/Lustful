// expect: L0602
// rustc E0382: an impl Trait value is not Copy unless its bounds say so; lust rejects a Copy hidden type there (W-CHECK-G3).
fn make() -> impl std::fmt::Display { 5u8 }
fn main() { let a = make(); let b = a; println!("{} {}", a, b); }
