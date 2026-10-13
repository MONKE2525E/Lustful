// expect: L0602
// Using the value of a fn that returns `impl Trait` is not supported yet.
fn evens() -> impl Iterator<Item = u32> {
    vec![2u32, 4].into_iter()
}

fn main() {
    let s: u32 = evens().sum();
    println!("{}", s);
}
