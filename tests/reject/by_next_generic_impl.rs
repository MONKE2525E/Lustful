// expect: L0640
// Valid Rust: adapters over a user iterator whose Iterator impl is
// generic (lust calls only non-generic `next` impls so far).
struct G<T>(Vec<T>);

impl<T> Iterator for G<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        self.0.pop()
    }
}

fn main() {
    let v: Vec<i32> = G(vec![1, 2]).map(|x| x * 2).collect();
    println!("{v:?}");
}
