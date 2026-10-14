// expect: L0602
// A generic fn's `impl Trait` return keeps the opaque type in its body,
// which the borrow checker does not track yet (W-BORROW).
struct M<K, V> {
    entries: Vec<(K, V)>,
}

impl<K: Clone, V> M<K, V> {
    fn keys_owned(&self) -> impl Iterator<Item = K> {
        let ks: Vec<K> = self.entries.iter().map(|e| e.0.clone()).collect();
        ks.into_iter()
    }
    fn len(&self) -> usize {
        self.entries.len()
    }
}

fn main() {
    let m = M { entries: vec![(1u8, 'a')] };
    println!("{}", m.len());
}
