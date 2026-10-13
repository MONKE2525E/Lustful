// Return-position `impl Trait` definitions: the hidden type must meet
// the bounds; callers that only define and check are fine (using the
// value is a later step).
struct Bag {
    v: Vec<u32>,
}

impl Bag {
    fn doubled(&self) -> impl Iterator<Item = u32> {
        self.v.clone().into_iter().map(|x| x * 2)
    }
    fn total(&self) -> u32 {
        self.v.iter().sum()
    }
}

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

fn count_up(n: u32) -> impl Iterator<Item = u32> {
    0..n
}

fn shown() -> impl std::fmt::Display {
    5
}

fn adder() -> impl Fn(u8) -> u8 {
    |x| x + 1
}

fn main() {
    let b = Bag { v: vec![1, 2, 3, 4] };
    let m = M { entries: vec![(1u8, 'a')] };
    println!("{} {}", b.total(), m.len());
}
