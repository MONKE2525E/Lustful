use std::collections::BTreeMap;
use std::time::Duration;

pub fn step() -> Duration {
    Duration::from_millis(250)
}

pub fn counts(words: &[&str]) -> BTreeMap<String, usize> {
    let mut m = BTreeMap::new();
    for w in words {
        *m.entry(w.to_string()).or_insert(0) += 1;
    }
    m
}
