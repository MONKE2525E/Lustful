use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::sync::LazyLock;

static WORDS: LazyLock<BTreeMap<String, usize>> = LazyLock::new(|| base::counts(&["b", "a", "b"]));

pub struct Meters<T>(pub f64, PhantomData<T>);

pub fn meters<T>(x: f64) -> Meters<T> {
    Meters(x, PhantomData)
}

pub fn words() -> &'static BTreeMap<String, usize> {
    &WORDS
}
