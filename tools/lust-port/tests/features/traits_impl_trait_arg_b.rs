// feature: traits.impl_trait_arg
// form: fn arg as impl Iterator with an item binding
fn total(it: impl Iterator<Item = i32>) -> i32 { it.sum() }
fn main() { println!("{}", total([1, 2, 3].into_iter())); }
