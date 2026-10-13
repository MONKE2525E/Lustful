// expect: L0102
// Valid Rust: the borrowing iterator types (slice::Iter<'a, T>) carry a
// lifetime the region signatures do not model yet.
fn first<'a>(v: &'a [u32]) -> std::slice::Iter<'a, u32> {
    v.iter()
}

fn main() {
    println!("{:?}", first(&[1, 2]).next());
}
