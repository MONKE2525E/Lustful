// An allocation failure aborts with std's alloc error hook text: the size
// line, then the RUST_BACKTRACE note (hunt7 05:15).
fn main() {
    println!("start");
    let b = Box::<[u8]>::new_uninit_slice(usize::MAX / 2);
    println!("len={}", b.len());
}
