// Deep recursion: Rust's guard-page handler prints its stack overflow
// text and aborts (134); the held partial line is lost.
// panic: has overflowed its stack
fn depth(n: u64) -> u64 {
    if n == 0 { 0 } else { 1 + depth(n - 1) + n % 3 }
}
fn main() {
    print!("partial ");
    println!("line");
    print!("held");
    let n = std::env::args().count() as u64;
    println!("{}", depth(n * 100_000_000));
}
