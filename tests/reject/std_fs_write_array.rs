// expect: L0612
// lust has no `[u8; N]: AsRef<[u8]>` impl yet, so a byte string literal
// cannot be fs::write contents (rustc accepts it). `&b"x"[..]` works.
fn main() {
    let dir = std::env::temp_dir().join(format!("lust_reject_{}", std::process::id()));
    let _ = std::fs::write(dir, b"x");
}
