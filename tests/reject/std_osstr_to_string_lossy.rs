// expect: L0104
// to_string_lossy returns Cow<str>; lust has no Cow yet (W-STD-B).
use std::ffi::OsStr;
fn main() {
    println!("{}", OsStr::new("a").to_string_lossy());
}
