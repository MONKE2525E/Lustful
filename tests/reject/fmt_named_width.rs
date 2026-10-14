// expect: L0641
// Valid Rust: a width or precision read from a named argument (`w$`,
// `p$`, captured from scope as in rustc). lust has only literal widths
// and precisions, so this is "not supported yet", not a syntax error.
fn main() {
    let w = 6;
    let p = 2;
    println!("[{:>w$}]", 42);
    println!("[{:.p$}]", 1.23456);
    println!("[{:>width$.prec$}]", 2.5, width = 8, prec = 1);
}
