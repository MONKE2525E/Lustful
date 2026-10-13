// expect: L0401
// An `fmt::Arguments` value outside write_fmt has no expanded form yet.
fn main() {
    let a = format_args!("x");
    println!("{}", a);
}
