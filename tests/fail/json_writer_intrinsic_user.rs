// expect: L0642
fn main() {
    let mut out = String::new();
    core::intrinsics::json_fmt_f64(&mut out, 1.0);
}
