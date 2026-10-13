// expect: L0203
// rustc E0597. Lust does not keep regions of body annotations yet, so an
// explicit `'static` in one is rejected (see tests/reject/body_static_annotation.rs).
fn main() {
    let r: &'static str;
    {
        let s = String::from("hi");
        r = &s;
    }
    println!("{}", r);
}
