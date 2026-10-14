// expect: L0102
// A static inside a fn body does not see std source types yet (block
// item types resolve without the std module walk; fz-resolve block
// scoping). rustc accepts this.
fn main() {
    static L: std::sync::LazyLock<u8> = std::sync::LazyLock::new(|| 3);
    println!("{}", *L);
}
