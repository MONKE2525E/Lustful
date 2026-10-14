// expect: L0630
// A static inside a fn body: its std source type resolves (fz-resolve
// block scoping), but a LazyLock init there does not become a hidden
// init fn yet, so the const evaluator rejects it. rustc accepts this.
fn main() {
    static L: std::sync::LazyLock<u8> = std::sync::LazyLock::new(|| 3);
    println!("{}", *L);
}
