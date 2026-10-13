// feature: ext.builtin_crates
// form: FxHashMap type and insert/get, as ts-rust writes it in most files
// oracle: lust-only
use rustc_hash::FxHashMap;
fn main() {
    let mut m: FxHashMap<String, i32> = FxHashMap::default();
    m.insert("a".to_string(), 1);
    println!("{}", m.get("a").copied().unwrap_or(0));
}
