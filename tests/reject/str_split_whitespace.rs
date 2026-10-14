// expect: L0104
// split_whitespace needs the str split iterator types, which lust does
// not have yet (W-STD owns them). The whitespace set it would use is
// already exact: see unicode_props_hash in tests/pass.
fn main() {
    for w in "a b".split_whitespace() {
        println!("{}", w);
    }
}
