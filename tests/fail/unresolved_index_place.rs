// expect: L9001
// `Vec::new` as a value reports in check (it reached lowering as an
// unresolved place before, L0310).
fn main() {
    let mut v = Vec::new+();
    println!("{}", v[0]);
}
