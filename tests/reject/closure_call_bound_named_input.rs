// expect: L0203
// Valid Rust that lust rejects on purpose: inside a closure, a call through
// an `Fn` bound whose argument names a lifetime of the enclosing fn (`'a`)
// is a stated cut (the closure body cannot name `'a`).
fn show(v: &u8) {
    println!("{}", v);
}

fn each<'a, P: Fn(&'a u8)>(x: &'a u8, p: &P) {
    let f = || p(x);
    f()
}

fn main() {
    let k = 1u8;
    each(&k, &show);
}
