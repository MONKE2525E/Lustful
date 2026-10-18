// capability: attributes: test, ignore, should_panic (`lust test` runs top-level #[test] fns, not ones inside a module)
// expect: ok
// command: test

#[test]
fn adds() {
    assert_eq!(1 + 1, 2);
}

#[test]
#[ignore]
fn slow() {
    panic!("ignored tests do not run");
}

#[test]
#[should_panic(expected = "boom")]
fn panics() {
    panic!("boom");
}

fn main() {}
