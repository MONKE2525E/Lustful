// capability: rejected: #[test] functions inside impl blocks (in `lust test`; rustc rejects them too)
// expect: L0402
// command: test

struct S;

impl S {
    #[test]
    fn t() {}
}

fn main() {}
