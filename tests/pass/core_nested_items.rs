fn outer() -> i64 {
    fn double_it(x: i64) -> i64 {
        x * 2
    }
    fn plus_one(x: i64) -> i64 {
        double_it(x) + 1
    }
    const FACTOR: i64 = 10;
    static LABEL: &str = "nested";
    println!("{}", LABEL);
    plus_one(20) + FACTOR
}

fn shadow() -> i64 {
    const V: i64 = 1;
    let a = V;
    {
        const V: i64 = 2;
        a + V
    }
}

fn main() {
    println!("{}", outer());
    println!("{}", shadow());
    fn local(x: i64) -> i64 {
        x + 100
    }
    println!("{}", local(5));
    let r = {
        fn inner() -> i64 {
            7
        }
        inner()
    };
    println!("{}", r);
    match 41 {
        LIMIT => println!("under"),
        _ => println!("over"),
    }
}

const LIMIT: i64 = 42;
