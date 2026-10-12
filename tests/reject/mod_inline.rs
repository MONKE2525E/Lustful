// expect: L0505
mod inner {
    pub fn one() -> i64 {
        1
    }
}

fn main() {
    println!("{}", inner::one());
}
