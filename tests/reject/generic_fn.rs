// expect: L0614
fn id<T>(x: T) -> T {
    x
}

fn main() {
    println!("{}", id(3));
}
