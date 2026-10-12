// expect: L0820
fn get() -> Option<i64> {
    let x = Some(3)?;
    Some(x + 1)
}

fn main() {
    println!("{}", get().unwrap());
}
