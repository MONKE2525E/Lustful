// expect: L0602
fn is_null(p: *const i64) -> bool {
    p.is_null()
}

fn main() {
    println!("{}", is_null(std::ptr::null()));
}
