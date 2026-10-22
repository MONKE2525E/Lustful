// capability: rejected: extern blocks outside the supported scalar C subset
// expect: L0810

unsafe extern "C" {
    safe fn abs(x: i32) -> i32;
}

fn main() {
    println!("{}", abs(-3));
}
