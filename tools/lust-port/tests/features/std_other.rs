// feature: std.other
// form: a std path with no precise rule yet, std::net address types
use std::net::Ipv4Addr;
fn main() {
    let a = Ipv4Addr::new(127, 0, 0, 1);
    println!("{} {}", a.is_loopback(), a.octets()[0]);
}
