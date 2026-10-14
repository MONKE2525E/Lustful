// expect: L0101
// Valid Rust. The socket types are W-SHIM's (system io); only the
// std::net address types are in lust std source (W-STD-C phase 2).
use std::net::TcpListener;
fn main() {
    let l = TcpListener::bind("127.0.0.1:0").unwrap();
    println!("{}", l.local_addr().unwrap().port() > 0);
}
