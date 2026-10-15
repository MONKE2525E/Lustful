// expect: L0104
// Socket read and write timeouts are not implemented yet.
use std::net::TcpStream;
use std::time::Duration;
fn main() {
    if let Ok(s) = TcpStream::connect("127.0.0.1:9") {
        let _ = s.set_read_timeout(Some(Duration::from_secs(1)));
    }
    println!("x");
}
