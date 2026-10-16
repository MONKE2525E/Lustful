// lust-reject: L0102
// flate2 1.1.10 write side: no encoder in the adapter (README in
// library/deps/flate2). A byte-exact copy of the miniz_oxide
// compressor is not a small adapter, so this must stay a
// compile-time reject, never a different gzip stream. The real
// crate builds and runs it (the ts-rust pprof shape).
use std::io::Write;

fn main() {
    let mut out: Vec<u8> = Vec::new();
    {
        let mut zw = flate2::write::GzEncoder::new(&mut out, flate2::Compression::fast());
        zw.write_all(b"profile bytes").unwrap();
        zw.finish().unwrap();
    }
    println!("{} {}", out.len(), out[0]);
}
