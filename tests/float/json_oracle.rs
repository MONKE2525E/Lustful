use std::io::{self, BufRead, Write};
fn main() {
    let input = io::stdin();
    let mut output = io::BufWriter::new(io::stdout().lock());
    let mut buffer = zmij::Buffer::new();
    for line in input.lock().lines() {
        let bits = u64::from_str_radix(&line.unwrap(), 16).unwrap();
        let value = f64::from_bits(bits);
        assert!(value.is_finite());
        writeln!(output, "{:016x}\t{}", bits, buffer.format_finite(value)).unwrap();
    }
}
