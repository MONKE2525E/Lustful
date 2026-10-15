// Lust adapter for flate2 1.1.10 (docs/ARCH.md section 3.6):
// the read side only. `read::GzDecoder`, `read::MultiGzDecoder`,
// `read::ZlibDecoder`, and `read::DeflateDecoder` decode with
// a pure-Rust inflate in this crate, with flate2's error kinds
// and messages for the corrupt forms. Encoding is not here:
// a byte-exact copy of miniz_oxide's compressor is not a small
// adapter, so `write` and `bufread` and the encoder types are
// absent and such code rejects in lust (README). Decoding is
// canonical, so every valid stream gives upstream's bytes.
//
// The first read pulls the whole input through (the decoders
// ts-rust feeds are byte slices); a decode error still returns
// the bytes decoded before it first, as upstream's streaming
// decoder does at read_to_end.

pub mod read;

mod inflate;

/// Compression level (the read side has no use for it, but the
/// type is part of the crate surface ts-rust names).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Compression(u32);

impl Compression {
    /// A level from 0 (none) to 9 (best); values above 9 clamp
    /// in upstream to 9 through its backend, kept raw here as
    /// upstream's own field does.
    pub const fn new(level: u32) -> Compression {
        Compression(level)
    }

    /// No compression (level 0).
    pub const fn none() -> Compression {
        Compression(0)
    }

    /// Fast compression (level 1).
    pub const fn fast() -> Compression {
        Compression(1)
    }

    /// Best compression (level 9).
    pub const fn best() -> Compression {
        Compression(9)
    }

    /// The level number.
    pub const fn level(self) -> u32 {
        self.0
    }
}

/// The io error of one corrupt-input kind, with flate2's text.
fn invalid(msg: &'static str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidInput, msg)
}

/// flate2's truncated-stream error.
fn eof_err() -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "unexpected end of file")
}

/// IEEE CRC32 of `data`, table-driven.
fn crc32(data: &[u8], start: u32) -> u32 {
    let mut table = [0u32; 256];
    for i in 0..256u32 {
        let mut c = i;
        for _ in 0..8 {
            c = if c & 1 != 0 { 0xedb88320 ^ (c >> 1) } else { c >> 1 };
        }
        table[i as usize] = c;
    }
    let mut crc = !start;
    for &b in data {
        crc = table[((crc ^ b as u32) & 0xff) as usize] ^ (crc >> 8);
    }
    !crc
}

/// Adler-32 of `data` continuing from `start`.
fn adler32(data: &[u8], start: u32) -> u32 {
    let mut a = start & 0xffff;
    let mut b = (start >> 16) & 0xffff;
    for &x in data {
        a = (a + x as u32) % 65521;
        b = (b + a) % 65521;
    }
    (b << 16) | a
}
