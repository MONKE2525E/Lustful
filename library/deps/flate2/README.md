# Adapter: flate2 1.1.10

Lust adapter crate (docs/ARCH.md section 3.6) for the read
side ts-rust uses (diagnostics_loc.rs decodes locale data with
MultiGzDecoder). Gate: `scripts/test-adapters.sh flate2`.

## Implemented, same results as upstream

- `read::GzDecoder`, `read::MultiGzDecoder`,
  `read::ZlibDecoder`, and `read::DeflateDecoder` over a
  pure-Rust inflate in the adapter, including gzip header
  forms (extra field, name, comment, header CRC), the gzip
  CRC and size trailer checks, and the zlib Adler check.
  Error kinds and messages match upstream for bad headers,
  corrupt deflate streams, bad checksums, and truncation.
- `Compression` (the level type alone; no encoder takes it).
- A decode error returns the bytes decoded before it first,
  as upstream's streaming decoder does at `read_to_end`.

## Known differences

- The first read pulls the whole input through the decoder,
  where upstream streams. A reader that never ends (a live
  pipe fed slowly) blocks here where upstream would return
  the bytes decoded so far per read.

## Rejected (lust error, never a different answer)

- All encoding: the `write` and `bufread` modules and every
  encoder type. A byte-exact copy of the miniz_oxide
  compressor is not a small adapter; pprof.rs (the gzip
  writer user) stays blocked on this crate for that form.
- `bufread` decoders, `Decompress` and the low-level types,
  `Crc` and `GzBuilder` helpers, and layout queries.
