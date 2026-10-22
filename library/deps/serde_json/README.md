# serde_json 1.0.151 adapter

This adapter supports integer-only `Value` construction and compact JSON output
in programs that use `std`. The supported feature names are `default`, `std`,
and `alloc`. Enabling `alloc` alone does not establish freestanding `no_std`
support.

`json!`, `to_value`, and `to_string` accept booleans, strings, the ten integer
types through 64 bits, and existing `Value` objects. Supported containers are
shared references, slices, arrays of length 0 through 32, `Vec`, `Option`, and
`Map<String, Value>`, with supported contents. Object keys sort lexicographically.
The conversion trait is sealed.

Parsing, typed Serde conversion, custom serializers, floating-point numbers,
128-bit integers, indexing, pretty output, and `raw_value` are unsupported.
Unsupported inputs fail compilation. This adapter does not claim upstream
layout compatibility or support for Verenu's complete JSON use.

Run the source comparison from the repository root:

```sh
LUST="$PWD/target/release/lust" JSON_TRACE=1 SANITIZE=1 bash scripts/test-json-source-adapter.sh
```

The runner compares output with upstream 1.0.151, checks unsupported inputs, and
runs generated C under ASan and UBSan. Rust compiles the independent upstream
oracle before the guarded Lust phase. Registry admission and daemon checks live
in `scripts/test-normal-graphs.sh`.
