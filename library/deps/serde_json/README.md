# serde_json 1.0.151 adapter

This adapter implements a closed owned Value reader and writer. Parsed floats
use the dedicated `json_fmt_f64` intrinsic for upstream default compact output.
The private `float_format` module is the only adapter call site; ordinary user
crates cannot call the intrinsic.

The owned read surface is `from_str::<Value>`, `from_slice::<Value>`,
and string-key `Value::get`. Inferred Value results work too. The owned decode
bound is sealed and has only a Value implementation; it is not a Serde trait.
The reader validates the complete document, JSON escapes, UTF-8, UTF-16
surrogate pairs, and the default upstream recursion limit. Object keys sort
lexicographically and duplicate keys retain the last value.

Number retains integer storage through the upstream ranges. Parsed decimals,
exponents, negative zero, and overflowed integers use finite f64 storage and
the upstream default numeric algorithm, not std float parsing. Integer writers
remain exact; parsed floats and Number Display/Debug use the private formatter.
No public float constructor or float JsonInput conversion is added.

The existing construction surface remains `json!`, `to_value`, and `to_string`
for booleans, strings, the ten integer types through 64 bits, and existing
Values. Containers are shared references, slices, arrays of length 0 through
32, Vec, Option, and Map<String, Value>, with supported contents.

Typed Serde conversion, custom serializers, borrowed decode outputs, 128-bit
integer inputs, indexing, pretty output, and unsupported features remain
outside the adapter. The admitted feature names stay default/std/alloc;
alloc alone does not establish freestanding no_std support. This adapter
does not establish support for Verenu's full JSON use or native application.

The source differential runner is `scripts/test-json-source-adapter.sh`.
Numeric output has a separate million-pattern comparison in `tests/float/json.sh`;
registry admission and daemon invalidation use `scripts/test-normal-graphs.sh`.
`scripts/test-json-production.mjs` compares unchanged Verenu model-list parser
bodies with an independently captured upstream oracle. Its target mode requires
an execution and network audit. Oracle Rust artifacts stay outside guarded Lust
execution. These checks do not establish full desktop support.
