# log 0.4.34 adapter

This source adapter implements logging through `Log`, with one-time global
registration, runtime level filtering, lazy arguments, record builders, and
call-site metadata. The five level macros and `log!` support global and explicit
loggers and targets. `log_enabled!` calls the selected logger's `enabled` method.

The adapter accepts the `alloc` and `std` features. Other features, including
`kv`, `serde`, and compile-time level caps, fail the existing adapter feature
check. `STATIC_MAX_LEVEL` is `Trace` for the accepted feature sets. Layout queries
on adapter types remain unsupported.

The public API is a subset of upstream. Missing APIs include boxed logger
registration, racy registration and filter setters, level parsing and iteration,
and `Log` implementations for `Box` and `Arc`. Those uses fail to compile.
`Record::to_builder` is absent, as in upstream with `kv` disabled. Key-value
macro syntax fails to compile here; upstream without `kv` can accept that syntax
and panic when the log is enabled. The adapter makes no type layout guarantee.

The corpus compares actual records and side effects against the registry crate:

```sh
LUST=./target/release/lust LUST_STRICT=1 bash scripts/test-adapters.sh log
```

The corpus includes concurrent registration, source locations, filter side
effects, repeated formatting, and explicit rejection of unsupported features
and layout queries. rustc builds the oracle. Lust builds the comparison programs.
This adapter does not make the Verenu desktop build without rustc.
