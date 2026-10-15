// `std::alloc` overlay (docs/ARCH.md section 3.1): only `System`
// today. `std::alloc::X` walks into this module only for the names
// it defines (`STD_MODULES` in src/stdmods.rs); `Layout` and
// `GlobalAlloc` stay compiler-rejected paths, as before.
//
// A `#[global_allocator]` static of this type is accepted and the
// lust runtime keeps its own allocator: allocation strategy does
// not change a program's output or exit code. Collect enforces
// the known-allocator rule (check/collect.rs).

/// The system allocator. Zero-sized, as in std.
#[derive(Copy, Clone, Default, Debug)]
pub struct System;
