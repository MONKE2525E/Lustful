# Diagnostic code registry

This file is the checked list of all `L####` diagnostic codes. It makes the
ranges in `docs/ARCH.md` Appendix A enforceable. `scripts/check-codes.sh`
reads the table below and fails when:

- a code in `src/` is not in this registry, or is still marked `reserved`;
- a code marked `in use` is not emitted in `src/`, has no page in this
  directory, or has no row in `src/explain.rs`;
- a code falls outside every range in this table (new codes must take a
  reserved range first, then flip to `in use` when first emitted);
- two rows claim the same code or overlapping ranges.

Rules for a new code:

1. Pick the next free code inside the reserved range for your area. If no
   range fits, add a new reserved row first (free space starts at L05xx;
   never reuse a code, and never renumber).
2. In the same change: emit the code, add its page `L####.md`, add its row
   to `src/explain.rs` and to the index in `README.md`, and flip or split
   the registry row so the code is `in use`.
3. Run `scripts/check-codes.sh` and `scripts/check-explain.sh`.

Status is `in use` (the compiler emits every code in the range today) or
`reserved` (planned, not yet emitted). `lust explain` reads this file: it
lists the in-use codes and the reserved ranges, and for a reserved code it
prints "reserved, not yet emitted".

| Code or range | Area | Owner | Status | Notes |
|---|---|---|---|---|
| L0001 | Syntax | lexer, parser | in use | |
| L0101-L0107 | Names, types, fields, methods, arity, duplicates | check, collect | in use | |
| L0110-L0119 | Type mismatch, inference, traits, operators, casts, literals | check, collect | in use | |
| L0120-L0122 | Break/continue, assignment target, `mut` under a reference | check | in use | |
| L0130 | No `main` function | driver | in use | |
| L0201-L0203 | References in fields, lifetime elision and syntax | collect, parser | in use | |
| L0301-L0312 | Borrow checker: moves, borrows, value lifetimes | borrowck | in use | |
| L0401-L0405 | User macros, attributes, derives, `unsafe`, `async` | parser, collect | in use | |
| L0501-L0509 | Modules and imports | W-RESOLVE | reserved | L0501 import cycle, L0502 ambiguous module file, L0503 module file not found, L0504 generated name changes an earlier resolution |
| L0510-L0519 | Visibility | W-RESOLVE | reserved | |
| L0520-L0529 | cfg and attributes | W-MACRO | reserved | L0520 unknown cfg name, L0521 unknown attribute |
| L0530-L0539 | Crate session | W-DRIVER | reserved | L0530 unsupported edition, L0531 unsupported deny-level lint |
| L0601-L0609 | Types and aliases | W-CORELANG | reserved | L0601 alias cycle |
| L0610-L0619 | Traits and inference | W-TRAITS-CORE | reserved | L0610 annotations needed, L0611 selection overflow, L0612 no impl, L0613 impl parameter not known, L0615 overlapping impls |
| L0620-L0629 | Associated items | W-TRAITS-CORE | reserved | L0620 GAT |
| L0630-L0639 | Const eval | W-CORELANG | reserved | L0630 outside the bounded evaluator, L0631 non-const call in a const context |
| L0640-L0649 | Std surface | W-STD | reserved | L0640 std item declared but not yet implemented |
| L0650-L0659 | Layout | W-CORELANG | reserved | L0650 `offset_of!` on a default-repr type, L0651 reference to a packed field, L0652 unsupported layout form |
| L0701-L0709 | dyn compatibility | W-TRAITS-CORE | reserved | L0701 not dyn compatible (name the offending item) |
| L0710-L0719 | Binders | W-TRAITS-CORE | reserved | L0710 nested higher-ranked binder |
| L0720-L0729 | Methods and receivers | W-TRAITS-CORE | reserved | L0720 ambiguous method, L0722 unsupported receiver type; plain "no such method" stays L0104 |
| L0730-L0739 | Regions and drop check | W-BORROW | reserved | L0730 drop check, L0731 explicit lifetime turbofish arg, L0732 placeholder region escapes |
| L0801-L0809 | Macros | W-MACRO | reserved | L0801 expansion caps, L0802 unknown macro, L0803 include file not found, L0804 proc-macro dependency, L0805 local ambiguity |
| L0810-L0819 | Foreign and shim boundary | W-SHIM | reserved | |
| L9001 | Feature not supported yet | all | in use | Do not add new L9001 sites for planned features; use the ranges above |
