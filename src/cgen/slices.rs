// Slice and Vec methods of TRIAGE R4 (tf-small-a): `[u8]::eq_ignore_ascii_case`
// and `is_ascii`, `[T]::rotate_left`/`rotate_right` and `partition_point`,
// and `Vec::extend_from_within`, `dedup_by`, `dedup_by_key` (`resize_with`
// expands in lower/iter.rs, which calls any callable).
// Each follows core/alloc 1.99: the same closure calls in the same order,
// the same drops at the same moments, core's panics at core's sites, and
// the Vec growth of `reserve`.

use super::*;

/// `std_loc` file index of core/src/slice/mod.rs (runtime/panic.c
/// `lust_std_files`).
const SLICE_MOD_RS: u64 = 14;

impl FnGen<'_, '_> {
    /// The R4 builtins; None for any other call.
    pub(super) fn slices_builtin(&mut self, b: Builtin, ops: &[Operand], vals: &[String], tys: &[CTy]) -> Option<String> {
        use Builtin as B;
        let slice_like = |t: &CTy, val: &str| -> (CTy, String, String) {
            match t {
                CTy::Ref(inner) => match &**inner {
                    CTy::Vec(e) => ((**e).clone(), format!("(({}*){val}->ptr)", ctype(e)), format!("{val}->len")),
                    CTy::Slice(e) => ((**e).clone(), format!("{val}->ptr"), format!("{val}->len")),
                    CTy::Array(e, n) => ((**e).clone(), format!("{val}->v"), format!("((uint64_t){n})")),
                    _ => unreachable!(),
                },
                CTy::Slice(e) => ((**e).clone(), format!("{val}.ptr"), format!("{val}.len")),
                CTy::Array(e, n) => ((**e).clone(), format!("{val}.v"), format!("((uint64_t){n})")),
                _ => unreachable!(),
            }
        };
        let vec_elem = |t: &CTy| -> CTy {
            let CTy::Ref(v) = t else { unreachable!() };
            let CTy::Vec(e) = &**v else { unreachable!() };
            (**e).clone()
        };
        Some(match b {
            B::SliceEqIgnoreAsciiCase => {
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (_, optr, olen) = slice_like(&tys[1], &vals[1]);
                let t = self.tmp();
                let _ = writeln!(self.out, "    uint8_t {t} = lust_bytes_eq_ignore_ascii_case({ptr}, {len}, {optr}, {olen});");
                t
            }
            B::SliceIsAscii => {
                let (_, ptr, len) = slice_like(&tys[0], &vals[0]);
                let (t, i) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    uint8_t {t} = 1;\n    for (uint64_t {i} = 0; {i} < {len}; {i}++) if ({ptr}[{i}] >= 0x80) {{ {t} = 0; break; }}");
                t
            }
            B::SliceRotateLeft | B::SliceRotateRight => {
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let n = &vals[1];
                let (cond, line) = if b == B::SliceRotateLeft { ("mid <= self.len()", 3904) } else { ("k <= self.len()", 3950) };
                let at = std_loc(SLICE_MOD_RS, line, 9);
                let mid = if b == B::SliceRotateLeft { n.clone() } else { format!("{len} - {n}") };
                let _ = writeln!(
                    self.out,
                    "    if (!({n} <= {len})) lust_panic_cstr(\"assertion failed: {cond}\", {at});\n    lust_slice_rotate_left({ptr}, {len}, sizeof({}), {mid});",
                    ctype(&e)
                );
                "((lust_Unit){})".into()
            }
            B::SlicePartitionPoint => {
                // core: `binary_search_by(|x| if pred(x) { Less } else
                // { Greater }).unwrap_or_else(|i| i)`; the comparator
                // never answers Equal, so the search ends in Err(i).
                let (e, ptr, len) = slice_like(&tys[0], &vals[0]);
                let size = c_size_align(self.p, &e).0;
                let f = self.adapter_callee(&ops[1]);
                let adapter = self.partition_adapter(&e, &f);
                let (c, r) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                let _ = writeln!(self.out, "    int64_t {r} = lust_binary_search({ptr}, {len}, {size}, (void*)&{c}, {adapter});");
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    let _ = writeln!(self.out, "    drop_{}(&{c});", mangle(&tys[1]));
                }
                format!("((uint64_t)(-{r} - 1))")
            }
            B::VecExtendFromWithin => {
                // `slice::range` (core's index.rs panics), `reserve`,
                // then each element of the range cloned and pushed in
                // order (the length grows per element, as alloc's
                // `SetLenOnDrop` keeps it).
                let e = vec_elem(&tys[0]);
                let et = ctype(&e);
                let vv = &vals[0];
                let (s, en, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    uint64_t {s}, {en};\n    lust_range_check({vv}->len, {}, {}, {}, {}, &{s}, &{en});\n    lust_vec_reserve({vv}, {en} - {s}, sizeof({et}), _Alignof({et}));",
                    vals[1], vals[2], vals[3], vals[4]
                );
                let elem = format!("(({et}*){vv}->ptr)[{i}]");
                let val = if is_copy_c(self.p, &e) {
                    elem
                } else {
                    self.want(Glue::Clone, &e);
                    format!("clone_{}(&{elem})", mangle(&e))
                };
                let _ = writeln!(self.out, "    for (uint64_t {i} = {s}; {i} < {en}; {i}++) {{ {et} c_ = {val}; (({et}*){vv}->ptr)[{vv}->len++] = c_; }}");
                "((lust_Unit){})".into()
            }
            B::VecDedupBy | B::VecDedupByKey => {
                // `VecDedup`'s loop with the closure as the test:
                // `same_bucket(&mut current, &mut previous_kept)`; for
                // `dedup_by_key`, `key(a) == key(b)` with the keys
                // dropped in reverse order, as the temporaries are.
                let e = vec_elem(&tys[0]);
                let et = ctype(&e);
                let vv = &vals[0];
                let f = self.adapter_callee(&ops[1]);
                let (c, w, r) = (self.tmp(), self.tmp(), self.tmp());
                let mut body = String::new();
                // panic=unwind: a panic in the closure (or a key's `==`)
                // keeps the element it saw; one in a duplicate's drop
                // counts that one removed. The unchecked rest moves down
                // behind the kept ones (std's `FillGapOnDrop`).
                let unw = self.p.unwind;
                let mine = "lust_unw_pending && lust_unw_mine()";
                let _ = writeln!(body, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                let _ = writeln!(body, "    if ({vv}->len > 1) {{\n      uint64_t {w} = 1, {r} = 1;\n      for (; {r} < {vv}->len; {r}++) {{");
                let cur = format!("(&(({et}*){vv}->ptr)[{r}])");
                let prev = format!("(&(({et}*){vv}->ptr)[{w} - 1])");
                let same = if b == B::VecDedupBy {
                    let same = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[cur, prev]).0;
                    if unw {
                        let _ = writeln!(body, "      if ({mine}) break;");
                    }
                    same
                } else {
                    let (ka, kt) = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[cur]);
                    if unw {
                        let _ = writeln!(body, "      if ({mine}) break;");
                    }
                    let (kb, _) = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[prev]);
                    if unw {
                        let drop_ka = self.unw_cleanup_drop(&ka, &kt);
                        let _ = writeln!(body, "      if ({mine}) {{{drop_ka} break; }}");
                    }
                    let eq = self.eq_expr(&kt, &format!("(&{ka})"), &format!("(&{kb})"));
                    let s = self.tmp();
                    let _ = writeln!(body, "      uint8_t {s} = {eq};");
                    if unw {
                        // `key(a) == key(b)`: both keys drop as the
                        // closure unwinds, the later one first.
                        let (drop_kb, drop_ka) = (self.unw_cleanup_drop(&kb, &kt), self.unw_cleanup_drop(&ka, &kt));
                        let _ = writeln!(body, "      if ({mine}) {{{drop_kb}{drop_ka} break; }}");
                    }
                    if needs_drop_c(self.p, &kt) {
                        self.want(Glue::Drop, &kt);
                        let _ = writeln!(body, "      drop_{0}(&{kb}); drop_{0}(&{ka});", mangle(&kt));
                    }
                    s
                };
                let drop_dup = if needs_drop_c(self.p, &e) {
                    self.want(Glue::Drop, &e);
                    let after = if unw { format!(" if ({mine}) {{ {r}++; break; }}") } else { String::new() };
                    format!("(void)(drop_{}(&(({et}*){vv}->ptr)[{r}]), 0);{after} ", mangle(&e))
                } else {
                    String::new()
                };
                let _ = writeln!(
                    body,
                    "        if ({same}) {{ {drop_dup}}} else {{ if ({w} != {r}) (({et}*){vv}->ptr)[{w}] = (({et}*){vv}->ptr)[{r}]; {w}++; }}\n      }}"
                );
                if unw {
                    let n = self.tmp();
                    let _ = writeln!(body, "      uint64_t {n} = {vv}->len - {r}; {vv}->len = {w} + {n};");
                    let _ = writeln!(body, "      if ({n} && {w} != {r}) lust_memmove((({et}*){vv}->ptr) + {w}, (({et}*){vv}->ptr) + {r}, {n} * sizeof({et}));\n    }}");
                } else {
                    let _ = writeln!(body, "      {vv}->len = {w};\n    }}");
                }
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    if unw {
                        let drop_c = self.unw_cleanup_drop(&c, &tys[1]);
                        let _ = writeln!(body, "    if ({mine}) {{{drop_c} }} else drop_{}(&{c});", mangle(&tys[1]));
                    } else {
                        let _ = writeln!(body, "    drop_{}(&{c});", mangle(&tys[1]));
                    }
                }
                let _ = write!(self.out, "{body}");
                "((lust_Unit){})".into()
            }
            // The `splice` steps on its `vec::Drain` (lower/iter/splice.rs).
            B::SpliceBegin | B::SpliceReserve | B::SpliceGap | B::SplicePut | B::SpliceMoveTail => {
                let CTy::Ref(dt) = &tys[0] else { unreachable!() };
                let CTy::VecDrain(e) = &**dt else { unreachable!() };
                let et = ctype(e);
                let (p, dv) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    lust_VecDrain *{p} = {}; lust_Vec *{dv} = (lust_Vec *){p}->vec;", vals[0]);
                match b {
                    // `drain.by_ref().for_each(drop)`; the tail length.
                    B::SpliceBegin => {
                        if needs_drop_c(self.p, e) {
                            self.want(Glue::Drop, e);
                            let i = self.tmp();
                            let _ = writeln!(self.out, "    for (uint64_t {i} = {p}->front; {i} < {p}->back; {i}++) drop_{}(&(({et}*){dv}->ptr)[{i}]);", mangle(e));
                        }
                        let _ = writeln!(self.out, "    {p}->front = {p}->back;");
                        format!("{p}->tail_len")
                    }
                    B::SpliceReserve => {
                        let _ = writeln!(self.out, "    lust_vec_reserve({dv}, {}, sizeof({et}), _Alignof({et}));", vals[1]);
                        "((lust_Unit){})".into()
                    }
                    B::SpliceGap => format!("({p}->start < {p}->tail_start)"),
                    B::SplicePut => {
                        let _ = writeln!(self.out, "    (({et}*){dv}->ptr)[{p}->start] = {}; {p}->start++; {dv}->len = {p}->start;", vals[1]);
                        "((lust_Unit){})".into()
                    }
                    _ => {
                        // `move_tail(n)`: `buf.reserve(tail_start + tail_len, n)`,
                        // then the tail moves up by n.
                        let (old, n) = (self.tmp(), &vals[1]);
                        let _ = writeln!(
                            self.out,
                            "    uint64_t {old} = {dv}->len; {dv}->len = {p}->tail_start + {p}->tail_len;\n    lust_vec_reserve({dv}, {n}, sizeof({et}), _Alignof({et})); {dv}->len = {old};\n    lust_memmove((({et}*){dv}->ptr) + {p}->tail_start + {n}, (({et}*){dv}->ptr) + {p}->tail_start, {p}->tail_len * sizeof({et})); {p}->tail_start += {n};"
                        );
                        "((lust_Unit){})".into()
                    }
                }
            }
            _ => return None,
        })
    }

    /// The `cmp(ctx, p)` adapter of `partition_point`: `pred(p)` as
    /// `Less` (-1) or `Greater` (1); ctx is the closure.
    fn partition_adapter(&mut self, elem: &CTy, f: &(sync::Callee, u8, CTy)) -> String {
        let name = format!("lust_bcmp_{}_{}", self.slots[self.body.fn_id.0 as usize], self.adapters);
        self.adapters += 1;
        let pt = ctype(&CTy::Ref(Box::new(elem.clone())));
        let mut body = String::new();
        let (r, _) = self.adapter_call_c(&mut body, f, "ctx", &[format!("(({pt})p)")]);
        let _ = writeln!(body, "  return {r} ? -1 : 1;");
        let _ = writeln!(self.prelude, "static int32_t {name}(void *ctx, const void *p) {{\n{body}}}");
        name
    }
}
