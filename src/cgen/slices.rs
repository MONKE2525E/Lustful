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
                let _ = writeln!(body, "    {} {c} = {};", ctype(&tys[1]), vals[1]);
                let _ = writeln!(body, "    if ({vv}->len > 1) {{\n      uint64_t {w} = 1;\n      for (uint64_t {r} = 1; {r} < {vv}->len; {r}++) {{");
                let cur = format!("(&(({et}*){vv}->ptr)[{r}])");
                let prev = format!("(&(({et}*){vv}->ptr)[{w} - 1])");
                let same = if b == B::VecDedupBy {
                    self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[cur, prev]).0
                } else {
                    let (ka, kt) = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[cur]);
                    let (kb, _) = self.adapter_call_c(&mut body, &f, &format!("&{c}"), &[prev]);
                    let eq = self.eq_expr(&kt, &format!("(&{ka})"), &format!("(&{kb})"));
                    let s = self.tmp();
                    let _ = writeln!(body, "      uint8_t {s} = {eq};");
                    if needs_drop_c(self.p, &kt) {
                        self.want(Glue::Drop, &kt);
                        let _ = writeln!(body, "      drop_{0}(&{kb}); drop_{0}(&{ka});", mangle(&kt));
                    }
                    s
                };
                let drop_dup = if needs_drop_c(self.p, &e) {
                    self.want(Glue::Drop, &e);
                    format!("drop_{}(&(({et}*){vv}->ptr)[{r}]); ", mangle(&e))
                } else {
                    String::new()
                };
                let _ = writeln!(
                    body,
                    "        if ({same}) {{ {drop_dup}}} else {{ if ({w} != {r}) (({et}*){vv}->ptr)[{w}] = (({et}*){vv}->ptr)[{r}]; {w}++; }}\n      }}\n      {vv}->len = {w};\n    }}"
                );
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    let _ = writeln!(body, "    drop_{}(&{c});", mangle(&tys[1]));
                }
                let _ = write!(self.out, "{body}");
                "((lust_Unit){})".into()
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
