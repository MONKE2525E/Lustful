// Owning pointers to unsized values (w-unsized): `Box<str>`, `Rc<str>`,
// `Arc<str>`, `Rc<[T]>`, `Arc<[T]>`, and `Arc<dyn Tr>` (`CTy::Own`).
// `Box<dyn Tr>`, `Rc<dyn Tr>`, and `Box<[T]>` keep their older forms
// (`BoxDyn`, `RcDyn`, `BoxSlice`), with the same C layout.
//
// The C value is the pointee's fat form: `lust_str`, the slice struct,
// or `lust_dyn`. A Box points at its own allocation. An Rc or Arc
// points at the value inside the counted allocation, after its two
// counts (`strong`, then `weak` with the strong refs' implicit weak
// ref, as `RcI_T` lays them out), so `Rc<T>` to `Rc<[T]>` or `Rc<dyn
// Tr>` only takes the value's address. Value glue (Eq, Cmp, Debug,
// Display, Hash) is the pointee's, through the same fat value.
pub use crate::check::own::Owner;

use super::*;

/// The `CTy::Own` form of `t`, if `t` is one of the owning pointers to
/// an unsized value this file emits.
pub(super) fn own_cty(tys: &impl TyIntern, t: Ty) -> Option<CTy> {
    let (k, e) = crate::check::own::own_parts(tys, t)?;
    let x = match (k, tys.kind(e)) {
        (_, TyKind::Str) => CTy::Str,
        (Owner::Rc | Owner::Arc, TyKind::Slice(el)) => CTy::Slice(Box::new(cty(tys, el))),
        (Owner::Arc, TyKind::Dyn(..)) => CTy::Dyn,
        _ if crate::check::own::dyn_cell_elem(tys, e).is_some() => CTy::DynCell,
        _ if crate::check::own::dyn_lock_elem(tys, e).is_some() => CTy::DynLock(false),
        _ => return None,
    };
    Some(CTy::Own(k, Box::new(x)))
}

/// The data pointer of the fat value `v` of pointee place `x`, as a
/// `uint64_t *` (the counts of an Rc or Arc sit at `[-2]` and `[-1]`).
pub(super) fn data_words(x: &CTy, v: &str) -> String {
    match x {
        CTy::Dyn | CTy::DynCell | CTy::DynLock(_) => format!("((uint64_t *)({v}).data)"),
        _ => format!("((uint64_t *)({v}).ptr)"),
    }
}

/// The byte size of the value behind the fat value `v` of pointee `x`.
fn value_size(x: &CTy, v: &str) -> String {
    match x {
        CTy::Str => format!("({v}).len"),
        CTy::Slice(e) => format!("(({v}).len * sizeof({}))", ctype(e)),
        // The flag, the value, and the padding to the cell's alignment.
        CTy::DynCell => {
            let a = cell_off(&format!("({v}).vt"));
            format!("(({a} + (uint64_t)(uintptr_t)({v}).vt[1] + {a} - 1) / {a} * {a})")
        }
        // The lock words, the value, and the padding to the lock's alignment.
        CTy::DynLock(_) => {
            let (o, a) = (lock_off(&format!("({v}).vt")), lock_align(&format!("({v}).vt")));
            format!("(({o} + (uint64_t)(uintptr_t)({v}).vt[1] + {a} - 1) / {a} * {a})")
        }
        _ => format!("(uint64_t)(uintptr_t)({v}).vt[1]"),
    }
}

/// C statements that drop the value behind the fat value `v` in place.
fn drop_value(p: &Program, x: &CTy, v: &str, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    match x {
        CTy::Slice(e) if needs_drop_c(p, e) => {
            need(Glue::Drop, e);
            format!("for (uint64_t i = 0; i < ({v}).len; i++) drop_{}(&({v}).ptr[i]); ", mangle(e))
        }
        CTy::Dyn => format!("if (({v}).vt[0]) ((void (*)(void *))({v}).vt[0])(({v}).data); "),
        CTy::DynCell | CTy::DynLock(_) => {
            let d = if *x == CTy::DynCell { dyn_cell_value(v) } else { dyn_lock_value(v) };
            format!("{{ lust_dyn c_ = {d}; if (c_.vt[0]) ((void (*)(void *))c_.vt[0])(c_.data); }} ")
        }
        _ => String::new(),
    }
}

/// The C condition that takes one from the count at `c` (a `uint64_t *`)
/// and is true when that was the last.
fn dec(k: Owner, c: &str) -> String {
    match k {
        Owner::Arc => format!("lust_arc_dec({c})"),
        _ => format!("(--*({c}) == 0)"),
    }
}

/// The glue `g` of `CTy::Own(k, x)`: its prototype to `protos` and its
/// definition to `defs`. Drop, Clone, and Default are the pointer's own;
/// the rest forward to the pointee's glue over the same fat value (`str`
/// through `&str`'s).
pub(super) fn own_glue_def(
    p: &Program,
    g: Glue,
    k: Owner,
    x: &CTy,
    protos: &mut String,
    defs: &mut String,
    need: &mut dyn FnMut(Glue, &CTy),
) {
    let t = CTy::Own(k, Box::new(x.clone()));
    let (m, ct) = (mangle(&t), ctype(&t));
    let (proto, body) = match g {
        Glue::Drop => {
            let body = if k == Owner::Box {
                // An empty Box<str> holds a dangling pointer: size 0 frees nothing.
                format!(
                    "  {}lust_dealloc((void *){}, {}, 1);\n",
                    drop_value(p, x, "(*p)", need),
                    data_words(x, "(*p)"),
                    value_size(x, "(*p)")
                )
            } else {
                let align = match x {
                    CTy::Dyn => "(uint64_t)(uintptr_t)p->vt[2]".to_string(),
                    CTy::DynCell => cell_off("p->vt"),
                    CTy::DynLock(_) => lock_align("p->vt"),
                    _ => "16".to_string(),
                };
                format!(
                    "  uint64_t *h = {} - 2;\n  if ({}) {{ {}if ({}) lust_dealloc((void *)h, 16 + {}, {align}); }}\n",
                    data_words(x, "(*p)"),
                    dec(k, "&h[0]"),
                    drop_value(p, x, "(*p)", need),
                    dec(k, "&h[1]"),
                    value_size(x, "(*p)"),
                )
            };
            (format!("void drop_{m}({ct} *p)"), body)
        }
        Glue::Clone => {
            let body = match k {
                Owner::Box => format!(
                    "  {ct} r = *p; r.ptr = ({})lust_alloc(p->len, 1); lust_memcpy((void *)r.ptr, (void *)p->ptr, p->len); return r;\n",
                    if *x == CTy::Str { "uint8_t *".to_string() } else { format!("{}*", ctype(x)) }
                ),
                Owner::Rc => format!("  {}[-2]++; return *p;\n", data_words(x, "(*p)")),
                Owner::Arc => format!("  lust_arc_inc(&{}[-2]); return *p;\n", data_words(x, "(*p)")),
            };
            (format!("{ct} clone_{m}({ct} *p)"), body)
        }
        // `Box<str>` is empty and allocates nothing; `Rc<str>` and
        // `Rc<[T]>` allocate their counts; every empty `Arc<str>` and
        // `Arc<[T]>` shares one static allocation, as std's do.
        Glue::Default => {
            let ptr = match x {
                CTy::Slice(e) => format!("{}*", ctype(e)),
                _ => "uint8_t *".into(),
            };
            let body = match k {
                Owner::Box => format!("  return ({ct}){{ ({ptr})1, 0 }};\n"),
                Owner::Rc => {
                    format!("  uint64_t *h = (uint64_t *)lust_alloc(16, 16); h[0] = 1; h[1] = 1; return ({ct}){{ ({ptr})(h + 2), 0 }};\n")
                }
                Owner::Arc => format!("  return ({ct}){{ ({ptr})lust_arc_empty(), 0 }};\n"),
            };
            (format!("{ct} default_{m}(void)"), body)
        }
        _ => {
            let view = match x {
                CTy::Str => CTy::Ref(Box::new(CTy::Str)),
                other => other.clone(),
            };
            need(g, &view);
            let vm = mangle(&view);
            match g {
                Glue::Eq => (format!("uint8_t eq_{m}({ct} *a, {ct} *b)"), format!("  return eq_{vm}(a, b);\n")),
                Glue::Cmp => (format!("int8_t cmp_{m}({ct} *a, {ct} *b)"), format!("  return cmp_{vm}(a, b);\n")),
                Glue::PCmp => (format!("int8_t pcmp_{m}({ct} *a, {ct} *b)"), format!("  return pcmp_{vm}(a, b);\n")),
                Glue::Debug => (format!("int dbg_{m}(lust_Formatter *f, {ct} *p)"), format!("  return dbg_{vm}(f, p);\n")),
                Glue::Display => (format!("int disp_{m}(lust_Formatter *f, {ct} *p)"), format!("  return disp_{vm}(f, p);\n")),
                _ => unreachable!("glue {g:?} of an owning fat pointer"),
            }
        }
    };
    let _ = writeln!(protos, "{proto};");
    let _ = writeln!(defs, "{proto} {{\n{body}}}\n");
}

impl FnGen<'_, '_> {
    /// The builtins that take or build an owning fat pointer: the counts
    /// and `ptr_eq` of an `Rc` or `Arc` over an unsized value, and the
    /// `From` conversions (`OwnFrom`, `OwnIntoString`). None for any
    /// other call.
    pub(super) fn own_builtin(&mut self, b: Builtin, vals: &[String], tys: &[CTy], loc: &str) -> Option<String> {
        use crate::check::sync::SyncOp as S;
        use Builtin as B;
        match b {
            B::OwnFrom(k) => return Some(self.own_from(k, &vals[0], &tys[0])),
            // `RefCell<dyn Tr>::borrow` and `borrow_mut`: the flag is the
            // cell's first word; the guard is the same fat value.
            B::RefCellBorrow | B::RefCellBorrowMut if tys.first() == Some(&CTy::DynCell) => {
                let t = self.tmp();
                let (busy, take, msg) = if b == B::RefCellBorrowMut {
                    ("*f_ != 0", "*f_ = -1", "RefCell already borrowed")
                } else {
                    ("*f_ < 0 || *f_ == 0x7fffffffffffffffLL", "(*f_)++", "RefCell already mutably borrowed")
                };
                let _ = writeln!(
                    self.out,
                    "    lust_dyn {t} = {}; {{ int64_t *f_ = (int64_t *){t}.data; if ({busy}) lust_panic_cstr_dyn(\"{msg}\", {loc}); {take}; }}",
                    vals[0]
                );
                return Some(t);
            }
            B::OwnIntoString => {
                let v = &vals[0];
                return Some(format!("((lust_String){{ ({v}).ptr, ({v}).len, ({v}).len }})"));
            }
            _ => {}
        }
        // `Mutex<dyn Tr>::lock` and `is_poisoned`: the futex word is the
        // lock's first word, the poison byte the fifth.
        if tys.first() == Some(&CTy::DynLock(false)) {
            let v = &vals[0];
            return Some(match b {
                B::Sync(S::MutexLock) => {
                    let guard = CTy::DynLock(true);
                    let res =
                        CTy::Result(Box::new(guard.clone()), Box::new(CTy::Sync(crate::ty::sync::SyncTy::PoisonError, Box::new(guard))));
                    collect_types(&res, &mut self.sig_types);
                    let (g, t) = (self.tmp(), self.tmp());
                    let (f, e) = (variant_field(self.p, &res, &t, 0, 0), variant_field(self.p, &res, &t, 1, 0));
                    let _ = writeln!(
                        self.out,
                        "    lust_dyn {g} = {v}; lust_mutex_lock((uint32_t *){g}.data); lust_poison_enter((uint8_t *){g}.data + 4);"
                    );
                    let _ = writeln!(
                        self.out,
                        "    {} {t}; if (((uint8_t *){g}.data)[4] & 1) {{ {} {e} = {g}; }} else {{ {} {f} = {g}; }}",
                        ctype(&res),
                        disc_set(self.p, &res, &t, 1),
                        disc_set(self.p, &res, &t, 0)
                    );
                    t
                }
                B::Sync(S::LockIsPoisoned) => format!("((uint8_t)(((uint8_t *)({v}).data)[4] & 1))"),
                _ => return None,
            });
        }
        // The count ops take `&Rc<T>` or `&Arc<T>`.
        let CTy::Ref(r) = tys.first()? else { return None };
        let CTy::Own(k, x) = &**r else { return None };
        let w = |v: &str| data_words(x, &format!("(*{v})"));
        // The `&mut` view of the pointee: the same fat value.
        let view = match &**x {
            CTy::Str => CTy::Ref(Box::new(CTy::Str)),
            other => other.clone(),
        };
        Some(match b {
            B::RcGetMut | B::Sync(S::ArcGetMut) => {
                let opt = CTy::Option(Box::new(view));
                collect_types(&opt, &mut self.sig_types);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let h = w(&vals[0]);
                let unique =
                    if *k == Owner::Arc { format!("lust_arc_is_unique({h} - 2)") } else { format!("({h}[-2] == 1 && {h}[-1] == 1)") };
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if ({unique}) {{ {field} = *{}; {some} }}", vals[0]);
                t
            }
            B::RcMakeMut | B::Sync(S::ArcMakeMut) => self.own_make_mut(*k, x, &vals[0]),
            B::RcStrongCount => format!("{}[-2]", w(&vals[0])),
            B::RcWeakCount => format!("({}[-1] - 1)", w(&vals[0])),
            B::RcPtrEq | B::Sync(S::ArcPtrEq) => format!("({} == {})", w(&vals[0]), w(&vals[1])),
            B::Sync(S::ArcStrongCount) => format!("lust_arc_load(&{}[-2])", w(&vals[0])),
            B::Sync(S::ArcWeakCount) => format!("lust_arc_weak_count({} - 2)", w(&vals[0])),
            _ => return None,
        })
    }

    /// `Rc::make_mut` or `Arc::make_mut` on `*v`, an `Rc` or `Arc` (owner
    /// `k`) of `str` or `[T]`: a shared value is cloned into a fresh
    /// allocation (this pointer's count drops by one); a value only Weaks
    /// share moves to a fresh allocation. Returns the `&mut` fat value.
    fn own_make_mut(&mut self, k: Owner, x: &CTy, v: &str) -> String {
        let t = CTy::Own(k, Box::new(x.clone()));
        let (ct, h, n, st) = (ctype(&t), self.tmp(), self.tmp(), self.tmp());
        let (e, et) = match x {
            CTy::Slice(e) => ((**e).clone(), ctype(e)),
            _ => (CTy::Int(IntTy::U8), "uint8_t".to_string()),
        };
        let size = format!("(*{v}).len * sizeof({et})");
        let copy = format!("lust_memcpy((void *)({n} + 2), (void *)(*{v}).ptr, {size});");
        let clone = if is_copy_c(self.p, &e) {
            copy.clone()
        } else {
            self.want(Glue::Clone, &e);
            format!("for (uint64_t i_ = 0; i_ < (*{v}).len; i_++) (({et}*)({n} + 2))[i_] = clone_{}(&(*{v}).ptr[i_]);", mangle(&e))
        };
        let fresh = format!("uint64_t *{n} = (uint64_t *)lust_alloc(16 + {size}, 16); {n}[0] = 1; {n}[1] = 1;");
        let _ = writeln!(self.out, "    uint64_t *{h} = {} - 2;", data_words(x, &format!("(*{v})")));
        match k {
            Owner::Arc => {
                // 0: shared, 1: only Weaks, 2: unique (runtime/sync.c).
                self.want(Glue::Drop, &t);
                let m = mangle(&t);
                let _ = writeln!(self.out, "    int {st} = lust_arc_make_mut_state({h});");
                let _ = writeln!(
                    self.out,
                    "    if ({st} != 2) {{ {fresh} {ct} o_ = *{v};\n      if ({st} == 0) {{ {clone} drop_{m}(&o_); }} else {{ {copy} if (lust_arc_dec(&{h}[1])) lust_dealloc((void *){h}, 16 + {size}, 16); }}\n      (*{v}).ptr = ({et}*)({n} + 2); }}"
                );
            }
            _ => {
                let _ = writeln!(
                    self.out,
                    "    if ({h}[0] > 1) {{ {fresh} {clone} {h}[0]--; (*{v}).ptr = ({et}*)({n} + 2); }}\n    else if ({h}[1] > 1) {{ {fresh} {copy} {h}[0] = 0; {h}[1]--; (*{v}).ptr = ({et}*)({n} + 2); }}"
                );
            }
        }
        format!("(*{v})")
    }

    /// `Box`, `Rc`, or `Arc` of `str` or `[T]` (owner `k`) from `v`, a
    /// value of `src`: `&str`, `String`, `Box<str>`, `&[T]` (cloned),
    /// `Vec<T>`, `Box<[T]>`, or `[T; N]` (moved). Moved sources give up
    /// their buffers. Returns the temporary that holds the fat value.
    fn own_from(&mut self, k: Owner, v: &str, src: &CTy) -> String {
        // (element type, data pointer, length, whether elements move,
        // statement that frees the source's buffer)
        let byte = CTy::Int(IntTy::U8);
        let (e, ptr, len, moved, free): (CTy, String, String, bool, String) = match src {
            CTy::Ref(s) if **s == CTy::Str => (byte, format!("({v}).ptr"), format!("({v}).len"), false, String::new()),
            CTy::Str => (byte, format!("({v}).ptr"), format!("({v}).len"), false, String::new()),
            CTy::String => {
                let s = self.tmp();
                let _ = writeln!(self.out, "    lust_String {s} = {v};");
                (byte, format!("{s}.ptr"), format!("{s}.len"), true, format!("lust_string_drop(&{s});"))
            }
            CTy::Own(Owner::Box, s) if **s == CTy::Str => {
                let s = self.tmp();
                let _ = writeln!(self.out, "    lust_str {s} = {v};");
                (byte, format!("{s}.ptr"), format!("{s}.len"), true, format!("lust_dealloc((void *){s}.ptr, {s}.len, 1);"))
            }
            CTy::Slice(e) => ((**e).clone(), format!("({v}).ptr"), format!("({v}).len"), false, String::new()),
            CTy::Vec(e) => {
                let (s, et) = (self.tmp(), ctype(e));
                let _ = writeln!(self.out, "    lust_Vec {s} = {v};");
                (
                    (**e).clone(),
                    format!("(({et}*){s}.ptr)"),
                    format!("{s}.len"),
                    true,
                    format!("lust_dealloc({s}.ptr, {s}.cap * sizeof({et}), _Alignof({et}));"),
                )
            }
            CTy::BoxSlice(e) => {
                let (s, et) = (self.tmp(), ctype(e));
                let _ = writeln!(self.out, "    {} {s} = {v};", ctype(src));
                (
                    (**e).clone(),
                    format!("{s}.ptr"),
                    format!("{s}.len"),
                    true,
                    format!("lust_dealloc((void *){s}.ptr, {s}.len * sizeof({et}), _Alignof({et}));"),
                )
            }
            CTy::Array(e, n) => {
                let s = self.tmp();
                let _ = writeln!(self.out, "    {} {s} = {v};", ctype(src));
                ((**e).clone(), format!("{s}.v"), format!("((uint64_t){n})"), true, String::new())
            }
            other => unreachable!("an owning pointer from {other:?}"),
        };
        let et = ctype(&e);
        let ft = if src == &CTy::String || matches!(src, CTy::Ref(_) | CTy::Str | CTy::Own(..)) {
            "lust_str".to_string()
        } else {
            ctype(&CTy::Slice(Box::new(e.clone())))
        };
        collect_types(&CTy::Slice(Box::new(e.clone())), &mut self.sig_types);
        let (r, n) = (self.tmp(), self.tmp());
        let _ = writeln!(self.out, "    uint64_t {n} = {len};\n    {ft} {r};\n    {r}.len = {n};");
        let size = format!("{n} * sizeof({et})");
        match k {
            Owner::Box => {
                let _ = writeln!(self.out, "    {r}.ptr = ({et}*)lust_alloc({size}, _Alignof({et}));");
            }
            Owner::Rc | Owner::Arc => {
                let _ = writeln!(
                    self.out,
                    "    {{ uint64_t *h_ = (uint64_t *)lust_alloc(16 + {size}, 16); h_[0] = 1; h_[1] = 1; {r}.ptr = ({et}*)(h_ + 2); }}"
                );
            }
        }
        if moved || is_copy_c(self.p, &e) {
            let _ = writeln!(self.out, "    if ({n}) lust_memcpy((void *){r}.ptr, (void *){ptr}, {size});");
        } else {
            self.want(Glue::Clone, &e);
            let _ = writeln!(self.out, "    for (uint64_t i_ = 0; i_ < {n}; i_++) {r}.ptr[i_] = clone_{}(&{ptr}[i_]);", mangle(&e));
        }
        if !free.is_empty() {
            let _ = writeln!(self.out, "    {free}");
        }
        r
    }
}

/// The byte offset of the value inside a `RefCell` whose value's vtable
/// is `vt`: after the `isize` borrow flag, at the value's alignment.
fn cell_off(vt: &str) -> String {
    format!("((uint64_t)(uintptr_t){vt}[2] > 8 ? (uint64_t)(uintptr_t){vt}[2] : 8)")
}

/// The dyn place of the value in the `RefCell<dyn Tr>` (or its guard)
/// whose fat value is `v`.
pub(super) fn dyn_cell_value(v: &str) -> String {
    format!("((lust_dyn){{ (void *)((char *)({v}).data + {}), ({v}).vt }})", cell_off(&format!("({v}).vt")))
}

/// The drop glue of a `Ref<dyn Tr>` or `RefMut<dyn Tr>` (`t`), which
/// gives the borrow back through the cell's flag word, or of a
/// `MutexGuard<dyn Tr>`, which unlocks (poisoning the lock when a panic
/// drops it, as `lust_poison_leave` does for a sized guard).
pub(super) fn dyn_guard_drop(t: &CTy, protos: &mut String, defs: &mut String) {
    let (mn, ct) = (mangle(t), ctype(t));
    let body = match t {
        CTy::DynGuard(m) => format!("((int64_t *)p->data)[0] {}= 1;", if *m { "+" } else { "-" }),
        _ => "lust_poison_leave((uint8_t *)p->data + 4); lust_mutex_unlock((uint32_t *)p->data);".into(),
    };
    let _ = writeln!(protos, "void drop_{mn}({ct} *p);");
    let _ = writeln!(defs, "void drop_{mn}({ct} *p) {{\n  {body}\n}}\n");
}

/// The byte offset of the value inside a `Mutex` whose value's vtable is
/// `vt`: after the `u32` futex word and the poison byte, at the value's
/// alignment (cgen/sync.rs `cell_words`).
fn lock_off(vt: &str) -> String {
    format!("((5 + (uint64_t)(uintptr_t){vt}[2] - 1) & ~((uint64_t)(uintptr_t){vt}[2] - 1))")
}

/// The alignment of a `Mutex` whose value's vtable is `vt`.
fn lock_align(vt: &str) -> String {
    format!("((uint64_t)(uintptr_t){vt}[2] > 4 ? (uint64_t)(uintptr_t){vt}[2] : 4)")
}

/// The dyn place of the value in the `Mutex<dyn Tr>` (or its guard)
/// whose fat value is `v`.
pub(super) fn dyn_lock_value(v: &str) -> String {
    format!("((lust_dyn){{ (void *)((char *)({v}).data + {}), ({v}).vt }})", lock_off(&format!("({v}).vt")))
}
