// Codegen for the `std::sync` and `std::thread` types (W-THREADS, ARCH
// 7.3): their C forms, layouts, glue, and the builtin calls check/sync.rs
// types. The operations call the runtime (src/runtime/sync.c), which
// holds every atomic and every OS call, so the generated code stays
// plain C that tcc and gcc compile the same way.
//
// Atomics are their value's C integer type (`uint8_t` for `AtomicBool`),
// accessed only through the runtime's `lust_at_*` functions, which take
// Rust's `atomic::Ordering` discriminant and panic on the orderings
// Rust's methods reject.
use super::*;
use crate::check::sync::SyncOp;
use crate::ty::sync::{AtomicVal, SyncTy};

/// The C type of a sync type with type argument `e`. `Arc<T>` and
/// `sync::Weak<T>` point at `Rc<T>`'s counted header (`RcI_T`).
pub(super) fn sync_ctype(k: SyncTy, e: &CTy) -> String {
    match (k, k.atomic_value()) {
        (SyncTy::Arc | SyncTy::ArcWeak, _) => format!("RcI_{}*", mangle(e)),
        (_, Some(AtomicVal::Bool)) => "uint8_t".into(),
        (_, Some(AtomicVal::Int(i))) => int_c(i).into(),
        (_, None) => unreachable!("a sync type with no C form"),
    }
}

/// The exact Rust layout of a sync type. An atomic is its value's
/// size and alignment with no niche (`UnsafeCell`); `Arc` and
/// `sync::Weak` are a non-null pointer.
pub(super) fn sync_layout(k: SyncTy) -> Option<Layout> {
    if matches!(k, SyncTy::Arc | SyncTy::ArcWeak) {
        return Some(layout::ptr_layout());
    }
    let v = k.atomic_value()?;
    let n = v.bytes() as u64;
    Some(plain_layout(n, n))
}

/// True when a value of the sync type needs drop glue.
pub(super) fn sync_needs_drop(k: SyncTy, _e: &CTy) -> bool {
    matches!(k, SyncTy::Arc | SyncTy::ArcWeak)
}

/// The C types a sync type's code names: `Arc` and `sync::Weak` need
/// `Rc`'s header struct for their element.
pub(super) fn sync_collect_types(k: SyncTy, e: &CTy, out: &mut HashSet<CTy>) {
    if matches!(k, SyncTy::Arc | SyncTy::ArcWeak) {
        out.insert(CTy::Rc(Box::new(e.clone())));
        collect_types(e, out);
    }
}

/// The glue function `g` of a sync type: its prototype to `protos` and
/// its definition to `defs`. Glue a type does not have is never asked
/// for (check answers the trait as not implemented).
pub(super) fn sync_glue_def(p: &Program, g: Glue, k: SyncTy, e: &CTy, protos: &mut String, defs: &mut String, need: &mut dyn FnMut(Glue, &CTy)) {
    let t = CTy::Sync(k, Box::new(e.clone()));
    let (m, ct) = (mangle(&t), ctype(&t));
    let it = format!("RcI_{}", mangle(e));
    let dealloc = format!("lust_dealloc((void*)*p, sizeof({it}), _Alignof({it}))");
    // `Arc`'s value glue (Eq, Cmp, Debug, Display, Default) is `Rc`'s:
    // the same header, read the same way.
    let forward = |g: Glue, rc: &CTy, need: &mut dyn FnMut(Glue, &CTy), protos: &mut String, defs: &mut String| {
        need(g, rc);
        let rm = mangle(rc);
        let (proto, call) = match g {
            Glue::Eq => (format!("uint8_t eq_{m}({ct} *a, {ct} *b)"), format!("eq_{rm}(a, b)")),
            Glue::Cmp => (format!("int8_t cmp_{m}({ct} *a, {ct} *b)"), format!("cmp_{rm}(a, b)")),
            Glue::Debug => (format!("int dbg_{m}(lust_Formatter *f, {ct} *p)"), format!("dbg_{rm}(f, p)")),
            Glue::Display => (format!("int disp_{m}(lust_Formatter *f, {ct} *p)"), format!("disp_{rm}(f, p)")),
            Glue::Default => (format!("{ct} default_{m}(void)"), format!("default_{rm}()")),
            Glue::Drop | Glue::Clone => unreachable!("Arc's own drop and clone"),
        };
        let _ = writeln!(protos, "{proto};");
        let _ = writeln!(defs, "{proto} {{\n  return {call};\n}}\n");
    };
    match (g, k) {
        // The last strong ref drops the value, then gives up the implicit
        // weak ref; the last weak ref frees the header.
        (Glue::Drop, SyncTy::Arc) => {
            let inner = if needs_drop_c(p, e) {
                need(Glue::Drop, e);
                format!("drop_{}(&(*p)->v); ", mangle(e))
            } else {
                String::new()
            };
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            let _ = writeln!(
                defs,
                "void drop_{m}({ct} *p) {{\n  if (lust_arc_dec(&(*p)->strong)) {{ {inner}if (lust_arc_dec(&(*p)->weak)) {dealloc}; }}\n}}\n"
            );
        }
        (Glue::Drop, SyncTy::ArcWeak) => {
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            let _ = writeln!(defs, "void drop_{m}({ct} *p) {{\n  if (*p != ({it}*)~(uint64_t)0 && lust_arc_dec(&(*p)->weak)) {dealloc};\n}}\n");
        }
        (Glue::Clone, SyncTy::Arc) => {
            let _ = writeln!(protos, "{ct} clone_{m}({ct} *p);");
            let _ = writeln!(defs, "{ct} clone_{m}({ct} *p) {{\n  lust_arc_inc(&(*p)->strong); return *p;\n}}\n");
        }
        (Glue::Clone, SyncTy::ArcWeak) => {
            let _ = writeln!(protos, "{ct} clone_{m}({ct} *p);");
            let _ = writeln!(defs, "{ct} clone_{m}({ct} *p) {{\n  if (*p != ({it}*)~(uint64_t)0) lust_arc_inc(&(*p)->weak); return *p;\n}}\n");
        }
        (Glue::Debug, SyncTy::ArcWeak) => forward(g, &CTy::Weak(Box::new(e.clone())), need, protos, defs),
        // `Weak::default()` is `Weak::new()`: the dangling pointer.
        (Glue::Default, SyncTy::ArcWeak) => {
            let _ = writeln!(protos, "{ct} default_{m}(void);");
            let _ = writeln!(defs, "{ct} default_{m}(void) {{\n  return ({it}*)~(uint64_t)0;\n}}\n");
        }
        (_, SyncTy::Arc) => forward(g, &CTy::Rc(Box::new(e.clone())), need, protos, defs),
        (Glue::Default, _) if k.atomic_value().is_some() => {
            let _ = writeln!(protos, "{ct} default_{m}(void);");
            let _ = writeln!(defs, "{ct} default_{m}(void) {{\n  return 0;\n}}\n");
        }
        (Glue::Drop, _) if k.atomic_value().is_some() => {
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            let _ = writeln!(defs, "void drop_{m}({ct} *p) {{\n  (void)p;\n}}\n");
        }
        _ => unreachable!("internal: no {g:?} glue for `{}`", k.name()),
    }
}

/// The runtime width suffix of an atomic (`1`, `2`, `4`, or `8`).
fn width(v: AtomicVal) -> u32 {
    v.bytes()
}

/// The atomic of a `&Atomic*` operand type.
fn atomic_of_ref(t: &CTy) -> AtomicVal {
    match t {
        CTy::Ref(inner) => atomic_of_ref(inner),
        CTy::Sync(k, _) => k.atomic_value().expect("an atomic receiver"),
        _ => unreachable!("an atomic receiver"),
    }
}

/// The C form of an atomic's value type.
pub(super) fn vt_of(v: AtomicVal) -> CTy {
    match v {
        AtomicVal::Bool => CTy::Bool,
        AtomicVal::Int(i) => CTy::Int(i),
    }
}

/// The C value of an `atomic::Ordering` operand (its discriminant).
fn ord(p: &Program, v: &str, t: &CTy) -> String {
    disc_call(p, t, &format!("(&{v})"))
}

impl FnGen<'_, '_, '_> {
    /// One sync builtin call: C statements to `self.out`, and the C
    /// expression of its value.
    pub(super) fn sync_builtin(&mut self, op: SyncOp, vals: &[String], tys: &[CTy], loc: &str) -> String {
        use crate::check::sync::FetchOp as F;
        use SyncOp as S;
        // The runtime works on unsigned words of the atomic's width: the
        // receiver pointer and the values cast to it, the result back.
        let atomic = |i: usize| atomic_of_ref(&tys[i]);
        let word = |v: AtomicVal| format!("uint{}_t", width(v) * 8);
        let ptr = |v: AtomicVal| format!("(({}*)({}))", word(v), vals[0]);
        let arg = |v: AtomicVal, i: usize| format!("(({})({}))", word(v), vals[i]);
        let back = |v: AtomicVal, call: String| format!("(({}){call})", ctype(&vt_of(v)));
        match op {
            S::AtomicNew(_) | S::AtomicFrom(_) | S::AtomicIntoInner | S::AtomicGetMut => vals[0].clone(),
            S::AtomicDefault(k) => format!("(({})0)", sync_ctype(k, &CTy::Unit)),
            S::AtomicLoad => {
                let v = atomic(0);
                back(v, format!("lust_at_load_{}({}, {}, {loc})", width(v), ptr(v), ord(self.p, &vals[1], &tys[1])))
            }
            S::AtomicStore => {
                let v = atomic(0);
                format!("(lust_at_store_{}({}, {}, {}, {loc}), ((lust_Unit){{}}))", width(v), ptr(v), arg(v, 1), ord(self.p, &vals[2], &tys[2]))
            }
            S::AtomicSwap => {
                let v = atomic(0);
                back(v, format!("lust_at_swap_{}({}, {}, {})", width(v), ptr(v), arg(v, 1), ord(self.p, &vals[2], &tys[2])))
            }
            S::AtomicFetch(f) => {
                let v = atomic(0);
                let signed = matches!(v, AtomicVal::Int(i) if i.signed());
                let name = match f {
                    F::Add => "add",
                    F::Sub => "sub",
                    F::And => "and",
                    F::Or => "or",
                    F::Xor => "xor",
                    F::Nand if v == AtomicVal::Bool => "bnand",
                    F::Nand => "nand",
                    F::Max if signed => "smax",
                    F::Max => "umax",
                    F::Min if signed => "smin",
                    F::Min => "umin",
                };
                back(v, format!("lust_at_fetch_{name}_{}({}, {}, {})", width(v), ptr(v), arg(v, 1), ord(self.p, &vals[2], &tys[2])))
            }
            S::AtomicFetchNot => {
                let v = atomic(0);
                back(v, format!("lust_at_fetch_xor_{}({}, 1, {})", width(v), ptr(v), ord(self.p, &vals[1], &tys[1])))
            }
            S::AtomicCompareExchange | S::AtomicCompareExchangeWeak => {
                let v = atomic(0);
                let res = CTy::Result(Box::new(vt_of(v)), Box::new(vt_of(v)));
                collect_types(&res, &mut self.sig_types);
                let (t, old) = (self.tmp(), self.tmp());
                let _ = writeln!(
                    self.out,
                    "    {} {t}; {} {old}; int {t}_ok = lust_at_cas_{}({}, {}, {}, {}, {}, &{old}, {loc});",
                    ctype(&res),
                    word(v),
                    width(v),
                    ptr(v),
                    arg(v, 1),
                    arg(v, 2),
                    ord(self.p, &vals[3], &tys[3]),
                    ord(self.p, &vals[4], &tys[4]),
                );
                let vt = ctype(&vt_of(v));
                let ok_f = variant_field(self.p, &res, &t, 0, 0);
                let err_f = variant_field(self.p, &res, &t, 1, 0);
                let set_ok = disc_set(self.p, &res, &t, 0);
                let set_err = disc_set(self.p, &res, &t, 1);
                let _ = writeln!(self.out, "    if ({t}_ok) {{ {set_ok} {ok_f} = ({vt}){old}; }} else {{ {set_err} {err_f} = ({vt}){old}; }}");
                t
            }
            S::Fence => format!("(lust_at_fence({}, {loc}), ((lust_Unit){{}}))", ord(self.p, &vals[0], &tys[0])),
            S::CompilerFence => format!("(lust_at_compiler_fence({}, {loc}), ((lust_Unit){{}}))", ord(self.p, &vals[0], &tys[0])),
            S::SpinLoop => "((lust_Unit){})".into(),
            S::ArcNew
            | S::ArcStrongCount
            | S::ArcWeakCount
            | S::ArcPtrEq
            | S::ArcDowngrade
            | S::ArcGetMut
            | S::ArcMakeMut
            | S::ArcTryUnwrap
            | S::ArcIntoInner
            | S::ArcUnwrapOrClone
            | S::ArcWeakNew
            | S::ArcWeakUpgrade
            | S::ArcWeakStrongCount
            | S::ArcWeakWeakCount
            | S::ArcWeakPtrEq => self.arc_builtin(op, vals, tys),
        }
    }

    /// `Arc` and `sync::Weak` calls, after alloc::sync: every count moves
    /// through the runtime's atomic `lust_arc_*` functions.
    fn arc_builtin(&mut self, op: SyncOp, vals: &[String], tys: &[CTy]) -> String {
        use SyncOp as S;
        // The element type of the first operand (`Arc<T>`, `&Arc<T>`,
        // `&mut Arc<T>`, `&Weak<T>`), or the operand itself for `new`.
        let elem = match op {
            S::ArcNew => tys[0].clone(),
            S::ArcWeakNew => CTy::Unit,
            _ => match deref_cty(&tys[0]) {
                CTy::Sync(_, e) => *e,
                other => unreachable!("an Arc or Weak operand, found {other:?}"),
            },
        };
        let it = format!("RcI_{}", mangle(&elem));
        let arc = CTy::Sync(SyncTy::Arc, Box::new(elem.clone()));
        collect_types(&arc, &mut self.sig_types);
        let h = |v: &str| format!("((uint64_t*){v})");
        let free = |v: &str| format!("if (lust_arc_dec(&{v}->weak)) lust_dealloc((void*){v}, sizeof({it}), _Alignof({it}));");
        let clone_of = |this: &mut Self, src: &str| -> String {
            if is_copy_c(this.p, &elem) {
                src.to_string()
            } else {
                this.want(Glue::Clone, &elem);
                format!("clone_{}(&{src})", mangle(&elem))
            }
        };
        match op {
            S::ArcNew => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {it} *{t} = ({it}*)lust_alloc(sizeof({it}), _Alignof({it})); {t}->strong = 1; {t}->weak = 1; {t}->v = {};", vals[0]);
                t
            }
            S::ArcStrongCount => format!("lust_arc_load(&(*{})->strong)", vals[0]),
            S::ArcWeakCount => format!("lust_arc_weak_count({})", h(&format!("*{}", vals[0]))),
            S::ArcPtrEq | S::ArcWeakPtrEq => format!("(*{} == *{})", vals[0], vals[1]),
            S::ArcDowngrade => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {it} *{t} = *{}; lust_arc_downgrade({});", vals[0], h(&t));
                t
            }
            S::ArcGetMut => {
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(elem.clone()))));
                collect_types(&opt, &mut self.sig_types);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let v = &vals[0];
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(self.out, "    if (lust_arc_is_unique({})) {{ {field} = &(*{v})->v; {some} }}", h(&format!("*{v}")));
                t
            }
            S::ArcMakeMut => {
                // 0: shared, clone into a fresh Arc and drop this one's
                // count; 1: Weaks only, move the value to a fresh Arc and
                // give up the implicit weak; 2: unique already.
                let v = &vals[0];
                let (st, n, old) = (self.tmp(), self.tmp(), self.tmp());
                let cloned = clone_of(self, &format!("(*{v})->v"));
                self.want(Glue::Drop, &arc);
                let am = mangle(&arc);
                let _ = writeln!(self.out, "    int {st} = lust_arc_make_mut_state({});", h(&format!("*{v}")));
                let _ = writeln!(
                    self.out,
                    "    if ({st} != 2) {{ {it} *{n} = ({it}*)lust_alloc(sizeof({it}), _Alignof({it})); {n}->strong = 1; {n}->weak = 1; {it} *{old} = *{v};"
                );
                let _ = writeln!(self.out, "      if ({st} == 0) {{ {n}->v = {cloned}; drop_{am}(&{old}); }} else {{ {n}->v = {old}->v; {} }}", free(&old));
                let _ = writeln!(self.out, "      *{v} = {n}; }}");
                format!("&(*{v})->v")
            }
            S::ArcTryUnwrap => {
                let res = CTy::Result(Box::new(elem.clone()), Box::new(arc.clone()));
                collect_types(&res, &mut self.sig_types);
                let t = self.tmp();
                let v = &vals[0];
                let ok_f = variant_field(self.p, &res, &t, 0, 0);
                let err_f = variant_field(self.p, &res, &t, 1, 0);
                let set_ok = disc_set(self.p, &res, &t, 0);
                let set_err = disc_set(self.p, &res, &t, 1);
                let _ = writeln!(self.out, "    {} {t};", ctype(&res));
                let _ = writeln!(
                    self.out,
                    "    if (lust_arc_take_unique({})) {{ {set_ok} {ok_f} = {v}->v; {} }} else {{ {set_err} {err_f} = {v}; }}",
                    h(v),
                    free(v)
                );
                t
            }
            S::ArcIntoInner | S::ArcUnwrapOrClone => {
                // The last strong Arc gives up its value; any other drops
                // its count (into_inner answers None, unwrap_or_clone a
                // clone taken before the count drops).
                let v = self.tmp();
                let _ = writeln!(self.out, "    {it} *{v} = {};", vals[0]);
                let t = self.tmp();
                if op == S::ArcIntoInner {
                    let opt = CTy::Option(Box::new(elem.clone()));
                    collect_types(&opt, &mut self.sig_types);
                    let (f, some, none) = (variant_field(self.p, &opt, &t, 1, 0), disc_set(self.p, &opt, &t, 1), disc_set(self.p, &opt, &t, 0));
                    let _ = writeln!(
                        self.out,
                        "    {} {t}; if (lust_arc_dec(&{v}->strong)) {{ {f} = {v}->v; {some} {} }} else {{ {none} }}",
                        ctype(&opt),
                        free(&v)
                    );
                } else {
                    let c = clone_of(self, &format!("{v}->v"));
                    self.want(Glue::Drop, &arc);
                    let am = mangle(&arc);
                    let _ = writeln!(
                        self.out,
                        "    {} {t}; if (lust_arc_take_unique({})) {{ {t} = {v}->v; {} }} else {{ {t} = {c}; drop_{am}(&{v}); }}",
                        ctype(&elem),
                        h(&v),
                        free(&v)
                    );
                }
                t
            }
            S::ArcWeakNew => "((void*)~(uint64_t)0)".into(),
            S::ArcWeakUpgrade => {
                let opt = CTy::Option(Box::new(arc.clone()));
                collect_types(&opt, &mut self.sig_types);
                let (t, w) = (self.tmp(), self.tmp());
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let _ = writeln!(self.out, "    {} {t}; {}", ctype(&opt), disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {it} *{w} = *{}; if ({w} != ({it}*)~(uint64_t)0 && lust_arc_upgrade({})) {{ {field} = {w}; {some} }}",
                    vals[0],
                    h(&w)
                );
                t
            }
            S::ArcWeakStrongCount => format!("(*{0} == (void*)~(uint64_t)0 ? (uint64_t)0 : lust_arc_load(&(*{0})->strong))", vals[0]),
            S::ArcWeakWeakCount => format!("(*{0} == (void*)~(uint64_t)0 ? (uint64_t)0 : lust_arc_weak_weak_count({1}))", vals[0], h(&format!("*{}", vals[0]))),
            _ => unreachable!("arc_builtin takes the Arc ops"),
        }
    }
}
