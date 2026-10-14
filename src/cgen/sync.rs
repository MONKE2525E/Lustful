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

/// The C type of a sync type with type argument `e`.
pub(super) fn sync_ctype(k: SyncTy, _e: &CTy) -> String {
    match k.atomic_value() {
        Some(AtomicVal::Bool) => "uint8_t".into(),
        Some(AtomicVal::Int(i)) => int_c(i).into(),
        None => unreachable!("every sync type is an atomic"),
    }
}

/// The exact Rust layout of a sync type. An atomic is its value's
/// size and alignment with no niche (`UnsafeCell`).
pub(super) fn sync_layout(k: SyncTy) -> Option<Layout> {
    let v = k.atomic_value()?;
    let n = v.bytes() as u64;
    Some(plain_layout(n, n))
}

/// True when a value of the sync type needs drop glue.
pub(super) fn sync_needs_drop(_k: SyncTy, _e: &CTy) -> bool {
    false
}

/// The glue function `g` of a sync type: its prototype to `protos` and
/// its definition to `defs`. Glue a type does not have is never asked
/// for (check answers the trait as not implemented).
pub(super) fn sync_glue_def(_p: &Program, g: Glue, k: SyncTy, e: &CTy, protos: &mut String, defs: &mut String, _need: &mut dyn FnMut(Glue, &CTy)) {
    let t = CTy::Sync(k, Box::new(e.clone()));
    let (m, ct) = (mangle(&t), ctype(&t));
    match (g, k.atomic_value()) {
        (Glue::Default, Some(_)) => {
            let _ = writeln!(protos, "{ct} default_{m}(void);");
            let _ = writeln!(defs, "{ct} default_{m}(void) {{\n  return 0;\n}}\n");
        }
        (Glue::Drop, Some(_)) => {
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
        }
    }
}
