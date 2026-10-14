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
        // A lock is its struct (`LkM_T`/`LkR_T`); a guard points at its
        // lock; a `PoisonError<G>` is `G` itself.
        (SyncTy::Mutex | SyncTy::RwLock | SyncTy::OnceLock, _) => {
            format!("Lk{}_{}", if k == SyncTy::Mutex { "M" } else if k == SyncTy::RwLock { "R" } else { "O" }, mangle(e))
        }
        (SyncTy::Condvar, _) => "uint32_t".into(),
        (SyncTy::Barrier, _) => "lust_Barrier".into(),
        (SyncTy::BarrierWaitResult, _) => "uint8_t".into(),
        (SyncTy::MutexGuard | SyncTy::RwLockReadGuard | SyncTy::RwLockWriteGuard, _) => format!("{}*", sync_ctype(k.guard().expect("a guard").0, e)),
        (SyncTy::PoisonError | SyncTy::SendError, _) => ctype(e),
        (SyncTy::Sender | SyncTy::SyncSender | SyncTy::Receiver, _) => "lust_Chan*".into(),
        (SyncTy::JoinHandle | SyncTy::ScopedJoinHandle, _) => "lust_JoinHdr*".into(),
        (SyncTy::Scope, _) => "lust_Scope".into(),
        (SyncTy::Thread, _) => "lust_ThreadInfo*".into(),
        (SyncTy::ThreadId, _) => "uint64_t".into(),
        // Never built (a panic aborts): a zero-size stand-in.
        (SyncTy::JoinError, _) => "lust_Unit".into(),
        (_, Some(AtomicVal::Bool)) => "uint8_t".into(),
        (_, Some(AtomicVal::Int(i))) => int_c(i).into(),
        (_, None) => unreachable!("a sync type with no C form"),
    }
}

/// The state words ahead of the value in a lock or `OnceLock` struct:
/// `st` (the futex word), then `wn` (an RwLock's sleepers) and `poison`.
pub(super) fn cell_words(k: SyncTy) -> &'static [IntTy] {
    match k {
        SyncTy::Mutex => &[IntTy::U32, IntTy::U8],
        SyncTy::RwLock => &[IntTy::U32, IntTy::U32, IntTy::U8],
        _ => &[IntTy::U32],
    }
}

/// The exact Rust layout of a sync type. An atomic is its value's
/// size and alignment with no niche (`UnsafeCell`); `Arc` and
/// `sync::Weak` are a non-null pointer.
pub(super) fn sync_layout(k: SyncTy) -> Option<Layout> {
    if matches!(
        k,
        SyncTy::Arc | SyncTy::ArcWeak | SyncTy::JoinHandle | SyncTy::ScopedJoinHandle | SyncTy::Thread | SyncTy::Sender | SyncTy::SyncSender | SyncTy::Receiver
    ) || k.guard().is_some()
    {
        return Some(layout::ptr_layout());
    }
    match k {
        SyncTy::Scope | SyncTy::Condvar => return Some(plain_layout(4, 4)),
        SyncTy::Barrier => return Some(plain_layout(32, 8)),
        SyncTy::BarrierWaitResult => return Some(plain_layout(1, 1)),
        _ => {}
    }
    if k == SyncTy::ThreadId {
        return Some(plain_layout(8, 8));
    }
    if k == SyncTy::JoinError {
        return Some(layout::zst_layout(1));
    }
    let v = k.atomic_value()?;
    let n = v.bytes() as u64;
    Some(plain_layout(n, n))
}

/// True when a value of the sync type needs drop glue.
pub(super) fn sync_needs_drop(p: &Program, k: SyncTy, e: &CTy) -> bool {
    match k {
        SyncTy::Mutex | SyncTy::RwLock | SyncTy::PoisonError | SyncTy::SendError | SyncTy::OnceLock => needs_drop_c(p, e),
        _ => {
            matches!(
                k,
                SyncTy::Arc
                    | SyncTy::ArcWeak
                    | SyncTy::JoinHandle
                    | SyncTy::ScopedJoinHandle
                    | SyncTy::Thread
                    | SyncTy::Sender
                    | SyncTy::SyncSender
                    | SyncTy::Receiver
            ) || k.guard().is_some()
        }
    }
}

/// The C types a sync type's code names: `Arc` and `sync::Weak` need
/// `Rc`'s header struct for their element.
pub(super) fn sync_collect_types(k: SyncTy, e: &CTy, out: &mut HashSet<CTy>) {
    if matches!(k, SyncTy::Arc | SyncTy::ArcWeak) {
        out.insert(CTy::Rc(Box::new(e.clone())));
        collect_types(e, out);
    }
    if let Some(l) = if k.is_cell_struct() { Some(k) } else { k.guard().map(|g| g.0) } {
        out.insert(CTy::Sync(l, Box::new(e.clone())));
        collect_types(e, out);
    }
    if matches!(k, SyncTy::PoisonError | SyncTy::SendError | SyncTy::Sender | SyncTy::SyncSender | SyncTy::Receiver | SyncTy::JoinHandle | SyncTy::ScopedJoinHandle) {
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
        (_, SyncTy::Mutex | SyncTy::RwLock | SyncTy::MutexGuard | SyncTy::RwLockReadGuard | SyncTy::RwLockWriteGuard | SyncTy::PoisonError) => {
            lock_glue_def(p, g, k, e, &m, &ct, protos, defs, need)
        }
        (_, SyncTy::JoinHandle | SyncTy::ScopedJoinHandle | SyncTy::Scope | SyncTy::Thread | SyncTy::ThreadId | SyncTy::JoinError) => {
            thread_glue_def(g, k, &m, &ct, protos, defs)
        }
        (_, SyncTy::Sender | SyncTy::SyncSender | SyncTy::Receiver | SyncTy::SendError) => chan_glue_def(p, g, k, e, &m, &ct, protos, defs, need),
        (_, SyncTy::Condvar | SyncTy::Barrier | SyncTy::BarrierWaitResult | SyncTy::OnceLock) => once_glue_def(p, g, k, e, &m, &ct, protos, defs, need),
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

/// Glue of `Condvar`, `Barrier`, `BarrierWaitResult`, and `OnceLock`.
#[allow(clippy::too_many_arguments)]
fn once_glue_def(p: &Program, g: Glue, k: SyncTy, e: &CTy, m: &str, ct: &str, protos: &mut String, defs: &mut String, need: &mut dyn FnMut(Glue, &CTy)) {
    let lit = |s: &str| format!("(lust_str){{(uint8_t*)\"{s}\", {}}}", s.len());
    let dbg = format!("int dbg_{m}(lust_Formatter *f, {ct} *p)");
    let (proto, body) = match (g, k) {
        (Glue::Drop, SyncTy::OnceLock) => {
            let body = if needs_drop_c(p, e) {
                need(Glue::Drop, e);
                format!("if (p->st == 2) drop_{}(&p->v);", mangle(e))
            } else {
                "(void)p;".into()
            };
            (format!("void drop_{m}({ct} *p)"), body)
        }
        (Glue::Drop, _) => (format!("void drop_{m}({ct} *p)"), "(void)p;".into()),
        (Glue::Default, _) => (format!("{ct} default_{m}(void)"), format!("{ct} r; memset(&r, 0, sizeof r); return r;")),
        // `OnceLock(5)` or `OnceLock(<uninit>)` (a `format_args!`).
        (Glue::Debug, SyncTy::OnceLock) => {
            let v = super::fmt::fmt_expr(e, FmtKind::Debug, "w", "(&p->v)", need);
            (
                dbg,
                format!(
                    "lust_DebugTuple b; lust_fmt_slot s; lust_Formatter *w; lust_dtuple_new(&b, f, {}); if ((w = lust_dtuple_field(&b, &s))) lust_dtuple_field_end(&b, &s, lust_once_is_done(&p->st) ? {v} : lust_f_write_str(w, {})); return lust_dtuple_finish(&b);",
                    lit("OnceLock"),
                    lit("<uninit>")
                ),
            )
        }
        (Glue::Debug, SyncTy::BarrierWaitResult) => (
            dbg,
            format!(
                "lust_DebugStruct b; lust_fmt_slot s; lust_Formatter *w; lust_dstruct_new(&b, f, {}); if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, lust_f_bool(w, *p)); return lust_dstruct_finish(&b);",
                lit("BarrierWaitResult"),
                lit("is_leader")
            ),
        ),
        (Glue::Debug, _) => (
            dbg,
            format!("(void)p; lust_DebugStruct b; lust_dstruct_new(&b, f, {}); return lust_dstruct_finish_ne(&b);", lit(k.name())),
        ),
        _ => unreachable!("internal: no {g:?} glue for `{}`", k.name()),
    };
    let _ = writeln!(protos, "{proto};");
    let _ = writeln!(defs, "{proto} {{\n  {body}\n}}\n");
}

/// Glue of the channel ends and `SendError` (std's impls).
#[allow(clippy::too_many_arguments)]
fn chan_glue_def(p: &Program, g: Glue, k: SyncTy, e: &CTy, m: &str, ct: &str, protos: &mut String, defs: &mut String, need: &mut dyn FnMut(Glue, &CTy)) {
    let lit = |s: &str| format!("(lust_str){{(uint8_t*)\"{s}\", {}}}", s.len());
    let (proto, body) = match (g, k) {
        (Glue::Drop, SyncTy::Sender | SyncTy::SyncSender) => (format!("void drop_{m}({ct} *p)"), "lust_chan_drop_sender(*p);".to_string()),
        (Glue::Drop, SyncTy::Receiver) => (format!("void drop_{m}({ct} *p)"), "lust_chan_drop_receiver(*p);".to_string()),
        (Glue::Drop, _) => {
            let body = if needs_drop_c(p, e) {
                need(Glue::Drop, e);
                format!("drop_{}(p);", mangle(e))
            } else {
                "(void)p;".into()
            };
            (format!("void drop_{m}({ct} *p)"), body)
        }
        (Glue::Clone, SyncTy::Sender | SyncTy::SyncSender) => (format!("{ct} clone_{m}({ct} *p)"), "return lust_chan_clone_sender(*p);".to_string()),
        // `Sender { .. }`, `SyncSender { .. }`, `Receiver { .. }`, and
        // `SendError { .. }`.
        (Glue::Debug, _) => (
            format!("int dbg_{m}(lust_Formatter *f, {ct} *p)"),
            format!("(void)p; lust_DebugStruct b; lust_dstruct_new(&b, f, {}); return lust_dstruct_finish_ne(&b);", lit(k.name())),
        ),
        (Glue::Display, SyncTy::SendError) => {
            (format!("int disp_{m}(lust_Formatter *f, {ct} *p)"), format!("(void)p; return lust_f_pad(f, {});", lit("sending on a closed channel")))
        }
        _ => unreachable!("internal: no {g:?} glue for `{}`", k.name()),
    };
    let _ = writeln!(protos, "{proto};");
    let _ = writeln!(defs, "{proto} {{\n  {body}\n}}\n");
}

/// Glue of the thread types (std's impls): a `JoinHandle` drop detaches
/// its thread; `Thread` is counted; `ThreadId` prints `ThreadId(N)`.
fn thread_glue_def(g: Glue, k: SyncTy, m: &str, ct: &str, protos: &mut String, defs: &mut String) {
    let lit = |s: &str| format!("(lust_str){{(uint8_t*)\"{s}\", {}}}", s.len());
    let dbg = format!("int dbg_{m}(lust_Formatter *f, {ct} *p)");
    let (proto, body) = match (g, k) {
        (Glue::Drop, SyncTy::JoinHandle | SyncTy::ScopedJoinHandle) => (format!("void drop_{m}({ct} *p)"), "lust_join_drop(*p);".to_string()),
        (Glue::Drop, SyncTy::Thread) => (format!("void drop_{m}({ct} *p)"), "lust_thread_drop(*p);".to_string()),
        (Glue::Drop, _) => (format!("void drop_{m}({ct} *p)"), "(void)p;".to_string()),
        (Glue::Clone, SyncTy::Thread) => (format!("{ct} clone_{m}({ct} *p)"), "return lust_thread_clone(*p);".to_string()),
        (Glue::Clone, SyncTy::ThreadId) => (format!("{ct} clone_{m}({ct} *p)"), "return *p;".to_string()),
        (Glue::Eq, SyncTy::ThreadId) => (format!("uint8_t eq_{m}({ct} *a, {ct} *b)"), "return *a == *b;".to_string()),
        (Glue::Debug, SyncTy::ThreadId) => (
            dbg,
            format!(
                "lust_DebugTuple b; lust_fmt_slot s; lust_Formatter *w; lust_dtuple_new(&b, f, {}); if ((w = lust_dtuple_field(&b, &s))) lust_dtuple_field_end(&b, &s, lust_f_u64(w, *p)); return lust_dtuple_finish(&b);",
                lit("ThreadId")
            ),
        ),
        // `Thread { id: ThreadId(N), name: Some("main"), .. }`.
        (Glue::Debug, SyncTy::Thread) => (
            dbg,
            format!(
                "lust_DebugStruct b; lust_fmt_slot s; lust_Formatter *w; lust_dstruct_new(&b, f, {}); \
if ((w = lust_dstruct_field(&b, &s, {}))) {{ lust_DebugTuple b2; lust_fmt_slot s2; lust_Formatter *w2; lust_dtuple_new(&b2, w, {}); if ((w2 = lust_dtuple_field(&b2, &s2))) lust_dtuple_field_end(&b2, &s2, lust_f_u64(w2, (*p)->id)); lust_dstruct_field_end(&b, &s, lust_dtuple_finish(&b2)); }} \
if ((w = lust_dstruct_field(&b, &s, {}))) {{ int e; if ((*p)->name) {{ lust_DebugTuple b3; lust_fmt_slot s3; lust_Formatter *w3; lust_dtuple_new(&b3, w, {}); if ((w3 = lust_dtuple_field(&b3, &s3))) lust_dtuple_field_end(&b3, &s3, lust_f_dbg_str(w3, (lust_str){{(uint8_t*)(*p)->name, (*p)->name_len}})); e = lust_dtuple_finish(&b3); }} else e = lust_f_write_str(w, {}); lust_dstruct_field_end(&b, &s, e); }} \
return lust_dstruct_finish_ne(&b);",
                lit("Thread"),
                lit("id"),
                lit("ThreadId"),
                lit("name"),
                lit("Some"),
                lit("None")
            ),
        ),
        (Glue::Debug, SyncTy::JoinHandle | SyncTy::ScopedJoinHandle) => (
            dbg,
            format!("(void)p; lust_DebugStruct b; lust_dstruct_new(&b, f, {}); return lust_dstruct_finish_ne(&b);", lit(k.name())),
        ),
        (Glue::Debug, SyncTy::JoinError) => (
            dbg,
            format!("(void)p; lust_DebugStruct b; lust_dstruct_new(&b, f, {}); return lust_dstruct_finish_ne(&b);", lit("Any")),
        ),
        _ => unreachable!("internal: no {g:?} glue for `{}`", k.name()),
    };
    let _ = writeln!(protos, "{proto};");
    let _ = writeln!(defs, "{proto} {{\n  {body}\n}}\n");
}

/// Glue of the locks, their guards, and `PoisonError` (std's impls).
#[allow(clippy::too_many_arguments)]
fn lock_glue_def(p: &Program, g: Glue, k: SyncTy, e: &CTy, m: &str, ct: &str, protos: &mut String, defs: &mut String, need: &mut dyn FnMut(Glue, &CTy)) {
    let lit = |s: &str| format!("(lust_str){{(uint8_t*)\"{s}\", {}}}", s.len());
    let (proto, body) = match (g, k) {
        (Glue::Drop, SyncTy::Mutex | SyncTy::RwLock | SyncTy::PoisonError) => {
            let inner = if needs_drop_c(p, e) {
                need(Glue::Drop, e);
                let at = if k == SyncTy::PoisonError { "p" } else { "&p->v" };
                format!("drop_{}({at});", mangle(e))
            } else {
                "(void)p;".into()
            };
            (format!("void drop_{m}({ct} *p)"), inner)
        }
        // A guard gives its lock back (runtime/sync.c).
        (Glue::Drop, SyncTy::MutexGuard) => (format!("void drop_{m}({ct} *p)"), "lust_mutex_unlock(&(*p)->st);".into()),
        (Glue::Drop, SyncTy::RwLockReadGuard) => (format!("void drop_{m}({ct} *p)"), "lust_rw_read_unlock(&(*p)->st);".into()),
        (Glue::Drop, SyncTy::RwLockWriteGuard) => (format!("void drop_{m}({ct} *p)"), "lust_rw_write_unlock(&(*p)->st);".into()),
        (Glue::Default, SyncTy::Mutex | SyncTy::RwLock) => {
            need(Glue::Default, e);
            (format!("{ct} default_{m}(void)"), format!("{ct} r; memset(&r, 0, sizeof r); r.v = default_{}(); return r;", mangle(e)))
        }
        // `Mutex { data: .., poisoned: false, .. }`: std's try_lock (or
        // try_read); a held lock prints the str `"<locked>"` (Debug).
        (Glue::Debug, SyncTy::Mutex | SyncTy::RwLock) => {
            let (name, try_, unlock) =
                if k == SyncTy::Mutex { ("Mutex", "lust_mutex_trylock", "lust_mutex_unlock") } else { ("RwLock", "lust_rw_tryread", "lust_rw_read_unlock") };
            let v = super::fmt::fmt_expr(e, FmtKind::Debug, "w", "(&p->v)", need);
            let body = format!(
                "lust_DebugStruct b; lust_fmt_slot s; lust_Formatter *w; lust_dstruct_new(&b, f, {}); \
if ({try_}(&p->st)) {{ if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, {v}); {unlock}(&p->st); }} \
else if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, lust_f_dbg_str(w, {})); \
if ((w = lust_dstruct_field(&b, &s, {}))) lust_dstruct_field_end(&b, &s, lust_f_bool(w, 0)); return lust_dstruct_finish_ne(&b);",
                lit(name),
                lit("data"),
                lit("data"),
                lit("<locked>"),
                lit("poisoned")
            );
            (format!("int dbg_{m}(lust_Formatter *f, {ct} *p)"), body)
        }
        // A guard formats its value.
        (Glue::Debug | Glue::Display, _) if k.guard().is_some() => {
            let kind = if g == Glue::Debug { FmtKind::Debug } else { FmtKind::Display };
            let v = super::fmt::fmt_expr(e, kind, "f", "(&(*p)->v)", need);
            let name = if g == Glue::Debug { "dbg" } else { "disp" };
            (format!("int {name}_{m}(lust_Formatter *f, {ct} *p)"), format!("return {v};"))
        }
        (Glue::Debug, SyncTy::PoisonError) => (
            format!("int dbg_{m}(lust_Formatter *f, {ct} *p)"),
            format!("(void)p; lust_DebugStruct b; lust_dstruct_new(&b, f, {}); return lust_dstruct_finish_ne(&b);", lit("PoisonError")),
        ),
        (Glue::Display, SyncTy::PoisonError) => (
            format!("int disp_{m}(lust_Formatter *f, {ct} *p)"),
            format!("(void)p; return lust_f_pad(f, {});", lit("poisoned lock: another task failed inside")),
        ),
        _ => unreachable!("internal: no {g:?} glue for `{}`", k.name()),
    };
    let _ = writeln!(protos, "{proto};");
    let _ = writeln!(defs, "{proto} {{\n  {body}\n}}\n");
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
            S::ThreadSpawn | S::ScopeSpawn | S::ThreadScope => unreachable!("closure-taking thread calls go through thread_closure_call"),
            S::ThreadCurrent => "lust_thread_current()".into(),
            S::ThreadYieldNow => "(lust_thread_yield(), ((lust_Unit){}))".into(),
            S::ThreadPanicking => "((uint8_t)0)".into(),
            S::JoinHandleJoin => {
                // `Ok(value)`: the result sits right after the header.
                let el = match &tys[0] {
                    CTy::Sync(_, e) => (**e).clone(),
                    other => unreachable!("a JoinHandle operand, found {other:?}"),
                };
                let res = CTy::Result(Box::new(el.clone()), Box::new(CTy::Sync(SyncTy::JoinError, Box::new(CTy::Unit))));
                collect_types(&res, &mut self.sig_types);
                let (t, h) = (self.tmp(), self.tmp());
                let f = variant_field(self.p, &res, &t, 0, 0);
                let _ = writeln!(
                    self.out,
                    "    lust_JoinHdr *{h} = {}; lust_thread_join({h}); {} {t}; {} {f} = ((struct {{ lust_JoinHdr h; {} ret; }} *){h})->ret; lust_join_free({h});",
                    vals[0],
                    ctype(&res),
                    disc_set(self.p, &res, &t, 0),
                    ctype(&el)
                );
                t
            }
            S::JoinHandleThread => format!("(&(*{})->th)", vals[0]),
            S::JoinHandleIsFinished => format!("((uint8_t)lust_join_is_finished(*{}))", vals[0]),
            S::ThreadGetId => format!("((*{})->id)", vals[0]),
            S::ThreadGetName => {
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(CTy::Str))));
                collect_types(&opt, &mut self.sig_types);
                let (t, th) = (self.tmp(), self.tmp());
                let f = variant_field(self.p, &opt, &t, 1, 0);
                let _ = writeln!(
                    self.out,
                    "    lust_ThreadInfo *{th} = *{}; {} {t}; if ({th}->name) {{ {} {f} = (lust_str){{(uint8_t*){th}->name, {th}->name_len}}; }} else {{ {} }}",
                    vals[0],
                    ctype(&opt),
                    disc_set(self.p, &opt, &t, 1),
                    disc_set(self.p, &opt, &t, 0)
                );
                t
            }
            S::Channel | S::SyncChannel => unreachable!("channel calls go through channel_new"),
            S::ChanSend => {
                let el = match deref_cty(&tys[0]) {
                    CTy::Sync(_, e) => *e,
                    other => unreachable!("a Sender operand, found {other:?}"),
                };
                let res = CTy::Result(Box::new(CTy::Unit), Box::new(CTy::Sync(SyncTy::SendError, Box::new(el.clone()))));
                collect_types(&res, &mut self.sig_types);
                let (t, v) = (self.tmp(), self.tmp());
                let err = variant_field(self.p, &res, &t, 1, 0);
                let _ = writeln!(
                    self.out,
                    "    {} {v} = {}; {} {t}; if (lust_chan_send(*{}, &{v})) {{ {} {err} = {v}; }} else {{ {} }}",
                    ctype(&el),
                    vals[1],
                    ctype(&res),
                    vals[0],
                    disc_set(self.p, &res, &t, 1),
                    disc_set(self.p, &res, &t, 0)
                );
                t
            }
            S::ChanRecv | S::ChanTryRecv => {
                let el = match deref_cty(&tys[0]) {
                    CTy::Sync(_, e) => *e,
                    other => unreachable!("a Receiver operand, found {other:?}"),
                };
                let def = if op == S::ChanRecv { crate::check::generics::recv_error_def() } else { crate::check::generics::try_recv_error_def() };
                let et = self.p.tys.local_adt_of(def).map_or(CTy::Unit, CTy::Adt);
                let res = CTy::Result(Box::new(el.clone()), Box::new(et.clone()));
                collect_types(&res, &mut self.sig_types);
                let (t, r) = (self.tmp(), self.tmp());
                let ok = variant_field(self.p, &res, &t, 0, 0);
                let err = variant_field(self.p, &res, &t, 1, 0);
                // try_recv: 1 is `Empty` (variant 0), 2 `Disconnected`.
                let err_val = if op == S::ChanRecv {
                    format!("memset(&{err}, 0, sizeof({err}));")
                } else {
                    format!("memset(&{err}, 0, sizeof({err})); if ({r} == 2) {{ {} }} else {{ {} }}", disc_set(self.p, &et, &err, 1), disc_set(self.p, &et, &err, 0))
                };
                let _ = writeln!(
                    self.out,
                    "    {} {t}; int {r} = lust_chan_recv(*{}, &{ok}, {}); if ({r} == 0) {{ {} }} else {{ {} {err_val} }}",
                    ctype(&res),
                    vals[0],
                    u8::from(op == S::ChanRecv),
                    disc_set(self.p, &res, &t, 0),
                    disc_set(self.p, &res, &t, 1)
                );
                t
            }
            _ => self.lock_builtin(op, vals, tys),
        }
    }

    /// `mpsc::channel()` or `sync_channel(cap)` into the C pair type
    /// `pair` (`(Sender<T>, Receiver<T>)`): one runtime channel that both
    /// ends point at, with `T`'s drop glue for values left queued.
    pub(super) fn channel_new(&mut self, pair: &CTy, cap: &str) -> String {
        let el = match pair {
            CTy::Tuple(es) => match es.first() {
                Some(CTy::Sync(_, e)) => (**e).clone(),
                _ => CTy::Unit,
            },
            _ => CTy::Unit,
        };
        collect_types(pair, &mut self.sig_types);
        let drop = if needs_drop_c(self.p, &el) {
            self.want(Glue::Drop, &el);
            format!("(void (*)(void *))drop_{}", mangle(&el))
        } else {
            "0".into()
        };
        let (t, c) = (self.tmp(), self.tmp());
        let _ = writeln!(
            self.out,
            "    lust_Chan *{c} = lust_chan_new(sizeof({0}), _Alignof({0}), {cap}, {drop}); {1} {t}; {t}.f0 = {c}; {t}.f1 = {c};",
            ctype(&el),
            ctype(pair)
        );
        t
    }

    /// `cv.wait_while(guard, f)`: waits while `f(&mut *guard)` holds; and
    /// `once.get_or_init(f)`: runs `f` only in the call that sets the
    /// value (a closure that never runs still drops its env).
    fn closure_wait_or_init(&mut self, op: SyncOp, ops: &[Operand], ci: usize, loc: &str, post: &mut Vec<String>) -> String {
        let (body_fn, once) = self.closure_of(&ops[ci]);
        let target = self.operand(&ops[0], loc, post).0;
        let guard = (op == SyncOp::CondvarWaitWhile).then(|| self.operand(&ops[1], loc, post));
        let (env, env_ty) = self.operand(&ops[ci], loc, post);
        collect_types(&env_ty, &mut self.sig_types);
        let ev = self.tmp();
        let _ = writeln!(self.out, "    {} {ev} = {env};", ctype(&env_ty));
        let arg = if once { ev.clone() } else { format!("&{ev}") };
        let drop_env = if needs_drop_c(self.p, &env_ty) {
            self.want(Glue::Drop, &env_ty);
            format!("drop_{}(&{ev});", mangle(&env_ty))
        } else {
            String::new()
        };
        let mut body = String::new();
        if let Some((g, gt)) = guard {
            let (r, _) = self.closure_call_c(&mut body, body_fn, &arg, &[format!("&({g})->v")]);
            let _ = writeln!(body, "  if (!{r}) break; lust_cv_wait({target}, &({g})->st);");
            let _ = writeln!(self.out, "    for (;;) {{\n{body}    }}\n    {drop_env}");
            let res = CTy::Result(Box::new(gt.clone()), Box::new(CTy::Sync(SyncTy::PoisonError, Box::new(gt))));
            collect_types(&res, &mut self.sig_types);
            let t = self.tmp();
            let f = variant_field(self.p, &res, &t, 0, 0);
            let _ = writeln!(self.out, "    {} {t}; {} {f} = {g};", ctype(&res), disc_set(self.p, &res, &t, 0));
            return t;
        }
        let (v, _) = self.closure_call_c(&mut body, body_fn, &arg, &[]);
        let after = if once { String::new() } else { drop_env.clone() };
        let _ = writeln!(
            self.out,
            "    if (lust_once_begin(&({target})->st)) {{\n{body}  ({target})->v = {v}; lust_once_finish(&({target})->st); {after}\n    }} else {{ {drop_env} }}"
        );
        format!("(&({target})->v)")
    }

    /// The closure body fn and FnOnce-ness of a closure operand.
    fn closure_of(&self, o: &Operand) -> (LocalDefId, bool) {
        let (Operand::Move(pl) | Operand::Copy(pl)) = o else { panic!("internal: a thread call takes a closure value") };
        let mut t = self.body.locals[pl.local as usize].ty;
        for pr in &pl.proj {
            t = match (self.body.tys.kind(t), pr) {
                (TyKind::Ref(_, _, i), Proj::Deref) => i,
                _ => panic!("internal: a thread closure place with projections"),
            };
        }
        let TyKind::Closure(def, _) = self.body.tys.kind(t) else { panic!("internal: a thread call takes a closure value") };
        let entry = &self.p.gx.closures[&def];
        (entry.body_fn, entry.kind == crate::check::closure::ClosureKind::FnOnce)
    }

    /// The thread calls that take a closure: `thread::spawn(f)` and
    /// `scope.spawn(f)` build a packet { header, result, closure env } on
    /// the heap and a trampoline (in this fn's prelude) that calls the
    /// closure's body on the new thread and stores its result;
    /// `thread::scope(f)` calls the closure on a fresh scope here, then
    /// waits for every packet of the scope.
    pub(super) fn thread_closure_call(&mut self, op: SyncOp, ops: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        let ci = match op {
            SyncOp::ScopeSpawn | SyncOp::OnceGetOrInit => 1,
            SyncOp::CondvarWaitWhile => 2,
            _ => 0,
        };
        if matches!(op, SyncOp::CondvarWaitWhile | SyncOp::OnceGetOrInit) {
            return self.closure_wait_or_init(op, ops, ci, loc, post);
        }
        let (body_fn, once) = self.closure_of(&ops[ci]);
        let scope = if op == SyncOp::ScopeSpawn { self.operand(&ops[0], loc, post).0 } else { "0".into() };
        let (env, env_ty) = self.operand(&ops[ci], loc, post);
        collect_types(&env_ty, &mut self.sig_types);
        let ret = cty(&self.p.tys, self.p.fn_info(body_fn).ret);
        collect_types(&ret, &mut self.sig_types);
        let drop_env = |this: &mut Self, out: &mut String, e: &str| {
            if !once && needs_drop_c(this.p, &env_ty) {
                this.want(Glue::Drop, &env_ty);
                let _ = writeln!(out, "  drop_{}(&{e});", mangle(&env_ty));
            }
        };
        if op == SyncOp::ThreadScope {
            let (sc, ev) = (self.tmp(), self.tmp());
            let _ = writeln!(self.out, "    lust_Scope {sc}; {sc}.live = 0; {} {ev} = {env};", ctype(&env_ty));
            let arg = if once { ev.clone() } else { format!("&{ev}") };
            let mut call = String::new();
            let (v, _) = self.closure_call_c(&mut call, body_fn, &arg, &[format!("&{sc}")]);
            drop_env(self, &mut call, &ev);
            let _ = writeln!(call, "  lust_scope_wait(&{sc});");
            self.out.push_str(&call);
            return v;
        }
        let pk = format!("struct {{ lust_JoinHdr h; {} ret; {} env; }}", ctype(&ret), ctype(&env_ty));
        let n = self.adapters;
        self.adapters += 1;
        let slot = self.slots[self.body.fn_id.0 as usize];
        let (run, drop) = (format!("lust_thr_{slot}_{n}"), format!("lust_thrdrop_{slot}_{n}"));
        let mut body = String::new();
        let arg = if once { "k->env".to_string() } else { "&k->env".to_string() };
        let (v, _) = self.closure_call_c(&mut body, body_fn, &arg, &[]);
        let _ = writeln!(body, "  k->ret = {v};");
        drop_env(self, &mut body, "k->env");
        let drop_ret = if needs_drop_c(self.p, &ret) {
            self.want(Glue::Drop, &ret);
            format!("drop_{}(&(({pk} *)hp)->ret);", mangle(&ret))
        } else {
            "(void)hp;".into()
        };
        let _ = writeln!(self.prelude, "static void {run}(lust_JoinHdr *hp) {{\n  {pk} *k = ({pk} *)hp;\n{body}}}");
        let _ = writeln!(self.prelude, "static void {drop}(lust_JoinHdr *hp) {{ {drop_ret} }}");
        let h = self.tmp();
        let _ = writeln!(
            self.out,
            "    {pk} *{h} = ({pk} *)lust_alloc(sizeof({pk}), _Alignof({pk})); {h}->h.run = {run}; {h}->h.drop_ret = {drop}; {h}->h.scope = {scope}; {h}->env = {env}; lust_thread_spawn(&{h}->h, {loc});"
        );
        format!("(&{h}->h)")
    }

    /// The lock calls: `Mutex` and `RwLock` (over the runtime's futex
    /// locks) and `PoisonError`'s accessors. No lock is ever poisoned
    /// (a panic aborts), so every `LockResult` is `Ok`.
    fn lock_builtin(&mut self, op: SyncOp, vals: &[String], tys: &[CTy]) -> String {
        use SyncOp as S;
        let (k, elem) = match op {
            S::LockNew(k) | S::LockFrom(k) => (k, tys[0].clone()),
            S::LockDefault(_) | S::PoisonNew | S::SyncNew(_) => (SyncTy::PoisonError, CTy::Unit),
            _ => match deref_cty(&tys[0]) {
                CTy::Sync(k, e) => (k, *e),
                other => unreachable!("a lock operand, found {other:?}"),
            },
        };
        // `Ok(v)` of a `LockResult<V>` (a `Result<V, V>` in C).
        let ok = |this: &mut Self, v_ty: CTy, v: String| -> String {
            let res = CTy::Result(Box::new(v_ty.clone()), Box::new(CTy::Sync(SyncTy::PoisonError, Box::new(v_ty))));
            collect_types(&res, &mut this.sig_types);
            let t = this.tmp();
            let f = variant_field(this.p, &res, &t, 0, 0);
            let _ = writeln!(this.out, "    {} {t}; {} {f} = {v};", ctype(&res), disc_set(this.p, &res, &t, 0));
            t
        };
        match op {
            S::LockNew(_) | S::LockFrom(_) => {
                let lock = CTy::Sync(k, Box::new(elem));
                collect_types(&lock, &mut self.sig_types);
                let t = self.tmp();
                let set = if k == SyncTy::OnceLock { format!(" {t}.st = 2;") } else { String::new() };
                let _ = writeln!(self.out, "    {} {t}; memset(&{t}, 0, sizeof {t}); {t}.v = {};{set}", ctype(&lock), vals[0]);
                t
            }
            S::LockDefault(_) => unreachable!("LockDefault calls the Default glue"),
            S::MutexLock | S::RwLockRead | S::RwLockWrite => {
                let (gk, call) = match op {
                    S::MutexLock => (SyncTy::MutexGuard, "lust_mutex_lock"),
                    S::RwLockRead => (SyncTy::RwLockReadGuard, "lust_rw_read"),
                    _ => (SyncTy::RwLockWriteGuard, "lust_rw_write"),
                };
                let g = self.tmp();
                let guard = CTy::Sync(gk, Box::new(elem.clone()));
                let _ = writeln!(self.out, "    {} {g} = {}; {call}(&{g}->st);", ctype(&guard), vals[0]);
                ok(self, guard, g)
            }
            S::LockGetMut => {
                let r = CTy::Ref(Box::new(elem.clone()));
                ok(self, r, format!("(&({})->v)", vals[0]))
            }
            S::LockIntoInner => ok(self, elem, format!("({}).v", vals[0])),
            S::LockIsPoisoned => format!("((void){}, (uint8_t)0)", vals[0]),
            S::LockClearPoison => format!("((void){}, ((lust_Unit){{}}))", vals[0]),
            S::PoisonNew => vals[0].clone(),
            S::SyncNew(SyncTy::Barrier) => format!("((lust_Barrier){{0, 0, 0, 0, {}}})", vals[0]),
            S::SyncNew(_) => "((uint32_t)0)".into(),
            S::CondvarWait => {
                let guard = tys[1].clone();
                let _ = writeln!(self.out, "    lust_cv_wait({}, &({})->st);", vals[0], vals[1]);
                ok(self, guard, vals[1].clone())
            }
            S::CondvarNotifyOne | S::CondvarNotifyAll => format!("(lust_cv_notify({}, {}), ((lust_Unit){{}}))", vals[0], u8::from(op == S::CondvarNotifyAll)),
            S::BarrierWait => format!("((uint8_t)lust_barrier_wait({}))", vals[0]),
            S::BarrierIsLeader => format!("(*{})", vals[0]),
            S::OnceGet | S::OnceGetMut => {
                let opt = CTy::Option(Box::new(CTy::Ref(Box::new(elem.clone()))));
                collect_types(&opt, &mut self.sig_types);
                let t = self.tmp();
                let f = variant_field(self.p, &opt, &t, 1, 0);
                let o = &vals[0];
                let _ = writeln!(
                    self.out,
                    "    {} {t}; if (lust_once_is_done(&({o})->st)) {{ {} {f} = &({o})->v; }} else {{ {} }}",
                    ctype(&opt),
                    disc_set(self.p, &opt, &t, 1),
                    disc_set(self.p, &opt, &t, 0),
                );
                t
            }
            S::OnceSet => {
                let res = CTy::Result(Box::new(CTy::Unit), Box::new(elem.clone()));
                collect_types(&res, &mut self.sig_types);
                let (t, v) = (self.tmp(), self.tmp());
                let err = variant_field(self.p, &res, &t, 1, 0);
                let o = &vals[0];
                let _ = writeln!(
                    self.out,
                    "    {} {v} = {}; {} {t}; if (lust_once_begin(&({o})->st)) {{ ({o})->v = {v}; lust_once_finish(&({o})->st); {} }} else {{ {} {err} = {v}; }}",
                    ctype(&elem),
                    vals[1],
                    ctype(&res),
                    disc_set(self.p, &res, &t, 0),
                    disc_set(self.p, &res, &t, 1),
                );
                t
            }
            S::OnceIntoInner | S::OnceTake => {
                let opt = CTy::Option(Box::new(elem.clone()));
                collect_types(&opt, &mut self.sig_types);
                let (t, o) = (self.tmp(), self.tmp());
                let f = variant_field(self.p, &opt, &t, 1, 0);
                let (decl, reset) = if op == S::OnceTake {
                    (format!("{} *{o} = {};", ctype(&tys[0]).trim_end_matches('*'), vals[0]), format!(" {o}->st = 0;"))
                } else {
                    (format!("{0} {o}_v = {1}; {0} *{o} = &{o}_v;", ctype(&tys[0]), vals[0]), String::new())
                };
                let _ = writeln!(
                    self.out,
                    "    {decl} {} {t}; if ({o}->st == 2) {{ {} {f} = {o}->v;{reset} }} else {{ {} }}",
                    ctype(&opt),
                    disc_set(self.p, &opt, &t, 1),
                    disc_set(self.p, &opt, &t, 0),
                );
                t
            }
            S::PoisonIntoInner => vals[0].clone(),
            S::PoisonGetRef | S::PoisonGetMut => vals[0].clone(),
            _ => unreachable!("lock_builtin takes the lock ops"),
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
