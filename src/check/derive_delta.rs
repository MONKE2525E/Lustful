// Derive reads (PLAN R12, package P3). A derive list answers many
// questions a body check asks without naming the Adt: is `(A, u8)` Copy,
// can `Option<A>` be cloned, does `A == A` have glue, does a `#[derive]`
// impl select. Every reader notes the Adt's template def in a per-thread
// log while a scope is open: `Program::derives_of` (the only way to read
// a derive list), and the trait index when it hands out a derived impl
// record (traits/index.rs `get`). Each body check (and its lowering and
// borrowck) runs inside a scope and stores one `ReadKey::Derives` read
// per noted def, so a derive edit rechecks the bodies that asked
// (driver/graph.rs). Trait selection records the same read for its Self
// head (`Program::impl_set`), which covers a derive the Adt lacks.
//
// The log is per thread because the walkers that read derives (is_copy,
// glue_*, has_default, ...) take no read sink, and body checks run in
// parallel. Outside a scope (collect's own passes, a one-shot compile)
// a note costs one thread-local load.
use crate::check::collect::Program;
use crate::def::DefId;
use crate::driver::graph::Reads;
use crate::ty::AdtId;
use std::cell::{Cell, RefCell};

thread_local! {
    /// Open scopes on this thread; zero means nothing is logged.
    static DEPTH: Cell<u32> = const { Cell::new(0) };
    /// The defs noted since the outermost scope opened, with repeats.
    static LOG: RefCell<Vec<DefId>> = const { RefCell::new(Vec::new()) };
}

/// True while a scope is open on this thread.
fn open() -> bool {
    DEPTH.with(Cell::get) != 0
}

/// Notes a read of the derive list of the Adt template `def`.
pub(crate) fn note_def(def: DefId) {
    if !open() {
        return;
    }
    LOG.with(|l| {
        let mut l = l.borrow_mut();
        if l.last() != Some(&def) {
            l.push(def);
        }
    });
}

/// Notes a read of the derive list of Adt `a` (its template's, for an
/// instance). Called by `Program::derives_of`.
pub(crate) fn note(p: &Program, a: AdtId) {
    if open()
        && let Some(def) = p.derive_def(a)
    {
        note_def(def);
    }
}

/// Runs `f` with the derive log open and returns the Adts it noted
/// (sorted, no repeats). Scopes nest: an inner scope's notes also count
/// for every outer scope (a closure body checks as its parent; a body
/// check runs inside the driver's per-body scope). With `on` false (a
/// sink nobody replays) `f` runs with no scope and nothing is noted.
pub(crate) fn scoped<R>(on: bool, f: impl FnOnce() -> R) -> (R, Vec<DefId>) {
    if !on {
        return (f(), Vec::new());
    }
    let start = LOG.with(|l| l.borrow().len());
    DEPTH.with(|d| d.set(d.get() + 1));
    // The guard closes the scope on unwind too (a checker panic caught
    // by the daemon must not leave this thread logging).
    struct Close;
    impl Drop for Close {
        fn drop(&mut self) {
            let depth = DEPTH.with(|d| {
                d.set(d.get() - 1);
                d.get()
            });
            if depth == 0 {
                LOG.with(|l| l.borrow_mut().clear());
            }
        }
    }
    let close = Close;
    let out = f();
    let mut noted = LOG.with(|l| l.borrow()[start..].to_vec());
    drop(close);
    noted.sort_unstable_by_key(|d| (d.krate.0, d.hash.0));
    noted.dedup();
    (out, noted)
}

/// Records one `Derives` read per noted def into `reads`.
pub(crate) fn record(p: &Program, reads: &mut Reads, noted: &[DefId]) {
    for &def in noted {
        p.record_derives(reads, def);
    }
}
