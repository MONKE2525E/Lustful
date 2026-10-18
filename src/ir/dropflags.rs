// Static drop flags: rustc's drop elaboration, for whole locals. Codegen gives a local whose type
// needs drop a flag `d{l}` that says whether it still owns a value: a move of the whole local
// clears it, an assignment to the whole local sets it, and each `Drop` (at scope exit or in a
// cleanup path) and each assignment's drop of the old value tests it. Most of those tests see the
// same value on every path that reaches them; this pass finds them, so codegen gives such a flag
// no storage, never stores it, and drops there unconditionally or not at all. Only flags whose
// value at some test depends on the path stay runtime flags. cgen and the LLVM backend both read
// the result; the LLVM backend's default leaves it off (`cgen::static_drop_flags`).
//
// A forward dataflow over the body's blocks and their call and statement unwind edges, with
// cgen's flag rules (`FnGen::operand`, `drop_old_value`, `emit_assign`, `StmtKind::Drop`):
//   - a parameter's flag starts set, every other flag clear;
//   - an assignment clears the flags of the whole locals its value moves, at its end; a call
//     clears its moved arguments before it runs, so its unwind edge sees them clear; a branch,
//     a print and a panic message read their operands and clear nothing;
//   - an assignment to a whole local tests its flag after the statement's moves (the old value
//     drops if set) and then sets it; a call does that on its normal edge only;
//   - a `Drop` tests the flag, then clears it before the drop runs.
// A statement's or call's unwind edge carries every state a panic inside it can leave: its start
// (when making the value or an indexed destination's place can panic), after its moves, and with
// its destination's flag clear for the old value's drop. That covers both unwinding modes (with
// unwind tables a panic leaves from inside the statement; with flags, from the check after the
// call that panicked).
// Move flags (`m{l}_{k}`, partial moves) are not changed here.
use std::collections::HashMap;

use super::{Body, Local, Operand, Place, Proj, Rvalue, StmtKind, Terminator, rvalue_moves};

/// No path reaches here yet; the flag is clear; set; or either, depending on the path.
const NONE: u8 = 0;
const CLEAR: u8 = 1;
const SET: u8 = 2;
const DYN: u8 = 3;

fn meet(a: u8, b: u8) -> u8 {
    if a == NONE || a == b {
        b
    } else if b == NONE {
        a
    } else {
        DYN
    }
}

/// What codegen needs to know about one body's whole-local drop flags.
pub struct DropFlags {
    /// Per local: its flag stays a runtime flag (a test sees a value that depends on the path).
    /// A local with no flag counts as kept: codegen treats it as before this pass.
    dynamic: Vec<bool>,
    /// For a local whose flag is static: the local tested at (block, statement index) and the
    /// value its test sees. An index equal to the block's statement count names its `Call`
    /// terminator.
    tests: HashMap<(u32, u32), (Local, bool)>,
}

impl DropFlags {
    /// Every flag a runtime flag: codegen as before this pass (`LUST_DROPFLAGS=0`).
    pub fn all_runtime(n_locals: usize) -> DropFlags {
        DropFlags { dynamic: vec![true; n_locals], tests: HashMap::new() }
    }

    /// The local keeps a runtime flag (codegen declares, stores and tests `d{l}`).
    pub fn keeps(&self, l: Local) -> bool {
        self.dynamic.get(l as usize).copied().unwrap_or(true)
    }

    /// The value the test of a static flag at (block, statement index) sees: true drops, false
    /// does not. None for a runtime flag.
    pub fn test(&self, at: (u32, u32), l: Local) -> Option<bool> {
        if self.keeps(l) {
            return None;
        }
        match self.tests.get(&at) {
            Some(&(t, v)) if t == l => Some(v),
            _ => panic!("drop flag of l{l} tested at {at:?} with no static value"),
        }
    }
}

/// The drop flags of `body`. `flagged[l]`: codegen gives local `l` a flag (its type needs drop).
pub fn analyze(body: &Body, flagged: &[bool]) -> DropFlags {
    let n = body.locals.len();
    let mut idx = vec![usize::MAX; n];
    let mut m = 0;
    for (l, slot) in idx.iter_mut().enumerate() {
        if flagged.get(l).copied().unwrap_or(false) {
            *slot = m;
            m += 1;
        }
    }
    if m == 0 || body.blocks.is_empty() {
        return DropFlags::all_runtime(n);
    }
    let whole = |p: &Place| if p.proj.is_empty() { idx.get(p.local as usize).copied().filter(|&k| k != usize::MAX) } else { None };
    let clear_moves = |s: &mut [u8], moved: &[&Place]| {
        for p in moved {
            if let Some(k) = whole(p) {
                s[k] = CLEAR;
            }
        }
    };
    let operand_clear = |s: &mut [u8], o: &Operand| {
        if let Operand::Move(p) = o
            && let Some(k) = whole(p)
        {
            s[k] = CLEAR;
        }
    };
    let meet_all = |a: &[u8], b: &[u8]| a.iter().zip(b).map(|(&x, &y)| meet(x, y)).collect::<Vec<u8>>();
    let unw: HashMap<(u32, u32), usize> = body.stmt_unwind.iter().map(|&(b, i, u)| ((b.0, i), u.0 as usize)).collect();
    let nb = body.blocks.len();
    let mut entry: Vec<Option<Vec<u8>>> = vec![None; nb];
    let mut init = vec![CLEAR; m];
    for l in 1..=body.arg_count.min(n.saturating_sub(1)) {
        if idx[l] != usize::MAX {
            init[idx[l]] = SET;
        }
    }
    entry[0] = Some(init);
    let mut work = vec![0usize];
    let mut queued = vec![false; nb];
    queued[0] = true;
    // (block, statement index) -> (tested local, value seen), from each block's last visit.
    let mut tests: HashMap<(u32, u32), (Local, u8)> = HashMap::new();
    while let Some(b) = work.pop() {
        queued[b] = false;
        let mut s = entry[b].clone().expect("queued blocks have a state");
        let block = &body.blocks[b];
        let mut outs: Vec<(usize, Vec<u8>)> = Vec::new();
        for (si, st) in block.stmts.iter().enumerate() {
            let edge = unw.get(&(b as u32, si as u32)).copied();
            match &st.kind {
                StmtKind::Assign(dest, rv) => {
                    let before = edge.map(|_| s.clone());
                    let mut moved = Vec::new();
                    rvalue_moves(rv, &mut moved);
                    clear_moves(&mut s, &moved);
                    let d = whole(dest);
                    if let Some(k) = d {
                        tests.insert((b as u32, si as u32), (dest.local, s[k]));
                    }
                    if let (Some(u), Some(before)) = (edge, before) {
                        // Where a panic inside can leave: while the value or an indexed
                        // destination's place is made (only when that can panic), else after the
                        // moves; the old value's drop panics with the destination's flag already
                        // clear.
                        let mut e = if may_panic_before_moves(dest, rv) { meet_all(&before, &s) } else { s.clone() };
                        if let Some(k) = d {
                            e[k] = meet(e[k], CLEAR);
                        }
                        outs.push((u, e));
                    }
                    if let Some(k) = d {
                        s[k] = SET;
                    }
                }
                StmtKind::Drop(l) => {
                    if let Some(k) = whole(&Place::local(*l)) {
                        tests.insert((b as u32, si as u32), (*l, s[k]));
                        s[k] = CLEAR;
                    }
                    if let Some(u) = edge {
                        outs.push((u, s.clone()));
                    }
                }
                // A print reads its arguments; like a branch and a panic, it clears no flag.
                StmtKind::Print { .. } | StmtKind::StorageDead(_) | StmtKind::FakeRead(_) => {
                    if let Some(u) = edge {
                        outs.push((u, s.clone()));
                    }
                }
            }
        }
        let nst = block.stmts.len() as u32;
        // A terminator's cleanup entry (a panic message's; a call has its own unwind
        // successor, which codegen uses instead): no flag changes before it can panic.
        if let Some(&u) = unw.get(&(b as u32, nst)) {
            outs.push((u, s.clone()));
        }
        match &block.term {
            Terminator::Goto(t) => outs.push((t.0 as usize, s)),
            // A branch on a moved operand clears no flag (cgen emits no moves for it).
            Terminator::If(_, a, c) => {
                outs.push((a.0 as usize, s.clone()));
                outs.push((c.0 as usize, s));
            }
            Terminator::Switch(_, cases, other) => {
                for (_, t) in cases {
                    outs.push((t.0 as usize, s.clone()));
                }
                outs.push((other.0 as usize, s));
            }
            Terminator::Call { args, dest, next, unwind, .. } => {
                for a in args {
                    operand_clear(&mut s, a);
                }
                if let Some(u) = unwind {
                    // The old value's drop after the call panics to the same cleanup, with the
                    // destination's flag already clear.
                    let mut e = s.clone();
                    if let Some(k) = whole(dest) {
                        e[k] = meet(e[k], CLEAR);
                    }
                    outs.push((u.0 as usize, e));
                }
                if let Some(k) = whole(dest) {
                    tests.insert((b as u32, nst), (dest.local, s[k]));
                    s[k] = SET;
                }
                outs.push((next.0 as usize, s));
            }
            Terminator::Panic(_) | Terminator::Return | Terminator::Unreachable => {}
        }
        for (t, st) in outs {
            let grew = match &mut entry[t] {
                Some(e) => {
                    let mut changed = false;
                    for (x, &y) in e.iter_mut().zip(&st) {
                        let v = meet(*x, y);
                        changed |= v != *x;
                        *x = v;
                    }
                    changed
                }
                None => {
                    entry[t] = Some(st);
                    true
                }
            };
            if grew && !queued[t] {
                queued[t] = true;
                work.push(t);
            }
        }
    }
    let mut dynamic: Vec<bool> = idx.iter().map(|&k| k == usize::MAX).collect();
    for &(l, v) in tests.values() {
        if v == DYN || v == NONE {
            dynamic[l as usize] = true;
        }
    }
    let tests = tests.into_iter().filter(|(_, (l, _))| !dynamic[*l as usize]).map(|(at, (l, v))| (at, (l, v == SET))).collect();
    DropFlags { dynamic, tests }
}

/// Whether an assignment of `rv` to `dest` can panic before its moves are done: an indexed
/// destination's bounds check, or making the value (lowering's `may_unwind` rule for an
/// rvalue: moves, borrows and value building of plain operands with no indexed place cannot).
fn may_panic_before_moves(dest: &Place, rv: &Rvalue) -> bool {
    let indexed = |pl: &Place| pl.proj.iter().any(|p| matches!(p, Proj::Index(_)));
    let op_indexed = |o: &Operand| matches!(o, Operand::Copy(pl) | Operand::Move(pl) if indexed(pl));
    if indexed(dest) {
        return true;
    }
    match rv {
        Rvalue::Use(o) | Rvalue::Opt(_, Some(o)) | Rvalue::Res(_, _, o) => op_indexed(o),
        Rvalue::Ref(_, pl) | Rvalue::Discriminant(pl) | Rvalue::SliceOf(pl) | Rvalue::LenOf(pl) => indexed(pl),
        Rvalue::Aggregate(_, _, os) | Rvalue::TupleAgg(_, os) | Rvalue::ArrayAgg(_, os) => os.iter().any(op_indexed),
        Rvalue::Opt(_, None) | Rvalue::StaticRef(_) | Rvalue::FnValue(..) | Rvalue::ItemShim(..) => false,
        Rvalue::MakeDyn { ptr, .. } | Rvalue::DynUpcast { ptr, .. } | Rvalue::DynMeta { ptr, .. } | Rvalue::DynData { ptr, .. } => {
            op_indexed(ptr)
        }
        _ => true,
    }
}
