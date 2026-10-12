// Borrow checking on the IR, one function at a time.
//
// 1. Initialization: forward dataflow of maybe-init and maybe-moved locals. Moves are
//    tracked per field path, so moving `p.x` leaves `p.y` usable (a partial move).
// 2. Loans: each `&place` creates a loan. Forward dataflow tracks which locals may hold
//    which loans, and (for lifetime checks at returns and parameter stores) every loan a
//    local was ever assigned, because a local has one fixed lifetime.
// 3. Liveness: backward dataflow. A loan is live where some live local may hold it. A
//    loan that flows into a return value or behind a parameter is also live at every
//    point reachable from the borrow, as in rustc's NLL (this rejects problem case 3,
//    which Polonius would accept).
// 4. Each access is checked against the live loans it conflicts with.
use crate::check::Builtin;
use crate::check::collect::*;
use crate::diag::{Diag, Span, unsupported};
use crate::ir::*;
use crate::ty::*;
use std::collections::HashSet;

/// A bitset over locals or loans. Most bodies fit in one word, and that word
/// is stored inline: dataflow clones these sets per block (two per local in
/// every `State`), so a heap allocation per set showed up once calls became
/// terminators and block counts grew.
#[derive(Clone, PartialEq, Eq)]
struct BitSet(Words);

#[derive(Clone, PartialEq, Eq)]
enum Words {
    One(u64),
    Many(Vec<u64>),
}

impl BitSet {
    fn new(n: usize) -> BitSet {
        let w = n.div_ceil(64).max(1);
        BitSet(if w == 1 { Words::One(0) } else { Words::Many(vec![0; w]) })
    }
    fn words(&self) -> &[u64] {
        match &self.0 {
            Words::One(w) => std::slice::from_ref(w),
            Words::Many(v) => v,
        }
    }
    fn words_mut(&mut self) -> &mut [u64] {
        match &mut self.0 {
            Words::One(w) => std::slice::from_mut(w),
            Words::Many(v) => v,
        }
    }
    fn insert(&mut self, i: usize) {
        self.words_mut()[i / 64] |= 1 << (i % 64);
    }
    fn remove(&mut self, i: usize) {
        self.words_mut()[i / 64] &= !(1 << (i % 64));
    }
    fn contains(&self, i: usize) -> bool {
        self.words()[i / 64] & (1 << (i % 64)) != 0
    }
    fn union(&mut self, o: &BitSet) -> bool {
        let mut changed = false;
        for (a, b) in self.words_mut().iter_mut().zip(o.words()) {
            let n = *a | b;
            changed |= n != *a;
            *a = n;
        }
        changed
    }
    fn clear(&mut self) {
        self.words_mut().iter_mut().for_each(|w| *w = 0);
    }
    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.words().iter().enumerate().flat_map(|(wi, &w)| (0..64).filter(move |b| w & (1 << b) != 0).map(move |b| wi * 64 + b))
    }
    fn is_empty(&self) -> bool {
        self.words().iter().all(|&w| w == 0)
    }
}

struct Loan {
    place: Place,
    mutable: bool,
    /// Stands for "whatever a reference parameter points to". Only used for return checks.
    synthetic: bool,
    /// Where the borrow starts. Used as a labeled secondary span in diagnostics.
    span: Span,
    /// The last use of the local that first holds this loan, if it is after the borrow.
    last_use: Option<Span>,
}

/// One field path below a local, as encoded projections (`Field`/`Downcast`). An empty path
/// is the whole local. Used to track partial moves per field.
type Path = Vec<u64>;

fn encode_proj(p: &Proj) -> Option<u64> {
    match p {
        Proj::Field(i) => Some((*i as u64) << 1),
        Proj::Downcast(v) => Some(((*v as u64) << 1) | 1),
        _ => None,
    }
}

/// The leading `Field`/`Downcast` part of a place, and whether that is the whole place.
/// A place that goes through a dereference or an index is not exact: its field prefix
/// still identifies the field of the root local that it reaches into.
fn field_prefix(p: &Place) -> (Path, bool) {
    let mut path = Vec::new();
    for pr in &p.proj {
        match encode_proj(pr) {
            Some(e) => path.push(e),
            None => return (path, false),
        }
    }
    (path, true)
}

fn is_prefix(a: &[u64], b: &[u64]) -> bool {
    a.len() <= b.len() && a.iter().zip(b).all(|(x, y)| x == y)
}

#[derive(Clone, PartialEq, Eq)]
struct State {
    maybe_init: BitSet,
    maybe_uninit: BitSet,
    maybe_moved: BitSet,
    /// For each local, the loans it may hold.
    holds: Vec<BitSet>,
    /// For each local, every loan it was ever assigned on this path. Unlike `holds` this is
    /// never overwritten by a later assignment (until storage ends). A local in Rust has
    /// one fixed lifetime, so at a return or a store behind a parameter every value the
    /// local ever held must satisfy that lifetime. Later assignments cannot hide an
    /// earlier one. This is only used at those sinks, not for loan liveness.
    origins: Vec<BitSet>,
    /// For each local, the field paths that may have been moved out of it. An empty path
    /// means the whole local may have been moved.
    moved_paths: Vec<std::collections::HashSet<Path>>,
}

impl State {
    fn join(&mut self, o: &State) -> bool {
        let mut c = self.maybe_init.union(&o.maybe_init);
        c |= self.maybe_uninit.union(&o.maybe_uninit);
        c |= self.maybe_moved.union(&o.maybe_moved);
        for (a, b) in self.holds.iter_mut().zip(&o.holds) {
            c |= a.union(b);
        }
        for (a, b) in self.origins.iter_mut().zip(&o.origins) {
            c |= a.union(b);
        }
        for (a, b) in self.moved_paths.iter_mut().zip(&o.moved_paths) {
            let before = a.len();
            a.extend(b.iter().cloned());
            c |= a.len() != before;
        }
        c
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Access {
    Read,
    Write,
    Move,
    BorrowShared,
    BorrowMut,
    /// Drop or StorageDead: ends the local's storage.
    Dead,
}

struct Ck<'b, 'p, 'a> {
    p: &'p Program<'a>,
    body: &'b Body<'p>,
    loans: Vec<Loan>,
    /// Loan created by each Ref statement, keyed by (block, statement index).
    loan_at: std::collections::HashMap<(u32, u32), usize>,
    preds: Vec<Vec<u32>>,
    /// Successor blocks per block, computed once: with call terminators most
    /// blocks end in a call, and recomputing edges in every pass showed up
    /// in profiles.
    succs: Vec<Vec<Bb>>,
    live_out_stmt: Vec<Vec<BitSet>>,
    /// Live locals at each block's entry, for the loans live after a block's
    /// terminating call.
    live_in_block: Vec<BitSet>,
    errs: Vec<Diag>,
    seen: HashSet<(&'static str, Span)>,
    report: bool,
    /// Loans that flow into a return value or behind a parameter reference. Their region
    /// must outlive a parameter lifetime, and rustc's NLL treats such a region as live at
    /// every point reachable from the borrow (not only where a holder local is used).
    /// This is what makes rustc reject NLL problem case 3; Polonius would accept it.
    escaped: BitSet,
    /// Creation point of each loan (`u32::MAX` for synthetic parameter loans).
    loan_block: Vec<u32>,
    loan_stmt: Vec<u32>,
    /// `reach[b]` is the set of blocks reachable from `b`, including `b`.
    reach: Vec<BitSet>,
    /// True in the pass that only collects `escaped` loans.
    collecting: bool,
}

/// Borrow-checks one function body.
pub fn borrowck(p: &Program, body: &Body) -> Vec<Diag> {
    let mut ck = Ck {
        p,
        body,
        loans: Vec::new(),
        loan_at: Default::default(),
        preds: vec![Vec::new(); body.blocks.len()],
        succs: Vec::new(),
        live_out_stmt: Vec::new(),
        live_in_block: Vec::new(),
        errs: Vec::new(),
        seen: HashSet::new(),
        report: false,
        escaped: BitSet::new(0),
        loan_block: Vec::new(),
        loan_stmt: Vec::new(),
        reach: Vec::new(),
        collecting: false,
    };
    ck.collect_loans();
    ck.escaped = BitSet::new(ck.loans.len());
    ck.compute_preds();
    ck.compute_reach();
    ck.liveness();
    ck.dataflow();
    ck.errs
}

fn successors(t: &Terminator) -> Vec<Bb> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::If(_, a, b) => vec![*a, *b],
        Terminator::Switch(_, cases, other) => cases.iter().map(|c| c.1).chain(std::iter::once(*other)).collect(),
        Terminator::Call { next, unwind, .. } => std::iter::once(*next).chain(*unwind).collect(),
        _ => Vec::new(),
    }
}

/// Calls `f` for every operand read by an rvalue, in evaluation order.
fn rvalue_operands<'r>(rv: &'r Rvalue, f: &mut impl FnMut(&'r Operand)) {
    match rv {
        Rvalue::Use(o) | Rvalue::Un(_, o) | Rvalue::Cast(o, _) | Rvalue::Opt(_, Some(o)) => f(o),
        Rvalue::Opt(_, None) => {}
        Rvalue::Bin(_, a, b) | Rvalue::StrCmp(_, a, b) | Rvalue::StringAdd(a, b) | Rvalue::Eq { a, b, .. } => {
            f(a);
            f(b);
        }
        Rvalue::VecRepeat(_, a, b) => {
            f(a);
            f(b);
        }
        Rvalue::Aggregate(_, _, ops) | Rvalue::VecLit(_, ops) => ops.iter().for_each(f),
        Rvalue::Format(parts) => parts.iter().for_each(|p| {
            if let FmtPart::Arg { value, .. } = p {
                f(value)
            }
        }),
        Rvalue::Ref(..) | Rvalue::Discriminant(_) => {}
    }
}

fn parts_operands<'r>(parts: &'r [FmtPart], f: &mut impl FnMut(&'r Operand)) {
    for p in parts {
        if let FmtPart::Arg { value, .. } = p {
            f(value);
        }
    }
}

/// True if two places may refer to overlapping memory.
fn overlap(a: &Place, b: &Place) -> bool {
    if a.local != b.local {
        return false;
    }
    for (x, y) in a.proj.iter().zip(&b.proj) {
        match (x, y) {
            (Proj::Field(i), Proj::Field(j)) if i != j => return false,
            _ => {}
        }
    }
    true
}

impl<'b, 'p, 'a> Ck<'b, 'p, 'a> {
    fn n_locals(&self) -> usize {
        self.body.locals.len()
    }
    fn local_name(&self, l: Local) -> String {
        match &self.body.locals[l as usize].name {
            Some(n) => format!("`{n}`"),
            None => "a temporary value".into(),
        }
    }
    fn err(&mut self, code: &'static str, span: Span, msg: String, fix: &str) {
        self.err_labeled(code, span, msg, fix, Vec::new());
    }

    /// Reports an error with labeled secondary spans (where a borrow starts, where it is used).
    fn err_labeled(&mut self, code: &'static str, span: Span, msg: String, fix: &str, labels: Vec<(Span, &'static str)>) {
        if self.report && self.seen.insert((code, span)) {
            let mut d = Diag::new(code, span, msg, fix);
            for (s, text) in labels {
                if s != span && s != Span::default() {
                    d = d.with_label(s, text);
                }
            }
            self.errs.push(d);
        }
    }

    /// Labels for a loan: where the borrow starts, and where the borrow is used later.
    fn loan_labels(loan: &Loan) -> Vec<(Span, &'static str)> {
        let mut labels = vec![(loan.span, if loan.mutable { "mutably borrowed here" } else { "borrowed here" })];
        if let Some(u) = loan.last_use {
            labels.push((u, "borrow later used here"));
        }
        labels
    }

    // ---------- Setup ----------

    fn collect_loans(&mut self) {
        // Synthetic loans for reference parameters, so returned references can be traced to them.
        for l in 1..=self.body.arg_count {
            if contains_ref(&self.body.tys, self.body.locals[l].ty) {
                self.loan_block.push(u32::MAX);
                self.loan_stmt.push(u32::MAX);
                self.loans.push(Loan {
                    place: Place::local(l as Local).deref(),
                    mutable: false,
                    synthetic: true,
                    span: Span::default(),
                    last_use: None,
                });
            }
        }
        let mut holders: Vec<Option<Local>> = vec![None; self.loans.len()];
        for (bi, b) in self.body.blocks.iter().enumerate() {
            for (si, s) in b.stmts.iter().enumerate() {
                if let StmtKind::Assign(dest, Rvalue::Ref(m, place)) = &s.kind {
                    self.loan_block.push(bi as u32);
                    self.loan_stmt.push(si as u32);
                    self.loan_at.insert((bi as u32, si as u32), self.loans.len());
                    holders.push(if dest.proj.is_empty() { Some(dest.local) } else { None });
                    self.loans.push(Loan { place: place.clone(), mutable: *m, synthetic: false, span: s.span, last_use: None });
                }
            }
        }
        // For each loan, find the last read of a local that holds it. Holders start at the
        // borrow's destination local and follow plain copies. This is the "borrow later used
        // here" label. It is an approximation: it does not follow calls or aggregates.
        let mut copies: Vec<(Local, Local)> = Vec::new();
        for b in &self.body.blocks {
            for s in &b.stmts {
                if let StmtKind::Assign(dest, Rvalue::Use(Operand::Copy(p) | Operand::Move(p))) = &s.kind
                    && dest.proj.is_empty()
                    && p.proj.is_empty()
                {
                    copies.push((p.local, dest.local));
                }
            }
        }
        let mut uses: Vec<(Local, Span)> = Vec::new();
        for b in &self.body.blocks {
            for s in &b.stmts {
                let mut note = |o: &Operand| {
                    if let Operand::Copy(p) | Operand::Move(p) = o {
                        uses.push((p.local, s.span));
                    }
                };
                match &s.kind {
                    // A reborrow of a holder (for example for a method call) also counts as a use.
                    StmtKind::Assign(_, Rvalue::Ref(_, p)) | StmtKind::Assign(_, Rvalue::Discriminant(p)) => uses.push((p.local, s.span)),
                    StmtKind::Assign(_, rv) => rvalue_operands(rv, &mut note),
                    StmtKind::Print { parts, .. } => parts_operands(parts, &mut note),
                    _ => {}
                }
            }
            let span = b.term_span;
            let mut note = |o: &Operand| {
                if let Operand::Copy(p) | Operand::Move(p) = o {
                    uses.push((p.local, span));
                }
            };
            match &b.term {
                Terminator::If(o, ..) | Terminator::Switch(o, ..) => note(o),
                Terminator::Call { args, .. } => args.iter().for_each(&mut note),
                Terminator::Panic(parts) => parts_operands(parts, &mut note),
                _ => {}
            }
        }
        for (i, loan) in self.loans.iter_mut().enumerate() {
            let Some(first) = holders[i] else { continue };
            let mut holders_set = vec![first];
            let mut at = 0;
            while at < holders_set.len() {
                let from = holders_set[at];
                at += 1;
                for &(src, dst) in &copies {
                    if src == from && !holders_set.contains(&dst) {
                        holders_set.push(dst);
                    }
                }
            }
            loan.last_use =
                uses.iter().filter(|&&(l, s)| s.lo > loan.span.lo && holders_set.contains(&l)).map(|&(_, s)| s).max_by_key(|s| s.lo);
        }
    }

    fn compute_preds(&mut self) {
        self.succs = self.body.blocks.iter().map(|b| successors(&b.term)).collect();
        for bi in 0..self.succs.len() {
            for k in 0..self.succs[bi].len() {
                let s = self.succs[bi][k];
                self.preds[s.0 as usize].push(bi as u32);
            }
        }
    }

    fn compute_reach(&mut self) {
        // reach[b] = {b} plus everything its successors reach, to a fixpoint.
        // The same sets a per-block search computes, without re-walking the
        // graph once per block.
        let nb = self.body.blocks.len();
        let mut reach = vec![BitSet::new(nb); nb];
        for (b, r) in reach.iter_mut().enumerate() {
            r.insert(b);
        }
        let mut changed = true;
        while changed {
            changed = false;
            for b in (0..nb).rev() {
                for k in 0..self.succs[b].len() {
                    let s = self.succs[b][k].0 as usize;
                    if s != b {
                        let (lo, hi) = if b < s { (b, s) } else { (s, b) };
                        let (left, right) = reach.split_at_mut(hi);
                        let (dst, src) = if b < s { (&mut left[lo], &right[0]) } else { (&mut right[0], &left[lo]) };
                        changed |= dst.union(src);
                    }
                }
            }
        }
        self.reach = reach;
    }

    /// True if block `b` can reach itself again through at least one edge (it is in a loop).
    fn loops_back(&self, b: u32) -> bool {
        self.succs[b as usize].iter().any(|s| self.reach[s.0 as usize].contains(b as usize))
    }

    // ---------- Liveness ----------

    fn uses_place(set: &mut BitSet, p: &Place) {
        set.insert(p.local as usize);
        for pr in &p.proj {
            if let Proj::Index(i) = pr {
                set.insert(*i as usize);
            }
        }
    }

    /// Backward transfer for one statement: live-in from live-out.
    fn live_stmt(s: &StmtKind, live: &mut BitSet) {
        match s {
            StmtKind::Assign(dest, rv) => {
                if dest.proj.is_empty() {
                    live.remove(dest.local as usize);
                } else {
                    Self::uses_place(live, dest);
                }
                let mut uses = |o: &Operand| {
                    if let Operand::Copy(p) | Operand::Move(p) = o {
                        Self::uses_place(live, p);
                    }
                };
                rvalue_operands(rv, &mut uses);
                if let Rvalue::Ref(_, p) | Rvalue::Discriminant(p) = rv {
                    Self::uses_place(live, p);
                }
            }
            StmtKind::StorageDead(l) => live.remove(*l as usize),
            StmtKind::Drop(_) => {}
            StmtKind::FakeRead(l) => live.insert(*l as usize),
            StmtKind::Print { parts, .. } => parts_operands(parts, &mut |o| {
                if let Operand::Copy(p) | Operand::Move(p) = o {
                    Self::uses_place(live, p);
                }
            }),
        }
    }

    fn live_term(t: &Terminator, live: &mut BitSet) {
        fn uses(live: &mut BitSet, o: &Operand) {
            if let Operand::Copy(p) | Operand::Move(p) = o {
                Ck::uses_place(live, p);
            }
        }
        match t {
            Terminator::If(o, ..) | Terminator::Switch(o, ..) => uses(live, o),
            Terminator::Call { args, dest, .. } => {
                if dest.proj.is_empty() {
                    live.remove(dest.local as usize);
                } else {
                    Self::uses_place(live, dest);
                }
                for o in args {
                    uses(live, o);
                }
            }
            Terminator::Return => live.insert(0),
            Terminator::Panic(parts) => parts_operands(parts, &mut |o| uses(live, o)),
            _ => {}
        }
    }

    fn liveness(&mut self) {
        let n = self.n_locals();
        let nb = self.body.blocks.len();
        let mut live_in = vec![BitSet::new(n); nb];
        let mut live = BitSet::new(n);
        let mut changed = true;
        while changed {
            changed = false;
            for bi in (0..nb).rev() {
                let b = &self.body.blocks[bi];
                live.clear();
                for s in &self.succs[bi] {
                    live.union(&live_in[s.0 as usize]);
                }
                Self::live_term(&b.term, &mut live);
                for s in b.stmts.iter().rev() {
                    Self::live_stmt(&s.kind, &mut live);
                }
                if live != live_in[bi] {
                    live_in[bi] = live.clone();
                    changed = true;
                }
            }
        }
        // Per-statement live-out sets.
        self.live_out_stmt = Vec::with_capacity(nb);
        for bi in 0..nb {
            let b = &self.body.blocks[bi];
            live.clear();
            for s in &self.succs[bi] {
                live.union(&live_in[s.0 as usize]);
            }
            Self::live_term(&b.term, &mut live);
            let mut outs = vec![BitSet::new(n); b.stmts.len()];
            for (si, s) in b.stmts.iter().enumerate().rev() {
                outs[si] = live.clone();
                Self::live_stmt(&s.kind, &mut live);
            }
            self.live_out_stmt.push(outs);
        }
        self.live_in_block = live_in;
    }

    // ---------- Forward dataflow and checks ----------

    fn entry_state(&self) -> State {
        let n = self.n_locals();
        let nl = self.loans.len();
        let mut st = State {
            maybe_init: BitSet::new(n),
            maybe_uninit: BitSet::new(n),
            maybe_moved: BitSet::new(n),
            holds: vec![BitSet::new(nl); n],
            origins: vec![BitSet::new(nl); n],
            moved_paths: vec![Default::default(); n],
        };
        for l in 0..n {
            if l >= 1 && l <= self.body.arg_count {
                st.maybe_init.insert(l);
            } else {
                st.maybe_uninit.insert(l);
            }
        }
        for (i, loan) in self.loans.iter().enumerate() {
            if loan.synthetic {
                st.holds[loan.place.local as usize].insert(i);
                st.origins[loan.place.local as usize].insert(i);
            }
        }
        st
    }

    fn dataflow(&mut self) {
        let nb = self.body.blocks.len();
        let mut entry: Vec<Option<State>> = vec![None; nb];
        entry[0] = Some(self.entry_state());
        let mut work: Vec<u32> = vec![0];
        let mut queued = vec![false; nb];
        queued[0] = true;
        // Fixpoint without reporting, then one reporting pass over the final states.
        while let Some(b) = work.pop() {
            queued[b as usize] = false;
            let mut st = entry[b as usize].clone().unwrap();
            self.run_block(b, &mut st);
            for k in 0..self.succs[b as usize].len() {
                let s = self.succs[b as usize][k];
                let si = s.0 as usize;
                let changed = match &mut entry[si] {
                    None => {
                        entry[si] = Some(st.clone());
                        true
                    }
                    Some(e) => e.join(&st),
                };
                if changed && !queued[si] {
                    queued[si] = true;
                    work.push(s.0);
                }
            }
        }
        // One pass to learn which loans escape into a return value or behind a parameter.
        // The reporting pass then keeps those loans live everywhere rustc's NLL does.
        self.collecting = true;
        for (b, st) in entry.iter().enumerate() {
            if let Some(mut st) = st.clone() {
                self.run_block(b as u32, &mut st);
            }
        }
        self.collecting = false;
        self.report = true;
        for (b, st) in entry.into_iter().enumerate() {
            if let Some(mut st) = st {
                self.run_block(b as u32, &mut st);
            }
        }
    }

    fn run_block(&mut self, b: u32, st: &mut State) {
        let body = self.body;
        let block = &body.blocks[b as usize];
        for (si, s) in block.stmts.iter().enumerate() {
            self.stmt(b, si as u32, &s.kind, s.span, st);
        }
        let span = block.term_span;
        let mut ops: Vec<&Operand> = Vec::new();
        match &block.term {
            Terminator::Call { target, args, dest, .. } => {
                let (target, args, dest) = (*target, args.clone(), dest.clone());
                self.call_term(b, target, &args, &dest, span, st);
            }
            Terminator::If(o, ..) | Terminator::Switch(o, ..) => ops.push(o),
            Terminator::Panic(parts) => parts_operands(parts, &mut |o| ops.push(o)),
            Terminator::Return if self.report => {
                self.check_return(st, span);
            }
            Terminator::Return if self.collecting => {
                let holds = st.holds[0].clone();
                let origins = st.origins[0].clone();
                self.escaped.union(&holds);
                self.escaped.union(&origins);
            }
            _ => {}
        }
        // Nothing runs after a terminator inside this block, so no loan is live past its reads.
        let none = BitSet::new(0);
        for o in ops {
            self.operand(o, span, st, &none);
        }
    }

    /// Loans that are live after the current statement: held by some live local, plus the
    /// escaped loans (see `escaped`) at every point reachable from their creation.
    fn live_loans(&self, st: &State, live: &BitSet, skip: Option<Local>, b: u32, si: u32) -> BitSet {
        let mut out = BitSet::new(self.loans.len());
        for l in live.iter() {
            if Some(l as Local) == skip {
                continue;
            }
            out.union(&st.holds[l]);
        }
        for li in self.escaped.iter() {
            let (lb, ls) = (self.loan_block[li], self.loan_stmt[li]);
            if lb == u32::MAX {
                continue;
            }
            let on = if lb == b { ls < si || (ls > si && self.loops_back(b)) } else { self.reach[lb as usize].contains(b as usize) };
            if on {
                out.insert(li);
            }
        }
        out
    }

    fn stmt(&mut self, b: u32, si: u32, s: &StmtKind, span: Span, st: &mut State) {
        // Loans live after this statement. Only needed in the reporting pass.
        let skip = match s {
            StmtKind::Assign(dest, _) if dest.proj.is_empty() => Some(dest.local),
            _ => None,
        };
        let live =
            if self.report { self.live_loans(st, &self.live_out_stmt[b as usize][si as usize], skip, b, si) } else { BitSet::new(0) };
        match s {
            StmtKind::Assign(dest, rv) => {
                // Reads and moves in the right-hand side.
                let mut ops: Vec<&Operand> = Vec::new();
                rvalue_operands(rv, &mut |o| ops.push(o));
                for o in &ops {
                    self.operand(o, span, st, &live);
                }
                let mut new_holds = BitSet::new(self.loans.len());
                let mut new_origins = BitSet::new(self.loans.len());
                match rv {
                    Rvalue::Ref(m, place) => {
                        self.check_init(place, span, st);
                        let kind = if *m { Access::BorrowMut } else { Access::BorrowShared };
                        if *m {
                            self.check_mutability(place, span, st, true);
                        }
                        self.access(place, kind, span, &live);
                        new_holds.insert(self.loan_at[&(b, si)]);
                        new_origins.insert(self.loan_at[&(b, si)]);
                        // A reborrow through a reference depends on that reference's loans.
                        if place.proj.contains(&Proj::Deref) {
                            let h = st.holds[place.local as usize].clone();
                            new_holds.union(&h);
                            let o = st.origins[place.local as usize].clone();
                            new_origins.union(&o);
                        }
                    }
                    Rvalue::Discriminant(place) => {
                        self.check_init(place, span, st);
                        self.access(place, Access::Read, span, &live);
                    }
                    _ => {
                        let ty = self.dest_ty(dest);
                        if contains_ref(&self.body.tys, ty) {
                            for o in &ops {
                                self.holds_of(o, st, &mut new_holds);
                                self.origins_of(o, st, &mut new_origins);
                            }
                        }
                    }
                }
                self.write_dest(dest, new_holds, &new_origins, span, &live, st);
            }
            StmtKind::Drop(l) | StmtKind::StorageDead(l) => {
                let place = Place::local(*l);
                self.access(&place, Access::Dead, span, &live);
                let li = *l as usize;
                st.maybe_init.remove(li);
                st.maybe_uninit.insert(li);
                if matches!(s, StmtKind::StorageDead(_)) {
                    st.holds[li].clear();
                    st.origins[li].clear();
                    st.moved_paths[li].clear();
                }
            }
            StmtKind::FakeRead(l) => {
                let place = Place::local(*l);
                self.access(&place, Access::Read, span, &live);
            }
            StmtKind::Print { parts, .. } => {
                let mut ops: Vec<&Operand> = Vec::new();
                parts_operands(parts, &mut |o| ops.push(o));
                for o in ops {
                    self.operand(o, span, st, &live);
                }
            }
        }
    }

    /// The write side of an assignment or a call's result store: mutability,
    /// conflicts with live loans, parameter-origin checks, and init state.
    fn write_dest(&mut self, dest: &Place, new_holds: BitSet, new_origins: &BitSet, span: Span, live: &BitSet, st: &mut State) {
        if dest.proj.is_empty() {
            let l = dest.local as usize;
            if !self.body.locals[l].mutable && st.maybe_init.contains(l) {
                let name = self.local_name(dest.local);
                self.err("L0302", span, format!("cannot assign twice to immutable variable {name}"), "Declare it with `let mut`.");
            }
            self.access(dest, Access::Write, span, live);
            self.check_store_into_param_ref(dest, new_origins, st, span);
            st.maybe_init.insert(l);
            st.maybe_uninit.remove(l);
            st.maybe_moved.remove(l);
            st.moved_paths[l].clear();
            st.holds[l] = new_holds;
            st.origins[l].union(new_origins);
        } else {
            self.check_init_write(dest, span, st);
            self.check_mutability(dest, span, st, false);
            self.access(dest, Access::Write, span, live);
            self.check_store_into_param_ref(dest, new_origins, st, span);
            // Writing a field puts back a field that was moved out, and every
            // field below it. Other moved fields stay moved.
            let (path, exact) = field_prefix(dest);
            if exact {
                st.moved_paths[dest.local as usize].retain(|m| !is_prefix(&path, m));
            }
            st.holds[dest.local as usize].union(&new_holds);
            st.origins[dest.local as usize].union(new_origins);
        }
    }

    /// One `Call` terminator, checked like the assignment it ends: argument
    /// reads first, then loan flow into the result and into `&mut` argument
    /// targets, then the write to `dest`. The loans live after the call are
    /// the ones its successors keep live.
    fn call_term(&mut self, b: u32, target: CallTarget, args: &[Operand], dest: &Place, span: Span, st: &mut State) {
        let si = self.body.blocks[b as usize].stmts.len() as u32;
        let skip = if dest.proj.is_empty() { Some(dest.local) } else { None };
        let live = if self.report {
            let mut locals = BitSet::new(self.n_locals());
            for s in &self.succs[b as usize] {
                locals.union(&self.live_in_block[s.0 as usize]);
            }
            self.live_loans(st, &locals, skip, b, si)
        } else {
            BitSet::new(0)
        };
        for o in args {
            self.operand(o, span, st, &live);
        }
        let mut new_holds = BitSet::new(self.loans.len());
        let mut new_origins = BitSet::new(self.loans.len());
        match target {
            CallTarget::Fn(f) => {
                let info = self.p.fn_info(f);
                if let Some(i) = info.ret_borrows_from {
                    self.holds_of(&args[i], st, &mut new_holds);
                    self.origins_of(&args[i], st, &mut new_origins);
                }
                self.flow_into_mut_args(args, st, span);
            }
            CallTarget::Builtin(_) | CallTarget::Intrinsic(_) => {
                // Builtins were plain rvalues before S7: a reference-typed
                // result may hold any argument's loans.
                let ty = self.dest_ty(dest);
                if contains_ref(&self.body.tys, ty) {
                    for o in args {
                        self.holds_of(o, st, &mut new_holds);
                        self.origins_of(o, st, &mut new_origins);
                    }
                }
                if target == CallTarget::Builtin(Builtin::VecPush) {
                    self.flow_into_mut_args(args, st, span);
                }
            }
        }
        self.write_dest(dest, new_holds, &new_origins, span, &live, st);
    }

    fn dest_ty(&self, dest: &Place) -> Ty {
        let mut t = self.body.locals[dest.local as usize].ty;
        for pr in &dest.proj {
            t = match (self.body.tys.kind(t), pr) {
                (TyKind::Ref(_, _, i), Proj::Deref) => i,
                (_, Proj::Index(_)) => match self.body.tys.vec_elem(t) {
                    Some(e) => e,
                    None => return ERROR,
                },
                _ => return ERROR,
            };
        }
        t
    }

    /// The parameter locals that the synthetic loans in `holds` stand for.
    fn loan_origins(&self, holds: &BitSet) -> Vec<Local> {
        let mut out: Vec<Local> = Vec::new();
        for li in holds.iter() {
            let loan = &self.loans[li];
            if loan.synthetic && !out.contains(&loan.place.local) {
                out.push(loan.place.local);
            }
        }
        out
    }

    /// True if a place root is one of the function's parameter locals.
    fn is_param(&self, l: Local) -> bool {
        l >= 1 && (l as usize) <= self.body.arg_count
    }

    /// True if `loan` may be stored where a reference with `origins` (parameter lifetimes
    /// from the signature) is required: it borrows from one of those parameters.
    /// A promoted constant (`&1`) is `'static` in Rust, but lust keeps it in a stack
    /// temporary, so storing it behind a parameter stays rejected here.
    fn store_loan_ok(&self, origins: &[Local], loan: &Loan) -> bool {
        if loan.synthetic {
            return origins.contains(&loan.place.local);
        }
        loan.place.proj.contains(&Proj::Deref) && origins.contains(&loan.place.local)
    }

    /// Reports the first loan in `incoming` that may not be stored behind `origins`.
    fn check_incoming_loans(&mut self, origins: &[Local], incoming: &BitSet, dest: Local, span: Span) {
        for li in incoming.iter() {
            let loan = &self.loans[li];
            if self.store_loan_ok(origins, loan) {
                continue;
            }
            let dest_name = self.local_name(dest);
            if loan.synthetic {
                let src = self.local_name(loan.place.local);
                let want = self.local_name(origins[0]);
                self.err(
                    "L0202",
                    span,
                    format!("this stores a reference that borrows from {src}, but {dest_name} must borrow from {want}"),
                    "Borrow from the same parameter. Lust ties each reference to one parameter, as Rust's elision does here.",
                );
            } else {
                let name = self.local_name(loan.place.local);
                self.err(
                    "L0306",
                    span,
                    format!("{name} does not live long enough: it is borrowed into {dest_name}, which borrows from a parameter"),
                    "Borrow from a parameter instead, or store an owned value (for example `*dest = value`).",
                );
            }
            return;
        }
    }

    /// A reference that comes from a parameter must keep borrowing from that parameter.
    /// Storing a borrow of a local value into such a place is an error even if the place
    /// is never read again (`v = &mut Vec::new()` for `v: &mut Vec<_>`), because the
    /// signature ties the place's reference to the caller's lifetime. This applies to a
    /// parameter local itself and to places behind a parameter-derived reference
    /// (`*slot = &local`), but not to a plain local holding a reborrow: its lifetime
    /// can shrink, so NLL rules apply there.
    fn check_store_into_param_ref(&mut self, dest: &Place, new_origins: &BitSet, st: &State, span: Span) {
        if !self.report && !self.collecting {
            return;
        }
        let root = dest.local;
        let direct_param = dest.proj.is_empty() && self.is_param(root);
        let through_deref = dest.proj.first() == Some(&Proj::Deref);
        if !direct_param && !through_deref {
            return;
        }
        let origins = self.loan_origins(&st.holds[root as usize]);
        if origins.is_empty() {
            return;
        }
        if self.collecting {
            self.escaped.union(new_origins);
            return;
        }
        // `new_origins` holds every loan the source local ever held, so a value that was
        // first borrowed from the wrong place and only later from the right parameter is
        // still rejected. Rust gives the source local one lifetime; it cannot change.
        self.check_incoming_loans(&origins, new_origins, root, span);
    }

    fn holds_of(&self, o: &Operand, st: &State, out: &mut BitSet) {
        if let Operand::Copy(p) | Operand::Move(p) = o {
            out.union(&st.holds[p.local as usize]);
        }
    }

    fn origins_of(&self, o: &Operand, st: &State, out: &mut BitSet) {
        if let Operand::Copy(p) | Operand::Move(p) = o {
            out.union(&st.origins[p.local as usize]);
        }
    }

    /// References passed to a call may be stored behind one of its `&mut` arguments, if that
    /// argument's target type can hold references (for example `v.push(&x)` on a `Vec<&T>`).
    fn flow_into_mut_args(&mut self, args: &[Operand], st: &mut State, span: Span) {
        for (i, a) in args.iter().enumerate() {
            let (Operand::Move(p) | Operand::Copy(p)) = a else { continue };
            let ty = self.place_ty(p);
            let TyKind::Ref(_, Mut::Mut, target) = self.body.tys.kind(ty) else { continue };
            if !contains_ref(&self.body.tys, target) {
                continue;
            }
            let mut incoming = BitSet::new(self.loans.len());
            let mut incoming_origins = BitSet::new(self.loans.len());
            for (j, b) in args.iter().enumerate() {
                if j != i {
                    self.holds_of(b, st, &mut incoming);
                    self.origins_of(b, st, &mut incoming_origins);
                }
            }
            if incoming.is_empty() && incoming_origins.is_empty() {
                continue;
            }
            let targets: Vec<Local> =
                st.holds[p.local as usize].iter().filter(|&l| self.loans[l].mutable).map(|l| self.loans[l].place.local).collect();
            for t in targets {
                // Storing into a target behind a parameter needs the same origin check
                // as a direct assignment behind a parameter reference.
                let origins = self.loan_origins(&st.holds[t as usize]);
                if !origins.is_empty() {
                    if self.collecting {
                        self.escaped.union(&incoming_origins);
                    }
                    if self.report {
                        self.check_incoming_loans(&origins, &incoming_origins, t, span);
                    }
                }
                st.holds[t as usize].union(&incoming);
                st.origins[t as usize].union(&incoming_origins);
            }
        }
    }

    fn place_ty(&self, p: &Place) -> Ty {
        if p.proj.is_empty() { self.body.locals[p.local as usize].ty } else { self.dest_ty(p) }
    }

    fn operand(&mut self, o: &Operand, span: Span, st: &mut State, live: &BitSet) {
        match o {
            Operand::Copy(p) => {
                self.check_init(p, span, st);
                self.access(p, Access::Read, span, live);
            }
            Operand::Move(p) => {
                self.check_init(p, span, st);
                self.access(p, Access::Move, span, live);
                // A move out of a local, or out of one of its fields. Moving one field is a
                // partial move: sibling fields stay usable, but the moved field and every
                // value that contains it do not, until the field is assigned again. Rust
                // also forbids partial moves out of a type with a `Drop` impl (E0509).
                // Lust rejects trait impls, so no lust type has a user `Drop` impl yet and
                // every struct, enum, and `Option` here may be moved out of by field. When
                // `Drop` impls land, reject a non-empty path for such a root type here.
                let (path, exact) = field_prefix(p);
                if exact {
                    let l = p.local as usize;
                    if path.is_empty() {
                        st.maybe_init.remove(l);
                        st.maybe_uninit.insert(l);
                        st.maybe_moved.insert(l);
                        st.moved_paths[l].clear();
                        st.moved_paths[l].insert(path);
                    } else {
                        st.moved_paths[l].insert(path);
                    }
                } else {
                    self.bad_move(p, span);
                }
            }
            Operand::Const(_) => {}
        }
    }

    fn bad_move(&mut self, p: &Place, span: Span) {
        if p.proj.contains(&Proj::Deref) {
            self.err(
                "L0305",
                span,
                "cannot move out of a reference".into(),
                "Clone the value with `.clone()`, or borrow it with `&` instead of moving it.",
            );
        } else if p.proj.iter().any(|x| matches!(x, Proj::Index(_))) {
            self.err(
                "L0305",
                span,
                "cannot move out of a Vec index".into(),
                "Borrow the element with `&v[i]`, or clone it with `v[i].clone()`.",
            );
        } else if self.report && self.seen.insert(("L9001", span)) {
            let mut d = unsupported(span, "moving a field out of a struct or enum");
            d.fix = "Clone the field with `.clone()`, or match on a reference (`match &value`) and borrow it.".into();
            self.errs.push(d);
        }
    }

    fn check_init(&mut self, p: &Place, span: Span, st: &State) {
        if !self.report {
            return;
        }
        let l = p.local as usize;
        let (path, exact) = field_prefix(p);
        // A moved field blocks uses of itself, of fields below it, and of every value
        // that contains it. A sibling field is fine.
        for m in &st.moved_paths[l] {
            let name = self.local_name(p.local);
            let fix = "Clone the value before the move with `.clone()`, or borrow it with `&` instead of moving it.";
            if is_prefix(m, &path) {
                self.err("L0301", span, format!("use of moved value: {name}"), fix);
                return;
            }
            if exact && is_prefix(&path, m) {
                self.err("L0301", span, format!("use of partially moved value: {name}"), fix);
                return;
            }
        }
        if st.maybe_uninit.contains(l) {
            let name = self.local_name(p.local);
            if st.maybe_moved.contains(l) {
                let fix = "Clone the value before the move with `.clone()`, or borrow it with `&` instead of moving it.";
                self.err("L0301", span, format!("use of moved value: {name}"), fix);
            } else {
                self.err(
                    "L0310",
                    span,
                    format!("{name} is used before it is assigned on some path"),
                    "Assign a value on every path before this use.",
                );
            }
        }
    }

    /// The check for a write through a projection (`p.x = ...`). Writing a moved-out
    /// field puts it back, and writing a value puts back every moved field below it.
    /// Writing under a moved-out field, or into a value that was never assigned, is
    /// still an error.
    fn check_init_write(&mut self, p: &Place, span: Span, st: &State) {
        if !self.report {
            return;
        }
        let l = p.local as usize;
        let (path, exact) = field_prefix(p);
        for m in &st.moved_paths[l] {
            let under_moved = is_prefix(m, &path) && !(exact && m.len() == path.len());
            if under_moved {
                let name = self.local_name(p.local);
                let fix = "Clone the value before the move with `.clone()`, or borrow it with `&` instead of moving it.";
                self.err("L0301", span, format!("use of moved value: {name}"), fix);
                return;
            }
        }
        if st.maybe_uninit.contains(l) && st.moved_paths[l].is_empty() {
            let name = self.local_name(p.local);
            if st.maybe_moved.contains(l) {
                let fix = "Clone the value before the move with `.clone()`, or borrow it with `&` instead of moving it.";
                self.err("L0301", span, format!("use of moved value: {name}"), fix);
            } else {
                self.err(
                    "L0310",
                    span,
                    format!("{name} is used before it is assigned on some path"),
                    "Assign a value on every path before this use.",
                );
            }
        }
    }

    /// Writes and `&mut` borrows need a `mut` root local, or a path through `&mut` references only.
    fn check_mutability(&mut self, p: &Place, span: Span, _st: &State, borrow: bool) {
        if !self.report {
            return;
        }
        let mut t = self.body.locals[p.local as usize].ty;
        let mut through_ref = false;
        let mut variant = 0;
        for pr in &p.proj {
            match (self.body.tys.kind(t), pr) {
                (TyKind::Ref(_, m, inner), Proj::Deref) => {
                    if !m.is_mut() {
                        let fix = "Take a `&mut` reference instead of `&`.";
                        if borrow {
                            self.err("L0308", span, "cannot borrow data behind a `&` reference as mutable".into(), fix);
                        } else {
                            self.err("L0309", span, "cannot assign through a `&` reference".into(), fix);
                        }
                        return;
                    }
                    through_ref = true;
                    t = inner;
                }
                (_, Proj::Index(_)) if self.body.tys.vec_elem(t).is_some() => t = self.body.tys.vec_elem(t).unwrap(),
                (TyKind::Adt(..), Proj::Field(i)) if self.body.tys.local_adt(t).is_some() => {
                    let a = self.body.tys.local_adt(t).unwrap();
                    t = self.p.adt(a).variants[variant as usize].fields[*i as usize].ty;
                    variant = 0;
                }
                (TyKind::Adt(..), Proj::Downcast(v)) => variant = *v,
                (_, Proj::Field(_)) if self.body.tys.option_elem(t).is_some() => t = self.body.tys.option_elem(t).unwrap(),
                _ => {}
            }
        }
        if !through_ref && !self.body.locals[p.local as usize].mutable {
            let name = self.local_name(p.local);
            if borrow {
                self.err(
                    "L0308",
                    span,
                    format!("cannot borrow {name} as mutable, because it is not declared as mutable"),
                    "Declare it with `let mut`.",
                );
            } else {
                self.err(
                    "L0302",
                    span,
                    format!("cannot assign to a field of {name}, because it is not declared as mutable"),
                    "Declare it with `let mut`.",
                );
            }
        }
    }

    /// Checks one access against the loans live after the statement.
    fn access(&mut self, p: &Place, kind: Access, span: Span, live_loans: &BitSet) {
        if !self.report {
            return;
        }
        for li in live_loans.iter() {
            let loan = &self.loans[li];
            if loan.synthetic {
                continue;
            }
            // A write to a whole local is shallow: writing a reference local itself does
            // not touch the value behind it, so a loan on `*a` does not block `a = ...`.
            if kind == Access::Write && p.proj.is_empty() && loan.place.proj.first() == Some(&Proj::Deref) {
                continue;
            }
            let conflict = match kind {
                Access::Read | Access::BorrowShared => loan.mutable && overlap(p, &loan.place),
                Access::Write | Access::Move | Access::BorrowMut => overlap(p, &loan.place),
                Access::Dead => loan.place.local == p.local && !loan.place.proj.contains(&Proj::Deref),
            };
            if !conflict {
                continue;
            }
            let name = self.local_name(loan.place.local);
            let (code, msg, fix) = match (kind, loan.mutable) {
                (Access::Dead, _) if self.body.locals[loan.place.local as usize].name.is_none() => (
                    "L0306",
                    "a temporary value is dropped while it is still borrowed".to_string(),
                    "Store the value in a variable with `let` first, so it lives long enough.",
                ),
                (Access::Dead, _) => (
                    "L0306",
                    format!("{name} does not live long enough: it is dropped while still borrowed"),
                    "Declare the value in an outer scope, or stop using the reference before the value goes out of scope.",
                ),
                (Access::Move, _) => (
                    "L0311",
                    format!("cannot move out of {name} because it is borrowed"),
                    "Stop using the reference before the move, or clone the value.",
                ),
                (Access::BorrowMut, true) => (
                    "L0304",
                    format!("cannot borrow {name} as mutable more than once at a time"),
                    "Finish using the first `&mut` reference before taking another one.",
                ),
                (Access::BorrowMut, false) => (
                    "L0303",
                    format!("cannot borrow {name} as mutable because it is also borrowed as immutable"),
                    "Finish using the shared reference before taking a `&mut` reference.",
                ),
                (Access::BorrowShared, _) => (
                    "L0303",
                    format!("cannot borrow {name} as immutable because it is also borrowed as mutable"),
                    "Finish using the `&mut` reference first.",
                ),
                (Access::Write, _) => (
                    "L0312",
                    format!("cannot assign to {name} because it is borrowed"),
                    "Finish using the reference before the assignment.",
                ),
                (Access::Read, _) => {
                    ("L0303", format!("cannot use {name} because it is mutably borrowed"), "Finish using the `&mut` reference first.")
                }
            };
            let labels = Self::loan_labels(loan);
            self.err_labeled(code, span, msg, fix, labels);
            return;
        }
    }

    fn check_return(&mut self, st: &State, span: Span) {
        let expected = self.p.fn_info(self.body.fn_id).ret_borrows_from.map(|i| (i + 1) as Local);
        // Every loan the return value ever held counts (see `State::origins`): a local
        // that first borrowed from a local value and only later from the right parameter
        // still cannot be returned, because its lifetime is fixed.
        let mut holds = st.holds[0].clone();
        holds.union(&st.origins[0].clone());
        for li in holds.iter() {
            let loan = &self.loans[li];
            let root = loan.place.local;
            let is_param = root >= 1 && (root as usize) <= self.body.arg_count;
            if !loan.place.proj.contains(&Proj::Deref) {
                let name = self.local_name(root);
                let labels = Self::loan_labels(loan);
                self.err_labeled(
                    "L0307",
                    span,
                    format!("cannot return a reference to {name}, which is owned by this function"),
                    "Return an owned value instead (for example `String` instead of `&str`).",
                    labels,
                );
            } else if is_param && Some(root) != expected && loan.place.proj.first() == Some(&Proj::Deref) {
                let name = self.local_name(root);
                self.err(
                    "L0202",
                    span,
                    format!("this returns a reference that borrows from {name}, but elision ties the result to another parameter"),
                    "Return an owned value, or change the signature so the reference comes from `self` or the only reference parameter.",
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::BitSet;

    /// One-word sets stay inline; wider sets spill to the heap form; both
    /// answer the same operations across the boundary.
    #[test]
    fn bitset_inline_and_wide_forms_agree() {
        let mut one = BitSet::new(64);
        one.insert(0);
        one.insert(63);
        assert!(one.contains(0) && one.contains(63) && !one.contains(1));
        assert_eq!(one.iter().collect::<Vec<_>>(), vec![0, 63]);
        one.remove(0);
        assert!(!one.contains(0) && !one.is_empty());

        let mut wide = BitSet::new(200);
        wide.insert(64);
        wide.insert(199);
        assert!(wide.contains(64) && wide.contains(199) && !wide.contains(63));
        assert_eq!(wide.iter().collect::<Vec<_>>(), vec![64, 199]);
        let mut other = BitSet::new(200);
        other.insert(199);
        assert!(!wide.union(&other), "no new bit, no change");
        other.insert(65);
        assert!(wide.union(&other), "a new bit is a change");
        wide.clear();
        assert!(wide.is_empty());
    }
}
