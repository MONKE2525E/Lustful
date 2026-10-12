// Borrow checking on the IR, one function at a time.
//
// 1. Initialization: forward dataflow of maybe-init and maybe-moved locals.
// 2. Loans: each `&place` creates a loan. Forward dataflow tracks which locals may hold which loans.
// 3. Liveness: backward dataflow. A loan is live where some live local may hold it (NLL style).
// 4. Each access is checked against the live loans it conflicts with.
use crate::check::Builtin;
use crate::collect::*;
use crate::diag::{Diag, Span, unsupported};
use crate::ir::*;
use crate::types::*;
use std::collections::HashSet;

#[derive(Clone, PartialEq, Eq)]
struct BitSet(Vec<u64>);

impl BitSet {
    fn new(n: usize) -> BitSet {
        BitSet(vec![0; n.div_ceil(64).max(1)])
    }
    fn insert(&mut self, i: usize) {
        self.0[i / 64] |= 1 << (i % 64);
    }
    fn remove(&mut self, i: usize) {
        self.0[i / 64] &= !(1 << (i % 64));
    }
    fn contains(&self, i: usize) -> bool {
        self.0[i / 64] & (1 << (i % 64)) != 0
    }
    fn union(&mut self, o: &BitSet) -> bool {
        let mut changed = false;
        for (a, b) in self.0.iter_mut().zip(&o.0) {
            let n = *a | b;
            changed |= n != *a;
            *a = n;
        }
        changed
    }
    fn clear(&mut self) {
        self.0.iter_mut().for_each(|w| *w = 0);
    }
    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.0.iter().enumerate().flat_map(|(wi, &w)| (0..64).filter(move |b| w & (1 << b) != 0).map(move |b| wi * 64 + b))
    }
    fn is_empty(&self) -> bool {
        self.0.iter().all(|&w| w == 0)
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

#[derive(Clone, PartialEq, Eq)]
struct State {
    maybe_init: BitSet,
    maybe_uninit: BitSet,
    maybe_moved: BitSet,
    /// For each local, the loans it may hold.
    holds: Vec<BitSet>,
}

impl State {
    fn join(&mut self, o: &State) -> bool {
        let mut c = self.maybe_init.union(&o.maybe_init);
        c |= self.maybe_uninit.union(&o.maybe_uninit);
        c |= self.maybe_moved.union(&o.maybe_moved);
        for (a, b) in self.holds.iter_mut().zip(&o.holds) {
            c |= a.union(b);
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
    live_out_stmt: Vec<Vec<BitSet>>,
    errs: Vec<Diag>,
    seen: HashSet<(&'static str, u32, u32)>,
    report: bool,
}

/// Borrow-checks one function body.
pub fn borrowck(p: &Program, body: &Body) -> Vec<Diag> {
    let mut ck = Ck {
        p,
        body,
        loans: Vec::new(),
        loan_at: Default::default(),
        preds: vec![Vec::new(); body.blocks.len()],
        live_out_stmt: Vec::new(),
        errs: Vec::new(),
        seen: HashSet::new(),
        report: false,
    };
    ck.collect_loans();
    ck.compute_preds();
    ck.liveness();
    ck.dataflow();
    ck.errs
}

fn successors(t: &Terminator) -> Vec<Bb> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::If(_, a, b) => vec![*a, *b],
        Terminator::Switch(_, cases, other) => cases.iter().map(|c| c.1).chain(std::iter::once(*other)).collect(),
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
        Rvalue::Aggregate(_, _, ops) | Rvalue::VecLit(_, ops) | Rvalue::Call(_, ops) | Rvalue::Builtin(_, ops) => ops.iter().for_each(f),
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
        if self.report && self.seen.insert((code, span.start, span.end)) {
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
            loan.last_use = uses
                .iter()
                .filter(|&&(l, s)| s.start > loan.span.start && holders_set.contains(&l))
                .map(|&(_, s)| s)
                .max_by_key(|s| s.start);
        }
    }

    fn compute_preds(&mut self) {
        for (bi, b) in self.body.blocks.iter().enumerate() {
            for s in successors(&b.term) {
                self.preds[s.0 as usize].push(bi as u32);
            }
        }
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
        let mut uses = |o: &Operand| {
            if let Operand::Copy(p) | Operand::Move(p) = o {
                Self::uses_place(live, p);
            }
        };
        match t {
            Terminator::If(o, ..) | Terminator::Switch(o, ..) => uses(o),
            Terminator::Return => live.insert(0),
            Terminator::Panic(parts) => parts_operands(parts, &mut uses),
            _ => {}
        }
    }

    fn liveness(&mut self) {
        let n = self.n_locals();
        let nb = self.body.blocks.len();
        let mut live_in = vec![BitSet::new(n); nb];
        let mut changed = true;
        while changed {
            changed = false;
            for bi in (0..nb).rev() {
                let b = &self.body.blocks[bi];
                let mut live = BitSet::new(n);
                for s in successors(&b.term) {
                    live.union(&live_in[s.0 as usize]);
                }
                Self::live_term(&b.term, &mut live);
                for s in b.stmts.iter().rev() {
                    Self::live_stmt(&s.kind, &mut live);
                }
                if live != live_in[bi] {
                    live_in[bi] = live;
                    changed = true;
                }
            }
        }
        // Per-statement live-out sets.
        self.live_out_stmt = Vec::with_capacity(nb);
        for bi in 0..nb {
            let b = &self.body.blocks[bi];
            let mut live = BitSet::new(n);
            for s in successors(&b.term) {
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
            for s in successors(&self.body.blocks[b as usize].term) {
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
            Terminator::If(o, ..) | Terminator::Switch(o, ..) => ops.push(o),
            Terminator::Panic(parts) => parts_operands(parts, &mut |o| ops.push(o)),
            Terminator::Return if self.report => {
                self.check_return(st, span);
            }
            _ => {}
        }
        // Nothing runs after a terminator inside this block, so no loan is live past its reads.
        let none = BitSet::new(0);
        for o in ops {
            self.operand(o, span, st, &none);
        }
    }

    /// Loans that are live after the current statement: held by some live local.
    fn live_loans(&self, st: &State, live: &BitSet, skip: Option<Local>) -> BitSet {
        let mut out = BitSet::new(self.loans.len());
        for l in live.iter() {
            if Some(l as Local) == skip {
                continue;
            }
            out.union(&st.holds[l]);
        }
        out
    }

    fn stmt(&mut self, b: u32, si: u32, s: &StmtKind, span: Span, st: &mut State) {
        // Loans live after this statement. Only needed in the reporting pass.
        let skip = match s {
            StmtKind::Assign(dest, _) if dest.proj.is_empty() => Some(dest.local),
            _ => None,
        };
        let live = if self.report { self.live_loans(st, &self.live_out_stmt[b as usize][si as usize], skip) } else { BitSet::new(0) };
        match s {
            StmtKind::Assign(dest, rv) => {
                // Reads and moves in the right-hand side.
                let mut ops: Vec<&Operand> = Vec::new();
                rvalue_operands(rv, &mut |o| ops.push(o));
                for o in &ops {
                    self.operand(o, span, st, &live);
                }
                let mut new_holds = BitSet::new(self.loans.len());
                match rv {
                    Rvalue::Ref(m, place) => {
                        self.check_init(place, span, st);
                        let kind = if *m { Access::BorrowMut } else { Access::BorrowShared };
                        if *m {
                            self.check_mutability(place, span, st, true);
                        }
                        self.access(place, kind, span, &live);
                        new_holds.insert(self.loan_at[&(b, si)]);
                        // A reborrow through a reference depends on that reference's loans.
                        if place.proj.contains(&Proj::Deref) {
                            let h = st.holds[place.local as usize].clone();
                            new_holds.union(&h);
                        }
                    }
                    Rvalue::Discriminant(place) => {
                        self.check_init(place, span, st);
                        self.access(place, Access::Read, span, &live);
                    }
                    Rvalue::Call(f, args) => {
                        let info = self.p.fn_info(*f);
                        if let Some(i) = info.ret_borrows_from {
                            self.holds_of(&args[i], st, &mut new_holds);
                        }
                        self.flow_into_mut_args(args, st);
                    }
                    _ => {
                        let ty = self.dest_ty(dest);
                        if contains_ref(&self.body.tys, ty) {
                            for o in &ops {
                                self.holds_of(o, st, &mut new_holds);
                            }
                        }
                        if let Rvalue::Builtin(Builtin::VecPush, args) = rv {
                            self.flow_into_mut_args(args, st);
                        }
                    }
                }
                // The write to the destination.
                if dest.proj.is_empty() {
                    let l = dest.local as usize;
                    if !self.body.locals[l].mutable && st.maybe_init.contains(l) {
                        let name = self.local_name(dest.local);
                        self.err("L0302", span, format!("cannot assign twice to immutable variable {name}"), "Declare it with `let mut`.");
                    }
                    self.access(dest, Access::Write, span, &live);
                    self.check_store_into_param_ref(dest.local, &new_holds, st, span);
                    st.maybe_init.insert(l);
                    st.maybe_uninit.remove(l);
                    st.maybe_moved.remove(l);
                    st.holds[l] = new_holds;
                } else {
                    self.check_init(dest, span, st);
                    self.check_mutability(dest, span, st, false);
                    self.access(dest, Access::Write, span, &live);
                    self.check_store_into_param_ref(dest.local, &new_holds, st, span);
                    st.holds[dest.local as usize].union(&new_holds);
                }
            }
            StmtKind::Drop(l) | StmtKind::StorageDead(l) => {
                let place = Place::local(*l);
                self.access(&place, Access::Dead, span, &live);
                let li = *l as usize;
                st.maybe_init.remove(li);
                st.maybe_uninit.insert(li);
                if matches!(s, StmtKind::StorageDead(_)) {
                    st.holds[li].clear();
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

    fn dest_ty(&self, dest: &Place) -> Ty {
        let mut t = self.body.locals[dest.local as usize].ty;
        for pr in &dest.proj {
            t = match (self.body.tys.kind(t), pr) {
                (TyKind::Ref(_, i), Proj::Deref) => i,
                (TyKind::Vec(e), Proj::Index(_)) => e,
                _ => return ERROR,
            };
        }
        t
    }

    /// A reference that comes from a parameter must keep borrowing from parameters.
    /// Storing a borrow of a local value into such a place is an error even if the
    /// place is never read again (`v = &mut Vec::new()` for `v: &mut Vec<_>`), because
    /// the signature ties the place's reference to the caller's lifetime.
    fn check_store_into_param_ref(&mut self, root: Local, new_holds: &BitSet, st: &State, span: Span) {
        if !self.report {
            return;
        }
        if !st.holds[root as usize].iter().any(|li| self.loans[li].synthetic) {
            return;
        }
        for li in new_holds.iter() {
            let loan = &self.loans[li];
            if loan.synthetic || loan.place.proj.contains(&Proj::Deref) {
                continue;
            }
            let name = self.local_name(loan.place.local);
            let dest = self.local_name(root);
            self.err(
                "L0306",
                span,
                format!("{name} does not live long enough: it is borrowed into {dest}, which borrows from a parameter"),
                "Borrow from a parameter instead, or store an owned value (for example `*dest = value`).",
            );
            return;
        }
    }

    fn holds_of(&self, o: &Operand, st: &State, out: &mut BitSet) {
        if let Operand::Copy(p) | Operand::Move(p) = o {
            out.union(&st.holds[p.local as usize]);
        }
    }

    /// References passed to a call may be stored behind one of its `&mut` arguments, if that
    /// argument's target type can hold references (for example `v.push(&x)` on a `Vec<&T>`).
    fn flow_into_mut_args(&self, args: &[Operand], st: &mut State) {
        for (i, a) in args.iter().enumerate() {
            let (Operand::Move(p) | Operand::Copy(p)) = a else { continue };
            let ty = self.place_ty(p);
            let TyKind::Ref(true, target) = self.body.tys.kind(ty) else { continue };
            if !contains_ref(&self.body.tys, target) {
                continue;
            }
            let mut incoming = BitSet::new(self.loans.len());
            for (j, b) in args.iter().enumerate() {
                if j != i {
                    self.holds_of(b, st, &mut incoming);
                }
            }
            if incoming.is_empty() {
                continue;
            }
            let targets: Vec<Local> =
                st.holds[p.local as usize].iter().filter(|&l| self.loans[l].mutable).map(|l| self.loans[l].place.local).collect();
            for t in targets {
                st.holds[t as usize].union(&incoming);
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
                // Moving a payload out of a local enum or struct (`match opt { Some(s) => .. }`)
                // moves the whole local: it cannot be used again.
                let partial = p.proj.iter().all(|x| matches!(x, Proj::Field(_) | Proj::Downcast(_)));
                if partial {
                    let l = p.local as usize;
                    st.maybe_init.remove(l);
                    st.maybe_uninit.insert(l);
                    st.maybe_moved.insert(l);
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
        } else if self.report && self.seen.insert(("L9001", span.start, span.end)) {
            let mut d = unsupported(span, "moving a field out of a struct or enum");
            d.fix = "Clone the field with `.clone()`, or match on a reference (`match &value`) and borrow it.".into();
            self.errs.push(d);
        }
    }

    fn check_init(&mut self, p: &Place, span: Span, st: &State) {
        let l = p.local as usize;
        if self.report && st.maybe_uninit.contains(l) {
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
                (TyKind::Ref(m, inner), Proj::Deref) => {
                    if !m {
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
                (TyKind::Vec(e), Proj::Index(_)) => t = e,
                (TyKind::Adt(a), Proj::Field(i)) => {
                    t = self.p.adt(a).variants[variant as usize].fields[*i as usize].ty;
                    variant = 0;
                }
                (TyKind::Adt(_), Proj::Downcast(v)) => variant = *v,
                (TyKind::Option(e), Proj::Field(_)) => t = e,
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
        let holds = st.holds[0].clone();
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
