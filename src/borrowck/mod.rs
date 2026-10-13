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
/// is stored inline, so temporary sets (new loans for one statement, live
/// loans at one point) need no heap allocation. Dataflow states do not use
/// this type: see `State`.
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
        bit_set(self.words_mut(), i);
    }
    fn remove(&mut self, i: usize) {
        bit_unset(self.words_mut(), i);
    }
    fn contains(&self, i: usize) -> bool {
        bit_has(self.words(), i)
    }
    fn union(&mut self, o: &BitSet) -> bool {
        bits_or(self.words_mut(), o.words())
    }
    /// Unions in a set stored as words (a row of a `State`).
    fn union_words(&mut self, o: &[u64]) -> bool {
        bits_or(self.words_mut(), o)
    }
    fn clear(&mut self) {
        self.words_mut().fill(0);
    }
    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        bit_iter(self.words())
    }
    fn is_empty(&self) -> bool {
        bits_none(self.words())
    }
}

// Bit operations on word slices: the rows of a `State` and the words of a `BitSet`.

fn bit_has(w: &[u64], i: usize) -> bool {
    w[i / 64] & (1 << (i % 64)) != 0
}

fn bit_set(w: &mut [u64], i: usize) {
    w[i / 64] |= 1 << (i % 64);
}

fn bit_unset(w: &mut [u64], i: usize) {
    w[i / 64] &= !(1 << (i % 64));
}

/// `dst |= src`; true if `dst` gained a bit.
fn bits_or(dst: &mut [u64], src: &[u64]) -> bool {
    let mut changed = 0;
    for (a, b) in dst.iter_mut().zip(src) {
        changed |= b & !*a;
        *a |= b;
    }
    changed != 0
}

fn bits_none(w: &[u64]) -> bool {
    w.iter().all(|&x| x == 0)
}

/// The set bits in ascending order.
fn bit_iter(w: &[u64]) -> impl Iterator<Item = usize> + '_ {
    w.iter().enumerate().flat_map(|(wi, &x)| {
        let mut x = x;
        std::iter::from_fn(move || {
            if x == 0 {
                return None;
            }
            let b = x.trailing_zeros() as usize;
            x &= x - 1;
            Some(wi * 64 + b)
        })
    })
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

/// Locals assigned exactly once, from a constant integer: the index
/// temporaries pattern and loop lowering make for fixed array slots.
/// A constant index into an array names one element like a field does,
/// so moves out of it are partial moves; any other index is not exact.
pub(crate) fn const_index_locals(body: &Body) -> std::collections::HashMap<Local, u64> {
    // Locals are dense indices into `body.locals`, so the scan is
    // two flat vectors (one hash map entry and insert per assign
    // was about 99M instructions on the 48k crate). Only the few
    // surviving locals enter the returned map, whose contents are
    // the same as a hashed scan would build.
    let mut writes: Vec<u32> = vec![0; body.locals.len()];
    let mut value: Vec<Option<u64>> = vec![None; body.locals.len()];
    let mut note_write = |dest: &Place, v: Option<u64>| {
        if dest.proj.is_empty() {
            let l = dest.local as usize;
            if l >= writes.len() {
                writes.resize(l + 1, 0);
                value.resize(l + 1, None);
            }
            writes[l] += 1;
            value[l] = v;
        }
    };
    for b in &body.blocks {
        for s in &b.stmts {
            if let StmtKind::Assign(dest, rv) = &s.kind {
                let v = match rv {
                    Rvalue::Use(Operand::Const(Const::Int(v, _))) if *v <= u64::MAX as u128 => Some(*v as u64),
                    _ => None,
                };
                note_write(dest, v);
            }
        }
        if let Terminator::Call { dest, .. } = &b.term {
            note_write(dest, None);
        }
    }
    value
        .into_iter()
        .enumerate()
        .filter_map(|(l, v)| if writes[l] == 1 { v.map(|v| (l as Local, v)) } else { None })
        .collect()
}

fn is_prefix(a: &[u64], b: &[u64]) -> bool {
    a.len() <= b.len() && a.iter().zip(b).all(|(x, y)| x == y)
}

/// The word layout of a `State` for one body: `n` locals, sets over locals
/// take `wn` words, sets over loans `wl` words, and the move-path set `wm`.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Shape {
    n: usize,
    wn: usize,
    wl: usize,
    wm: usize,
}

/// The forward dataflow state at one program point. Every set lives in one
/// flat word vector, so copying a block's entry state is one memcpy and a
/// join is one pass of word ORs. (Per-local vectors and hash sets made
/// state copies most of borrowck's time on large crates.) The sets:
///
/// - `init`, `uninit`, `moved`: maybe-initialized, maybe-uninitialized,
///   and maybe-moved locals.
/// - `holds(l)`: the loans local `l` may hold.
/// - `origins(l)`: every loan local `l` was ever assigned on this path.
///   Unlike `holds` this is never overwritten by a later assignment (until
///   storage ends). A local in Rust has one fixed lifetime, so at a return
///   or a store behind a parameter every value the local ever held must
///   satisfy that lifetime. Later assignments cannot hide an earlier one.
///   This is only used at those sinks, not for loan liveness.
/// - `paths`: the field paths that may have been moved out of their local,
///   one bit per entry of `Ck::mpaths`. The empty path means the whole
///   local may have been moved.
#[derive(Clone, PartialEq, Eq)]
struct State {
    sh: Shape,
    w: Vec<u64>,
}

impl State {
    fn new(sh: Shape) -> State {
        State { sh, w: vec![0; 3 * sh.wn + 2 * sh.n * sh.wl + sh.wm] }
    }
    fn init(&self) -> &[u64] {
        &self.w[..self.sh.wn]
    }
    fn init_mut(&mut self) -> &mut [u64] {
        let wn = self.sh.wn;
        &mut self.w[..wn]
    }
    fn uninit(&self) -> &[u64] {
        &self.w[self.sh.wn..2 * self.sh.wn]
    }
    fn uninit_mut(&mut self) -> &mut [u64] {
        let wn = self.sh.wn;
        &mut self.w[wn..2 * wn]
    }
    fn moved(&self) -> &[u64] {
        &self.w[2 * self.sh.wn..3 * self.sh.wn]
    }
    fn moved_mut(&mut self) -> &mut [u64] {
        let wn = self.sh.wn;
        &mut self.w[2 * wn..3 * wn]
    }
    fn holds_at(&self, l: usize) -> usize {
        3 * self.sh.wn + l * self.sh.wl
    }
    fn origins_at(&self, l: usize) -> usize {
        3 * self.sh.wn + (self.sh.n + l) * self.sh.wl
    }
    fn holds(&self, l: usize) -> &[u64] {
        let a = self.holds_at(l);
        &self.w[a..a + self.sh.wl]
    }
    fn holds_mut(&mut self, l: usize) -> &mut [u64] {
        let (a, wl) = (self.holds_at(l), self.sh.wl);
        &mut self.w[a..a + wl]
    }
    fn origins(&self, l: usize) -> &[u64] {
        let a = self.origins_at(l);
        &self.w[a..a + self.sh.wl]
    }
    fn origins_mut(&mut self, l: usize) -> &mut [u64] {
        let (a, wl) = (self.origins_at(l), self.sh.wl);
        &mut self.w[a..a + wl]
    }
    fn paths(&self) -> &[u64] {
        &self.w[3 * self.sh.wn + 2 * self.sh.n * self.sh.wl..]
    }
    fn paths_mut(&mut self) -> &mut [u64] {
        let a = 3 * self.sh.wn + 2 * self.sh.n * self.sh.wl;
        &mut self.w[a..]
    }
    fn join(&mut self, o: &State) -> bool {
        bits_or(&mut self.w, &o.w)
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
    /// The index of a block's first statement in body-wide statement order.
    stmt_base: Vec<usize>,
    /// Loan created by each statement (`u32::MAX` if none), by body-wide index.
    loan_at: Vec<u32>,
    preds: Vec<Vec<u32>>,
    /// Successor blocks per block, computed once: with call terminators most
    /// blocks end in a call, and recomputing edges in every pass showed up
    /// in profiles.
    succs: Vec<Vec<Bb>>,
    /// Live locals after each statement, `sh.wn` words per statement, by
    /// body-wide statement index.
    live_out: Vec<u64>,
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
    /// Defs of Adts with a user `Drop` impl (any impl of the lang `Drop`
    /// trait whose Self head is that Adt). Computed once per body from
    /// the impl index; the partial-move checks below read it.
    drop_heads: HashSet<crate::def::DefId>,
    /// Index locals with a known constant value (see `const_index_locals`).
    const_index: std::collections::HashMap<Local, u64>,
    /// The layout of every `State` of this body.
    sh: Shape,
    /// Every exact path the body moves out of (see `prefix_of`), as
    /// `(local, path)`, sorted. `State::paths` has one bit per entry.
    mpaths: Vec<(Local, Path)>,
    /// The `mpaths` index range of each local's paths.
    mpath_at: Vec<(u32, u32)>,
    /// Per local: its type contains a reference (computed once; every
    /// assignment asks, in every pass).
    ref_local: Vec<bool>,
    /// Reused operand list of the statement being checked, so a statement
    /// visit does not allocate.
    ops_buf: Vec<&'b Operand>,
}

/// The Adt defs that have a user `Drop` impl: every impl of the lang
/// `Drop` trait whose Self type head is an Adt. Conditional impls
/// count (the partial-move checks are conservative).
fn drop_heads(p: &Program) -> HashSet<crate::def::DefId> {
    let mut out = HashSet::new();
    for &id in p.gx.index.impls_of_trait(p.gx.lang.drop) {
        let rec = p.gx.index.get(id);
        if let Some(self_ty) = p.tys.args(rec.trait_ref.args).first().and_then(|g| g.as_ty()) {
            if let TyKind::Adt(def, _) = p.tys.kind(self_ty) {
                out.insert(def);
            }
        }
    }
    out
}

/// Borrow-checks one function body.
pub fn borrowck(p: &Program, body: &Body) -> Vec<Diag> {
    let drop_heads = drop_heads(p);
    let mut ck = Ck {
        p,
        body,
        loans: Vec::new(),
        stmt_base: Vec::new(),
        loan_at: Vec::new(),
        preds: vec![Vec::new(); body.blocks.len()],
        succs: Vec::new(),
        live_out: Vec::new(),
        live_in_block: Vec::new(),
        errs: Vec::new(),
        seen: HashSet::new(),
        report: false,
        escaped: BitSet::new(0),
        loan_block: Vec::new(),
        loan_stmt: Vec::new(),
        reach: Vec::new(),
        collecting: false,
        drop_heads,
        const_index: const_index_locals(body),
        sh: Shape { n: 0, wn: 0, wl: 0, wm: 0 },
        mpaths: Vec::new(),
        mpath_at: Vec::new(),
        ref_local: body.locals.iter().map(|l| contains_ref(&body.tys, l.ty)).collect(),
        ops_buf: Vec::new(),
    };
    if !body.lower_errs.is_empty() {
        return body.lower_errs.clone();
    }
    ck.collect_loans();
    ck.collect_move_paths();
    let n = body.locals.len();
    // A body with no loans keeps no loan rows in its states
    // (`wl` 0: every holds/origins row is empty), and the two
    // passes that only exist to answer which loans are live
    // (reachability for escaped loans, local liveness) skip:
    // `live_loans` is empty at every point of such a body, and
    // the two call sites that ask for it short-circuit below.
    ck.sh = Shape { n, wn: n.div_ceil(64).max(1), wl: ck.loans.len().div_ceil(64), wm: ck.mpaths.len().div_ceil(64) };
    ck.escaped = BitSet::new(ck.loans.len());
    ck.compute_preds();
    if !ck.loans.is_empty() {
        ck.compute_reach();
        ck.liveness();
    }
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
        Rvalue::Use(o) | Rvalue::Un(_, o) | Rvalue::Cast(o, _) | Rvalue::Opt(_, Some(o)) | Rvalue::Res(_, _, o) => f(o),
        Rvalue::Opt(_, None) => {}
        Rvalue::Bin(_, a, b) | Rvalue::StrCmp(_, a, b) | Rvalue::StringAdd(a, b) | Rvalue::Eq { a, b, .. } => {
            f(a);
            f(b);
        }
        Rvalue::VecRepeat(_, a, b) => {
            f(a);
            f(b);
        }
        Rvalue::Aggregate(_, _, ops) | Rvalue::VecLit(_, ops) | Rvalue::TupleAgg(_, ops) | Rvalue::ArrayAgg(_, ops) => {
            ops.iter().for_each(f)
        }
        Rvalue::ArrayRepeat(_, o, _) => f(o),
        Rvalue::Format(parts) => parts.iter().for_each(|p| {
            if let FmtPart::Arg { value, .. } = p {
                f(value)
            }
        }),
        Rvalue::Ref(..)
        | Rvalue::Discriminant(_)
        | Rvalue::SliceOf(_)
        | Rvalue::LenOf(_)
        | Rvalue::StaticLoad(_)
        | Rvalue::StaticRef(_)
        | Rvalue::FnValue(..) => {}
        Rvalue::Subslice { lo, hi, .. } => {
            f(lo);
            if let Some(h) = hi {
                f(h);
            }
        }
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
        let mut base = 0;
        for b in &self.body.blocks {
            self.stmt_base.push(base);
            base += b.stmts.len();
        }
        self.loan_at = vec![u32::MAX; base];
        for (bi, b) in self.body.blocks.iter().enumerate() {
            for (si, s) in b.stmts.iter().enumerate() {
                // SliceOf and Subslice make slice references, so they create
                // loans just like Ref (W-CORELANG); mutability comes from the
                // destination local's slice reference type.
                let loan_src: Option<(bool, &Place)> = match &s.kind {
                    StmtKind::Assign(_, Rvalue::Ref(m, place)) => Some((*m, place)),
                    StmtKind::Assign(dest, Rvalue::SliceOf(place)) => Some((self.slice_dest_mut(dest), place)),
                    StmtKind::Assign(_, Rvalue::Subslice { base, mutable, .. }) => Some((*mutable, base)),
                    _ => None,
                };
                if let (StmtKind::Assign(dest, _), Some((m, place))) = (&s.kind, loan_src) {
                    self.loan_block.push(bi as u32);
                    self.loan_stmt.push(si as u32);
                    self.loan_at[self.stmt_base[bi] + si] = self.loans.len() as u32;
                    holders.push(if dest.proj.is_empty() { Some(dest.local) } else { None });
                    self.loans.push(Loan { place: place.clone(), mutable: m, synthetic: false, span: s.span, last_use: None });
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
                    StmtKind::Assign(_, Rvalue::Ref(_, p))
                    | StmtKind::Assign(_, Rvalue::Discriminant(p))
                    | StmtKind::Assign(_, Rvalue::LenOf(p))
                    | StmtKind::Assign(_, Rvalue::SliceOf(p))
                    | StmtKind::Assign(_, Rvalue::Subslice { base: p, .. }) => uses.push((p.local, s.span)),
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
                Terminator::Call { target, args, .. } => {
                    if let CallTarget::Indirect(callee) = target {
                        note(&Operand::Copy(Place::local(*callee)));
                    }
                    args.iter().for_each(&mut note);
                }
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

    /// Fills `mpaths`: the exact paths (`prefix_of`) of every move operand,
    /// at the same operand sites `operand` checks (rvalue and print
    /// operands, call arguments, branch conditions, panic arguments).
    /// Needs `const_index`.
    fn collect_move_paths(&mut self) {
        let mut all: Vec<(Local, Path)> = Vec::new();
        let mut note = |o: &Operand| {
            if let Operand::Move(p) = o
                && let (path, true) = self.prefix_of(p)
            {
                all.push((p.local, path));
            }
        };
        for b in &self.body.blocks {
            for s in &b.stmts {
                match &s.kind {
                    StmtKind::Assign(_, rv) => rvalue_operands(rv, &mut note),
                    StmtKind::Print { parts, .. } => parts_operands(parts, &mut note),
                    _ => {}
                }
            }
            match &b.term {
                Terminator::Call { args, .. } => args.iter().for_each(&mut note),
                Terminator::If(o, ..) | Terminator::Switch(o, ..) => note(o),
                Terminator::Panic(parts) => parts_operands(parts, &mut note),
                _ => {}
            }
        }
        all.sort();
        all.dedup();
        let mut at = vec![(0u32, 0u32); self.body.locals.len()];
        for (i, (l, _)) in all.iter().enumerate() {
            let e = &mut at[*l as usize];
            if e.1 == 0 {
                e.0 = i as u32;
            }
            e.1 = i as u32 + 1;
        }
        self.mpaths = all;
        self.mpath_at = at;
    }

    /// The `mpaths` indices of local `l`'s move paths.
    fn mpath_range(&self, l: usize) -> std::ops::Range<usize> {
        let (a, b) = self.mpath_at[l];
        a as usize..b as usize
    }

    /// The `mpaths` index of local `l`'s exact path `path`, if the body
    /// moves out of it.
    fn mpath_index(&self, l: usize, path: &[u64]) -> Option<usize> {
        self.mpath_range(l).find(|&i| self.mpaths[i].1 == path)
    }

    /// Clears every moved path of local `l`.
    fn clear_paths(&self, st: &mut State, l: usize) {
        for i in self.mpath_range(l) {
            bit_unset(st.paths_mut(), i);
        }
    }

    /// The moved paths of local `l` in `st`, in `mpaths` order.
    fn moved_paths<'s>(&'s self, st: &'s State, l: usize) -> impl Iterator<Item = &'s Path> + 's {
        self.mpath_range(l).filter(move |&i| bit_has(st.paths(), i)).map(move |i| &self.mpaths[i].1)
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
                if let Rvalue::Ref(_, p) | Rvalue::Discriminant(p) | Rvalue::SliceOf(p) | Rvalue::LenOf(p) = rv {
                    Self::uses_place(live, p);
                }
                if let Rvalue::Subslice { base, .. } = rv {
                    Self::uses_place(live, base);
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
            Terminator::Call { target, args, dest, .. } => {
                if dest.proj.is_empty() {
                    live.remove(dest.local as usize);
                } else {
                    Self::uses_place(live, dest);
                }
                if let CallTarget::Indirect(callee) = target {
                    live.insert(*callee as usize);
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
        // Backward problem: visit reachable blocks in postorder (successors
        // first, back edges aside), then unreachable ones, so a sweep mostly
        // sees final successor sets and few sweeps run. The result is the
        // same in any order.
        let mut order: Vec<u32> = self.reverse_postorder();
        order.reverse();
        let mut listed = vec![false; nb];
        for &b in &order {
            listed[b as usize] = true;
        }
        order.extend((0..nb as u32).rev().filter(|&b| !listed[b as usize]));
        let mut changed = true;
        while changed {
            changed = false;
            for &bi in &order {
                let bi = bi as usize;
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
        // Per-statement live-out sets, flat.
        let wn = live.words().len();
        let total: usize = self.body.blocks.iter().map(|b| b.stmts.len()).sum();
        self.live_out = vec![0; total * wn];
        for bi in 0..nb {
            let b = &self.body.blocks[bi];
            live.clear();
            for s in &self.succs[bi] {
                live.union(&live_in[s.0 as usize]);
            }
            Self::live_term(&b.term, &mut live);
            for (si, s) in b.stmts.iter().enumerate().rev() {
                let at = (self.stmt_base[bi] + si) * wn;
                self.live_out[at..at + wn].copy_from_slice(live.words());
                Self::live_stmt(&s.kind, &mut live);
            }
        }
        self.live_in_block = live_in;
    }

    /// The live locals after statement `si` of block `b`.
    fn live_after(&self, b: u32, si: u32) -> &[u64] {
        let wn = self.sh.wn;
        let at = (self.stmt_base[b as usize] + si as usize) * wn;
        &self.live_out[at..at + wn]
    }

    // ---------- Forward dataflow and checks ----------

    fn entry_state(&self) -> State {
        let n = self.n_locals();
        let mut st = State::new(self.sh);
        for l in 0..n {
            if l >= 1 && l <= self.body.arg_count {
                bit_set(st.init_mut(), l);
            } else {
                bit_set(st.uninit_mut(), l);
            }
        }
        for (i, loan) in self.loans.iter().enumerate() {
            if loan.synthetic {
                bit_set(st.holds_mut(loan.place.local as usize), i);
                bit_set(st.origins_mut(loan.place.local as usize), i);
            }
        }
        st
    }

    /// The blocks reachable from the entry, in reverse postorder: every
    /// block comes after all its predecessors except along back edges.
    fn reverse_postorder(&self) -> Vec<u32> {
        let nb = self.body.blocks.len();
        let mut seen = vec![false; nb];
        let mut post = Vec::with_capacity(nb);
        // (block, next successor index), an explicit DFS stack.
        let mut stack: Vec<(u32, usize)> = vec![(0, 0)];
        seen[0] = true;
        while let Some(top) = stack.last_mut() {
            let (b, k) = *top;
            match self.succs[b as usize].get(k) {
                Some(s) => {
                    top.1 += 1;
                    if !seen[s.0 as usize] {
                        seen[s.0 as usize] = true;
                        stack.push((s.0, 0));
                    }
                }
                None => {
                    post.push(b);
                    stack.pop();
                }
            }
        }
        post.reverse();
        post
    }

    fn dataflow(&mut self) {
        let nb = self.body.blocks.len();
        let mut entry: Vec<Option<State>> = vec![None; nb];
        entry[0] = Some(self.entry_state());
        // Visit pending blocks in reverse postorder, in rounds: a block's
        // predecessors (back edges aside) run before it in the same round,
        // so most blocks run once and only loops take another round. The
        // fixpoint is the same in any visit order.
        let rpo = self.reverse_postorder();
        let mut pending = vec![false; nb];
        pending[0] = true;
        // Fixpoint without reporting, then one reporting pass over the final states.
        // `st` is the one scratch state: each visit copies a block's entry state
        // into it, so no visit allocates.
        //
        // The fixpoint also learns which loans escape into a return value or
        // behind a parameter (`collecting`); the reporting pass then keeps those
        // loans live everywhere rustc's NLL does. Collecting during the fixpoint
        // gives the same set as a pass over the final states: states only grow
        // toward the final ones, the escape rules are monotone in the state, and
        // every block's last visit runs on its final entry state.
        self.collecting = true;
        let mut st = State::new(self.sh);
        while pending.contains(&true) {
            for &b in &rpo {
                if !pending[b as usize] {
                    continue;
                }
                pending[b as usize] = false;
                st.w.copy_from_slice(&entry[b as usize].as_ref().unwrap().w);
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
                    // A successor later in the order runs in this round; one at
                    // or before `b` (a back edge) runs in the next.
                    pending[si] |= changed;
                }
            }
        }
        self.collecting = false;
        self.report = true;
        for (b, e) in entry.iter().enumerate() {
            if let Some(e) = e {
                st.w.copy_from_slice(&e.w);
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
            Terminator::Call { target, args, dest, .. } => self.call_term(b, *target, args, dest, span, st),
            Terminator::If(o, ..) | Terminator::Switch(o, ..) => ops.push(o),
            Terminator::Panic(parts) => parts_operands(parts, &mut |o| ops.push(o)),
            Terminator::Return if self.report => {
                self.check_return(st, span);
            }
            Terminator::Return if self.collecting => {
                self.escaped.union_words(st.holds(0));
                self.escaped.union_words(st.origins(0));
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
    fn live_loans(&self, st: &State, live: &[u64], skip: Option<Local>, b: u32, si: u32) -> BitSet {
        let mut out = BitSet::new(self.loans.len());
        for l in bit_iter(live) {
            if Some(l as Local) == skip {
                continue;
            }
            out.union_words(st.holds(l));
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

    fn stmt(&mut self, b: u32, si: u32, s: &'b StmtKind, span: Span, st: &mut State) {
        // Loans live after this statement. Only needed in the reporting pass.
        let skip = match s {
            StmtKind::Assign(dest, _) if dest.proj.is_empty() => Some(dest.local),
            _ => None,
        };
        let live = if self.report && !self.loans.is_empty() {
            self.live_loans(st, self.live_after(b, si), skip, b, si)
        } else {
            BitSet::new(0)
        };
        match s {
            StmtKind::Assign(dest, rv) => {
                // Reads and moves in the right-hand side.
                let mut ops = std::mem::take(&mut self.ops_buf);
                ops.clear();
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
                        let loan = self.loan_at[self.stmt_base[b as usize] + si as usize] as usize;
                        new_holds.insert(loan);
                        new_origins.insert(loan);
                        // A reborrow through a reference depends on that reference's loans.
                        if place.proj.contains(&Proj::Deref) {
                            new_holds.union_words(st.holds(place.local as usize));
                            new_origins.union_words(st.origins(place.local as usize));
                        }
                    }
                    Rvalue::SliceOf(place) => {
                        let m = self.slice_dest_mut(dest);
                        self.check_init(place, span, st);
                        let kind = if m { Access::BorrowMut } else { Access::BorrowShared };
                        if m {
                            self.check_mutability(place, span, st, true);
                        }
                        self.access(place, kind, span, &live);
                        let loan = self.loan_at[self.stmt_base[b as usize] + si as usize] as usize;
                        new_holds.insert(loan);
                        new_origins.insert(loan);
                        if place.proj.contains(&Proj::Deref) {
                            new_holds.union_words(st.holds(place.local as usize));
                            new_origins.union_words(st.origins(place.local as usize));
                        }
                    }
                    Rvalue::Subslice { base: place, mutable, .. } => {
                        let m = *mutable;
                        self.check_init(place, span, st);
                        let kind = if m { Access::BorrowMut } else { Access::BorrowShared };
                        if m {
                            self.check_mutability(place, span, st, true);
                        }
                        self.access(place, kind, span, &live);
                        let loan = self.loan_at[self.stmt_base[b as usize] + si as usize] as usize;
                        new_holds.insert(loan);
                        new_origins.insert(loan);
                        if place.proj.contains(&Proj::Deref) {
                            new_holds.union_words(st.holds(place.local as usize));
                            new_origins.union_words(st.origins(place.local as usize));
                        }
                    }
                    Rvalue::Discriminant(place) | Rvalue::LenOf(place) => {
                        self.check_init(place, span, st);
                        self.access(place, Access::Read, span, &live);
                    }
                    _ => {
                        if self.dest_holds_refs(dest) {
                            for o in &ops {
                                self.holds_of(o, st, &mut new_holds);
                                self.origins_of(o, st, &mut new_origins);
                            }
                        }
                    }
                }
                self.write_dest(dest, new_holds, &new_origins, span, &live, st);
                self.ops_buf = ops;
            }
            StmtKind::Drop(l) | StmtKind::StorageDead(l) => {
                let place = Place::local(*l);
                self.access(&place, Access::Dead, span, &live);
                let li = *l as usize;
                bit_unset(st.init_mut(), li);
                bit_set(st.uninit_mut(), li);
                if matches!(s, StmtKind::StorageDead(_)) {
                    st.holds_mut(li).fill(0);
                    st.origins_mut(li).fill(0);
                    self.clear_paths(st, li);
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
            if !self.body.locals[l].mutable && bit_has(st.init(), l) {
                let name = self.local_name(dest.local);
                self.err("L0302", span, format!("cannot assign twice to immutable variable {name}"), "Declare it with `let mut`.");
            }
            self.access(dest, Access::Write, span, live);
            self.check_store_into_param_ref(dest, new_origins, st, span);
            bit_set(st.init_mut(), l);
            bit_unset(st.uninit_mut(), l);
            bit_unset(st.moved_mut(), l);
            self.clear_paths(st, l);
            // Zip, not copy_from_slice: with no loans the row is
            // empty while `new_holds` keeps its one inline (zero)
            // word. With loans the lengths are both `wl`.
            for (a, b) in st.holds_mut(l).iter_mut().zip(new_holds.words()) {
                *a = *b;
            }
            bits_or(st.origins_mut(l), new_origins.words());
        } else {
            self.check_init_write(dest, span, st);
            self.check_mutability(dest, span, st, false);
            self.access(dest, Access::Write, span, live);
            self.check_store_into_param_ref(dest, new_origins, st, span);
            // Writing a field puts back a field that was moved out, and every
            // field below it. Other moved fields stay moved.
            let l = dest.local as usize;
            if self.mpath_range(l).any(|i| bit_has(st.paths(), i)) {
                let (path, exact) = self.prefix_of(dest);
                if exact {
                    for i in self.mpath_range(l) {
                        if is_prefix(&path, &self.mpaths[i].1) {
                            bit_unset(st.paths_mut(), i);
                        }
                    }
                }
            }
            bits_or(st.holds_mut(l), new_holds.words());
            bits_or(st.origins_mut(l), new_origins.words());
        }
    }

    /// One `Call` terminator, checked like the assignment it ends: argument
    /// reads first, then loan flow into the result and into `&mut` argument
    /// targets, then the write to `dest`. The loans live after the call are
    /// the ones its successors keep live.
    fn call_term(&mut self, b: u32, target: CallTarget, args: &[Operand], dest: &Place, span: Span, st: &mut State) {
        let si = self.body.blocks[b as usize].stmts.len() as u32;
        let skip = if dest.proj.is_empty() { Some(dest.local) } else { None };
        let live = if self.report && !self.loans.is_empty() {
            let mut locals = BitSet::new(self.n_locals());
            for s in &self.succs[b as usize] {
                locals.union(&self.live_in_block[s.0 as usize]);
            }
            self.live_loans(st, locals.words(), skip, b, si)
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
                } else if contains_ref(&self.body.tys, self.dest_ty(dest)) {
                    // A result that holds references with no single
                    // source parameter (a generic `fn keep<F>(f: F) -> F`
                    // called with a closure that borrows): it may hold
                    // any argument's loans, as in the indirect case.
                    for o in args {
                        self.holds_of(o, st, &mut new_holds);
                        self.origins_of(o, st, &mut new_origins);
                    }
                }
                self.flow_into_mut_args(args, st, span);
            }
            CallTarget::Indirect(callee) => {
                // The callee signature is not a fn the checker can
                // summarize yet, so treat the call conservatively: the
                // callee local is read, a reference result may hold any
                // argument's loans, and loans flow into &mut args. The
                // IR owner refines this when fn pointers lower.
                self.operand(&Operand::Copy(Place::local(callee)), span, st, &live);
                if self.dest_holds_refs(dest) {
                    for o in args {
                        self.holds_of(o, st, &mut new_holds);
                        self.origins_of(o, st, &mut new_origins);
                    }
                }
                self.flow_into_mut_args(args, st, span);
            }
            CallTarget::Builtin(_) | CallTarget::Intrinsic(_) => {
                // Builtins were plain rvalues before S7: a reference-typed
                // result may hold any argument's loans.
                if self.dest_holds_refs(dest) {
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

    /// True when the type written at `dest` contains a reference.
    fn dest_holds_refs(&self, dest: &Place) -> bool {
        if dest.proj.is_empty() { self.ref_local[dest.local as usize] } else { contains_ref(&self.body.tys, self.dest_ty(dest)) }
    }

    /// True when a slice-making assignment's destination is a `&mut [T]` local.
    fn slice_dest_mut(&self, dest: &Place) -> bool {
        dest.proj.is_empty() && matches!(self.body.tys.kind(self.body.locals[dest.local as usize].ty), TyKind::Ref(_, Mut::Mut, _))
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
    fn loan_origins(&self, holds: &[u64]) -> Vec<Local> {
        let mut out: Vec<Local> = Vec::new();
        for li in bit_iter(holds) {
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
        let origins = self.loan_origins(st.holds(root as usize));
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
            out.union_words(st.holds(p.local as usize));
        }
    }

    fn origins_of(&self, o: &Operand, st: &State, out: &mut BitSet) {
        if let Operand::Copy(p) | Operand::Move(p) = o {
            out.union_words(st.origins(p.local as usize));
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
                bit_iter(st.holds(p.local as usize)).filter(|&l| self.loans[l].mutable).map(|l| self.loans[l].place.local).collect();
            for t in targets {
                // Storing into a target behind a parameter needs the same origin check
                // as a direct assignment behind a parameter reference.
                let origins = self.loan_origins(st.holds(t as usize));
                if !origins.is_empty() {
                    if self.collecting {
                        self.escaped.union(&incoming_origins);
                    }
                    if self.report {
                        self.check_incoming_loans(&origins, &incoming_origins, t, span);
                    }
                }
                bits_or(st.holds_mut(t as usize), incoming.words());
                bits_or(st.origins_mut(t as usize), incoming_origins.words());
            }
        }
    }

    fn place_ty(&self, p: &Place) -> Ty {
        if p.proj.is_empty() { self.body.locals[p.local as usize].ty } else { self.dest_ty(p) }
    }

    /// The type one `Field` projection down from `t` (in the variant a
    /// preceding `Downcast` selected), or the error type when unknown.
    fn step_field_ty(&self, t: Ty, variant: u32, i: u32) -> Ty {
        match self.body.tys.kind(t) {
            TyKind::Tuple(ts) => self.body.tys.tys_of(ts).get(i as usize).copied().unwrap_or(ERROR),
            TyKind::Adt(..) => match self.body.tys.local_adt(t) {
                Some(a) => self
                    .p
                    .adt(a)
                    .variants
                    .get(variant as usize)
                    .and_then(|v| v.fields.get(i as usize))
                    .map(|f| f.ty)
                    .unwrap_or(ERROR),
                None => ERROR,
            },
            _ if self.body.tys.option_elem(t).is_some() => self.body.tys.option_elem(t).unwrap(),
            _ => ERROR,
        }
    }

    /// The leading exact part of a place as an encoded path, and whether
    /// that is the whole place. Fields, downcasts, and constant indexes
    /// into arrays are exact; a dereference or any other index is not,
    /// and the prefix still identifies the field the place reaches into.
    /// Encodings sit in the low two bits: 0 field, 1 downcast, 2 index.
    fn prefix_of(&self, p: &Place) -> (Path, bool) {
        let mut path = Vec::new();
        let mut t = self.body.locals[p.local as usize].ty;
        let mut variant = 0u32;
        for pr in &p.proj {
            match pr {
                Proj::Field(i) => {
                    path.push((*i as u64) << 2);
                    t = self.step_field_ty(t, variant, *i);
                    variant = 0;
                }
                Proj::Downcast(v) => {
                    path.push(((*v as u64) << 2) | 1);
                    variant = *v;
                }
                Proj::Index(l) => match self.body.tys.kind(t) {
                    TyKind::Array(e, _) => match self.const_index.get(l) {
                        Some(&c) if c < (1 << 60) => {
                            path.push((c << 2) | 2);
                            t = e;
                        }
                        _ => return (path, false),
                    },
                    _ => return (path, false),
                },
                Proj::Deref => return (path, false),
            }
        }
        (path, true)
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
                // also forbids partial moves out of a type with a `Drop` impl (E0509);
                // `check_partial_move` enforces that. Codegen drops only the parts a
                // partially moved local still owns (`cgen::FnGen::elab_drop`).
                let (path, exact) = self.prefix_of(p);
                if exact && !path.is_empty() {
                    self.check_partial_move(p, span);
                }
                // `collect_move_paths` gave every exact moved place an entry.
                let l = p.local as usize;
                match if exact { self.mpath_index(l, &path) } else { None } {
                    Some(id) => {
                        if path.is_empty() {
                            bit_unset(st.init_mut(), l);
                            bit_set(st.uninit_mut(), l);
                            bit_set(st.moved_mut(), l);
                            self.clear_paths(st, l);
                        }
                        bit_set(st.paths_mut(), id);
                    }
                    None => self.bad_move(p, span, st),
                }
            }
            Operand::Const(_) => {}
        }
    }

    /// Follows a `Param(i)` head through `env` (the type arguments of
    /// the Adt application the type was read from). An unresolvable
    /// param stays a param: it is a generic of the enclosing fn, whose
    /// drop behavior is unknown here.
    fn head_resolve(&self, mut t: Ty, env: &[Ty]) -> Ty {
        while let TyKind::Param(p) = self.body.tys.kind(t) {
            match env.get(p.0 as usize) {
                Some(&next) if next != t => t = next,
                _ => break,
            }
        }
        t
    }

    /// The type arguments of an Adt application, head-resolved through
    /// `env`, as the env for reading that Adt's field types.
    fn adt_env(&self, t: Ty, env: &[Ty]) -> Vec<Ty> {
        match self.body.tys.adt_parts(t) {
            Some((_, args)) => self.body.tys.args(args).iter().map(|g| self.head_resolve(g.as_ty().unwrap_or(ERROR), env)).collect(),
            None => Vec::new(),
        }
    }

    /// Rust's E0509 on an exact field path: no field moves out of a
    /// type with a `Drop` impl, at any step of the path. Copy fields
    /// are exempt: copying out is legal even from a `Drop` type.
    fn check_partial_move(&mut self, p: &Place, span: Span) {
        if !self.report {
            return;
        }
        let mut cur = self.body.locals[p.local as usize].ty;
        let mut env: Vec<Ty> = Vec::new();
        let mut variant = 0u32;
        let mut drop_container: Option<Ty> = None;
        for pr in &p.proj {
            match pr {
                Proj::Downcast(v) => variant = *v,
                Proj::Field(i) => {
                    let container = self.head_resolve(cur, &env);
                    if let Some((def, _)) = self.body.tys.adt_parts(container) {
                        if self.drop_heads.contains(&def) && self.body.tys.local_adt(container).is_some() {
                            drop_container = Some(container);
                        }
                    }
                    let next = match self.body.tys.kind(container) {
                        TyKind::Tuple(ts) => self.body.tys.tys_of(ts).get(*i as usize).copied().unwrap_or(ERROR),
                        TyKind::Adt(..) if self.body.tys.option_elem(container).is_some() => {
                            self.body.tys.option_elem(container).unwrap_or(ERROR)
                        }
                        TyKind::Adt(..) if self.body.tys.result_args(container).is_some() => {
                            let (a, b) = self.body.tys.result_args(container).unwrap();
                            if variant == 0 { a } else { b }
                        }
                        TyKind::Adt(..) => match self.body.tys.local_adt(container) {
                            Some(a) => {
                                let f = self.p.adt(a).variants.get(variant as usize).and_then(|v| v.fields.get(*i as usize));
                                match f {
                                    Some(f) => {
                                        let ty = f.ty;
                                        env = self.adt_env(container, &env);
                                        ty
                                    }
                                    None => ERROR,
                                }
                            }
                            None => ERROR,
                        },
                        _ => ERROR,
                    };
                    if next == ERROR {
                        return;
                    }
                    cur = next;
                    variant = 0;
                }
                Proj::Index(_) => {
                    // A constant index into an array is a partial move
                    // like a field; an array has no `Drop` impl of its own.
                    let container = self.head_resolve(cur, &env);
                    match self.body.tys.kind(container) {
                        TyKind::Array(e, _) => cur = e,
                        _ => return,
                    }
                }
                _ => return,
            }
        }
        let moved = self.head_resolve(cur, &env);
        if is_copy(self.p, &self.body.tys, moved) {
            return;
        }
        // A generic field is a move unless the bounds make it Copy:
        // the template check's body store carries its param env, so
        // `is_copy` above answers a param from its bounds.
        if let Some(container) = drop_container {
            self.err(
                "L0305",
                span,
                format!("cannot move out of {}, because it implements `Drop`", ty_name(self.p, &self.body.tys, container)),
                "Borrow the field with `&`, clone it, or use `std::mem::replace` (not yet supported) style code.",
            );
        }
    }

    /// The container type at the first `Index` step of `place`, when
    /// it indexes an array, a slice, or a `Vec`. Field and deref
    /// steps before the index step through their types.
    fn index_container_ty(&self, place: &Place) -> Option<Ty> {
        let mut t = self.body.locals[place.local as usize].ty;
        let mut variant = 0;
        for pr in &place.proj {
            match pr {
                Proj::Field(i) => {
                    t = self.step_field_ty(t, variant, *i);
                    variant = 0;
                }
                Proj::Downcast(v) => variant = *v,
                Proj::Deref => {
                    if let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
                        t = inner;
                    }
                }
                Proj::Index(_) => {
                    return match self.body.tys.kind(t) {
                        TyKind::Array(..) | TyKind::Slice(_) => Some(t),
                        _ if self.body.tys.vec_elem(t).is_some() => Some(t),
                        _ => None,
                    };
                }
            }
        }
        None
    }

    /// The diagnostic for a move out of an index read, in rustc's
    /// text classes (E0508 for an array or slice, E0507 for a
    /// `Vec`): a direct `Index` place, or the synthetic borrow
    /// temporary lowering routes a non-Copy index read through
    /// (`lower::operand_raw`), whose loan still names the indexed
    /// place. A named reference local keeps the plain reference
    /// text instead, as in rustc (`let x = *r;` is E0507 behind a
    /// reference, not E0508).
    fn index_move_diag(&self, p: &Place, st: &State) -> Option<(String, &'static str)> {
        let container = self.index_container_ty(p).or_else(|| {
            if self.body.locals[p.local as usize].name.is_some() {
                return None;
            }
            bit_iter(st.holds(p.local as usize)).find_map(|li| self.index_container_ty(&self.loans[li].place))
        })?;
        let name = self.container_name(container);
        Some(match self.body.tys.kind(container) {
            TyKind::Array(..) => (
                format!("cannot move out of type `{name}`, a non-copy array"),
                "Borrow the element with `&a[i]`, clone it, or move it out with an array pattern such as `let [x, ..] = a;`.",
            ),
            TyKind::Slice(_) => (
                format!("cannot move out of type `{name}`, a non-copy slice"),
                "Borrow the element with `&s[i]`, or clone it with `s[i].clone()`.",
            ),
            _ => (format!("cannot move out of index of `{name}`"), "Borrow the element with `&v[i]`, or clone it with `v[i].clone()`."),
        })
    }

    /// A container type name for `index_move_diag`: like
    /// `ty_name`, but an array length prints its value when the
    /// body knows it (the shared printer shows `_` today).
    fn container_name(&self, t: Ty) -> String {
        match self.body.tys.kind(t) {
            TyKind::Array(e, c) => match self.body.tys.const_kind(c) {
                ConstKind::Int(n) => format!("[{}; {}]", self.container_name(e), n),
                _ => ty_name(self.p, &self.body.tys, t),
            },
            TyKind::Slice(e) => format!("[{}]", self.container_name(e)),
            _ => ty_name(self.p, &self.body.tys, t),
        }
    }

    fn bad_move(&mut self, p: &Place, span: Span, st: &State) {
        if let Some((msg, fix)) = self.index_move_diag(p, st) {
            self.err("L0305", span, msg, fix);
        } else if p.proj.contains(&Proj::Deref) {
            self.err(
                "L0305",
                span,
                "cannot move out of a reference".into(),
                "Clone the value with `.clone()`, or borrow it with `&` instead of moving it.",
            );
        } else if p.proj.iter().any(|x| matches!(x, Proj::Index(_))) {
            // Name the indexed thing: a Vec's elements sit behind its
            // buffer, an array or slice index with a variable index
            // cannot name one element either.
            let mut t = self.body.locals[p.local as usize].ty;
            let mut variant = 0;
            for pr in &p.proj {
                match pr {
                    Proj::Field(i) => {
                        t = self.step_field_ty(t, variant, *i);
                        variant = 0;
                    }
                    Proj::Downcast(v) => variant = *v,
                    Proj::Deref => {
                        if let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
                            t = inner;
                        }
                    }
                    Proj::Index(_) => break,
                }
            }
            let what = if self.body.tys.vec_elem(t).is_some() { "a Vec index" } else { "an index" };
            self.err(
                "L0305",
                span,
                format!("cannot move out of {what}"),
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
        let (path, exact) = self.prefix_of(p);
        // A moved field blocks uses of itself, of fields below it, and of every value
        // that contains it. A sibling field is fine.
        let hit = self.moved_paths(st, l).find_map(|m| {
            if is_prefix(m, &path) {
                Some("use of moved value")
            } else if exact && is_prefix(&path, m) {
                Some("use of partially moved value")
            } else {
                None
            }
        });
        if let Some(what) = hit {
            let name = self.local_name(p.local);
            let fix = "Clone the value before the move with `.clone()`, or borrow it with `&` instead of moving it.";
            self.err("L0301", span, format!("{what}: {name}"), fix);
            return;
        }
        if bit_has(st.uninit(), l) {
            let name = self.local_name(p.local);
            if bit_has(st.moved(), l) {
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
        let (path, exact) = self.prefix_of(p);
        if self.moved_paths(st, l).any(|m| is_prefix(m, &path) && !(exact && m.len() == path.len())) {
            let name = self.local_name(p.local);
            let fix = "Clone the value before the move with `.clone()`, or borrow it with `&` instead of moving it.";
            self.err("L0301", span, format!("use of moved value: {name}"), fix);
            return;
        }
        if bit_has(st.uninit(), l) && self.moved_paths(st, l).next().is_none() {
            let name = self.local_name(p.local);
            if bit_has(st.moved(), l) {
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
                (TyKind::Array(e, _) | TyKind::Slice(e), Proj::Index(_)) => t = e,
                (TyKind::Tuple(ts), Proj::Field(i)) => {
                    t = self.body.tys.tys_of(ts).get(*i as usize).copied().unwrap_or(ERROR);
                }
                (TyKind::Adt(..), Proj::Field(i)) if self.body.tys.local_adt(t).is_some() => {
                    let a = self.body.tys.local_adt(t).unwrap();
                    t = self.p.adt(a).variants[variant as usize].fields[*i as usize].ty;
                    variant = 0;
                }
                (TyKind::Adt(..), Proj::Downcast(v)) => variant = *v,
                (_, Proj::Field(_)) if self.body.tys.option_elem(t).is_some() => t = self.body.tys.option_elem(t).unwrap(),
                (_, Proj::Field(_)) if self.body.tys.result_args(t).is_some() => {
                    let (a, b) = self.body.tys.result_args(t).unwrap();
                    t = if variant == 0 { a } else { b };
                    variant = 0;
                }
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
        let mut holds = BitSet::new(self.loans.len());
        holds.union_words(st.holds(0));
        holds.union_words(st.origins(0));
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
    use super::{BitSet, Shape, State, bit_has, bit_iter, bit_set};

    /// The flat state keeps every set apart: a bit in one local's loan row
    /// shows up in no other row or set, and a join reports only new bits.
    #[test]
    fn flat_state_rows_are_disjoint() {
        let sh = Shape { n: 70, wn: 2, wl: 2, wm: 1 };
        let mut a = State::new(sh);
        bit_set(a.holds_mut(69), 127);
        bit_set(a.origins_mut(0), 0);
        bit_set(a.uninit_mut(), 69);
        bit_set(a.paths_mut(), 5);
        assert_eq!(bit_iter(a.holds(69)).collect::<Vec<_>>(), vec![127]);
        assert!((0..69).all(|l| bit_iter(a.holds(l)).next().is_none()));
        assert!(bit_has(a.origins(0), 0) && !bit_has(a.holds(0), 0));
        assert!(bit_has(a.uninit(), 69) && !bit_has(a.init(), 69) && !bit_has(a.moved(), 69));
        assert_eq!(bit_iter(a.paths()).collect::<Vec<_>>(), vec![5]);
        let mut b = State::new(sh);
        assert!(b.join(&a), "new bits are a change");
        assert!(!b.join(&a), "the same bits are not");
        assert!(b == a);
    }

    /// A no-loan body has `wl` 0: loan rows are empty, and the move
    /// paths start right after the local sets (no row words between).
    #[test]
    fn zero_loan_state_has_no_rows() {
        let sh = Shape { n: 3, wn: 1, wl: 0, wm: 1 };
        let mut a = State::new(sh);
        assert!(a.holds(0).is_empty() && a.holds(2).is_empty() && a.origins(1).is_empty());
        bit_set(a.paths_mut(), 4);
        bit_set(a.moved_mut(), 2);
        assert_eq!(bit_iter(a.paths()).collect::<Vec<_>>(), vec![4]);
        assert!(bit_has(a.moved(), 2) && !bit_has(a.init(), 2));
        let mut b = State::new(sh);
        assert!(b.join(&a) && b == a);
    }

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
