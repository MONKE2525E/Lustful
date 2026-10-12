// Trait selection without search (docs/ARCH.md section 2.4), the
// provably-false check behind the clause filter, and normalization
// of associated-type projections (section 2.5).
//
// Selection matches the whole trait reference, Self and every input
// argument, by tentative probe unifications over header patterns.
// At most one probe is ever confirmed. The clause filter can only
// remove candidates whose where clauses are provably false; it
// never selects a candidate because its clauses held, and anything
// it cannot decide stays ambiguous and defers. There is no
// backtracking and no speculative predicate search anywhere here.
//
// The solver runs over the `SolveCx` interface so the checker (with
// body-local inference variables) and mono (with concrete types,
// through `PureCx`) share one algorithm.
use super::index::{ImplId, ImplIndex, ImplRecord, head_of, subst_predicate, subst_trait_ref_pub};
use crate::def::DefId;
use crate::intern::FxMap;
use crate::ty::*;

/// The shared depth cap of selection, the clause filter, and
/// normalization (section 2.4 step 7). Re-entering one trait ref on
/// the stack, or passing the cap, is an overflow.
pub const MAX_DEPTH: usize = 64;

/// The unification surface selection needs. `snapshot` and
/// `rollback` make probes tentative: every binding a probe makes is
/// undone by rollback, and fresh variables stay allocated (their ids
/// remain usable in argument lists built during the probe).
pub trait SolveCx {
    /// A saved unification state, restored by `rollback`.
    type Snapshot;
    /// The type store of the running body (or of mono).
    type Store: TyIntern;
    fn tys(&mut self) -> &mut Self::Store;
    /// Deeply follows inference links in one type.
    fn deep_resolve(&mut self, t: Ty) -> Ty;
    /// Unifies two types, binding inference variables. False on a
    /// mismatch; bindings made before the mismatch may stand, which
    /// is why probes run under a snapshot.
    fn unify(&mut self, a: Ty, b: Ty) -> bool;
    /// A fresh type inference variable.
    fn fresh_var(&mut self) -> Ty;
    fn snapshot(&mut self) -> Self::Snapshot;
    fn rollback(&mut self, snap: Self::Snapshot);
    /// Records one `ImplSet` read (section 8.2): the bucket for this
    /// trait and Self type was read, and was empty when `failed`.
    fn record_impl_set(&mut self, trait_def: DefId, self_ty: Ty, failed: bool);
}

/// The answer of one selection (section 2.4).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Selection {
    /// One impl confirmed. `args` are the impl's parameters in
    /// declared order, deeply resolved; a parameter in `unbound`
    /// could not be bound by the header, an obligation binding, or
    /// step 4, and defers (at body end it is the impl-parameter error of step 4). `nested` are
    /// the impl's predicates, substituted and elaborated, which the
    /// caller must prove; a failure there is an error, never a
    /// reason to try another candidate.
    Impl { id: ImplId, args: Vec<GenericArg>, nested: Vec<Predicate>, unbound: Vec<ParamId> },
    /// A param-env predicate proves the obligation (step 1). The
    /// payload is that predicate's index in the env slice passed
    /// to `select`. Mono re-solves with concrete types.
    ParamEvidence(usize),
    /// Two or more answers remain, or the Self type has no known
    /// head yet. The caller defers (step 6).
    Ambiguous,
    /// No candidate can apply and inference cannot change that
    /// (step 5). The caller reports the no-impl error.
    NoImpl,
    /// The depth cap or the cycle set stopped selection (step 7).
    /// The caller reports the selection-overflow error.
    Overflow,
}

/// One body's solver state: the selection memo and cycle stack
/// (section 2.4 step 7). Memos are keyed by deeply resolved trait
/// refs, so they never outlive the inference variables they name.
#[derive(Default)]
pub struct Solver {
    /// Deep trait ref to the impl or env index a full selection
    /// confirmed. A hit re-runs that one probe to bind variables,
    /// instead of scanning every candidate again.
    memo: FxMap<TraitRef, MemoSel>,
    /// Deep trait ref to its provably-false answer. The check binds
    /// nothing, so its answers are safe to reuse as they are.
    false_memo: FxMap<TraitRef, bool>,
    /// The trait refs on the selection stack, for cycle detection.
    stack: Vec<TraitRef>,
}

#[derive(Clone, Copy)]
enum MemoSel {
    Impl(ImplId),
    Param(usize),
    NoImpl,
}

impl Solver {
    /// A solver with empty memos, for one body.
    pub fn new() -> Solver {
        Solver::default()
    }
}

/// Deeply resolves every type in one trait ref, so memo keys and
/// candidate probes see the current state of inference.
fn deep_trait_ref<C: SolveCx>(cx: &mut C, tr: TraitRef) -> TraitRef {
    let old_args: Vec<GenericArg> = cx.tys().args(tr.args).to_vec();
    let mut new_args: Vec<GenericArg> = Vec::with_capacity(old_args.len());
    for g in old_args {
        new_args.push(match g {
            GenericArg::Ty(t) => GenericArg::Ty(cx.deep_resolve(t)),
            other => other,
        });
    }
    let args = cx.tys().intern_args(&new_args);
    let old_b: Vec<(DefId, GenericArg)> = cx.tys().bindings(tr.bindings).to_vec();
    let mut new_b: Vec<(DefId, GenericArg)> = Vec::with_capacity(old_b.len());
    for (d, g) in old_b {
        new_b.push((
            d,
            match g {
                GenericArg::Ty(t) => GenericArg::Ty(cx.deep_resolve(t)),
                other => other,
            },
        ));
    }
    let bindings = cx.tys().intern_bindings(&new_b);
    TraitRef { def: tr.def, args, bindings }
}

/// The Self type of a trait ref (`args[0]`).
fn self_ty_of(cx: &impl TyIntern, tr: &TraitRef) -> Ty {
    cx.args(tr.args)[0].as_ty().expect("trait ref args start with the Self type")
}

/// Unifies two trait refs that name the same trait: every type
/// argument, and every associated binding present on both sides.
/// A binding written on one side only is an extra fact (an
/// `AssocEq` after elaboration), not a mismatch.
fn unify_trait_refs<C: SolveCx>(cx: &mut C, a: TraitRef, b: TraitRef) -> bool {
    let (aa, ba): (Vec<GenericArg>, Vec<GenericArg>) = (cx.tys().args(a.args).to_vec(), cx.tys().args(b.args).to_vec());
    if aa.len() != ba.len() {
        return false;
    }
    for (x, y) in aa.iter().zip(&ba) {
        let ok = match (x, y) {
            (GenericArg::Ty(u), GenericArg::Ty(v)) => cx.unify(*u, *v),
            (GenericArg::Lifetime(_), GenericArg::Lifetime(_)) => true,
            _ => x == y,
        };
        if !ok {
            return false;
        }
    }
    let ab: Vec<(DefId, GenericArg)> = cx.tys().bindings(a.bindings).to_vec();
    let bb: Vec<(DefId, GenericArg)> = cx.tys().bindings(b.bindings).to_vec();
    for (assoc, ga) in &ab {
        if let (GenericArg::Ty(x), Some((_, GenericArg::Ty(y)))) = (ga, bb.iter().find(|(d, _)| d == assoc))
            && !cx.unify(*x, *y)
        {
            return false;
        }
    }
    true
}

/// Fresh instantiation arguments for one item's parameters: a fresh
/// variable per type parameter, an erased region per lifetime, and
/// a fresh const variable per const parameter.
fn fresh_inst_args<C: SolveCx>(cx: &mut C, generics: &Generics) -> Vec<GenericArg> {
    let mut out = Vec::with_capacity(generics.params.len());
    let mut next_const = 0u32;
    for p in &generics.params {
        out.push(match p.kind {
            ParamKind::Type => GenericArg::Ty(cx.fresh_var()),
            ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
            ParamKind::Const(_) => {
                // Const inference variables are numbered in their
                // own space per instantiation. Unification of const
                // arguments is by equality outside the solver, so a
                // const param of an impl binds only where a header
                // argument already names it; that subset limit is
                // recorded in the W-TRAITS-CORE report.
                let id = cx.tys().intern_const(ConstKind::Infer(next_const));
                next_const += 1;
                GenericArg::Const(id)
            }
        });
    }
    out
}

impl Solver {
    /// Probes one impl header against the obligation: instantiates
    /// the impl pattern with fresh variables, unifies the whole
    /// trait ref, then unifies each obligation binding with the
    /// impl's binding for that associated item. On success the
    /// probe's bindings stand and the instantiation args are
    /// returned; on failure the caller rolls back.
    fn probe_impl<C: SolveCx>(&self, cx: &mut C, rec: &ImplRecord, obl: TraitRef) -> Option<Vec<GenericArg>> {
        let inst = fresh_inst_args(cx, &rec.generics);
        let pattern = subst_trait_ref_pub(cx.tys(), rec.trait_ref, &inst);
        if !unify_trait_refs(cx, pattern, obl) {
            return None;
        }
        let obl_bindings: Vec<(DefId, GenericArg)> = cx.tys().bindings(obl.bindings).to_vec();
        for (assoc, ga) in obl_bindings {
            let GenericArg::Ty(want) = ga else { continue };
            let pat = rec.assoc_ty(assoc)?;
            let have = subst(cx.tys(), pat, &inst);
            if !cx.unify(want, have) {
                return None;
            }
        }
        Some(inst)
    }

    /// The impl's predicates after confirmation: substituted with
    /// the confirmed args, then elaborated (supertraits and
    /// associated equalities) through the index.
    fn nested_predicates<C: SolveCx>(&self, cx: &mut C, index: &ImplIndex, rec: &ImplRecord, inst: &[GenericArg]) -> Vec<Predicate> {
        let written: Vec<Predicate> = rec.generics.predicates.iter().map(|&p| subst_predicate(cx.tys(), p, inst)).collect();
        // `elaborate` needs a `&dyn Fn` over the store only, but the
        // index's supertrait walk must intern into the same store.
        // Run the fixpoint here instead of through `ty::elaborate`,
        // which stays the one implementation for param envs built
        // over the global store at collect (where a shared provider
        // over an immutable store is exact).
        elaborate_in(cx.tys(), index, &written)
    }

    /// Step 4: binds impl parameters the header left free (the
    /// `unbound` list), from associated equalities in the impl's
    /// own elaborated predicates whose projection normalizes now.
    /// One pass, no search. Obligation bindings already bound their
    /// parameters during the probe (step 4a), so only 4b runs here.
    fn bind_unbound_from_assoc_eqs<C: SolveCx>(
        &mut self,
        cx: &mut C,
        index: &ImplIndex,
        env: &[Predicate],
        nested: &[Predicate],
        inst: &[GenericArg],
    ) {
        for pred in nested {
            let Predicate::AssocEq(b) = pred else { continue };
            if b.count != 0 {
                continue;
            }
            let eq = b.value;
            // Only an equality whose right side is exactly one still
            // free impl parameter variable can bind it.
            let rhs = cx.deep_resolve(eq.ty);
            if !matches!(cx.tys().kind(rhs), TyKind::Infer(_)) || !inst.iter().any(|g| g.as_ty() == Some(rhs)) {
                continue;
            }
            let proj = cx.tys().intern(TyKind::Projection(AssocId(eq.assoc), eq.trait_args));
            let normed = self.normalize_inner(cx, index, env, proj, 0);
            // "Normalizes now" means the top projection rewrote.
            // Binding the variable to an unrewritten projection (its
            // Ty id can differ from `proj`'s by re-interning) would
            // only move the unknown, so it does not count.
            let normed = cx.deep_resolve(normed);
            if !matches!(cx.tys().kind(normed), TyKind::Projection(..)) && normed != rhs {
                cx.unify(rhs, normed);
            }
        }
    }

    /// Confirms one candidate (steps 3 and 4): re-runs its probe
    /// without rollback, binds free impl parameters where step 4
    /// can, and builds the nested predicates the caller must prove.
    /// Callers reach this only with exactly one candidate left.
    fn confirm_impl<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], id: ImplId, obl: TraitRef) -> Selection {
        let rec = index.get(id).clone();
        let Some(inst) = self.probe_impl(cx, &rec, obl) else {
            // The candidate matched a probe a moment ago; a failure
            // here means inference moved under it. Defer rather
            // than guess.
            return Selection::Ambiguous;
        };
        let nested = self.nested_predicates(cx, index, &rec, &inst);
        self.bind_unbound_from_assoc_eqs(cx, index, env, &nested, &inst);
        let mut args: Vec<GenericArg> = Vec::with_capacity(inst.len());
        let mut unbound: Vec<ParamId> = Vec::new();
        for (i, g) in inst.iter().enumerate() {
            match g {
                GenericArg::Ty(t) => {
                    let r = cx.deep_resolve(*t);
                    if rec.generics.params[i].kind == ParamKind::Type && matches!(cx.tys().kind(r), TyKind::Infer(_)) {
                        unbound.push(ParamId(i as u32));
                    }
                    args.push(GenericArg::Ty(r));
                }
                other => args.push(*other),
            }
        }
        Selection::Impl { id, args, nested, unbound }
    }

    /// True when a deeply resolved Self type settles the candidate
    /// set for good: a known head and no inference variable in it
    /// that could still change the head. The head is the outermost
    /// form, so variables inside a fixed constructor cannot.
    fn head_is_settled<C: SolveCx>(&self, cx: &mut C, self_ty: Ty) -> bool {
        let resolved = cx.deep_resolve(self_ty);
        head_of(cx.tys(), resolved, &|t| t).is_some()
    }

    /// Selects evidence for one obligation (the algorithm of
    /// section 2.4). `env` is the elaborated param env already
    /// substituted into this body's types. A confirmed selection
    /// commits its probe bindings; every other answer binds
    /// nothing.
    pub fn select<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], obl: TraitRef) -> Selection {
        let obl = deep_trait_ref(cx, obl);
        if self.stack.len() >= MAX_DEPTH || self.stack.contains(&obl) {
            return Selection::Overflow;
        }
        // A bare parameter Self with no env evidence cannot be
        // selected from impls at all: only the param env speaks
        // for it (mono re-solves the rest with concrete types).
        self.stack.push(obl);
        let out = self.select_inner(cx, index, env, obl);
        self.stack.pop();
        out
    }

    fn select_inner<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], obl: TraitRef) -> Selection {
        // The memo re-runs one known probe instead of scanning.
        match self.memo.get(&obl).copied() {
            Some(MemoSel::Impl(id)) => return self.confirm_impl(cx, index, env, id, obl),
            Some(MemoSel::Param(i)) => {
                if let Some(Predicate::Trait(b)) = env.get(i).copied() {
                    unify_trait_refs(cx, b.value, obl);
                }
                return Selection::ParamEvidence(i);
            }
            Some(MemoSel::NoImpl) => return Selection::NoImpl,
            None => {}
        }

        // Step 1: param-env evidence wins over impls. Two matching
        // predicates defer; the first match is never taken.
        let mut env_hits: Vec<usize> = Vec::new();
        for (i, pred) in env.iter().enumerate() {
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 || b.value.def != obl.def {
                continue;
            }
            let snap = cx.snapshot();
            let ok = unify_trait_refs(cx, b.value, obl);
            cx.rollback(snap);
            if ok {
                env_hits.push(i);
            }
        }
        match env_hits.len() {
            1 => {
                let i = env_hits[0];
                if let Predicate::Trait(b) = env[i] {
                    unify_trait_refs(cx, b.value, obl);
                }
                self.memo.insert(obl, MemoSel::Param(i));
                return Selection::ParamEvidence(i);
            }
            2.. => return Selection::Ambiguous,
            _ => {}
        }

        // Step 6's other half, checked before any candidate can
        // confirm: with no known head, selection always defers.
        // A blanket probe binding here would pick the blanket
        // before inference can name the concrete impl.
        {
            let self_ty = self_ty_of(cx.tys(), &obl);
            let deep = cx.deep_resolve(self_ty);
            if head_of(cx.tys(), deep, &|t| t).is_none() {
                return Selection::Ambiguous;
            }
        }

        // Step 2: header candidates by probe unification.
        let self_ty = self_ty_of(cx.tys(), &obl);
        let cands: Vec<ImplId> = {
            // `candidates` reads through an immutable store view;
            // resolve in a snapshot-free way by deep-resolving Self
            // first, so `&|t| t` is exact for its head test.
            let self_deep = cx.deep_resolve(self_ty);
            index.candidates(cx.tys(), obl.def, self_deep, &|t| t)
        };
        cx.record_impl_set(obl.def, self_ty, cands.is_empty());
        let mut matched: Vec<ImplId> = Vec::new();
        for id in cands {
            let rec = index.get(id).clone();
            let snap = cx.snapshot();
            let ok = self.probe_impl(cx, &rec, obl).is_some();
            cx.rollback(snap);
            if ok {
                matched.push(id);
            }
        }

        // Step 3: the clause filter. It runs only when more than
        // one candidate matched and Self is settled enough to ask
        // the provably-false question.
        if matched.len() > 1 && self.head_is_settled(cx, self_ty) {
            let before = matched.clone();
            matched.retain(|&id| {
                let rec = index.get(id).clone();
                let snap = cx.snapshot();
                let dropped = match self.probe_impl(cx, &rec, obl) {
                    Some(inst) => rec.generics.predicates.iter().any(|&p| {
                        let p = subst_predicate(cx.tys(), p, &inst);
                        matches!(p, Predicate::Trait(b) if b.count == 0)
                            && self.provably_false(
                                cx,
                                index,
                                env,
                                match p {
                                    Predicate::Trait(b) => b.value,
                                    _ => unreachable!(),
                                },
                            )
                    }),
                    None => true,
                };
                cx.rollback(snap);
                !dropped
            });
            let _ = before;
        }

        match matched.len() {
            1 => {
                let id = matched[0];
                self.memo.insert(obl, MemoSel::Impl(id));
                self.confirm_impl(cx, index, env, id, obl)
            }
            0 => {
                // Step 5 or step 6, by whether inference can still
                // change the candidate set.
                if self.head_is_settled(cx, self_ty) {
                    self.memo.insert(obl, MemoSel::NoImpl);
                    Selection::NoImpl
                } else {
                    Selection::Ambiguous
                }
            }
            _ => Selection::Ambiguous,
        }
    }

    /// The provably-false check of section 2.4. True only on a
    /// definite "no": a param-env match, an unknown head, a cycle,
    /// a cap, or a clause that can hold all answer false. Binds
    /// nothing and commits nothing; records the same `ImplSet`
    /// reads as a failed selection.
    pub fn provably_false<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], tr: TraitRef) -> bool {
        let tr = deep_trait_ref(cx, tr);
        if let Some(&memo) = self.false_memo.get(&tr) {
            return memo;
        }
        let out = self.provably_false_inner(cx, index, env, tr);
        self.false_memo.insert(tr, out);
        out
    }

    fn provably_false_inner<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], tr: TraitRef) -> bool {
        if self.stack.len() >= MAX_DEPTH || self.stack.contains(&tr) {
            return false;
        }
        // A param-env match can hold by definition.
        for pred in env {
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 || b.value.def != tr.def {
                continue;
            }
            let snap = cx.snapshot();
            let ok = unify_trait_refs(cx, b.value, tr);
            cx.rollback(snap);
            if ok {
                return false;
            }
        }
        let self_ty = self_ty_of(cx.tys(), &tr);
        let self_deep = cx.deep_resolve(self_ty);
        if head_of(cx.tys(), self_deep, &|t| t).is_none() {
            return false;
        }
        let cands = index.candidates(cx.tys(), tr.def, self_deep, &|t| t);
        cx.record_impl_set(tr.def, self_ty, cands.is_empty());
        if cands.is_empty() {
            return true;
        }
        // False only when every candidate is dead: its header does
        // not actually match, or one of its trait clauses is itself
        // provably false under its own probe bindings. Recursing
        // through candidates is what makes the two-level
        // `Box<[T]>` case work.
        self.stack.push(tr);
        let mut all_dead = true;
        'cands: for id in cands {
            let rec = index.get(id).clone();
            let snap = cx.snapshot();
            let dead = match self.probe_impl(cx, &rec, tr) {
                None => true,
                Some(inst) => {
                    let mut any_false_clause = false;
                    for &p in &rec.generics.predicates {
                        let p = subst_predicate(cx.tys(), p, &inst);
                        if let Predicate::Trait(b) = p
                            && b.count == 0
                            && self.provably_false(cx, index, env, b.value)
                        {
                            any_false_clause = true;
                            break;
                        }
                    }
                    any_false_clause
                }
            };
            cx.rollback(snap);
            if !dead {
                all_dead = false;
                break 'cands;
            }
        }
        self.stack.pop();
        all_dead
    }
}

/// Elaboration over a mutable store: the fixpoint of section 2.1
/// (written predicates, supertraits through the index, one
/// `AssocEq` per type binding under its binder, deduplicated in
/// first-occurrence order). `ty::elaborate` is the same fixpoint
/// over an immutable store plus a caller provider, for the global
/// param envs in `Defs`; bodies elaborate substituted predicates
/// here because supertrait substitution must intern into the
/// body's own store.
pub fn elaborate_in(tys: &mut impl TyIntern, index: &ImplIndex, written: &[Predicate]) -> Vec<Predicate> {
    let mut out: Vec<Predicate> = Vec::new();
    let mut work: Vec<Predicate> = written.to_vec();
    let mut i = 0;
    while i < work.len() {
        let p = work[i];
        i += 1;
        if out.contains(&p) {
            continue;
        }
        out.push(p);
        if let Predicate::Trait(b) = p {
            for &(assoc, arg) in tys.bindings(b.value.bindings) {
                if let GenericArg::Ty(ty) = arg {
                    work.push(Predicate::AssocEq(Binder { count: b.count, value: AssocEqData { assoc, trait_args: b.value.args, ty } }));
                }
            }
            work.extend(index.supertraits_of(tys, &b.value));
        }
    }
    out
}

/// Normalizes one type (section 2.5): rewrites projections through
/// the impl selection picks, through param-env associated
/// equalities, and recurses. A projection that cannot rewrite
/// stays a projection. This is the `normalize` of section 2.1; it
/// lives with selection because it needs the solver, while
/// `ty::subst` stays pure in `ty`.
pub fn normalize<C: SolveCx>(solver: &mut Solver, cx: &mut C, index: &ImplIndex, env: &[Predicate], t: Ty) -> Ty {
    solver.normalize_inner(cx, index, env, t, 0)
}

impl Solver {
    fn normalize_inner<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], t: Ty, depth: usize) -> Ty {
        let t = cx.deep_resolve(t);
        if depth >= MAX_DEPTH || !cx.tys().flags(t).contains_projection() {
            return t;
        }
        match cx.tys().kind(t) {
            TyKind::Projection(assoc, args) => {
                let Some(trait_def) = index.trait_of_assoc(assoc.0) else { return t };
                // Normalize inside the trait args first, so nested
                // projections reach selection in their simplest form.
                let normed_args = self.normalize_args(cx, index, env, args, depth + 1);
                let t = cx.tys().intern(TyKind::Projection(assoc, normed_args));
                let tr = TraitRef { def: trait_def, args: normed_args, bindings: EMPTY_BINDINGS };
                match self.select(cx, index, env, tr) {
                    Selection::Impl { id, args: inst, .. } => {
                        let rec = index.get(id);
                        match rec.assoc_ty(assoc.0) {
                            Some(pat) => {
                                let bound = subst(cx.tys(), pat, &inst);
                                self.normalize_inner(cx, index, env, bound, depth + 1)
                            }
                            None => t,
                        }
                    }
                    Selection::ParamEvidence(_) => match self.env_assoc_eq(cx, env, assoc.0, normed_args) {
                        Some(ty) => self.normalize_inner(cx, index, env, ty, depth + 1),
                        None => t,
                    },
                    _ => t,
                }
            }
            TyKind::Ref(r, m, e) => {
                let e = self.normalize_inner(cx, index, env, e, depth + 1);
                cx.tys().intern(TyKind::Ref(r, m, e))
            }
            TyKind::RawPtr(m, e) => {
                let e = self.normalize_inner(cx, index, env, e, depth + 1);
                cx.tys().intern(TyKind::RawPtr(m, e))
            }
            TyKind::Slice(e) => {
                let e = self.normalize_inner(cx, index, env, e, depth + 1);
                cx.tys().intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.normalize_inner(cx, index, env, e, depth + 1);
                cx.tys().intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let old: Vec<Ty> = cx.tys().tys_of(ts).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.normalize_inner(cx, index, env, e, depth + 1)).collect();
                let ts = cx.tys().intern_tys(&new);
                cx.tys().intern(TyKind::Tuple(ts))
            }
            TyKind::Adt(d, a) => {
                let a = self.normalize_args(cx, index, env, a, depth + 1);
                cx.tys().intern(TyKind::Adt(d, a))
            }
            TyKind::FnDef(d, a) => {
                let a = self.normalize_args(cx, index, env, a, depth + 1);
                cx.tys().intern(TyKind::FnDef(d, a))
            }
            TyKind::Closure(d, a) => {
                let a = self.normalize_args(cx, index, env, a, depth + 1);
                cx.tys().intern(TyKind::Closure(d, a))
            }
            TyKind::Opaque(d, a) => {
                let a = self.normalize_args(cx, index, env, a, depth + 1);
                cx.tys().intern(TyKind::Opaque(d, a))
            }
            TyKind::FnPtr(sig) => {
                let b = cx.tys().sig(sig);
                let old: Vec<Ty> = cx.tys().tys_of(b.value.inputs).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.normalize_inner(cx, index, env, e, depth + 1)).collect();
                let inputs = cx.tys().intern_tys(&new);
                let output = self.normalize_inner(cx, index, env, b.value.output, depth + 1);
                let sig = cx.tys().intern_sig(Binder { count: b.count, value: FnSig { inputs, output, ..b.value } });
                cx.tys().intern(TyKind::FnPtr(sig))
            }
            _ => t,
        }
    }

    fn normalize_args<C: SolveCx>(&mut self, cx: &mut C, index: &ImplIndex, env: &[Predicate], a: ArgsId, depth: usize) -> ArgsId {
        let old: Vec<GenericArg> = cx.tys().args(a).to_vec();
        let new: Vec<GenericArg> = old
            .iter()
            .map(|&g| match g {
                GenericArg::Ty(e) => GenericArg::Ty(self.normalize_inner(cx, index, env, e, depth)),
                other => other,
            })
            .collect();
        cx.tys().intern_args(&new)
    }

    /// The right side of a param-env associated equality for this
    /// projection, matched under its binder. Only rank-0 binders
    /// match here; a higher-ranked equality (a `for<'a> Fn` output)
    /// is instantiated by the closure call path, not by this
    /// rewrite, and the projection stays.
    fn env_assoc_eq<C: SolveCx>(&self, cx: &mut C, env: &[Predicate], assoc: DefId, trait_args: ArgsId) -> Option<Ty> {
        for pred in env {
            let Predicate::AssocEq(b) = pred else { continue };
            if b.count != 0 || b.value.assoc != assoc {
                continue;
            }
            let snap = cx.snapshot();
            let (xs, ys): (Vec<GenericArg>, Vec<GenericArg>) =
                (cx.tys().args(b.value.trait_args).to_vec(), cx.tys().args(trait_args).to_vec());
            let ok = xs.len() == ys.len()
                && xs.iter().zip(&ys).all(|(x, y)| match (x, y) {
                    (GenericArg::Ty(u), GenericArg::Ty(v)) => cx.unify(*u, *v),
                    _ => x == y,
                });
            if ok {
                // Keep the bindings: they only ever equate the
                // projection's own args with the env fact's args.
                return Some(b.value.ty);
            }
            cx.rollback(snap);
        }
        None
    }
}

// ---------- A pure SolveCx over a body-local store ----------

/// A self-contained `SolveCx`: a body-local `Tys` plus its own
/// inference variables with a rollback trail. Mono uses it to
/// re-solve param evidence over concrete types (its variables exist
/// only inside impl probes), and unit tests drive selection with
/// it. `reads` records every `ImplSet` read as
/// `(trait, Self type, bucket was empty)`, which mono translates
/// into graph reads and tests assert on.
pub struct PureCx<'g> {
    pub tys: Tys<'g>,
    vars: Vec<Option<Ty>>,
    trail: Vec<u32>,
    pub reads: Vec<(DefId, Ty, bool)>,
}

impl<'g> PureCx<'g> {
    /// A pure context over the given global store.
    pub fn new(global: &'g GlobalTys) -> PureCx<'g> {
        PureCx { tys: Tys::new(global), vars: Vec::new(), trail: Vec::new(), reads: Vec::new() }
    }

    fn resolve_shallow(&self, mut t: Ty) -> Ty {
        while let TyKind::Infer(v) = self.tys.kind(t) {
            match self.vars[v.index() as usize] {
                Some(b) => t = b,
                None => return t,
            }
        }
        t
    }

    fn occurs(&self, var: u32, t: Ty) -> bool {
        let t = self.resolve_shallow(t);
        match self.tys.kind(t) {
            TyKind::Infer(v) => v.index() == var,
            TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => self.occurs(var, e),
            TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => {
                self.tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| self.occurs(var, e)))
            }
            TyKind::Tuple(ts) => self.tys.tys_of(ts).iter().any(|&e| self.occurs(var, e)),
            _ => false,
        }
    }

    fn bind(&mut self, var: u32, t: Ty) {
        self.trail.push(var);
        self.vars[var as usize] = Some(t);
    }

    fn unify_args(&mut self, a: ArgsId, b: ArgsId) -> bool {
        let n = self.tys.args(a).len();
        if n != self.tys.args(b).len() {
            return false;
        }
        for i in 0..n {
            let ok = match (self.tys.args(a)[i], self.tys.args(b)[i]) {
                (GenericArg::Ty(x), GenericArg::Ty(y)) => self.unify(x, y),
                (GenericArg::Lifetime(_), GenericArg::Lifetime(_)) => true,
                (x, y) => x == y,
            };
            if !ok {
                return false;
            }
        }
        true
    }
}

impl<'g> SolveCx for PureCx<'g> {
    type Snapshot = usize;
    type Store = Tys<'g>;

    fn tys(&mut self) -> &mut Tys<'g> {
        &mut self.tys
    }

    /// Deeply resolves variables, rebuilding compound types whose
    /// parts moved. A type with no inference variable (the cached
    /// flag) comes back as it is.
    fn deep_resolve(&mut self, t: Ty) -> Ty {
        let t = self.resolve_shallow(t);
        if !self.tys.flags(t).contains_infer() {
            return t;
        }
        match self.tys.kind(t) {
            TyKind::Ref(r, m, e) => {
                let e = self.deep_resolve(e);
                self.tys.intern(TyKind::Ref(r, m, e))
            }
            TyKind::RawPtr(m, e) => {
                let e = self.deep_resolve(e);
                self.tys.intern(TyKind::RawPtr(m, e))
            }
            TyKind::Slice(e) => {
                let e = self.deep_resolve(e);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.deep_resolve(e);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let old: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.deep_resolve(e)).collect();
                let ts = self.tys.intern_tys(&new);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::Adt(d, a) => {
                let old: Vec<GenericArg> = self.tys.args(a).to_vec();
                let new: Vec<GenericArg> = old
                    .iter()
                    .map(|&g| match g {
                        GenericArg::Ty(e) => GenericArg::Ty(self.deep_resolve(e)),
                        other => other,
                    })
                    .collect();
                let a = self.tys.intern_args(&new);
                self.tys.intern(TyKind::Adt(d, a))
            }
            TyKind::Projection(d, a) => {
                let old: Vec<GenericArg> = self.tys.args(a).to_vec();
                let new: Vec<GenericArg> = old
                    .iter()
                    .map(|&g| match g {
                        GenericArg::Ty(e) => GenericArg::Ty(self.deep_resolve(e)),
                        other => other,
                    })
                    .collect();
                let a = self.tys.intern_args(&new);
                self.tys.intern(TyKind::Projection(d, a))
            }
            _ => t,
        }
    }

    fn unify(&mut self, a: Ty, b: Ty) -> bool {
        let (a, b) = (self.resolve_shallow(a), self.resolve_shallow(b));
        if a == b {
            return true;
        }
        match (self.tys.kind(a), self.tys.kind(b)) {
            (TyKind::Error, _) | (_, TyKind::Error) => true,
            (TyKind::Infer(v), TyKind::Infer(w)) => {
                if v.is_int() && !w.is_int() {
                    self.bind(w.index(), a);
                } else {
                    self.bind(v.index(), b);
                }
                true
            }
            (TyKind::Infer(v), k) | (k, TyKind::Infer(v)) => {
                if v.is_int() && !matches!(k, TyKind::Int(_)) {
                    return false;
                }
                let other = if matches!(self.tys.kind(a), TyKind::Infer(_)) { b } else { a };
                if self.occurs(v.index(), other) {
                    return false;
                }
                self.bind(v.index(), other);
                true
            }
            (TyKind::Ref(_, m, x), TyKind::Ref(_, n, y)) => m == n && self.unify(x, y),
            (TyKind::RawPtr(m, x), TyKind::RawPtr(n, y)) => m == n && self.unify(x, y),
            (TyKind::Slice(x), TyKind::Slice(y)) => self.unify(x, y),
            (TyKind::Array(x, cx), TyKind::Array(y, cy)) => cx == cy && self.unify(x, y),
            (TyKind::Tuple(x), TyKind::Tuple(y)) => {
                let (xs, ys): (Vec<Ty>, Vec<Ty>) = (self.tys.tys_of(x).to_vec(), self.tys.tys_of(y).to_vec());
                xs.len() == ys.len() && xs.iter().zip(&ys).all(|(&u, &v)| self.unify(u, v))
            }
            (TyKind::Adt(d, x), TyKind::Adt(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::Projection(d, x), TyKind::Projection(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::FnDef(d, x), TyKind::FnDef(e, y)) => d == e && self.unify_args(x, y),
            (ka, kb) => ka == kb,
        }
    }

    fn fresh_var(&mut self) -> Ty {
        self.vars.push(None);
        let id = self.vars.len() as u32 - 1;
        self.tys.intern(TyKind::Infer(InferId(id, false)))
    }

    fn snapshot(&mut self) -> usize {
        self.trail.len()
    }

    fn rollback(&mut self, snap: usize) {
        while self.trail.len() > snap {
            let var = self.trail.pop().unwrap();
            self.vars[var as usize] = None;
        }
    }

    fn record_impl_set(&mut self, trait_def: DefId, self_ty: Ty, failed: bool) {
        self.reads.push((trait_def, self_ty, failed));
    }
}

impl PureCx<'_> {
    /// A fresh integer-literal variable, for callers modeling
    /// `{integer}` inference (the `s[x]` case of section 2.4).
    pub fn fresh_int_var(&mut self) -> Ty {
        self.vars.push(None);
        let id = self.vars.len() as u32 - 1;
        self.tys.intern(TyKind::Infer(InferId(id, true)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::def::{DefPathHash, LOCAL_CRATE};
    use crate::diag::Span;
    use crate::traits::index::{ImplRecord, Synthetic, TraitRecord, pattern_head};

    fn def(hash: u64) -> DefId {
        DefId { krate: LOCAL_CRATE, hash: DefPathHash(hash) }
    }

    fn ty_param(g: &mut GlobalTys, i: u32) -> Ty {
        g.intern(TyKind::Param(ParamId(i)))
    }

    fn params(n: usize) -> Vec<ParamDef> {
        (0..n).map(|_| ParamDef { name: crate::intern::Sym(0), kind: ParamKind::Type, span: Span::default() }).collect()
    }

    /// Declares a trait with `n_inputs` written params (Self is
    /// prepended by the module convention) and the given supertrait
    /// predicates and associated types.
    fn declare_trait(index: &mut ImplIndex, trait_def: DefId, n_inputs: usize, predicates: Vec<Predicate>, assoc_tys: Vec<DefId>) {
        index.insert_trait(TraitRecord {
            def: trait_def,
            name: crate::intern::Sym(0),
            generics: Generics { parent: None, params: params(n_inputs + 1), predicates },
            assoc_items: assoc_tys.iter().map(|&d| (d, crate::intern::Sym(0), true)).collect(),
            methods: Vec::new(),
            local: true,
            span: Span::default(),
        });
    }

    fn trait_pred(g: &mut impl TyIntern, trait_def: DefId, args: &[Ty]) -> Predicate {
        let args: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
        let args = g.intern_args(&args);
        Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }))
    }

    fn trait_ref(g: &mut impl TyIntern, trait_def: DefId, args: &[Ty]) -> TraitRef {
        let args: Vec<GenericArg> = args.iter().map(|&t| GenericArg::Ty(t)).collect();
        let args = g.intern_args(&args);
        TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }
    }

    /// Inserts one impl; its bucket head comes from `pattern_head`,
    /// exactly as collect computes it.
    fn add_impl(
        g: &mut GlobalTys,
        index: &mut ImplIndex,
        impl_hash: u64,
        trait_def: DefId,
        self_pat: Ty,
        rest_args: &[Ty],
        n_params: usize,
        predicates: Vec<Predicate>,
        assoc_tys: Vec<(DefId, Ty)>,
    ) -> ImplId {
        let mut all = vec![GenericArg::Ty(self_pat)];
        all.extend(rest_args.iter().map(|&t| GenericArg::Ty(t)));
        let args = g.intern_args(&all);
        let (head, blanket) = pattern_head(g, self_pat, &[]).unwrap();
        index.insert_impl(ImplRecord {
            def: def(impl_hash),
            trait_def,
            trait_ref: TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS },
            generics: Generics { parent: None, params: params(n_params), predicates },
            assoc_tys,
            assoc_consts: Vec::new(),
            items: Vec::new(),
            synthetic: Synthetic::None,
            local: true,
            span: Span::default(),
            head,
            blanket,
        })
    }

    fn u8_ty() -> Ty {
        int(IntTy::U8)
    }
    fn u16_ty() -> Ty {
        int(IntTy::U16)
    }

    /// Section 2.4: two impls on one Self with different trait
    /// inputs are picked apart by the whole trait ref.
    #[test]
    fn same_self_different_inputs() {
        let mut g = GlobalTys::new();
        let (tr, s) = (def(10), def(20));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, tr, 1, vec![], vec![]);
        let s_ty = g.mk_adt(s, &[]);
        add_impl(&mut g, &mut index, 100, tr, s_ty, &[u8_ty()], 0, vec![], vec![]);
        add_impl(&mut g, &mut index, 101, tr, s_ty, &[u16_ty()], 0, vec![], vec![]);
        for (input, want_hash) in [(u8_ty(), 100u64), (u16_ty(), 101)] {
            let mut cx = PureCx::new(&g);
            let obl = trait_ref(&mut cx.tys, tr, &[s_ty, input]);
            match Solver::new().select(&mut cx, &index, &[], obl) {
                Selection::Impl { id, unbound, .. } => {
                    assert_eq!(index.get(id).def, def(want_hash));
                    assert!(unbound.is_empty());
                }
                other => panic!("expected impl {want_hash}, got {other:?}"),
            }
        }
        // An input no impl names is NoImpl, not a guess.
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, tr, &[s_ty, BOOL]);
        assert_eq!(Solver::new().select(&mut cx, &index, &[], obl), Selection::NoImpl);
        assert!(cx.reads.iter().any(|(d, _, failed)| *d == tr && !failed), "the non-empty bucket read is recorded");
    }

    /// The N1 shape (2.4 step 3): a concrete impl and a bounded
    /// bare-param blanket both match by header; the blanket's
    /// clause is provably false for the concrete type, so the
    /// concrete impl wins. For an iterator type the blanket wins.
    #[test]
    fn clause_filter_picks_concrete_over_blanket() {
        let mut g = GlobalTys::new();
        let (iter_tr, into_tr, local, local_it) = (def(10), def(11), def(20), def(21));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, iter_tr, 0, vec![], vec![]);
        declare_trait(&mut index, into_tr, 0, vec![], vec![]);
        let p0 = ty_param(&mut g, 0);
        let local_ty = g.mk_adt(local, &[]);
        let it_ty = g.mk_adt(local_it, &[]);
        // impl Iterator for LocalIt; impl IntoIterator for Local;
        // impl<I: Iterator> IntoIterator for I.
        add_impl(&mut g, &mut index, 100, iter_tr, it_ty, &[], 0, vec![], vec![]);
        let concrete = add_impl(&mut g, &mut index, 101, into_tr, local_ty, &[], 0, vec![], vec![]);
        let blanket_pred = trait_pred(&mut g, iter_tr, &[p0]);
        let blanket = add_impl(&mut g, &mut index, 102, into_tr, p0, &[], 1, vec![blanket_pred], vec![]);

        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, into_tr, &[local_ty]);
        match Solver::new().select(&mut cx, &index, &[], obl) {
            Selection::Impl { id, .. } => assert_eq!(id, concrete),
            other => panic!("expected the concrete impl, got {other:?}"),
        }
        // The filter read the Iterator bucket for Local and found
        // it empty: that failed lookup is a recorded read.
        assert!(cx.reads.iter().any(|(d, _, failed)| *d == iter_tr && *failed));

        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, into_tr, &[it_ty]);
        match Solver::new().select(&mut cx, &index, &[], obl) {
            Selection::Impl { id, args, nested, .. } => {
                assert_eq!(id, blanket);
                assert_eq!(args[0].as_ty(), Some(it_ty));
                assert_eq!(nested.len(), 1, "the blanket clause is a nested obligation");
            }
            other => panic!("expected the blanket impl, got {other:?}"),
        }
    }

    /// Two blanket impls whose clauses can both hold stay
    /// ambiguous: the filter never selects on a "yes".
    #[test]
    fn clause_filter_never_selects_on_yes() {
        let mut g = GlobalTys::new();
        let (a_tr, b_tr, tr, s) = (def(10), def(11), def(12), def(20));
        let mut index = ImplIndex::new();
        for t in [a_tr, b_tr, tr] {
            declare_trait(&mut index, t, 0, vec![], vec![]);
        }
        let p0 = ty_param(&mut g, 0);
        let s_ty = g.mk_adt(s, &[]);
        add_impl(&mut g, &mut index, 100, a_tr, s_ty, &[], 0, vec![], vec![]);
        add_impl(&mut g, &mut index, 101, b_tr, s_ty, &[], 0, vec![], vec![]);
        let pa = trait_pred(&mut g, a_tr, &[p0]);
        let pb = trait_pred(&mut g, b_tr, &[p0]);
        add_impl(&mut g, &mut index, 102, tr, p0, &[], 1, vec![pa], vec![]);
        add_impl(&mut g, &mut index, 103, tr, p0, &[], 1, vec![pb], vec![]);
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, tr, &[s_ty]);
        assert_eq!(Solver::new().select(&mut cx, &index, &[], obl), Selection::Ambiguous);
    }

    /// The two-level shape (2.4): `Box2<[u8]>` matches the
    /// `Iterator` blanket only through `Iterator for Box2<J>`,
    /// which needs `[u8]: Iterator`, and that has no candidate at
    /// all. One level of filter is not enough.
    #[test]
    fn clause_filter_is_multi_level() {
        let mut g = GlobalTys::new();
        let (iter_tr, into_tr, box2) = (def(10), def(11), def(20));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, iter_tr, 0, vec![], vec![]);
        declare_trait(&mut index, into_tr, 0, vec![], vec![]);
        let p0 = ty_param(&mut g, 0);
        // impl<J: Iter> Iter for Box2<J>
        let box_p = g.mk_adt(box2, &[GenericArg::Ty(p0)]);
        let jp = trait_pred(&mut g, iter_tr, &[p0]);
        add_impl(&mut g, &mut index, 100, iter_tr, box_p, &[], 1, vec![jp], vec![]);
        // impl<T> Into for Box2<[T]> (the direct impl)
        let slice_p = g.intern(TyKind::Slice(p0));
        let box_slice = g.mk_adt(box2, &[GenericArg::Ty(slice_p)]);
        let direct = add_impl(&mut g, &mut index, 101, into_tr, box_slice, &[], 1, vec![], vec![]);
        // impl<I: Iter> Into for I (the blanket)
        let ip = trait_pred(&mut g, iter_tr, &[p0]);
        add_impl(&mut g, &mut index, 102, into_tr, p0, &[], 1, vec![ip], vec![]);

        let mut cx = PureCx::new(&g);
        let slice_u8 = cx.tys.intern(TyKind::Slice(u8_ty()));
        let self_ty = cx.tys.mk_adt(box2, &[GenericArg::Ty(slice_u8)]);
        // One level down: `Box2<[u8]>: Iter` is provably false.
        let iter_obl = trait_ref(&mut cx.tys, iter_tr, &[self_ty]);
        assert!(Solver::new().provably_false(&mut cx, &index, &[], iter_obl));
        let obl = trait_ref(&mut cx.tys, into_tr, &[self_ty]);
        match Solver::new().select(&mut cx, &index, &[], obl) {
            Selection::Impl { id, args, .. } => {
                assert_eq!(id, direct);
                assert_eq!(args[0].as_ty(), Some(u8_ty()));
            }
            other => panic!("expected the direct impl, got {other:?}"),
        }
    }

    /// Steps 1 and 6: param-env evidence wins, and two predicates
    /// that both match an open obligation defer (E0283 parity),
    /// while a concrete input picks one.
    #[test]
    fn param_env_wins_and_two_matches_defer() {
        let mut g = GlobalTys::new();
        let from_tr = def(10);
        let mut index = ImplIndex::new();
        declare_trait(&mut index, from_tr, 1, vec![], vec![]);
        let p0 = ty_param(&mut g, 0);
        // The env of `fn f<T: From<u8> + From<u16>>()`, with T still
        // the abstract parameter type.
        let env = [trait_pred(&mut g, from_tr, &[p0, u8_ty()]), trait_pred(&mut g, from_tr, &[p0, u16_ty()])];

        // `T: From<?X>` matches both: ambiguous, and ?X stays free.
        let mut cx = PureCx::new(&g);
        let x = cx.fresh_var();
        let obl = trait_ref(&mut cx.tys, from_tr, &[p0, x]);
        assert_eq!(Solver::new().select(&mut cx, &index, &env, obl), Selection::Ambiguous);
        let rx = cx.deep_resolve(x);
        assert!(matches!(cx.tys.kind(rx), TyKind::Infer(_)), "an ambiguous selection binds nothing");

        // `T: From<u8>` matches one and commits.
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, from_tr, &[p0, u8_ty()]);
        assert_eq!(Solver::new().select(&mut cx, &index, &env, obl), Selection::ParamEvidence(0));

        // A bare parameter Self with no env match defers; it is
        // never NoImpl, because mono may still prove it.
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, from_tr, &[p0, BOOL]);
        assert_eq!(Solver::new().select(&mut cx, &index, &env, obl), Selection::Ambiguous);
    }

    /// Step 3 binds inference: one `FromIter` candidate fixes the
    /// element type of a `Bag<_>` target (the `Vec<_>` collect
    /// shape), and one `Index` candidate fixes an integer variable
    /// to `usize` (the `s[x]` shape).
    #[test]
    fn one_candidate_binds_inference_vars() {
        let mut g = GlobalTys::new();
        let (from_iter, index_tr, bag, arr_like) = (def(10), def(11), def(20), def(21));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, from_iter, 1, vec![], vec![]);
        declare_trait(&mut index, index_tr, 1, vec![], vec![]);
        let p0 = ty_param(&mut g, 0);
        // impl<A> FromIter<A> for Bag<A>
        let bag_p = g.mk_adt(bag, &[GenericArg::Ty(p0)]);
        add_impl(&mut g, &mut index, 100, from_iter, bag_p, &[p0], 1, vec![], vec![]);
        // impl Index<usize> for ArrLike
        let arr_ty = g.mk_adt(arr_like, &[]);
        add_impl(&mut g, &mut index, 101, index_tr, arr_ty, &[USIZE], 0, vec![], vec![]);

        let mut cx = PureCx::new(&g);
        let elem = cx.fresh_var();
        let bag_ty = cx.tys.mk_adt(bag, &[GenericArg::Ty(elem)]);
        let obl = trait_ref(&mut cx.tys, from_iter, &[bag_ty, u8_ty()]);
        assert!(matches!(Solver::new().select(&mut cx, &index, &[], obl), Selection::Impl { .. }));
        assert_eq!(cx.deep_resolve(elem), u8_ty(), "the element type is fixed by the one candidate");

        let mut cx = PureCx::new(&g);
        let x = cx.fresh_int_var();
        let obl = trait_ref(&mut cx.tys, index_tr, &[arr_ty, x]);
        assert!(matches!(Solver::new().select(&mut cx, &index, &[], obl), Selection::Impl { .. }));
        assert_eq!(cx.deep_resolve(x), USIZE, "the integer variable is fixed to usize");
    }

    /// Section 2.5: an associated equality on a supertrait bound
    /// reaches normalization through elaboration, and a concrete
    /// impl's binding normalizes at mono time.
    #[test]
    fn assoc_eq_normalizes_through_supertrait_and_impl() {
        let mut g = GlobalTys::new();
        let (iter_tr, byte_tr, item, count) = (def(10), def(11), def(30), def(20));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, iter_tr, 0, vec![], vec![item]);
        // trait ByteIter: Iter<Item = u8> -- the supertrait pred
        // over ByteIter's own Self (Param 0), with the binding.
        let p0 = ty_param(&mut g, 0);
        let super_args = g.intern_args(&[GenericArg::Ty(p0)]);
        let super_bindings = g.intern_bindings(&[(item, GenericArg::Ty(u8_ty()))]);
        let super_pred = Predicate::Trait(Binder::plain(TraitRef { def: iter_tr, args: super_args, bindings: super_bindings }));
        declare_trait(&mut index, byte_tr, 0, vec![super_pred], vec![]);
        let count_ty = g.mk_adt(count, &[]);
        add_impl(&mut g, &mut index, 100, iter_tr, count_ty, &[], 0, vec![], vec![(item, u8_ty())]);
        add_impl(&mut g, &mut index, 101, byte_tr, count_ty, &[], 0, vec![], vec![]);

        // Inside `fn sum<I: ByteIter>(..)`: <I as Iter>::Item is u8.
        let mut cx = PureCx::new(&g);
        let byte_pred = trait_pred(&mut cx.tys, byte_tr, &[p0]);
        let env = elaborate_in(&mut cx.tys, &index, &[byte_pred]);
        let proj_args = cx.tys.intern_args(&[GenericArg::Ty(p0)]);
        let proj = cx.tys.intern(TyKind::Projection(AssocId(item), proj_args));
        assert_eq!(normalize(&mut Solver::new(), &mut cx, &index, &env, proj), u8_ty());

        // At mono time with Count: the impl binding rewrites it.
        let mut cx = PureCx::new(&g);
        let proj_args = cx.tys.intern_args(&[GenericArg::Ty(count_ty)]);
        let proj = cx.tys.intern(TyKind::Projection(AssocId(item), proj_args));
        assert_eq!(normalize(&mut Solver::new(), &mut cx, &index, &[], proj), u8_ty());

        // With no evidence at all the projection stays a projection.
        let other = g.mk_adt(def(77), &[]);
        let mut cx = PureCx::new(&g);
        let proj_args = cx.tys.intern_args(&[GenericArg::Ty(other)]);
        let proj = cx.tys.intern(TyKind::Projection(AssocId(item), proj_args));
        assert_eq!(normalize(&mut Solver::new(), &mut cx, &index, &[], proj), proj);
    }

    /// Step 4b: `impl<T, U> Tr for T where T: A<Item = U>` binds U
    /// from the equality once `<u8 as A>::Item` normalizes. With a
    /// Self that has no `A` impl the parameter stays unbound (the
    /// impl-parameter case), never guessed.
    #[test]
    fn step4_binds_impl_param_from_assoc_eq() {
        let mut g = GlobalTys::new();
        let (a_tr, tr, item, no_a) = (def(10), def(11), def(30), def(20));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, a_tr, 0, vec![], vec![item]);
        declare_trait(&mut index, tr, 0, vec![], vec![]);
        // impl A for u8 { type Item = u16 }
        add_impl(&mut g, &mut index, 100, a_tr, u8_ty(), &[], 0, vec![], vec![(item, u16_ty())]);
        // impl<T, U> Tr for T where T: A<Item = U>
        let (p0, p1) = (ty_param(&mut g, 0), ty_param(&mut g, 1));
        let clause_args = g.intern_args(&[GenericArg::Ty(p0)]);
        let clause_bindings = g.intern_bindings(&[(item, GenericArg::Ty(p1))]);
        let clause = Predicate::Trait(Binder::plain(TraitRef { def: a_tr, args: clause_args, bindings: clause_bindings }));
        add_impl(&mut g, &mut index, 101, tr, p0, &[], 2, vec![clause], vec![]);

        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, tr, &[u8_ty()]);
        match Solver::new().select(&mut cx, &index, &[], obl) {
            Selection::Impl { args, unbound, .. } => {
                assert_eq!(args[0].as_ty(), Some(u8_ty()));
                assert_eq!(args[1].as_ty(), Some(u16_ty()), "U is bound from the associated equality");
                assert!(unbound.is_empty());
            }
            other => panic!("expected an impl selection, got {other:?}"),
        }

        let no_a_ty = g.mk_adt(no_a, &[]);
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, tr, &[no_a_ty]);
        match Solver::new().select(&mut cx, &index, &[], obl) {
            Selection::Impl { args, unbound, .. } => {
                assert_eq!(unbound, [ParamId(1)], "the impl-parameter split: it stays unbound, args {args:?}")
            }
            other => panic!("expected an impl selection with an unbound param, got {other:?}"),
        }
    }

    /// A clause cycle is unknown, never false, and never loops:
    /// `Tr` needs `A`, `A` needs `Tr`, both by blanket.
    #[test]
    fn provably_false_cycle_is_unknown() {
        let mut g = GlobalTys::new();
        let (a_tr, tr, s) = (def(10), def(11), def(20));
        let mut index = ImplIndex::new();
        declare_trait(&mut index, a_tr, 0, vec![], vec![]);
        declare_trait(&mut index, tr, 0, vec![], vec![]);
        let p0 = ty_param(&mut g, 0);
        let need_a = trait_pred(&mut g, a_tr, &[p0]);
        let need_tr = trait_pred(&mut g, tr, &[p0]);
        add_impl(&mut g, &mut index, 100, tr, p0, &[], 1, vec![need_a], vec![]);
        add_impl(&mut g, &mut index, 101, a_tr, p0, &[], 1, vec![need_tr], vec![]);
        let s_ty = g.mk_adt(s, &[]);
        let mut cx = PureCx::new(&g);
        let obl = trait_ref(&mut cx.tys, tr, &[s_ty]);
        assert!(!Solver::new().provably_false(&mut cx, &index, &[], obl));
    }
}
