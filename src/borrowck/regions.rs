// Regions over the loan engine (docs/ARCH.md section 5): rustc's NLL for one body.
//
// Checked types are region-erased. This file renumbers every region slot of every
// local's type into a region variable, adds outlives constraints (`'a: 'b`, an edge
// a -> b) from each statement and call by relating types with variance, and solves
// them by reachability. A loan's region then reaches a set of locals (those whose
// types it flows into) and maybe universal regions (`'static` or a lifetime param of
// the fn). `mod.rs` turns that into loan scopes: a loan is in scope from its borrow
// on, through points where one of those locals is live, and everywhere reachable
// when it reaches a universal region. Region values are location-insensitive sets,
// as in rustc, so a reference local that is reassigned keeps every loan it ever held
// for as long as it is live (Polonius would forget them; rustc does not).
//
// Slots of an erased type, in canonical pre-order: a reference contributes its own
// region, then its pointee's slots; an Adt its region params (builtin `Chars` has
// one), then its type args in order; tuples, arrays, slices, and raw pointers their
// elements; a closure its upvar types. Type params, projections, fn pointers, fn
// items, and scalars have none.
//
// Signatures keep their regions in a side table (`RegionTables`) that collect fills
// with the resolver's keep mode (check/generics.rs `RegionMode`): `Region::Static`
// for `'static`, `Region::Param(i)` for the i-th universal region (each elided input
// gets its own, outputs follow Rust's elision rules). Fns without an entry (lang
// trait stubs, instances) get a conservative signature from their erased types.
use super::bit_iter;
use crate::check::collect::*;
use crate::diag::{Diag, Span};
use crate::intern::FxMap;
use crate::ir::*;
use crate::ty::*;

/// The variance of a type position.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Variance {
    Co,
    Contra,
    Inv,
    /// Unused: no constraint. The bottom of `join`.
    Bi,
}

impl Variance {
    /// The variance of a position of variance `inner` inside one of variance `self`.
    pub fn then(self, inner: Variance) -> Variance {
        use Variance::*;
        match (self, inner) {
            (Bi, _) | (_, Bi) => Bi,
            (Inv, _) | (_, Inv) => Inv,
            (Co, x) => x,
            (Contra, Co) => Contra,
            (Contra, Contra) => Co,
        }
    }
    /// The variance of a parameter used at both positions.
    pub fn join(self, o: Variance) -> Variance {
        use Variance::*;
        match (self, o) {
            (Bi, x) | (x, Bi) => x,
            (a, b) if a == b => a,
            _ => Inv,
        }
    }
}

/// How dropping a value of an Adt touches values of one of its type params
/// (drop check, ARCH 5.4): not at all, by dropping them (their own drop check
/// applies), or through a user `Drop` impl that may read all of them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DropMode {
    None,
    Owned,
    All,
}

impl DropMode {
    /// The mode of a position inside a position of mode `self`.
    fn then(self, inner: DropMode) -> DropMode {
        match (self, inner) {
            (DropMode::None, _) | (_, DropMode::None) => DropMode::None,
            (DropMode::All, _) | (_, DropMode::All) => DropMode::All,
            _ => DropMode::Owned,
        }
    }
    fn join(self, o: DropMode) -> DropMode {
        match (self, o) {
            (DropMode::All, _) | (_, DropMode::All) => DropMode::All,
            (DropMode::Owned, _) | (_, DropMode::Owned) => DropMode::Owned,
            _ => DropMode::None,
        }
    }
}

/// The region signature of one fn: params (self first) and return with regions
/// kept, in the shape of the erased types in `FnInfo`. Universal region `i` is
/// `Region::Param(i)`; `'static` is `Region::Static`. `facts` are the known
/// outlives relations `'a: 'b` between universals (from where clauses; implied
/// bounds of the signature types are added when a body is checked).
#[derive(Clone, Debug)]
pub struct RegionSig {
    pub n_univ: u32,
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub facts: Vec<(Region, Region)>,
    /// Display names of the universals, for diagnostics (`'a`, or the
    /// parameter an elided region sits in).
    pub names: Vec<String>,
    /// Per named lifetime (universals `0..early.len()`): early-bound.
    pub early: Vec<bool>,
}

/// The borrow checker's side table of region signatures (W-BORROW, ARCH 5),
/// filled by collect. Read-only after collect, apart from the Adt tables that
/// are computed on first use.
#[derive(Default)]
pub struct RegionTables {
    /// Source fns and methods, by local def.
    pub fns: FxMap<LocalDefId, RegionSig>,
    /// Trait method signatures by method def (the stubs' callee signatures).
    pub trait_methods: FxMap<DefId, RegionSig>,
    /// Regioned field types of each user Adt template, by def: per variant,
    /// per field, with the Adt's lifetime params as `Region::Param(i)`.
    pub adt_fields: FxMap<DefId, Vec<Vec<Ty>>>,
    adts: std::sync::OnceLock<AdtTables>,
    /// The trait method of each trait method stub (the reverse of
    /// `GenTables::trait_method_stubs`), built on first use.
    stub_methods: std::sync::OnceLock<FxMap<LocalDefId, DefId>>,
}

/// Per user Adt template: variance and drop mode of each generic param, by
/// param index (const params are `Bi` and `None`).
#[derive(Default)]
struct AdtTables {
    variance: FxMap<DefId, Vec<Variance>>,
    drop: FxMap<DefId, Vec<DropMode>>,
    /// Per lifetime param of each user Adt template (W-BORROW): its
    /// variance, and whether dropping the Adt may need it live.
    region_variance: FxMap<DefId, Vec<Variance>>,
    region_drop: FxMap<DefId, Vec<DropMode>>,
}

impl RegionTables {
    /// The Adt tables, computed once from the program's Adt templates.
    fn adts(&self, p: &Program) -> &AdtTables {
        self.adts.get_or_init(|| AdtTables::compute(p))
    }

    /// The trait method a stub fn stands for (a stub has its own def).
    fn stub_method(&self, p: &Program, f: LocalDefId) -> Option<DefId> {
        self.stub_methods.get_or_init(|| p.gx.trait_method_stubs.iter().map(|(&m, &s)| (s, m)).collect()).get(&f).copied()
    }
}

/// The user Adt templates: (def, template id), skipping builtins and
/// materialized instances.
fn adt_templates(p: &Program) -> Vec<(DefId, AdtId)> {
    let mut out = Vec::new();
    for i in 0..p.adts.len() {
        let id = AdtId(i as u32);
        if let Some(def) = p.defs.def_of_adt(id)
            && p.defs.local_adt(def) == Some(id)
        {
            out.push((def, id));
        }
    }
    out
}

/// The number of generic params an Adt def's args carry (types and consts).
fn adt_param_count(p: &Program, def: DefId) -> usize {
    p.defs.generics_of(def).map_or(0, |g| g.params.len())
}

impl AdtTables {
    /// Variance and drop mode of every user Adt template's params, by
    /// fixpoint over field types (ARCH 5.3): start unused, join the variance
    /// of each use, and iterate until no table changes. Recursive types
    /// converge because both lattices are finite.
    fn compute(p: &Program) -> AdtTables {
        let templates = adt_templates(p);
        let mut t = AdtTables::default();
        for &(def, _) in &templates {
            let n = adt_param_count(p, def);
            t.variance.insert(def, vec![Variance::Bi; n]);
            let has_drop = super::drop_heads(p).contains(&def);
            t.drop.insert(def, vec![if has_drop { DropMode::All } else { DropMode::None }; n]);
        }
        for &(def, _) in &templates {
            let n = p.gx.adt_lifetimes.get(&def).map_or(0, |v| v.len());
            let has_drop = super::drop_heads(p).contains(&def);
            t.region_variance.insert(def, vec![Variance::Bi; n]);
            t.region_drop.insert(def, vec![if has_drop { DropMode::All } else { DropMode::None }; n]);
        }
        loop {
            let mut changed = false;
            for &(def, id) in &templates {
                let n = adt_param_count(p, def);
                let mut var = vec![Variance::Bi; n];
                let mut drop = t.drop[&def].clone();
                for v in &p.adt(id).variants {
                    for f in &v.fields {
                        t.param_uses(p, f.ty, Variance::Co, DropMode::Owned, &mut var, &mut drop);
                    }
                }
                if t.variance[&def] != var {
                    t.variance.insert(def, var);
                    changed = true;
                }
                if t.drop[&def] != drop {
                    t.drop.insert(def, drop);
                    changed = true;
                }
                // Lifetime params, from the regioned field types.
                let nr = t.region_variance[&def].len();
                if nr > 0 {
                    let mut rvar = vec![Variance::Bi; nr];
                    let mut rdrop = t.region_drop[&def].clone();
                    if let Some(fields) = p.regions.adt_fields.get(&def) {
                        for v in fields {
                            for &f in v {
                                t.region_uses(p, f, Variance::Co, DropMode::Owned, &mut rvar, &mut rdrop);
                            }
                        }
                    }
                    if t.region_variance[&def] != rvar {
                        t.region_variance.insert(def, rvar);
                        changed = true;
                    }
                    if t.region_drop[&def] != rdrop {
                        t.region_drop.insert(def, rdrop);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        t
    }

    /// Joins into `var` and `drop` the uses of each lifetime param
    /// (`Region::Param(i)`) in regioned field type `ty`, at variance `v`
    /// and drop mode `m`: a reference's region at the reference's own
    /// position (only a `Drop` impl reading through it needs it live), an
    /// Adt's region args at that Adt's param variance and drop mode.
    fn region_uses(&self, p: &Program, ty: Ty, v: Variance, m: DropMode, var: &mut [Variance], drop: &mut [DropMode]) {
        let note = |r: Region, v: Variance, m: DropMode, var: &mut [Variance], drop: &mut [DropMode]| {
            if let Region::Param(i) = r {
                if let Some(x) = var.get_mut(i as usize) {
                    *x = x.join(v);
                }
                if let Some(x) = drop.get_mut(i as usize) {
                    *x = x.join(if m == DropMode::All { DropMode::All } else { DropMode::None });
                }
            }
        };
        match p.tys.kind(ty) {
            TyKind::Ref(r, mt, inner) => {
                note(r, v, m, var, drop);
                let iv = if mt.is_mut() { Variance::Inv } else { Variance::Co };
                self.region_uses(p, inner, v.then(iv), if m == DropMode::All { DropMode::All } else { DropMode::None }, var, drop);
            }
            TyKind::RawPtr(mt, inner) => {
                let iv = if mt.is_mut() { Variance::Inv } else { Variance::Co };
                self.region_uses(p, inner, v.then(iv), DropMode::None, var, drop);
            }
            TyKind::Tuple(ts) => {
                for &e in p.tys.tys_of(ts) {
                    self.region_uses(p, e, v, m, var, drop);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.region_uses(p, e, v, m, var, drop),
            TyKind::Adt(def, args) => {
                let (mut k, mut j) = (0usize, 0usize);
                for g in p.tys.args(args) {
                    match *g {
                        GenericArg::Lifetime(r) => {
                            let rv = self.region_variance.get(&def).and_then(|x| x.get(k)).copied().unwrap_or(Variance::Inv);
                            let rm = self.region_drop.get(&def).and_then(|x| x.get(k)).copied().unwrap_or(DropMode::All);
                            let mm = if m == DropMode::None { DropMode::None } else { m.join(rm) };
                            note(r, v.then(rv), mm, var, drop);
                            k += 1;
                        }
                        GenericArg::Ty(e) => {
                            let (pv, pm) = self.arg_modes(p, def, j);
                            self.region_uses(p, e, v.then(pv), m.then(pm), var, drop);
                            j += 1;
                        }
                        GenericArg::Const(_) => j += 1,
                    }
                }
            }
            _ => {
                // A region inside anything else (fn pointers, dyn, closures)
                // is held invariant and drop-visible: the safe answer.
                let mut rs = Vec::new();
                regions_of(&p.tys, ty, &mut rs);
                for r in rs {
                    note(r, Variance::Inv, if m == DropMode::None { DropMode::None } else { DropMode::All }, var, drop);
                }
            }
        }
    }

    /// The variance and drop mode of lifetime param `k` of Adt `def`.
    fn region_modes(&self, def: DefId, k: usize) -> (Variance, DropMode) {
        let v = self.region_variance.get(&def).and_then(|x| x.get(k)).copied().unwrap_or(Variance::Inv);
        let m = self.region_drop.get(&def).and_then(|x| x.get(k)).copied().unwrap_or(DropMode::All);
        (v, m)
    }

    /// Joins into `var` and `drop` the uses of each `Param(i)` in field type `ty`
    /// at position variance `v` and drop mode `m`.
    fn param_uses(&self, p: &Program, ty: Ty, v: Variance, m: DropMode, var: &mut [Variance], drop: &mut [DropMode]) {
        match p.tys.kind(ty) {
            TyKind::Param(i) => {
                if let Some(x) = var.get_mut(i.0 as usize) {
                    *x = x.join(v);
                }
                if let Some(x) = drop.get_mut(i.0 as usize) {
                    *x = x.join(m);
                }
            }
            TyKind::Ref(_, mt, inner) => {
                let iv = if mt.is_mut() { Variance::Inv } else { Variance::Co };
                self.param_uses(p, inner, v.then(iv), DropMode::None, var, drop);
            }
            TyKind::RawPtr(mt, inner) => {
                let iv = if mt.is_mut() { Variance::Inv } else { Variance::Co };
                self.param_uses(p, inner, v.then(iv), DropMode::None, var, drop);
            }
            TyKind::Tuple(ts) => {
                for &e in p.tys.tys_of(ts) {
                    self.param_uses(p, e, v, m, var, drop);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.param_uses(p, e, v, m, var, drop),
            TyKind::Adt(def, args) => {
                for (j, g) in p.tys.args(args).iter().enumerate() {
                    if let GenericArg::Ty(e) = g {
                        let (pv, pm) = self.arg_modes(p, def, j);
                        self.param_uses(p, *e, v.then(pv), m.then(pm), var, drop);
                    }
                }
            }
            TyKind::FnPtr(sig) => {
                let s = p.tys.sig(sig).value;
                for &i in p.tys.tys_of(s.inputs) {
                    self.param_uses(p, i, v.then(Variance::Contra), DropMode::None, var, drop);
                }
                self.param_uses(p, s.output, v, DropMode::None, var, drop);
            }
            // Anything else that names a param (closures, fn items, projections,
            // dyn, opaque types) is held invariant and fully drop-visible: the
            // conservative answer.
            _ => {
                if p.tys.flags(ty).contains_param() {
                    for x in var.iter_mut() {
                        *x = x.join(Variance::Inv);
                    }
                    if m != DropMode::None {
                        for x in drop.iter_mut() {
                            *x = x.join(DropMode::All);
                        }
                    }
                }
            }
        }
    }

    /// The variance and drop mode of arg `j` of Adt `def`: builtin containers
    /// are covariant and own their elements; a user Adt answers from the table
    /// (unknown defs are invariant and fully drop-visible).
    fn arg_modes(&self, p: &Program, def: DefId, j: usize) -> (Variance, DropMode) {
        use crate::ty::iter::IterKind;
        match p.tys.builtins().kind_of(def) {
            // `slice::IterMut<'a, T>` holds `&'a mut [T]`: invariant in `T`.
            Some(BuiltinTy::Iter(IterKind::SliceIterMut)) => return (Variance::Inv, DropMode::None),
            Some(BuiltinTy::Iter(IterKind::SliceIter)) => return (Variance::Co, DropMode::None),
            Some(_) => return (Variance::Co, DropMode::Owned),
            None => {}
        }
        let v = self.variance.get(&def).and_then(|v| v.get(j)).copied().unwrap_or(Variance::Inv);
        let m = self.drop.get(&def).and_then(|d| d.get(j)).copied().unwrap_or(DropMode::All);
        (v, m)
    }
}

/// The number of region params an Adt type carries ahead of its type args:
/// a user Adt's declared lifetimes, or one for the builtin borrowing
/// iterators (`Chars`, `slice::Iter`, `slice::IterMut`, whose erased types
/// drop the lifetime).
fn adt_regions(p: &Program, tys: &impl TyIntern, t: Ty) -> u32 {
    use crate::ty::iter::IterKind;
    match tys.builtin_of(t) {
        Some(BuiltinTy::Chars | BuiltinTy::Iter(IterKind::SliceIter | IterKind::SliceIterMut)) => return 1,
        // A Debug builder holds `&mut Formatter` (W-STD-B).
        Some(BuiltinTy::Fmt(k)) if k.is_builder() => return 1,
        Some(_) => return 0,
        None => {}
    }
    match tys.kind(t) {
        TyKind::Adt(def, _) => p.gx.adt_lifetimes.get(&def).map_or(0, |v| v.len() as u32),
        _ => 0,
    }
}

/// Type facts the region walks need, over one type store.
pub(super) struct SlotCx<'t, 'p, 'a, T: TyIntern> {
    pub tys: &'t T,
    pub p: &'p Program<'a>,
    memo: FxMap<Ty, u32>,
}

impl<'t, 'p, 'a, T: TyIntern> SlotCx<'t, 'p, 'a, T> {
    pub fn new(tys: &'t T, p: &'p Program<'a>) -> Self {
        SlotCx { tys, p, memo: FxMap::default() }
    }

    /// The number of region slots of an erased type.
    pub fn slots(&mut self, t: Ty) -> u32 {
        if let Some(&n) = self.memo.get(&t) {
            return n;
        }
        let n = match self.tys.kind(t) {
            TyKind::Ref(_, _, inner) => 1 + self.slots(inner),
            TyKind::Adt(_, args) => {
                let mut n = adt_regions(self.p, self.tys, t);
                for g in self.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        n += self.slots(e);
                    }
                }
                n
            }
            TyKind::Tuple(ts) => self.tys.tys_of(ts).to_vec().into_iter().map(|e| self.slots(e)).sum(),
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.slots(e),
            TyKind::Closure(_, args) => closure_fields(self.tys, args).into_iter().map(|e| self.slots(e)).sum(),
            _ => 0,
        };
        self.memo.insert(t, n);
        n
    }

    /// The region an erased type keeps at each of its slots (`Erased`, or
    /// `'static` where the erased form kept it), in slot order.
    pub fn slot_regions(&mut self, t: Ty, out: &mut Vec<Region>) {
        match self.tys.kind(t) {
            TyKind::Ref(r, _, inner) => {
                out.push(r);
                self.slot_regions(inner, out);
            }
            TyKind::Adt(_, args) => {
                for _ in 0..adt_regions(self.p, self.tys, t) {
                    out.push(Region::Erased);
                }
                for g in self.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.slot_regions(e, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.tys.tys_of(ts).to_vec() {
                    self.slot_regions(e, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.slot_regions(e, out),
            TyKind::Closure(_, args) => {
                for e in closure_fields(self.tys, args) {
                    self.slot_regions(e, out);
                }
            }
            _ => {}
        }
    }

    /// Calls `f(slot, variance)` for each slot of `t`, in order, starting at
    /// slot index `at`, where `t` sits at position variance `v`. Returns the
    /// next slot index.
    pub fn each_slot(&mut self, t: Ty, v: Variance, at: u32, f: &mut impl FnMut(u32, Variance)) -> u32 {
        match self.tys.kind(t) {
            TyKind::Ref(_, m, inner) => {
                f(at, v);
                let iv = if m.is_mut() { Variance::Inv } else { Variance::Co };
                self.each_slot(inner, v.then(iv), at + 1, f)
            }
            TyKind::Adt(def, args) => {
                let mut at = at;
                for k in 0..adt_regions(self.p, self.tys, t) {
                    let rv = if self.tys.builtin_of(t).is_some() { Variance::Co } else { self.p.regions.adts(self.p).region_modes(def, k as usize).0 };
                    f(at, v.then(rv));
                    at += 1;
                }
                for (j, g) in self.tys.args(args).to_vec().into_iter().enumerate() {
                    if let GenericArg::Ty(e) = g {
                        let (pv, _) = self.p.regions.adts(self.p).arg_modes(self.p, def, j);
                        at = self.each_slot(e, v.then(pv), at, f);
                    }
                }
                at
            }
            TyKind::Tuple(ts) => {
                let mut at = at;
                for e in self.tys.tys_of(ts).to_vec() {
                    at = self.each_slot(e, v, at, f);
                }
                at
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.each_slot(e, v, at, f),
            TyKind::RawPtr(m, e) => self.each_slot(e, v.then(if m.is_mut() { Variance::Inv } else { Variance::Co }), at, f),
            TyKind::Closure(_, args) => {
                let mut at = at;
                for e in closure_fields(self.tys, args) {
                    at = self.each_slot(e, Variance::Inv, at, f);
                }
                at
            }
            _ => at,
        }
    }

    /// Marks in `out` (one bool per slot of `t`, starting at `at`) the slots a
    /// drop of a value of type `t` at mode `m` may need live (drop check, ARCH
    /// 5.4): every slot under a user `Drop` impl, the owned parts below
    /// containers, and nothing behind a reference. Returns the next index.
    pub fn drop_slots(&mut self, t: Ty, m: DropMode, at: u32, out: &mut Vec<bool>) -> u32 {
        let all = m == DropMode::All;
        match self.tys.kind(t) {
            TyKind::Ref(_, _, inner) => {
                out[at as usize] = all;
                self.drop_slots(inner, if all { DropMode::All } else { DropMode::None }, at + 1, out)
            }
            TyKind::RawPtr(_, inner) => self.drop_slots(inner, if all { DropMode::All } else { DropMode::None }, at, out),
            TyKind::Adt(def, args) => {
                let mut at = at;
                for k in 0..adt_regions(self.p, self.tys, t) {
                    let rm = if self.tys.builtin_of(t).is_some() { DropMode::None } else { self.p.regions.adts(self.p).region_modes(def, k as usize).1 };
                    out[at as usize] = all || (m != DropMode::None && rm == DropMode::All);
                    at += 1;
                }
                for (j, g) in self.tys.args(args).to_vec().into_iter().enumerate() {
                    if let GenericArg::Ty(e) = g {
                        let (_, pm) = self.p.regions.adts(self.p).arg_modes(self.p, def, j);
                        at = self.drop_slots(e, m.then(pm), at, out);
                    }
                }
                at
            }
            TyKind::Tuple(ts) => {
                let mut at = at;
                for e in self.tys.tys_of(ts).to_vec() {
                    at = self.drop_slots(e, m, at, out);
                }
                at
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.drop_slots(e, m, at, out),
            TyKind::Closure(_, args) => {
                let mut at = at;
                for e in closure_fields(self.tys, args) {
                    at = self.drop_slots(e, m, at, out);
                }
                at
            }
            _ => at,
        }
    }
}

/// `t` with every region erased: references get `Region::Erased`, Adt lifetime
/// args are dropped. The erased form is what check, mono, and cgen read.
#[allow(dead_code)] // Collect resolves signatures twice today; Adt lifetime params erase with this.
pub fn erase(tys: &mut impl TyIntern, t: Ty) -> Ty {
    match tys.kind(t) {
        TyKind::Ref(r, m, inner) => {
            let i = erase(tys, inner);
            if r == Region::Erased && i == inner { t } else { tys.intern(TyKind::Ref(Region::Erased, m, i)) }
        }
        TyKind::RawPtr(m, inner) => {
            let i = erase(tys, inner);
            if i == inner { t } else { tys.intern(TyKind::RawPtr(m, i)) }
        }
        TyKind::Slice(e) => {
            let i = erase(tys, e);
            if i == e { t } else { tys.intern(TyKind::Slice(i)) }
        }
        TyKind::Array(e, n) => {
            let i = erase(tys, e);
            if i == e { t } else { tys.intern(TyKind::Array(i, n)) }
        }
        TyKind::Tuple(ts) => {
            let old = tys.tys_of(ts).to_vec();
            let new: Vec<Ty> = old.iter().map(|&e| erase(tys, e)).collect();
            if new == old { t } else {
                let id = tys.intern_tys(&new);
                tys.intern(TyKind::Tuple(id))
            }
        }
        TyKind::Adt(def, args) => {
            let (new, same) = erase_args(tys, args);
            if same { t } else { tys.mk_adt(def, &new) }
        }
        TyKind::Projection(a, args) => {
            let (new, same) = erase_args(tys, args);
            if same { t } else {
                let id = tys.intern_args(&new);
                tys.intern(TyKind::Projection(a, id))
            }
        }
        _ => t,
    }
}

/// An arg list with regions erased and lifetime args dropped, and whether
/// it is unchanged.
fn erase_args(tys: &mut impl TyIntern, args: ArgsId) -> (Vec<GenericArg>, bool) {
    let old = tys.args(args).to_vec();
    let mut new = Vec::with_capacity(old.len());
    for g in &old {
        match *g {
            GenericArg::Ty(e) => new.push(GenericArg::Ty(erase(tys, e))),
            GenericArg::Lifetime(_) => {}
            c => new.push(c),
        }
    }
    let same = new == old;
    (new, same)
}

/// Every region of a regioned type, in slot order.
pub fn regions_of(tys: &impl TyIntern, t: Ty, out: &mut Vec<Region>) {
    match tys.kind(t) {
        TyKind::Ref(r, _, inner) => {
            out.push(r);
            regions_of(tys, inner, out);
        }
        TyKind::Adt(_, args) => {
            if tys.is_chars_ty(t) {
                out.push(Region::Erased);
            }
            for g in tys.args(args).to_vec() {
                match g {
                    GenericArg::Ty(e) => regions_of(tys, e, out),
                    GenericArg::Lifetime(r) => out.push(r),
                    GenericArg::Const(_) => {}
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                regions_of(tys, e, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => regions_of(tys, e, out),
        TyKind::Closure(_, args) => {
            for e in closure_fields(tys, args) {
                regions_of(tys, e, out);
            }
        }
        _ => {}
    }
}

/// `t` (a template-form type over the Adt's params) with `args` substituted,
/// if every type it needs is already interned. Never interns.
fn subst_get(tys: &impl TyIntern, t: Ty, args: &[GenericArg]) -> Option<Ty> {
    if !tys.flags(t).contains_param() {
        return Some(t);
    }
    match tys.kind(t) {
        TyKind::Param(j) => args.get(j.0 as usize)?.as_ty(),
        TyKind::Ref(r, m, i) => {
            let i = subst_get(tys, i, args)?;
            tys.get(TyKind::Ref(r, m, i))
        }
        TyKind::RawPtr(m, i) => {
            let i = subst_get(tys, i, args)?;
            tys.get(TyKind::RawPtr(m, i))
        }
        TyKind::Slice(e) => {
            let e = subst_get(tys, e, args)?;
            tys.get(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = subst_get(tys, e, args)?;
            tys.get(TyKind::Array(e, n))
        }
        TyKind::Tuple(ts) => {
            let v: Option<Vec<Ty>> = tys.tys_of(ts).to_vec().into_iter().map(|e| subst_get(tys, e, args)).collect();
            let id = tys.get_tys(&v?)?;
            tys.get(TyKind::Tuple(id))
        }
        TyKind::Adt(d, a) => {
            let v: Option<Vec<GenericArg>> = tys
                .args(a)
                .to_vec()
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(e) => subst_get(tys, e, args).map(GenericArg::Ty),
                    x => Some(x),
                })
                .collect();
            let id = tys.get_args(&v?)?;
            tys.get(TyKind::Adt(d, id))
        }
        _ => None,
    }
}

/// A universal region index: 0 is `'static`, `k + 1` is `Region::Param(k)`.
pub(super) type Univ = u32;

/// The universal regions of the body being checked: per parameter local and
/// the return place, the universal of each slot, plus known relations.
pub(super) struct OwnSig {
    pub n_univ: u32,
    /// Per local `0..=arg_count`: the universal of each slot.
    pub slots: Vec<Vec<Univ>>,
    /// Known `'a: 'b` facts between universals (closed by `known`).
    pub facts: Vec<(Univ, Univ)>,
    /// Display names, by universal (index 0 is `'static`).
    pub names: Vec<String>,
    /// Report universal relations that do not hold (false in instance
    /// bodies: rustc checks the template, and lust's call rules are coarser
    /// than a template's opaque type params).
    pub check: bool,
    /// A closure body: its universals are the closure rule's, not its
    /// parent's named lifetimes.
    pub closure: bool,
}

/// The universal of a regioned signature region.
fn univ_of(r: Region, fresh: &mut impl FnMut() -> Univ) -> Univ {
    match r {
        Region::Static => 0,
        Region::Param(k) => k + 1,
        _ => fresh(),
    }
}

impl OwnSig {
    /// The own signature of a body. `sig` is its fn's region signature, if
    /// any; `closure` marks a closure body (env first). Slots `sig` cannot
    /// pair with the erased local types get fresh, unrelated universals:
    /// conservative inside the body, and callers use the same signature.
    pub fn build<'p, 'a>(p: &'p Program<'a>, body: &Body<'p>, sig: Option<&RegionSig>, closure: bool, check: bool) -> OwnSig {
        let mut sc = SlotCx::new(&body.tys, p);
        let mut own = OwnSig { n_univ: 0, slots: Vec::new(), facts: Vec::new(), names: vec!["'static".into()], check, closure };
        if closure {
            own.closure_sig(p, body, &mut sc);
            return own;
        }
        let f = p.fn_info(body.fn_id);
        if let Some(sig) = sig {
            own.n_univ = sig.n_univ;
            own.names.extend(sig.names.iter().cloned());
            while own.names.len() < own.n_univ as usize + 1 {
                own.names.push(format!("'{}", own.names.len()));
            }
            for &(a, b) in &sig.facts {
                let mut none = || 0;
                own.facts.push((univ_of(a, &mut none), univ_of(b, &mut none)));
            }
        }
        // Type param bindings shared across the signature (instances).
        let mut binds: FxMap<u32, Vec<Univ>> = FxMap::default();
        for l in 0..=body.arg_count {
            let erased = body.locals[l].ty;
            let regioned = sig.and_then(|s| if l == 0 { Some(s.ret) } else { s.params.get(l - 1).copied() });
            let mut out = Vec::new();
            let ok = match regioned {
                Some(r) => own.pair(&mut sc, r, erased, &mut binds, &mut out),
                None => false,
            };
            let n = sc.slots(erased) as usize;
            if !ok || out.len() != n {
                out.clear();
                for _ in 0..n {
                    out.push(own.fresh_univ(&f.name, p));
                }
            }
            own.slots.push(out);
        }
        own.implied(&mut sc, body);
        own
    }

    fn fresh_univ(&mut self, fname: &crate::intern::Sym, p: &Program) -> Univ {
        self.n_univ += 1;
        self.names.push(format!("an anonymous lifetime of `{}`", p.display_name(*fname)));
        self.n_univ
    }

    /// Pairs regioned signature type `r` with erased local type `e`, pushing
    /// the universal of each slot. False when the shapes differ.
    fn pair<T: TyIntern>(&mut self, sc: &mut SlotCx<'_, '_, '_, T>, r: Ty, e: Ty, binds: &mut FxMap<u32, Vec<Univ>>, out: &mut Vec<Univ>) -> bool {
        let tys = sc.tys;
        match (tys.kind(r), tys.kind(e)) {
            (TyKind::Param(j), _) => {
                let n = sc.slots(e) as usize;
                if let TyKind::Param(k) = tys.kind(e)
                    && k == j
                {
                    return true;
                }
                let us = match binds.get(&j.0) {
                    Some(us) if us.len() == n => us.clone(),
                    Some(_) => return false,
                    None => {
                        let us: Vec<Univ> = (0..n)
                            .map(|_| {
                                self.n_univ += 1;
                                self.names.push("a lifetime of a type argument".into());
                                self.n_univ
                            })
                            .collect();
                        binds.insert(j.0, us.clone());
                        us
                    }
                };
                out.extend(us);
                true
            }
            (TyKind::Ref(rr, rm, ri), TyKind::Ref(_, em, ei)) if rm == em => {
                let mut fresh = || {
                    self.n_univ += 1;
                    self.n_univ
                };
                let u = univ_of(rr, &mut fresh);
                while self.names.len() < self.n_univ as usize + 1 {
                    self.names.push("an anonymous lifetime".into());
                }
                out.push(u);
                self.pair(sc, ri, ei, binds, out)
            }
            (TyKind::Adt(rd, ra), TyKind::Adt(ed, ea)) if rd == ed => {
                let lts: Vec<Region> = tys.args(ra).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g { Some(*r) } else { None }).collect();
                for k in 0..adt_regions(sc.p, tys, e) as usize {
                    let mut fresh = || {
                        self.n_univ += 1;
                        self.n_univ
                    };
                    let u = match lts.get(k) {
                        Some(&r) => univ_of(r, &mut fresh),
                        None => fresh(),
                    };
                    while self.names.len() < self.n_univ as usize + 1 {
                        self.names.push("an anonymous lifetime".into());
                    }
                    out.push(u);
                }
                let rargs: Vec<Ty> = tys.args(ra).iter().filter_map(|g| g.as_ty()).collect();
                let eargs: Vec<Ty> = tys.args(ea).iter().filter_map(|g| g.as_ty()).collect();
                rargs.len() == eargs.len() && rargs.iter().zip(&eargs).all(|(&a, &b)| self.pair(sc, a, b, binds, out))
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (a, b) = (tys.tys_of(a).to_vec(), tys.tys_of(b).to_vec());
                a.len() == b.len() && a.iter().zip(&b).all(|(&x, &y)| self.pair(sc, x, y, binds, out))
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.pair(sc, a, b, binds, out)
            }
            _ => r == e && sc.slots(e) == 0,
        }
    }

    /// A closure body's universals: the env reference's region, one class
    /// for every captured region and the output (the creator equates them),
    /// and one distinct universal per input slot (inputs may be any region).
    fn closure_sig<T: TyIntern>(&mut self, p: &Program, body: &Body, sc: &mut SlotCx<'_, '_, '_, T>) {
        let class: Univ = 1;
        self.n_univ = 1;
        self.names.push("the closure's captured lifetimes".into());
        let mut env_ref: Option<Univ> = None;
        for l in 0..=body.arg_count {
            let t = body.locals[l].ty;
            let n = sc.slots(t) as usize;
            let mut out = Vec::with_capacity(n);
            if l == 0 {
                out.resize(n, class);
            } else if l == 1 {
                if let TyKind::Ref(..) = sc.tys.kind(t) {
                    self.n_univ += 1;
                    self.names.push("the closure environment's lifetime".into());
                    env_ref = Some(self.n_univ);
                    out.push(self.n_univ);
                    out.resize(n, class);
                } else {
                    out.resize(n, class);
                }
            } else {
                for _ in 0..n {
                    self.n_univ += 1;
                    self.names.push("a closure argument's lifetime".into());
                    out.push(self.n_univ);
                }
            }
            self.slots.push(out);
        }
        if let Some(e) = env_ref {
            self.facts.push((class, e));
        }
        let _ = p;
        self.implied(sc, body);
    }

    /// Adds the implied bounds of the parameter and return types (rustc's
    /// implied outlives bounds): `&'a T` gives `T: 'a`, so every region
    /// inside a reference outlives the reference's own region.
    fn implied<T: TyIntern>(&mut self, sc: &mut SlotCx<'_, '_, '_, T>, body: &Body) {
        for l in 0..=body.arg_count.min(self.slots.len().saturating_sub(1)) {
            let t = body.locals[l].ty;
            let us = self.slots[l].clone();
            let mut facts = Vec::new();
            implied_walk(sc, t, &us, &mut 0, &mut Vec::new(), &mut facts);
            self.facts.extend(facts);
        }
    }

    /// The reflexive, transitive closure of the facts, as a dense matrix:
    /// `m[a * n + b]` is true when `a: b` is known. `'static` outlives all.
    pub fn known(&self) -> Vec<bool> {
        let n = self.n_univ as usize + 1;
        let mut m = vec![false; n * n];
        for a in 0..n {
            m[a * n + a] = true;
            m[a] = true; // row 0: 'static: a
        }
        for &(a, b) in &self.facts {
            if (a as usize) < n && (b as usize) < n {
                m[a as usize * n + b as usize] = true;
            }
        }
        for k in 0..n {
            for a in 0..n {
                if m[a * n + k] {
                    for b in 0..n {
                        if m[k * n + b] {
                            m[a * n + b] = true;
                        }
                    }
                }
            }
        }
        m
    }
}

/// Walks erased type `t` with slot universals `us` from `*at`, pushing a
/// fact `inner: outer` for every slot inside each enclosing reference.
fn implied_walk<T: TyIntern>(sc: &mut SlotCx<'_, '_, '_, T>, t: Ty, us: &[Univ], at: &mut usize, outer: &mut Vec<Univ>, facts: &mut Vec<(Univ, Univ)>) {
    let each = |u: Univ, facts: &mut Vec<(Univ, Univ)>, outer: &Vec<Univ>| {
        for &o in outer {
            facts.push((u, o));
        }
    };
    match sc.tys.kind(t) {
        TyKind::Ref(_, _, inner) => {
            let Some(&u) = us.get(*at) else { return };
            each(u, facts, outer);
            *at += 1;
            outer.push(u);
            implied_walk(sc, inner, us, at, outer, facts);
            outer.pop();
        }
        TyKind::Adt(_, args) => {
            for _ in 0..adt_regions(sc.p, sc.tys, t) {
                if let Some(&u) = us.get(*at) {
                    each(u, facts, outer);
                }
                *at += 1;
            }
            for g in sc.tys.args(args).to_vec() {
                if let GenericArg::Ty(e) = g {
                    implied_walk(sc, e, us, at, outer, facts);
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in sc.tys.tys_of(ts).to_vec() {
                implied_walk(sc, e, us, at, outer, facts);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => implied_walk(sc, e, us, at, outer, facts),
        TyKind::Closure(_, args) => {
            // A closure's captured regions are one class (see `closure_sig`).
            let start = *at;
            for e in closure_fields(sc.tys, args) {
                implied_walk(sc, e, us, at, outer, facts);
            }
            for i in start..*at {
                for j in start..*at {
                    if let (Some(&a), Some(&b)) = (us.get(i), us.get(j)) {
                        facts.push((a, b));
                    }
                }
            }
        }
        _ => {}
    }
}

/// The region solution of one body, as the loan checks need it.
pub(super) struct Solution {
    /// Words per locals bitset.
    pub wn: usize,
    /// Per loan (`wn` words each): locals whose slots the loan's region
    /// reaches, and locals whose drop-live slots it reaches.
    pub use_locals: Vec<u64>,
    pub drop_locals: Vec<u64>,
    /// Per loan: its region reaches a universal region (it must outlive the
    /// whole body), and it reaches a slot of the return place.
    pub univ: Vec<bool>,
    pub to_ret: Vec<bool>,
    /// Per local: whether a `Drop` of it is a use of some of its regions.
    pub drop_live: Vec<bool>,
    /// Universal relations that do not hold (L0733).
    pub errs: Vec<Diag>,
}

impl Solution {
    pub fn use_set(&self, loan: usize) -> &[u64] {
        &self.use_locals[loan * self.wn..(loan + 1) * self.wn]
    }
    pub fn drop_set(&self, loan: usize) -> &[u64] {
        &self.drop_locals[loan * self.wn..(loan + 1) * self.wn]
    }
}

/// Builds the region constraints of one body and solves them.
pub(super) struct Builder<'b, 'p, 'a> {
    p: &'p Program<'a>,
    body: &'b Body<'p>,
    sc: SlotCx<'b, 'p, 'a, Tys<'p>>,
    own: OwnSig,
    local_base: Vec<u32>,
    /// Per var: owning local + 1, or 0.
    owner: Vec<u32>,
    /// Per var: a drop-live slot of its owner.
    drop_slot: Vec<bool>,
    loan_var: Vec<u32>,
    edges: Vec<(u32, u32)>,
    edge_span: Vec<Span>,
    span: Span,
    /// The loan created by each statement, by body-wide statement index.
    loan_at: &'b [u32],
    stmt_base: &'b [usize],
    /// Errors the constraint walk finds (annotations it cannot follow).
    errs: Vec<Diag>,
    /// While a trait's signature is instantiated over an impl method's
    /// types (`trait_view`): fresh vars per projection, which the impl's
    /// own instantiation constrains.
    proj: Option<FxMap<Ty, Vec<u32>>>,
}

impl<'b, 'p, 'a> Builder<'b, 'p, 'a> {
    pub fn new(p: &'p Program<'a>, body: &'b Body<'p>, own: OwnSig, n_loans: usize, loan_at: &'b [u32], stmt_base: &'b [usize]) -> Self {
        let mut b = Builder {
            p,
            body,
            sc: SlotCx::new(&body.tys, p),
            local_base: Vec::with_capacity(body.locals.len()),
            owner: Vec::new(),
            drop_slot: Vec::new(),
            loan_var: Vec::with_capacity(n_loans),
            edges: Vec::new(),
            edge_span: Vec::new(),
            span: Span::default(),
            loan_at,
            stmt_base,
            own,
            errs: Vec::new(),
            proj: None,
        };
        // Vars 0..=n_univ: 'static and the universals.
        for _ in 0..=b.own.n_univ {
            b.owner.push(0);
            b.drop_slot.push(false);
        }
        let drops = !super::drop_heads(p).is_empty();
        for (l, decl) in body.locals.iter().enumerate() {
            let n = b.local_slots(l as Local);
            let base = b.owner.len() as u32;
            b.local_base.push(base);
            let mut dl = vec![false; n as usize];
            if drops && n > 0 && !fat_local(&body.tys, decl.ty) {
                b.sc.drop_slots(decl.ty, DropMode::Owned, 0, &mut dl);
            }
            for i in 0..n as usize {
                b.owner.push(l as u32 + 1);
                b.drop_slot.push(dl[i]);
            }
        }
        for _ in 0..n_loans {
            let v = b.fresh();
            b.loan_var.push(v);
        }
        b
    }

    fn fresh(&mut self) -> u32 {
        self.owner.push(0);
        self.drop_slot.push(false);
        (self.owner.len() - 1) as u32
    }

    fn edge(&mut self, sup: u32, sub: u32) {
        if sup != sub && sup != 0 {
            self.edges.push((sup, sub));
            self.edge_span.push(self.span);
        }
    }

    /// Edges for slot `x` of a subtype against slot `y` of its supertype.
    fn edge_v(&mut self, x: u32, y: u32, v: Variance) {
        match v {
            Variance::Co => self.edge(x, y),
            Variance::Contra => self.edge(y, x),
            Variance::Inv => {
                self.edge(x, y);
                self.edge(y, x);
            }
            Variance::Bi => {}
        }
    }

    /// Makes every var in `a` and `b` equal, through one hub var.
    fn equate_all(&mut self, a: &[u32], b: &[u32]) {
        if a.len() + b.len() < 2 {
            return;
        }
        let h = self.fresh();
        for &x in a.iter().chain(b) {
            self.edge(x, h);
            self.edge(h, x);
        }
    }

    /// Every var of `from` outlives every var of `to` (through a hub).
    fn flow_all(&mut self, from: &[u32], to: &[u32]) {
        if from.is_empty() || to.is_empty() {
            return;
        }
        let h = self.fresh();
        for &x in from {
            self.edge(x, h);
        }
        for &y in to {
            self.edge(h, y);
        }
    }

    /// The slot count of a local: its type's, plus one leading pointer
    /// slot for a bare slice or `str` local (lowering keeps a subslice in
    /// such a fat-pointer temporary before it becomes a reference).
    fn local_slots(&mut self, l: Local) -> u32 {
        let t = self.body.locals[l as usize].ty;
        self.sc.slots(t) + u32::from(fat_local(&self.body.tys, t))
    }

    fn local_vars(&mut self, l: Local, out: &mut Vec<u32>) {
        let base = self.local_base[l as usize];
        let n = self.local_slots(l);
        out.clear();
        out.extend(base..base + n);
    }

    /// The erased type of `place` and its slot vars, and the reborrow chain
    /// (one `(region var, mutable)` per dereferenced reference, in order).
    /// A projection lust cannot follow exactly returns `ERROR` with the
    /// vars reached so far; relating it equates everything (conservative).
    fn place(&mut self, place: &Place, out: &mut Vec<u32>, derefs: &mut Vec<(u32, bool)>) -> Ty {
        self.local_vars(place.local, out);
        derefs.clear();
        let mut ty = self.body.locals[place.local as usize].ty;
        if fat_local(&self.body.tys, ty) {
            // A fat-pointer local reads as the reference it stands for; an
            // index into it drops the pointer slot.
            if let Some(Proj::Index(_)) = place.proj.first() {
                out.remove(0);
            } else {
                match self.body.tys.get(TyKind::Ref(Region::Erased, Mut::Shared, ty)) {
                    Some(r) => ty = r,
                    None => return ERROR,
                }
            }
        }
        let mut variant = 0u32;
        for pr in &place.proj {
            let tys = &self.body.tys;
            match *pr {
                Proj::Downcast(v) => variant = v,
                Proj::Deref => match tys.kind(ty) {
                    TyKind::Ref(_, m, inner) => {
                        derefs.push((out[0], m.is_mut()));
                        out.remove(0);
                        ty = inner;
                    }
                    TyKind::Adt(..) if tys.adt_first_ty_arg(ty).is_some() && !tys.is_chars_ty(ty) => {
                        // A smart pointer (`Box<T>`): its pointee is its first type arg.
                        let inner = tys.adt_first_ty_arg(ty).unwrap();
                        let n = self.sc.slots(inner) as usize;
                        out.truncate(n);
                        ty = inner;
                    }
                    _ => return ERROR,
                },
                Proj::Field(i) => {
                    let next = self.field(ty, variant, i, out);
                    variant = 0;
                    match next {
                        Some(t) => ty = t,
                        None => return ERROR,
                    }
                }
                Proj::Index(_) => match tys.kind(ty) {
                    TyKind::Array(e, _) | TyKind::Slice(e) => ty = e,
                    _ => match tys.vec_elem(ty) {
                        Some(e) => ty = e,
                        None => return ERROR,
                    },
                },
            }
        }
        ty
    }

    /// Steps `out` (the vars of a value of type `ty`) to field `i` of
    /// `variant`; returns the field's erased type.
    fn field(&mut self, ty: Ty, variant: u32, i: u32, out: &mut Vec<u32>) -> Option<Ty> {
        let tys = &self.body.tys;
        match tys.kind(ty) {
            TyKind::Tuple(ts) => {
                let elems = tys.tys_of(ts).to_vec();
                self.sub_range(&elems, i as usize, 0, out)
            }
            TyKind::Closure(_, args) => {
                let elems = closure_fields(tys, args);
                self.sub_range(&elems, i as usize, 0, out)
            }
            TyKind::Adt(def, args) => {
                if let Some(e) = tys.option_elem(ty) {
                    return Some(e);
                }
                if let Some((t, e)) = tys.result_args(ty) {
                    let elems = [t, e];
                    return self.sub_range(&elems, if variant == 0 { 0 } else { 1 }, 0, out);
                }
                let tmpl = self.p.defs.local_adt(def)?;
                let ftmpl = self.p.adt(tmpl).variants.get(variant as usize)?.fields.get(i as usize)?.ty;
                let gargs = tys.args(args).to_vec();
                // The vars of each type arg inside `out`.
                let mut ranges: Vec<(usize, usize)> = Vec::with_capacity(gargs.len());
                let mut at = adt_regions(self.p, tys, ty) as usize;
                for g in &gargs {
                    let n = match g {
                        GenericArg::Ty(e) => self.sc.slots(*e) as usize,
                        _ => 0,
                    };
                    ranges.push((at, n));
                    at += n;
                }
                // The field's regioned form names the Adt's lifetime params;
                // without one (no references written) the erased template is
                // the same shape.
                let freg = self.p.regions.adt_fields.get(&def).and_then(|v| v.get(variant as usize)).and_then(|f| f.get(i as usize)).copied();
                let mut sub = Vec::new();
                self.subst_vars(freg.unwrap_or(ftmpl), &ranges, out, &mut sub);
                let fty = subst_get(&self.body.tys, ftmpl, &gargs)
                    .or_else(|| {
                        let a = self.body.tys.local_adt(ty)?;
                        Some(self.p.adt(a).variants.get(variant as usize)?.fields.get(i as usize)?.ty)
                    })?;
                if self.sc.slots(fty) as usize != sub.len() {
                    return None;
                }
                *out = sub;
                Some(fty)
            }
            _ => None,
        }
    }

    /// Narrows `out` to the vars of element `i` of `elems` (laid out in
    /// order after `skip` leading vars).
    fn sub_range(&mut self, elems: &[Ty], i: usize, skip: usize, out: &mut Vec<u32>) -> Option<Ty> {
        let mut at = skip;
        for (k, &e) in elems.iter().enumerate() {
            let n = self.sc.slots(e) as usize;
            if k == i {
                let v: Vec<u32> = out.get(at..at + n)?.to_vec();
                *out = v;
                return Some(e);
            }
            at += n;
        }
        None
    }

    /// The vars of regioned field type `f` (template form) under the Adt's
    /// vars: its lifetime param `k` is `vars[k]`, type param `j` the vars in
    /// `ranges[j]`, `'static` var 0.
    fn subst_vars(&mut self, f: Ty, ranges: &[(usize, usize)], vars: &[u32], out: &mut Vec<u32>) {
        let tys = &self.p.tys;
        let region = |r: Region| match r {
            Region::Param(k) => vars.get(k as usize).copied().unwrap_or(0),
            _ => 0,
        };
        match tys.kind(f) {
            TyKind::Param(j) => {
                if let Some(&(s, n)) = ranges.get(j.0 as usize) {
                    out.extend_from_slice(&vars[s.min(vars.len())..(s + n).min(vars.len())]);
                }
            }
            TyKind::Ref(r, _, inner) => {
                out.push(region(r));
                self.subst_vars(inner, ranges, vars, out);
            }
            TyKind::Adt(_, args) => {
                let lts: Vec<Region> = tys.args(args).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g { Some(*r) } else { None }).collect();
                for k in 0..adt_regions(self.p, tys, f) as usize {
                    out.push(lts.get(k).map_or(0, |&r| region(r)));
                }
                for g in tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.subst_vars(e, ranges, vars, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in tys.tys_of(ts).to_vec() {
                    self.subst_vars(e, ranges, vars, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.subst_vars(e, ranges, vars, out),
            TyKind::Closure(_, args) => {
                for e in closure_fields(tys, args) {
                    self.subst_vars(e, ranges, vars, out);
                }
            }
            _ => {}
        }
    }

    /// Adds the edges for `a <: b` at variance `v`. Returns false (after
    /// equating every slot of both sides) when the shapes cannot be paired.
    fn relate(&mut self, a: Ty, av: &[u32], b: Ty, bv: &[u32], v: Variance) -> bool {
        if av.is_empty() && bv.is_empty() {
            return true;
        }
        if a == b && a != ERROR && av.len() == bv.len() {
            let mut pairs: Vec<(u32, Variance)> = Vec::with_capacity(av.len());
            self.sc.each_slot(a, v, 0, &mut |i, var| pairs.push((i, var)));
            for (i, var) in pairs {
                self.edge_v(av[i as usize], bv[i as usize], var);
            }
            return true;
        }
        let (mut ia, mut ib) = (0usize, 0usize);
        if a != ERROR && b != ERROR && self.walk(a, av, &mut ia, b, bv, &mut ib, v) && ia == av.len() && ib == bv.len() {
            return true;
        }
        self.equate_all(av, bv);
        false
    }

    #[allow(clippy::too_many_arguments)]
    fn walk(&mut self, a: Ty, av: &[u32], ia: &mut usize, b: Ty, bv: &[u32], ib: &mut usize, v: Variance) -> bool {
        let tys = &self.body.tys;
        match (tys.kind(a), tys.kind(b)) {
            (TyKind::Ref(_, am, ai), TyKind::Ref(_, bm, bi)) => {
                let (Some(&x), Some(&y)) = (av.get(*ia), bv.get(*ib)) else { return false };
                self.edge_v(x, y, v);
                *ia += 1;
                *ib += 1;
                let iv = if am.is_mut() && bm.is_mut() { Variance::Inv } else { Variance::Co };
                self.walk(ai, av, ia, bi, bv, ib, v.then(iv))
            }
            (TyKind::Ref(_, _, ai), TyKind::RawPtr(bm, bi)) => {
                *ia += 1;
                self.walk(ai, av, ia, bi, bv, ib, v.then(if bm.is_mut() { Variance::Inv } else { Variance::Co }))
            }
            (TyKind::Adt(ad, aa), TyKind::Adt(bd, ba)) if ad == bd => {
                for k in 0..adt_regions(self.p, tys, a) {
                    let (Some(&x), Some(&y)) = (av.get(*ia), bv.get(*ib)) else { return false };
                    let rv = if tys.builtin_of(a).is_some() { Variance::Co } else { self.p.regions.adts(self.p).region_modes(ad, k as usize).0 };
                    self.edge_v(x, y, v.then(rv));
                    *ia += 1;
                    *ib += 1;
                }
                let (xs, ys) = (tys.args(aa).to_vec(), tys.args(ba).to_vec());
                if xs.len() != ys.len() {
                    return false;
                }
                for (j, (x, y)) in xs.into_iter().zip(ys).enumerate() {
                    if let (GenericArg::Ty(x), GenericArg::Ty(y)) = (x, y) {
                        let (pv, _) = self.p.regions.adts(self.p).arg_modes(self.p, ad, j);
                        if !self.walk(x, av, ia, y, bv, ib, v.then(pv)) {
                            return false;
                        }
                    }
                }
                true
            }
            (TyKind::Adt(..), TyKind::Slice(be)) if tys.vec_elem(a).is_some() => {
                let ae = tys.vec_elem(a).unwrap();
                self.walk(ae, av, ia, be, bv, ib, v)
            }
            (TyKind::Tuple(x), TyKind::Tuple(y)) => {
                let (xs, ys) = (tys.tys_of(x).to_vec(), tys.tys_of(y).to_vec());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.walk(x, av, ia, y, bv, ib, v))
            }
            (TyKind::Array(x, _) | TyKind::Slice(x), TyKind::Array(y, _) | TyKind::Slice(y)) => self.walk(x, av, ia, y, bv, ib, v),
            (TyKind::RawPtr(m, x), TyKind::RawPtr(_, y)) => {
                self.walk(x, av, ia, y, bv, ib, v.then(if m.is_mut() { Variance::Inv } else { Variance::Co }))
            }
            (TyKind::Closure(x, xa), TyKind::Closure(y, ya)) if x == y => {
                let (xs, ys) = (closure_fields(tys, xa), closure_fields(tys, ya));
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.walk(x, av, ia, y, bv, ib, Variance::Inv))
            }
            _ => self.sc.slots(a) == 0 && self.sc.slots(b) == 0,
        }
    }
}

/// Callee signature shapes the call rules distinguish.
enum Callee<'s> {
    /// A fn with a region signature: precise instantiation.
    Sig(&'s RegionSig),
    /// A closure body fn: env first, captured regions and output one class.
    Closure,
    /// Anything else: results may hold any argument's regions.
    Opaque,
}

impl<'b, 'p, 'a> Builder<'b, 'p, 'a> {
    /// The region of each slot of erased type `e` under its regioned
    /// annotation `r` (`Erased` where the annotation left it free). False
    /// when the two shapes differ.
    fn annotation_regions(&mut self, r: Ty, e: Ty, out: &mut Vec<Region>) -> bool {
        let et = &self.body.tys;
        match (et.kind(r), et.kind(e)) {
            (TyKind::Ref(rr, rm, ri), TyKind::Ref(_, em, ei)) if rm == em => {
                out.push(rr);
                self.annotation_regions(ri, ei, out)
            }
            (TyKind::Adt(rd, ra), TyKind::Adt(ed, ea)) if rd == ed => {
                let lts: Vec<Region> = et.args(ra).iter().filter_map(|g| if let GenericArg::Lifetime(x) = g { Some(*x) } else { None }).collect();
                for k in 0..adt_regions(self.p, et, e) as usize {
                    out.push(lts.get(k).copied().unwrap_or(Region::Erased));
                }
                let rargs: Vec<Ty> = et.args(ra).iter().filter_map(|g| g.as_ty()).collect();
                let eargs: Vec<Ty> = et.args(ea).iter().filter_map(|g| g.as_ty()).collect();
                rargs.len() == eargs.len() && rargs.into_iter().zip(eargs).all(|(x, y)| self.annotation_regions(x, y, out))
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (xs, ys) = (et.tys_of(a).to_vec(), et.tys_of(b).to_vec());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.annotation_regions(x, y, out))
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.annotation_regions(a, b, out)
            }
            _ => r == e || self.sc.slots(e) == 0,
        }
    }

    /// The vars of an operand (empty for constants, which hold only
    /// `'static` data) and its erased type (`ERROR` for constants).
    fn operand(&mut self, o: &Operand, out: &mut Vec<u32>) -> Ty {
        match o {
            Operand::Copy(p) | Operand::Move(p) => {
                let mut d = Vec::new();
                self.place(p, out, &mut d)
            }
            Operand::Const(_) => {
                out.clear();
                ERROR
            }
        }
    }

    /// Relates operand `o` into the place reached by `dest` plus `proj`.
    fn into_place(&mut self, o: &Operand, dest: &Place, proj: &[Proj]) {
        let mut ov = Vec::new();
        let ot = self.operand(o, &mut ov);
        if ov.is_empty() {
            return;
        }
        let mut target = dest.clone();
        target.proj.extend_from_slice(proj);
        let (mut dv, mut d) = (Vec::new(), Vec::new());
        let dt = self.place(&target, &mut dv, &mut d);
        self.relate(ot, &ov, dt, &dv, Variance::Co);
    }

    /// The constraints of every statement, terminator, and the entry.
    pub fn build(&mut self) {
        // Every local's type is well formed (`&'a T` needs `T: 'a`), and a
        // region the erased type kept (`&'static dyn Tr`, see
        // `check::object`) is `'static`.
        let mut vars = Vec::new();
        let mut regs = Vec::new();
        for l in 0..self.body.locals.len() {
            let t = self.body.locals[l].ty;
            if self.sc.slots(t) == 0 {
                continue;
            }
            self.local_vars(l as Local, &mut vars);
            let skip = usize::from(fat_local(&self.body.tys, t));
            let inner = vars[skip..].to_vec();
            self.implied_edges(t, &inner, &mut 0, &mut Vec::new());
            regs.clear();
            self.sc.slot_regions(t, &mut regs);
            for (i, r) in regs.iter().enumerate() {
                if *r == Region::Static
                    && let Some(&v) = inner.get(i)
                {
                    self.edge(v, 0);
                }
            }
        }
        // `let` annotations with explicit lifetimes (W-BORROW): the local's
        // regions equal the written ones (`'static`, or a named lifetime of
        // the fn); an elided one is free.
        for &(l, r) in &self.body.annotations.clone() {
            self.local_vars(l, &mut vars);
            let t = self.body.locals[l as usize].ty;
            let mut regs = Vec::new();
            let ok = !fat_local(&self.body.tys, t) && self.annotation_regions(r, t, &mut regs) && regs.len() == vars.len();
            if !ok {
                self.errs.push(Diag::new(
                    "L0203",
                    self.p.fn_info(self.body.fn_id).def.name_span,
                    "an explicit lifetime in a `let` annotation here is not supported yet",
                    "Drop the lifetime from the annotation, or write `'_`.",
                ));
                continue;
            }
            for (i, reg) in regs.into_iter().enumerate() {
                match reg {
                    Region::Static => self.edge(vars[i], 0),
                    Region::Param(k) if self.own.closure => {
                        let _ = k;
                        self.errs.push(Diag::new(
                            "L0203",
                            self.p.fn_info(self.body.fn_id).def.name_span,
                            "a named lifetime in a `let` annotation inside a closure is not supported yet",
                            "Drop the lifetime from the annotation, or write `'_`.",
                        ));
                    }
                    Region::Param(k) if k < self.own.n_univ => {
                        let u = k + 1;
                        self.edge(vars[i], u);
                        self.edge(u, vars[i]);
                    }
                    _ => {}
                }
            }
        }
        // Entry: parameter locals and the return place equal the signature.
        for l in 0..=self.body.arg_count.min(self.own.slots.len().saturating_sub(1)) {
            let base = self.local_base[l];
            for (i, u) in self.own.slots[l].clone().into_iter().enumerate() {
                self.edge(base + i as u32, u);
                self.edge(u, base + i as u32);
            }
        }
        let body = self.body;
        for (bi, b) in body.blocks.iter().enumerate() {
            for (si, s) in b.stmts.iter().enumerate() {
                self.span = s.span;
                if let StmtKind::Assign(dest, rv) = &s.kind {
                    self.assign(bi, si, dest, rv);
                }
            }
            self.span = b.term_span;
            if let Terminator::Call { target, args, dest, .. } = &b.term {
                self.call(*target, args, dest);
            }
        }
    }

    fn assign(&mut self, bi: usize, si: usize, dest: &Place, rv: &Rvalue) {
        let (mut dv, mut d) = (Vec::new(), Vec::new());
        match rv {
            Rvalue::Use(o) | Rvalue::Cast(o, _) => {
                let mut ov = Vec::new();
                let ot = self.operand(o, &mut ov);
                if ov.is_empty() {
                    return;
                }
                let dt = self.place(dest, &mut dv, &mut d);
                self.relate(ot, &ov, dt, &dv, Variance::Co);
            }
            Rvalue::Ref(_, place) | Rvalue::SliceOf(place) | Rvalue::Subslice { base: place, .. } => {
                let li = self.loan_at[self.stmt_base[bi] + si];
                if li == u32::MAX {
                    return;
                }
                let lv = self.loan_var[li as usize];
                let mutable = match rv {
                    Rvalue::Ref(m, _) => *m,
                    Rvalue::Subslice { mutable, .. } => *mutable,
                    _ => matches!(self.body.tys.kind(self.body.locals[dest.local as usize].ty), TyKind::Ref(_, Mut::Mut, _)),
                };
                let (mut pv, mut derefs) = (Vec::new(), Vec::new());
                let pt = self.place(place, &mut pv, &mut derefs);
                // Reborrow constraints (rustc `add_reborrow_constraint`): each
                // dereferenced reference outlives the new loan, from the last
                // deref back, stopping after the first shared one.
                for &(r, is_mut) in derefs.iter().rev() {
                    self.edge(r, lv);
                    if !is_mut {
                        break;
                    }
                }
                // The new reference is well formed: every region in the
                // borrowed value outlives it (`&'l T` needs `T: 'l`).
                for &v in &pv {
                    self.edge(v, lv);
                }
                let dt = self.place(dest, &mut dv, &mut d);
                let Some(&d0) = dv.first() else { return };
                self.edge(lv, d0);
                if let TyKind::Ref(_, _, dinner) = self.body.tys.kind(dt) {
                    let inner_v = if mutable { Variance::Inv } else { Variance::Co };
                    self.relate(pt, &pv, dinner, &dv[1..], inner_v);
                } else {
                    self.equate_all(&pv, &dv);
                }
            }
            Rvalue::Aggregate(_, variant, ops) => {
                for (i, o) in ops.iter().enumerate() {
                    self.into_place(o, dest, &[Proj::Downcast(*variant), Proj::Field(i as u32)]);
                }
            }
            Rvalue::Opt(_, Some(o)) => self.into_place(o, dest, &[Proj::Downcast(1), Proj::Field(0)]),
            Rvalue::Res(_, ok, o) => self.into_place(o, dest, &[Proj::Downcast(if *ok { 0 } else { 1 }), Proj::Field(0)]),
            Rvalue::TupleAgg(ty, ops) => {
                for (i, o) in ops.iter().enumerate() {
                    self.into_place(o, dest, &[Proj::Field(i as u32)]);
                }
                if let TyKind::Closure(..) = self.body.tys.kind(*ty) {
                    // A closure's captured regions form one class: its body
                    // may move data between captures and into its output.
                    self.place(dest, &mut dv, &mut d);
                    self.equate_all(&dv, &[]);
                }
            }
            Rvalue::ArrayAgg(_, ops) | Rvalue::VecLit(_, ops) => {
                for o in ops {
                    self.into_place(o, dest, &[Proj::Index(0)]);
                }
            }
            Rvalue::ArrayRepeat(_, o, _) | Rvalue::VecRepeat(_, o, _) => self.into_place(o, dest, &[Proj::Index(0)]),
            Rvalue::MakeDyn { ptr: o, .. } | Rvalue::DynUpcast { ptr: o, .. } => {
                // A dyn pointer from a thin one (or a narrower dyn): the
                // pointer's region carries over. The object lifetime is
                // `check::object`'s; the data's own regions stay alive
                // through the pointer by its well-formedness (`T: 'p`).
                let mut ov = Vec::new();
                self.operand(o, &mut ov);
                let dt = self.place(dest, &mut dv, &mut d);
                let _ = dt;
                if let (Some(&x), Some(&y)) = (ov.first(), dv.first()) {
                    self.edge(x, y);
                }
                if ov.len() > 1 && dv.len() > 1 {
                    self.equate_all(&ov[1..], &dv[1..]);
                }
            }
            _ => {}
        }
    }

    fn callee(&self, f: LocalDefId) -> Callee<'p> {
        let p = self.p;
        if p.gx.closure_fns.contains_key(&f) {
            return Callee::Closure;
        }
        if let Some(s) = p.regions.fns.get(&f) {
            return Callee::Sig(s);
        }
        if let Some(inst) = p.gx.instances.get(&f)
            && let Some(t) = inst.template_local
            && let Some(s) = p.regions.fns.get(&t)
        {
            return Callee::Sig(s);
        }
        if p.gx.fn_class.get(f.0 as usize) == Some(&crate::check::generics::FnClass::Stub)
            && let Some(m) = p.regions.stub_method(p, f)
            && let Some(s) = p.regions.trait_methods.get(&m)
        {
            return Callee::Sig(s);
        }
        Callee::Opaque
    }

    /// The trait method behind a vtable call. Lowering upcasts the
    /// receiver to the method's own trait first, so the receiver's
    /// principal owns the slot.
    fn dyn_method(&self, recv: Ty, slot: u32) -> Option<DefId> {
        let TyKind::Ref(_, _, obj) = self.body.tys.kind(recv) else { return None };
        let owner = crate::check::object::principal_of(&self.body.tys, obj)?;
        let info = self.p.gx.dyn_infos.get(&owner.def)?;
        let j = slot.checked_sub(crate::check::object::VT_HEADER + info.supers.len() as u32)?;
        Some(info.methods.get(j as usize)?.def)
    }

    /// A call of a trait impl method also takes the trait method's
    /// signature: rustc checks every call against the trait item, and an
    /// impl may refine it (take `&str` where the trait takes `&'static
    /// str`, return `&'static str` or its own `'a` where the trait borrows
    /// `self`). The trait's signature is instantiated over the called fn's
    /// erased types, on top of the impl's own constraints, which the
    /// trait's imply (`impl_contract`). A std trait has no region
    /// signature; its methods elide, so a returned reference borrows
    /// `self`.
    fn trait_view(&mut self, f: LocalDefId, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) {
        let p = self.p;
        let Some(tmeth) = impl_trait_method(p, f) else { return };
        if let Some(tsig) = p.regions.trait_methods.get(&tmeth) {
            let info = p.fn_info(f);
            self.proj = Some(FxMap::default());
            let preds = p.gx.trait_methods.get(&tmeth).map_or(&[][..], |t| &t.generics.predicates[..]);
            let ok = self.call_sig_with(tsig, &info.params, info.ret, avs, dt, dv, preds);
            self.proj = None;
            if !ok {
                self.call_opaque(avs, dt, dv);
            }
        } else if let Some(lm) = p.gx.lang_method_sigs.get(&tmeth)
            && matches!(lm.self_kind, Some(crate::ast::SelfKind::Ref | crate::ast::SelfKind::RefMut))
            && matches!(p.tys.kind(lm.ret), TyKind::Ref(..))
            && let Some((rt, rv)) = avs.first()
            && matches!(self.body.tys.kind(*rt), TyKind::Ref(..))
            && matches!(self.body.tys.kind(dt), TyKind::Ref(..))
            && let (Some(&s), Some(&d)) = (rv.first(), dv.first())
        {
            self.edge(s, d);
        }
    }

    fn call(&mut self, target: CallTarget, args: &[Operand], dest: &Place) {
        let mut avs: Vec<(Ty, Vec<u32>)> = Vec::with_capacity(args.len());
        for o in args {
            let mut v = Vec::new();
            let t = self.operand(o, &mut v);
            avs.push((t, v));
        }
        let (mut dv, mut d) = (Vec::new(), Vec::new());
        let dt = self.place(dest, &mut dv, &mut d);
        // A vtable call takes the trait method's signature, which every
        // impl satisfies (`impl_contract`). The object's hidden regions
        // stay alive through the pointer's region (`MakeDyn`), so a
        // `-> &'static str` method borrows nothing and a `&'static str`
        // argument must be `'static`.
        if let CallTarget::Dyn(slot) = target
            && let Some(def) = avs.first().and_then(|(rt, _)| self.dyn_method(*rt, slot))
            && let Some(sig) = self.p.regions.trait_methods.get(&def)
            && let Some(t) = self.p.gx.trait_methods.get(&def)
        {
            if !self.call_sig_with(sig, &t.params, t.ret, &avs, dt, &dv, &[]) {
                self.call_opaque(&avs, dt, &dv);
            }
            return;
        }
        let callee = match target {
            CallTarget::Fn(f) => Some((f, self.callee(f))),
            _ => None,
        };
        match callee {
            Some((f, Callee::Sig(sig))) => {
                if !self.call_sig(f, sig, &avs, dt, &dv) {
                    self.call_opaque(&avs, dt, &dv);
                }
                self.trait_view(f, &avs, dt, &dv);
            }
            Some((_, Callee::Closure)) => {
                // The env's captured regions and the result are one class.
                let class = self.fresh();
                if let Some((et, ev)) = avs.first() {
                    let skip = usize::from(matches!(self.body.tys.kind(*et), TyKind::Ref(..)));
                    for &x in ev.iter().skip(skip) {
                        self.edge(x, class);
                        self.edge(class, x);
                    }
                }
                for &y in &dv {
                    self.edge(class, y);
                }
            }
            _ if matches!(target, CallTarget::Builtin(b) if fmt_builder_builtin(b)) => {
                // A Debug builder (W-STD-B) borrows only what its receiver
                // does: `debug_struct(&mut self, &str)` and `entry(&mut
                // self, &dyn Debug) -> &mut Self` format their other
                // arguments at once and never store them.
                if let Some((rt, rv)) = avs.first() {
                    let (rt, rv) = (*rt, rv.clone());
                    // `&mut Self` back: the receiver's own regions, slot
                    // by slot; a new builder: what the `&mut Formatter`
                    // borrow allows.
                    if !self.relate(rt, &rv, dt, &dv, Variance::Co) {
                        self.flow_all(&rv, &dv);
                    }
                }
            }
            _ if matches!(target, CallTarget::Builtin(b) if item_builtin(b)) => {
                // An iterator item (or a collection of items) borrows what
                // the iterator's sources borrow: not the temporary `&mut`
                // of the iterator, and not a closure's captures (a lust
                // closure cannot return a reference). W-STD-A, ty/iter.rs.
                let mut from: Vec<u32> = Vec::new();
                for (t, v) in &avs {
                    let (inner, vars) = match self.body.tys.kind(*t) {
                        TyKind::Ref(_, _, inner) if !v.is_empty() => (inner, &v[1..]),
                        _ => (*t, &v[..]),
                    };
                    self.non_closure_slots(inner, vars, &mut 0, &mut from);
                }
                self.flow_all(&from, &dv);
            }
            _ if matches!(target, CallTarget::Builtin(b) if receiver_builtin(b)) && self.call_receiver(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(_)) && matches!(self.body.tys.builtin_of(dt), Some(BuiltinTy::Iter(_))) => {
                self.call_adapter(&avs, dt, &dv);
            }
            _ => self.call_opaque(&avs, dt, &dv),
        }
    }

    /// A builtin that borrows into its receiver (`v.get(i)`, `v.last_mut()`,
    /// `s.trim()`, `v.iter()`): Rust's `fn f<'r>(&'r self, ..) -> R<'r>`.
    /// Each part of the result whose type is one of the receiver's
    /// components (a `Vec`'s element type, a slice's) equals that
    /// component's regions; every other region of the result is outlived
    /// by the receiver borrow's region. The other arguments do not flow
    /// into the result. False (nothing added) when the receiver is not a
    /// reference.
    fn call_receiver(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, _, x) = self.body.tys.kind(*t0) else { return false };
        let Some((&r, xv)) = v0.split_first() else { return false };
        let tys = &self.body.tys;
        let comp: Option<Ty> = match tys.kind(x) {
            TyKind::Slice(e) | TyKind::Array(e, _) => Some(e),
            _ => tys.vec_elem(x),
        };
        // The element type sits at the end of the receiver's slots (after
        // any region params of the container, which these builtins lack).
        let comp_vars: Vec<u32> = match comp {
            Some(e) => {
                let n = self.sc.slots(e) as usize;
                if n > xv.len() {
                    return false;
                }
                xv[xv.len() - n..].to_vec()
            }
            None => Vec::new(),
        };
        let mut at = 0usize;
        self.receiver_walk(dt, dv, &mut at, r, comp, &comp_vars);
        true
    }

    fn receiver_walk(&mut self, t: Ty, dv: &[u32], at: &mut usize, r: u32, comp: Option<Ty>, comp_vars: &[u32]) {
        if comp == Some(t) && self.sc.slots(t) as usize == comp_vars.len() {
            for (i, &c) in comp_vars.iter().enumerate() {
                if let Some(&d) = dv.get(*at + i) {
                    self.edge(c, d);
                    self.edge(d, c);
                }
            }
            *at += comp_vars.len();
            return;
        }
        let tys = &self.body.tys;
        match tys.kind(t) {
            TyKind::Ref(_, _, inner) => {
                if let Some(&d) = dv.get(*at) {
                    self.edge(r, d);
                }
                *at += 1;
                self.receiver_walk(inner, dv, at, r, comp, comp_vars);
            }
            TyKind::Adt(_, args) => {
                for _ in 0..adt_regions(self.p, tys, t) {
                    if let Some(&d) = dv.get(*at) {
                        self.edge(r, d);
                    }
                    *at += 1;
                }
                for g in tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.receiver_walk(e, dv, at, r, comp, comp_vars);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in tys.tys_of(ts).to_vec() {
                    self.receiver_walk(e, dv, at, r, comp, comp_vars);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.receiver_walk(e, dv, at, r, comp, comp_vars),
            _ => {
                let n = self.sc.slots(t) as usize;
                for i in 0..n {
                    if let Some(&d) = dv.get(*at + i) {
                        self.edge(r, d);
                    }
                }
                *at += n;
            }
        }
    }

    /// A builtin that builds an iterator adapter (`map`, `filter`,
    /// `inspect`, ...): the adapter stores its arguments as its type args,
    /// so an argument whose type is one of those args flows into that part
    /// only (a closure's captures do not reach the source iterator's
    /// regions). Any other argument flows into every part.
    fn call_adapter(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) {
        let Some((_, args)) = self.body.tys.adt_parts(dt) else { return self.call_opaque(avs, dt, dv) };
        let comps: Vec<Ty> = self.body.tys.args(args).iter().filter_map(|g| g.as_ty()).collect();
        let mut ranges: Vec<(usize, usize)> = Vec::with_capacity(comps.len());
        let mut at = adt_regions(self.p, &self.body.tys, dt) as usize;
        for &c in &comps {
            let n = self.sc.slots(c) as usize;
            ranges.push((at, n));
            at += n;
        }
        if at != dv.len() {
            return self.call_opaque(avs, dt, dv);
        }
        let mut used = vec![false; comps.len()];
        for (t, v) in avs {
            if v.is_empty() {
                continue;
            }
            match (0..comps.len()).find(|&j| !used[j] && comps[j] == *t && ranges[j].1 == v.len()) {
                Some(j) => {
                    used[j] = true;
                    let (s0, n) = ranges[j];
                    let part = dv[s0..s0 + n].to_vec();
                    if !self.relate(*t, v, comps[j], &part, Variance::Co) {
                        self.flow_all(v, dv);
                    }
                }
                None => self.flow_all(v, dv),
            }
        }
    }

    /// The vars of the slots of `t` (laid out from `*at` in `vars`) that do
    /// not sit inside a closure type.
    fn non_closure_slots(&mut self, t: Ty, vars: &[u32], at: &mut usize, out: &mut Vec<u32>) {
        let n = self.sc.slots(t) as usize;
        if let TyKind::Closure(..) = self.body.tys.kind(t) {
            *at += n;
            return;
        }
        match self.body.tys.kind(t) {
            TyKind::Ref(_, _, inner) => {
                if let Some(&v) = vars.get(*at) {
                    out.push(v);
                }
                *at += 1;
                self.non_closure_slots(inner, vars, at, out);
            }
            TyKind::Adt(_, args) => {
                for _ in 0..adt_regions(self.p, &self.body.tys, t) {
                    if let Some(&v) = vars.get(*at) {
                        out.push(v);
                    }
                    *at += 1;
                }
                for g in self.body.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.non_closure_slots(e, vars, at, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.body.tys.tys_of(ts).to_vec() {
                    self.non_closure_slots(e, vars, at, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.non_closure_slots(e, vars, at, out),
            _ => {
                out.extend(vars.iter().skip(*at).take(n).copied());
                *at += n;
            }
        }
    }

    /// The conservative call rule: the result may hold any argument's
    /// regions (equal to them when it holds a `&mut`), and each `&mut`
    /// argument's target may receive every other argument's regions.
    fn call_opaque(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) {
        let all: Vec<u32> = avs.iter().flat_map(|(_, v)| v.iter().copied()).collect();
        if has_mut_ref(&self.body.tys, dt) {
            self.equate_all(&all, dv);
        } else {
            self.flow_all(&all, dv);
        }
        for (i, (t, v)) in avs.iter().enumerate() {
            if let TyKind::Ref(_, Mut::Mut, _) = self.body.tys.kind(*t)
                && v.len() > 1
            {
                let others: Vec<u32> = avs.iter().enumerate().filter(|(j, _)| *j != i).flat_map(|(_, (_, v))| v.iter().copied()).collect();
                self.flow_all(&others, &v[1..]);
            }
        }
    }

    /// Instantiates `sig` at a call of `f`: fresh vars for its universals,
    /// type params bound from `f`'s erased param types, `arg <: param` and
    /// `ret <: dest`, plus the callee's facts and implied bounds. False when
    /// the signature cannot be paired with the call's types.
    fn call_sig(&mut self, f: LocalDefId, sig: &RegionSig, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let p = self.p;
        let info = p.fn_info(f);
        // The callee's bounds name the template's params, like `sig`.
        let src = p.gx.instances.get(&f).and_then(|i| i.template_local).unwrap_or(f);
        let preds = p.gx.fn_templates.get(src.0 as usize).and_then(|t| t.as_ref()).map_or(&[][..], |t| &t.generics.predicates[..]);
        self.call_sig_with(sig, &info.params, info.ret, avs, dt, dv, preds)
    }

    /// `call_sig` over the callee's erased param and return types. A
    /// `T: 'static` bound makes every region bound to `T` outlive
    /// `'static` (check proves the rest of the bound; regions are here).
    #[allow(clippy::too_many_arguments)]
    fn call_sig_with(
        &mut self,
        sig: &RegionSig,
        params: &[Ty],
        ret: Ty,
        avs: &[(Ty, Vec<u32>)],
        dt: Ty,
        dv: &[u32],
        preds: &[Predicate],
    ) -> bool {
        if params.len() != sig.params.len() || avs.len() != sig.params.len() {
            return false;
        }
        let univ: Vec<u32> = (0..sig.n_univ).map(|_| self.fresh()).collect();
        let mut binds: FxMap<u32, Vec<u32>> = FxMap::default();
        let mut ok = true;
        // A callee type that names type params (a template called in
        // check mode, a stub) has no slots where its params are: the
        // call's own types give them, so the params bind their slots.
        let has_param = |t: Ty| self.p.tys.flags(t).contains_param();
        for i in 0..avs.len() {
            let (at, av) = &avs[i];
            let et = if has_param(params[i]) { *at } else { params[i] };
            let mut pv = Vec::new();
            ok &= self.inst(sig.params[i], et, &univ, &mut binds, &mut pv);
            if !av.is_empty() {
                ok &= self.relate(*at, av, et, &pv, Variance::Co);
            }
        }
        let er = if has_param(ret) { dt } else { ret };
        let mut rv = Vec::new();
        ok &= self.inst(sig.ret, er, &univ, &mut binds, &mut rv);
        if !dv.is_empty() {
            ok &= self.relate(er, &rv, dt, dv, Variance::Co);
        }
        for &(a, b) in &sig.facts {
            let (x, y) = (self.inst_region(a, &univ), self.inst_region(b, &univ));
            self.edge(x, y);
        }
        for pred in preds {
            if let Predicate::TypeOutlives(t, Region::Static) = pred
                && let TyKind::Param(j) = self.p.tys.kind(*t)
                && let Some(vs) = binds.get(&j.0)
            {
                for &v in vs {
                    self.edge(v, 0);
                }
            }
        }
        ok
    }

    fn inst_region(&mut self, r: Region, univ: &[u32]) -> u32 {
        match r {
            Region::Static => 0,
            Region::Param(k) => univ.get(k as usize).copied().unwrap_or_else(|| self.fresh()),
            _ => self.fresh(),
        }
    }

    /// The vars of erased type `e` under regioned signature type `r`:
    /// universals map through `univ`, each type param binds once (fresh
    /// vars shared by all its occurrences). Also adds the implied bounds of
    /// `r` (every region inside a reference outlives it) as constraints.
    fn inst(&mut self, r: Ty, e: Ty, univ: &[u32], binds: &mut FxMap<u32, Vec<u32>>, out: &mut Vec<u32>) -> bool {
        let start = out.len();
        let ok = self.inst_walk(r, e, univ, binds, out);
        if !ok {
            out.truncate(start);
            let n = self.sc.slots(e);
            for _ in 0..n {
                let v = self.fresh();
                out.push(v);
            }
            return false;
        }
        let mut refs: Vec<u32> = Vec::new();
        let vars = out[start..].to_vec();
        self.implied_edges(e, &vars, &mut 0, &mut refs);
        true
    }

    fn inst_walk(&mut self, r: Ty, e: Ty, univ: &[u32], binds: &mut FxMap<u32, Vec<u32>>, out: &mut Vec<u32>) -> bool {
        let tys = &self.p.tys;
        let et = &self.body.tys;
        match (tys.kind(r), et.kind(e)) {
            (TyKind::Param(j), _) => {
                let n = self.sc.slots(e) as usize;
                match binds.get(&j.0) {
                    Some(v) if v.len() == n => out.extend_from_slice(v),
                    Some(_) => return false,
                    None => {
                        let v: Vec<u32> = (0..n).map(|_| self.fresh()).collect();
                        out.extend_from_slice(&v);
                        binds.insert(j.0, v);
                    }
                }
                true
            }
            (TyKind::Projection(..), _) if self.proj.is_some() => {
                let n = self.sc.slots(e) as usize;
                let have = self.proj.as_ref().and_then(|m| m.get(&r)).cloned();
                match have {
                    Some(v) if v.len() == n => out.extend_from_slice(&v),
                    Some(_) => return false,
                    None => {
                        let v: Vec<u32> = (0..n).map(|_| self.fresh()).collect();
                        out.extend_from_slice(&v);
                        if let Some(m) = self.proj.as_mut() {
                            m.insert(r, v);
                        }
                    }
                }
                true
            }
            (TyKind::Ref(rr, rm, ri), TyKind::Ref(_, em, ei)) if rm == em => {
                let v = self.inst_region(rr, univ);
                out.push(v);
                self.inst_walk(ri, ei, univ, binds, out)
            }
            (TyKind::Adt(rd, ra), TyKind::Adt(ed, ea)) if rd == ed => {
                let lts: Vec<Region> = tys.args(ra).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g { Some(*r) } else { None }).collect();
                for k in 0..adt_regions(self.p, et, e) as usize {
                    let v = match lts.get(k) {
                        Some(&r) => self.inst_region(r, univ),
                        None => self.fresh(),
                    };
                    out.push(v);
                }
                let rargs: Vec<Ty> = tys.args(ra).iter().filter_map(|g| g.as_ty()).collect();
                let eargs: Vec<Ty> = et.args(ea).iter().filter_map(|g| g.as_ty()).collect();
                rargs.len() == eargs.len() && rargs.into_iter().zip(eargs).all(|(x, y)| self.inst_walk(x, y, univ, binds, out))
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (xs, ys) = (tys.tys_of(a).to_vec(), et.tys_of(b).to_vec());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.inst_walk(x, y, univ, binds, out))
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.inst_walk(a, b, univ, binds, out)
            }
            _ => self.sc.slots(e) == 0,
        }
    }

    /// Edges for the implied bounds of a type with slot vars: every slot
    /// inside a reference outlives the reference's region.
    fn implied_edges(&mut self, t: Ty, vars: &[u32], at: &mut usize, refs: &mut Vec<u32>) {
        let tys = &self.body.tys;
        match tys.kind(t) {
            TyKind::Ref(_, _, inner) => {
                let Some(&v) = vars.get(*at) else { return };
                for &o in refs.iter() {
                    self.edge(v, o);
                }
                *at += 1;
                refs.push(v);
                self.implied_edges(inner, vars, at, refs);
                refs.pop();
            }
            TyKind::Adt(_, args) => {
                for _ in 0..adt_regions(self.p, tys, t) {
                    if let Some(&v) = vars.get(*at) {
                        for &o in refs.iter() {
                            self.edge(v, o);
                        }
                    }
                    *at += 1;
                }
                for g in tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.implied_edges(e, vars, at, refs);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in tys.tys_of(ts).to_vec() {
                    self.implied_edges(e, vars, at, refs);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.implied_edges(e, vars, at, refs),
            TyKind::Closure(_, args) => {
                for e in closure_fields(tys, args) {
                    self.implied_edges(e, vars, at, refs);
                }
            }
            _ => {}
        }
    }
}

/// True for a bare slice or `str` type: as a local's type it is a fat
/// pointer that borrows its base (see `Builder::local_slots`).
fn fat_local(tys: &impl TyIntern, t: Ty) -> bool {
    matches!(tys.kind(t), TyKind::Slice(_) | TyKind::Str)
}

/// The builtins that borrow into their receiver (or move elements out of
/// it) and return nothing of their other arguments, storing nothing
/// either (see `Builder::call_receiver`).
fn receiver_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(
        b,
        B::VecGet
            | B::VecFirst
            | B::VecLast
            | B::VecGetMut
            | B::VecFirstMut
            | B::VecLastMut
            | B::VecAsSlice
            | B::VecAsMutSlice
            | B::StringAsStr
            | B::StrTrim
            | B::StrTrimStart
            | B::StrTrimEnd
            | B::StrStripPrefix
            | B::StrStripSuffix
            | B::IterIter
            | B::IterIterMut
            | B::VecPop
            | B::VecRemove
            | B::VecSwapRemove
            | B::VecSplitOff
    )
}

/// The builtin iterator calls whose result is an item (or a collection
/// of items): their regions come from the iterator's sources.
/// The `core::fmt` builtins whose result borrows from the receiver
/// alone (a builder, or `&mut Self` of one).
fn fmt_builder_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(
        b,
        B::FmtDebugStruct
            | B::FmtDebugTuple
            | B::FmtDebugList
            | B::FmtDebugSet
            | B::FmtDebugMap
            | B::DsField
            | B::DtField
            | B::DlEntry
            | B::DmEntry
            | B::DmKey
            | B::DmValue
    )
}

fn item_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(
        b,
        B::IterNext | B::IterNth | B::IterFind | B::IterFindMap | B::IterLast | B::IterMin | B::IterMax | B::IterMinByKey | B::IterMaxByKey | B::IterCollect
    )
}

/// True when a type holds a `&mut` reference somewhere.
fn has_mut_ref(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(_, m, inner) => m.is_mut() || has_mut_ref(tys, inner),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| has_mut_ref(tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) => has_mut_ref(tys, e),
        TyKind::Adt(_, a) | TyKind::Closure(_, a) => tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_mut_ref(tys, e))),
        _ => false,
    }
}

impl Builder<'_, '_, '_> {
    /// Solves the constraints: strongly connected components of the
    /// outlives graph, then per component (sinks first) the locals,
    /// drop-live locals, and universals it reaches.
    pub fn solve(self) -> Solution {
        let nv = self.owner.len();
        let nl = self.body.locals.len();
        let wn = nl.div_ceil(64).max(1);
        // CSR adjacency.
        let mut start = vec![0u32; nv + 1];
        for &(a, _) in &self.edges {
            start[a as usize + 1] += 1;
        }
        for i in 0..nv {
            start[i + 1] += start[i];
        }
        let mut adj = vec![0u32; self.edges.len()];
        let mut fill = start.clone();
        for &(a, b) in &self.edges {
            adj[fill[a as usize] as usize] = b;
            fill[a as usize] += 1;
        }
        let (scc, n_scc) = tarjan(nv, &start, &adj);
        // Components in emission order are sinks first; members by component.
        let nu = self.own.n_univ as usize + 1;
        let wu = nu.div_ceil(64).max(1);
        let mut use_l = vec![0u64; n_scc * wn];
        let mut drop_l = vec![0u64; n_scc * wn];
        let mut univ = vec![0u64; n_scc * wu];
        let mut ret = vec![false; n_scc];
        let mut members: Vec<Vec<u32>> = vec![Vec::new(); n_scc];
        for v in 0..nv {
            members[scc[v] as usize].push(v as u32);
        }
        for c in 0..n_scc {
            for &v in &members[c] {
                let v = v as usize;
                if v < nu {
                    univ[c * wu + v / 64] |= 1 << (v % 64);
                }
                let o = self.owner[v];
                if o > 0 {
                    let l = (o - 1) as usize;
                    use_l[c * wn + l / 64] |= 1 << (l % 64);
                    if self.drop_slot[v] {
                        drop_l[c * wn + l / 64] |= 1 << (l % 64);
                    }
                    if l == 0 {
                        ret[c] = true;
                    }
                }
                for k in start[v]..start[v + 1] {
                    let d = scc[adj[k as usize] as usize] as usize;
                    if d != c {
                        for w in 0..wn {
                            use_l[c * wn + w] |= use_l[d * wn + w];
                            drop_l[c * wn + w] |= drop_l[d * wn + w];
                        }
                        for w in 0..wu {
                            univ[c * wu + w] |= univ[d * wu + w];
                        }
                        ret[c] |= ret[d];
                    }
                }
            }
        }
        let n_loans = self.loan_var.len();
        let mut sol = Solution {
            wn,
            use_locals: vec![0; n_loans * wn],
            drop_locals: vec![0; n_loans * wn],
            univ: vec![false; n_loans],
            to_ret: vec![false; n_loans],
            drop_live: vec![false; nl],
            errs: self.errs.clone(),
        };
        for (i, &lv) in self.loan_var.iter().enumerate() {
            let c = scc[lv as usize] as usize;
            sol.use_locals[i * wn..(i + 1) * wn].copy_from_slice(&use_l[c * wn..(c + 1) * wn]);
            sol.drop_locals[i * wn..(i + 1) * wn].copy_from_slice(&drop_l[c * wn..(c + 1) * wn]);
            sol.univ[i] = univ[c * wu..(c + 1) * wu].iter().any(|&w| w != 0);
            sol.to_ret[i] = ret[c];
        }
        for v in 0..nv {
            if self.drop_slot[v] && self.owner[v] > 0 {
                sol.drop_live[(self.owner[v] - 1) as usize] = true;
            }
        }
        if self.own.check {
            let known = self.own.known();
            let mut reported: Vec<(usize, usize)> = Vec::new();
            for u in 1..nu {
                let c = scc[u] as usize;
                for v in bit_iter(&univ[c * wu..(c + 1) * wu]) {
                    if v == u || v >= nu || known[u * nu + v] || reported.contains(&(u, v)) {
                        continue;
                    }
                    reported.push((u, v));
                    let span = self.path_span(u as u32, v as u32, &start, &adj);
                    let (a, b) = (&self.own.names[u], &self.own.names[v]);
                    sol.errs.push(Diag::new(
                        "L0733",
                        span,
                        format!("lifetime may not live long enough: {a} must outlive {b}"),
                        "Return or store data that borrows from the right parameter, or declare the relation (`'a: 'b`).",
                    ));
                }
            }
        }
        sol
    }

    /// The span of the statement whose constraint completes the path from
    /// `from` to `to`, for an error at the right place.
    fn path_span(&self, from: u32, to: u32, start: &[u32], adj: &[u32]) -> Span {
        let nv = self.owner.len();
        let mut parent: Vec<u32> = vec![u32::MAX; nv];
        parent[from as usize] = from;
        let mut queue = std::collections::VecDeque::from([from]);
        while let Some(v) = queue.pop_front() {
            if v == to {
                break;
            }
            for k in start[v as usize]..start[v as usize + 1] {
                let w = adj[k as usize];
                if parent[w as usize] == u32::MAX {
                    parent[w as usize] = v;
                    queue.push_back(w);
                }
            }
        }
        // Walk back from `to`; the last edge with a real span wins.
        let mut v = to;
        let mut best = Span::default();
        while parent[v as usize] != u32::MAX && parent[v as usize] != v {
            let u = parent[v as usize];
            if let Some(i) = self.edges.iter().position(|&e| e == (u, v))
                && self.edge_span[i] != Span::default()
                && best == Span::default()
            {
                best = self.edge_span[i];
            }
            v = u;
        }
        if best == Span::default() { self.p.fn_info(self.body.fn_id).def.name_span } else { best }
    }
}

/// Tarjan's strongly connected components, iteratively. Returns the
/// component of each node, numbered in completion order (sinks first),
/// and the component count.
fn tarjan(n: usize, start: &[u32], adj: &[u32]) -> (Vec<u32>, usize) {
    const NONE: u32 = u32::MAX;
    let mut index = vec![NONE; n];
    let mut low = vec![0u32; n];
    let mut on_stack = vec![false; n];
    let mut comp = vec![NONE; n];
    let mut stack: Vec<u32> = Vec::new();
    let mut next = 0u32;
    let mut n_comp = 0u32;
    // (node, next edge offset)
    let mut work: Vec<(u32, u32)> = Vec::new();
    for root in 0..n as u32 {
        if index[root as usize] != NONE {
            continue;
        }
        work.push((root, start[root as usize]));
        index[root as usize] = next;
        low[root as usize] = next;
        next += 1;
        stack.push(root);
        on_stack[root as usize] = true;
        while let Some(&mut (v, ref mut k)) = work.last_mut() {
            if *k < start[v as usize + 1] {
                let w = adj[*k as usize];
                *k += 1;
                if index[w as usize] == NONE {
                    index[w as usize] = next;
                    low[w as usize] = next;
                    next += 1;
                    stack.push(w);
                    on_stack[w as usize] = true;
                    work.push((w, start[w as usize]));
                } else if on_stack[w as usize] {
                    low[v as usize] = low[v as usize].min(index[w as usize]);
                }
            } else {
                work.pop();
                if let Some(&(u, _)) = work.last() {
                    low[u as usize] = low[u as usize].min(low[v as usize]);
                }
                if low[v as usize] == index[v as usize] {
                    loop {
                        let w = stack.pop().unwrap();
                        on_stack[w as usize] = false;
                        comp[w as usize] = n_comp;
                        if w == v {
                            break;
                        }
                    }
                    n_comp += 1;
                }
            }
        }
    }
    (comp, n_comp as usize)
}

/// The trait method an impl method implements, for a fn of a trait impl
/// (or an instance of one); None for inherent methods and plain fns.
pub fn impl_trait_method(p: &Program, f: LocalDefId) -> Option<DefId> {
    let src = p.gx.instances.get(&f).and_then(|i| i.template_local).unwrap_or(f);
    let impl_def = p.defs.parent_of(p.def_id(src))?;
    let (_, rec) = p.gx.index.by_def(impl_def)?;
    p.gx.index.trait_record(rec.trait_def)?.method_by_name(p.fn_info(src).name)
}

/// The trait-contract check of an impl method's regions (W-BORROW, rustc
/// compare_impl_method): the trait's signature must be a subtype of the
/// impl's for every choice of the trait's lifetimes. The trait's
/// universals are placeholders, the impl's are free; `trait param <: impl
/// param` and `impl ret <: trait ret` give outlives edges, and a
/// placeholder that must then outlive another (or `'static`) without a
/// trait fact or implied bound is L0734. The impl may promise more (a
/// `'static` result where the trait borrows), never less.
pub(super) fn impl_contract(p: &Program, f: LocalDefId) -> Option<Diag> {
    let own = p.regions.fns.get(&f)?;
    let info = p.fn_info(f);
    let tmeth = impl_trait_method(p, f)?;
    let tsig = p.regions.trait_methods.get(&tmeth)?;
    if tsig.params.len() != own.params.len() {
        return None;
    }
    let nt = tsig.n_univ as usize;
    let n = 1 + nt + own.n_univ as usize;
    let mut cx = Contract { p, nt, edges: Vec::new() };
    for (&t, &i) in tsig.params.iter().zip(&own.params) {
        cx.walk(t, i, Variance::Co, true);
    }
    cx.walk(own.ret, tsig.ret, Variance::Co, false);
    // Known relations among the trait's lifetimes: its facts and the
    // implied bounds of its signature types, closed transitively.
    let mut known = vec![false; (nt + 1) * (nt + 1)];
    for a in 0..=nt {
        known[a * (nt + 1) + a] = true;
        known[a] = true;
    }
    let add_known = |a: Region, b: Region, known: &mut Vec<bool>| {
        let idx = |r: Region| match r {
            Region::Static => Some(0),
            Region::Param(k) if (k as usize) < nt => Some(1 + k as usize),
            _ => None,
        };
        if let (Some(x), Some(y)) = (idx(a), idx(b)) {
            known[x * (nt + 1) + y] = true;
        }
    };
    for &(a, b) in &tsig.facts {
        add_known(a, b, &mut known);
    }
    for &t in tsig.params.iter().chain(std::iter::once(&tsig.ret)) {
        let mut facts = Vec::new();
        implied_regioned(&p.tys, t, &mut Vec::new(), &mut facts);
        for (a, b) in facts {
            add_known(a, b, &mut known);
        }
    }
    let w = nt + 1;
    for k in 0..w {
        for a in 0..w {
            if known[a * w + k] {
                for b in 0..w {
                    if known[k * w + b] {
                        known[a * w + b] = true;
                    }
                }
            }
        }
    }
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); n];
    for &(a, b) in &cx.edges {
        adj[a].push(b);
    }
    for pl in 1..=nt {
        let mut seen = vec![false; n];
        let mut stack = vec![pl];
        seen[pl] = true;
        while let Some(x) = stack.pop() {
            for &y in &adj[x] {
                if !seen[y] {
                    seen[y] = true;
                    stack.push(y);
                }
            }
        }
        for q in 0..=nt {
            if q != pl && seen[q] && !known[pl * w + q] {
                return Some(Diag::new(
                    "L0734",
                    info.def.name_span,
                    format!("lifetime mismatch: method `{}` does not fit the lifetimes of the trait's signature", p.display_name(info.name)),
                    "Match the trait method's signature: return at least what it promises, and take at least what it accepts.",
                ));
            }
        }
    }
    None
}

/// The edge walk of `impl_contract` over two regioned types.
struct Contract<'p, 'a> {
    p: &'p Program<'a>,
    /// Trait universal count: node 0 is `'static`, `1..=nt` the trait's,
    /// the impl's after them.
    nt: usize,
    edges: Vec<(usize, usize)>,
}

impl Contract<'_, '_> {
    /// The node of region `r` on the trait side or the impl side.
    fn node(&self, r: Region, trait_side: bool) -> Option<usize> {
        match r {
            Region::Static => Some(0),
            Region::Param(k) if trait_side => Some(1 + k as usize),
            Region::Param(k) => Some(1 + self.nt + k as usize),
            _ => None,
        }
    }

    /// Edges for `a <: b` at variance `v`; `a_trait` says which side `a`
    /// comes from (the other side is `b`).
    fn walk(&mut self, a: Ty, b: Ty, v: Variance, a_trait: bool) {
        let tys = &self.p.tys;
        match (tys.kind(a), tys.kind(b)) {
            (TyKind::Ref(ra, ma, ia), TyKind::Ref(rb, mb, ib)) if ma == mb => {
                self.slot(ra, rb, v, a_trait);
                let iv = if ma.is_mut() { Variance::Inv } else { Variance::Co };
                self.walk(ia, ib, v.then(iv), a_trait);
            }
            (TyKind::Adt(da, xa), TyKind::Adt(db, xb)) if da == db => {
                let (xs, ys) = (tys.args(xa).to_vec(), tys.args(xb).to_vec());
                let (mut k, mut j) = (0usize, 0usize);
                for (x, y) in xs.into_iter().zip(ys) {
                    match (x, y) {
                        (GenericArg::Lifetime(rx), GenericArg::Lifetime(ry)) => {
                            let rv = self.p.regions.adts(self.p).region_modes(da, k).0;
                            self.slot(rx, ry, v.then(rv), a_trait);
                            k += 1;
                        }
                        (GenericArg::Ty(x), GenericArg::Ty(y)) => {
                            let (pv, _) = self.p.regions.adts(self.p).arg_modes(self.p, da, j);
                            self.walk(x, y, v.then(pv), a_trait);
                            j += 1;
                        }
                        _ => j += 1,
                    }
                }
            }
            (TyKind::Tuple(x), TyKind::Tuple(y)) => {
                for (x, y) in tys.tys_of(x).to_vec().into_iter().zip(tys.tys_of(y).to_vec()) {
                    self.walk(x, y, v, a_trait);
                }
            }
            (TyKind::Array(x, _), TyKind::Array(y, _)) | (TyKind::Slice(x), TyKind::Slice(y)) => self.walk(x, y, v, a_trait),
            _ => {}
        }
    }

    fn slot(&mut self, ra: Region, rb: Region, v: Variance, a_trait: bool) {
        let (Some(x), Some(y)) = (self.node(ra, a_trait), self.node(rb, !a_trait)) else { return };
        match v {
            Variance::Co => self.edges.push((x, y)),
            Variance::Contra => self.edges.push((y, x)),
            Variance::Inv => {
                self.edges.push((x, y));
                self.edges.push((y, x));
            }
            Variance::Bi => {}
        }
        // `'static` outlives everything: no edges out of it are needed.
        self.edges.retain(|&(a, _)| a != 0);
    }
}

/// Implied outlives facts of a regioned type: every region inside a
/// reference outlives the reference's own region.
fn implied_regioned(tys: &impl TyIntern, t: Ty, outer: &mut Vec<Region>, out: &mut Vec<(Region, Region)>) {
    let note = |r: Region, outer: &Vec<Region>, out: &mut Vec<(Region, Region)>| {
        for &o in outer {
            out.push((r, o));
        }
    };
    match tys.kind(t) {
        TyKind::Ref(r, _, inner) => {
            note(r, outer, out);
            outer.push(r);
            implied_regioned(tys, inner, outer, out);
            outer.pop();
        }
        TyKind::Adt(_, args) => {
            for g in tys.args(args).to_vec() {
                match g {
                    GenericArg::Lifetime(r) => note(r, outer, out),
                    GenericArg::Ty(e) => implied_regioned(tys, e, outer, out),
                    GenericArg::Const(_) => {}
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                implied_regioned(tys, e, outer, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => implied_regioned(tys, e, outer, out),
        _ => {}
    }
}

/// The fn item coercion check (W-BORROW, ARCH 5.5): a fn pointer type is
/// generic over its lifetimes, so a fn item with an early-bound lifetime
/// (named in a bound, or in no input) does not coerce to one (rustc E0308).
pub(super) fn fn_item_coercions(p: &Program, body: &Body) -> Vec<Diag> {
    let mut out = Vec::new();
    for b in &body.blocks {
        for s in &b.stmts {
            let StmtKind::Assign(_, Rvalue::FnValue(f, ty)) = &s.kind else { continue };
            if !matches!(body.tys.kind(*ty), TyKind::FnPtr(_)) {
                continue;
            }
            let sig = p.regions.fns.get(f).or_else(|| p.gx.instances.get(f).and_then(|i| p.regions.fns.get(&i.template_local?)));
            if sig.is_some_and(|s| s.early.iter().any(|&e| e)) {
                out.push(Diag::new(
                    "L0110",
                    s.span,
                    format!("`{}` has an early-bound lifetime, so it cannot become a fn pointer that is generic over it", p.display_name(p.fn_info(*f).name)),
                    "Call the fn directly, or remove the bound that makes its lifetime early-bound.",
                ));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::{Variance, tarjan};

    /// Components come out sinks first, and a cycle is one component.
    #[test]
    fn tarjan_orders_sinks_first() {
        // 0 -> 1 -> 2 -> 1, 0 -> 3
        let edges: Vec<(u32, u32)> = vec![(0, 1), (1, 2), (2, 1), (0, 3)];
        let n = 4;
        let mut start = vec![0u32; n + 1];
        for &(a, _) in &edges {
            start[a as usize + 1] += 1;
        }
        for i in 0..n {
            start[i + 1] += start[i];
        }
        let mut adj = vec![0u32; edges.len()];
        let mut fill = start.clone();
        for &(a, b) in &edges {
            adj[fill[a as usize] as usize] = b;
            fill[a as usize] += 1;
        }
        let (comp, nc) = tarjan(n, &start, &adj);
        assert_eq!(nc, 3);
        assert_eq!(comp[1], comp[2], "the cycle is one component");
        assert!(comp[0] > comp[1] && comp[0] > comp[3], "the source completes after its successors");
    }

    /// The variance algebra matches Rust's composition rules.
    #[test]
    fn variance_compose_and_join() {
        use Variance::*;
        assert_eq!(Co.then(Contra), Contra);
        assert_eq!(Contra.then(Contra), Co);
        assert_eq!(Contra.then(Inv), Inv);
        assert_eq!(Bi.then(Inv), Bi);
        assert_eq!(Co.join(Contra), Inv);
        assert_eq!(Bi.join(Contra), Contra);
        assert_eq!(Co.join(Co), Co);
    }
}
