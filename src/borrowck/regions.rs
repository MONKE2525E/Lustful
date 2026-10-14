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
    /// The `Fn*(A..) -> R` bounds on the type params of the fn, its impl,
    /// or its trait, with regions (see `FnBound`).
    pub fn_bounds: Vec<FnBound>,
    /// The `T: Tr<'a, ..>` bounds on type params (the fn's, its impl's,
    /// its trait's, and `impl Tr<'a>` arguments) for traits with lifetime
    /// params, with the written lifetime args (see `TraitLts`).
    pub trait_bounds: Vec<TraitLts>,
}

/// A bound `T: Tr<'a, ..>` on type param `param` for a trait with lifetime
/// params: the lifetime args as written (`Region::Param` of the fn's
/// universals, or `Region::Static`). A call of a `Tr` method through `T`
/// instantiates the trait's lifetimes with them, and a call that binds
/// `T` replays the selected impl's lifetimes against them.
#[derive(Clone, Debug)]
pub struct TraitLts {
    pub param: u32,
    pub trait_def: DefId,
    pub lifetimes: Vec<Region>,
}

/// One impl of a trait with lifetime params (W-BORROW): its regioned Self
/// type and the lifetime args of its trait ref, over the impl's lifetimes
/// (`impl Tr<'static> for S`: `[Static]`; `impl<'d> Tr<'d> for S<'d>`:
/// `[Param(0)]`, matched through Self).
#[derive(Clone, Debug)]
pub struct ImplHead {
    pub self_ty: Ty,
    pub trait_lifetimes: Vec<Region>,
    /// The impl's own bounds on its type params for traits with lifetime
    /// params (`impl<'a, T: Tr<'a>> Tr<'a> for Wrap<T>`), replayed
    /// through the parts of Self they name (`trait_lts_for`).
    pub where_lts: Vec<TraitLts>,
}

/// A `F: Fn*(A..) -> R` bound on a type param, with regions: a lifetime
/// the bound writes as itself (the fn's universal or `'static`), an elided
/// one `Region::Bound` (higher-ranked by the sugar). Closures passed for
/// `F` (`link_bound_closure`) and calls through `F` in the body
/// (`call_fn_bound`) follow it.
#[derive(Clone, Debug)]
pub struct FnBound {
    /// The type param's index.
    pub param: u32,
    pub inputs: Vec<Ty>,
    /// The written output type (`-> R`); `None` for `()`.
    pub output: Option<Ty>,
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
    /// The headers of impls of traits with lifetime params, by impl def.
    pub impl_heads: FxMap<DefId, ImplHead>,
    /// Declared outlives facts between an Adt's lifetime params
    /// (`struct H<'a, 'b: 'a>`), by def: `(x, y)` is `'x: 'y` by param
    /// index, `y == STATIC_FACT` is `'static`. Every use of the type must
    /// meet them (well-formedness), and a signature that names the type
    /// may assume them (implied bounds).
    pub adt_facts: FxMap<DefId, Vec<(u32, u32)>>,
    adts: std::sync::OnceLock<AdtTables>,
    /// The trait method of each trait method stub (the reverse of
    /// `GenTables::trait_method_stubs`), built on first use.
    stub_methods: std::sync::OnceLock<FxMap<LocalDefId, DefId>>,
    /// Per trait, its impls with `X: 'static` where-clauses (the impl and
    /// those params), built on first use (`Builder::impl_static_edges`).
    static_impls: std::sync::OnceLock<FxMap<DefId, Vec<(crate::traits::index::ImplId, Vec<u32>)>>>,
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

    /// The impls of `trait_def` with `X: 'static` where-clauses.
    fn static_impls(&self, p: &Program, trait_def: DefId) -> &[(crate::traits::index::ImplId, Vec<u32>)] {
        let all = self.static_impls.get_or_init(|| {
            let mut m: FxMap<DefId, Vec<(crate::traits::index::ImplId, Vec<u32>)>> = FxMap::default();
            for (id, rec) in p.gx.index.all_impls() {
                let ks: Vec<u32> = rec
                    .generics
                    .predicates
                    .iter()
                    .filter_map(|pr| match pr {
                        Predicate::TypeOutlives(x, Region::Static) => match p.tys.kind(*x) {
                            TyKind::Param(k) => Some(k.0),
                            _ => None,
                        },
                        _ => None,
                    })
                    .collect();
                if !ks.is_empty() {
                    m.entry(rec.trait_def).or_default().push((id, ks));
                }
            }
            m
        });
        all.get(&trait_def).map_or(&[], |v| v.as_slice())
    }

    /// The trait method a stub fn stands for (a stub has its own def).
    /// The region signature body `f` is checked against: its own, its
    /// template's (an instance), or its trait method's (a trait default
    /// body: a template fn with the trait method's def, or its stub).
    pub fn body_sig(&self, p: &Program, f: LocalDefId) -> Option<&RegionSig> {
        let of = |g: LocalDefId| {
            self.fns
                .get(&g)
                .or_else(|| p.fn_defs.get(g.0 as usize).and_then(|d| self.trait_methods.get(d)))
                .or_else(|| self.stub_method(p, g).and_then(|m| self.trait_methods.get(&m)))
        };
        of(f).or_else(|| of(p.gx.instances.get(&f)?.template_local?))
    }

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
                // `PhantomData<T>` acts as a field of type T (std source,
                // W-STD-C): covariant, and owned for drop.
                if p.is_phantom_adt(id) {
                    var.iter_mut().for_each(|x| *x = x.join(Variance::Co));
                    drop.iter_mut().for_each(|x| *x = x.join(DropMode::Owned));
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
            // A dyn's object lifetime: covariant (`dyn Tr + 'long` is a
            // `dyn Tr + 'short`), drop-visible (an unknown destructor).
            TyKind::Dyn(_, r) => note(r, v.then(Variance::Co), if m == DropMode::None { DropMode::None } else { DropMode::All }, var, drop),
            _ => {
                // A region inside anything else (fn pointers, closures)
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
            // `mpsc::Iter<'a, T>` holds `&'a Receiver<T>` (invariant in
            // `T`); `mpsc::IntoIter<T>` owns the receiver, whose `Drop`
            // reads `T` (W-THREADS).
            Some(BuiltinTy::Iter(IterKind::RecvIter | IterKind::RecvTryIter)) => return (Variance::Inv, DropMode::None),
            Some(BuiltinTy::Iter(IterKind::RecvIntoIter)) => return (Variance::Inv, DropMode::All),
            // `slice::IterMut<'a, T>` holds `&'a mut [T]`: invariant in `T`.
            Some(BuiltinTy::Iter(IterKind::SliceIterMut)) => return (Variance::Inv, DropMode::None),
            Some(BuiltinTy::Iter(IterKind::SliceIter)) => return (Variance::Co, DropMode::None),
            // `hash_map::IterMut<'a, K, V>` and `ValuesMut` hold `&'a mut V`
            // (W-STD-B): invariant in V, covariant in K, no drop.
            Some(BuiltinTy::Iter(IterKind::MapIterMut | IterKind::MapValuesMut)) => {
                return if j == 1 { (Variance::Inv, DropMode::None) } else { (Variance::Co, DropMode::None) };
            }
            // The hashed collections (W-STD-B): HashMap and HashSet are
            // covariant and own their elements (hashbrown's RawTable);
            // `BuildHasherDefault<H>` holds `PhantomData<fn() -> H>`; an
            // Entry holds `&'a mut HashMap<K, V>`: invariant, and it owns
            // only its probe key.
            Some(BuiltinTy::Hash(k)) => {
                use crate::ty::hash::HashTy;
                return match k {
                    HashTy::HashMap | HashTy::HashSet => (Variance::Co, DropMode::Owned),
                    HashTy::BuildHasherDefault => (Variance::Co, DropMode::None),
                    HashTy::Entry => (Variance::Inv, if j == 0 { DropMode::Owned } else { DropMode::None }),
                    HashTy::RandomState | HashTy::DefaultHasher => (Variance::Inv, DropMode::Owned),
                    // The C forms of the iterators are never types (no def).
                    HashTy::IterPairs | HashTy::IterKeys | HashTy::IterValues | HashTy::IntoPairs | HashTy::IntoKeys | HashTy::IntoValues => {
                        (Variance::Inv, DropMode::All)
                    }
                };
            }
            // Owning containers and the other iterators: covariant, their
            // drop may reach the elements. Exhaustive on purpose: a new
            // builtin picks its variance here (a `Cell`-like type is
            // invariant; covariance there would be unsound).
            Some(
                BuiltinTy::String
                | BuiltinTy::Vec
                | BuiltinTy::Option
                | BuiltinTy::Result
                | BuiltinTy::Boxed
                | BuiltinTy::Rc
                | BuiltinTy::Chars
                | BuiltinTy::Args
                | BuiltinTy::Iter(_)
                | BuiltinTy::Weak,
            ) => return (Variance::Co, DropMode::Owned),
            // `fmt` types (W-STD-B) and `ExitCode` take no type args.
            Some(BuiltinTy::Fmt(_) | BuiltinTy::ExitCode) => return (Variance::Inv, DropMode::Owned),
            // `LocalKey<T>` holds an `fn` that returns `*const T`:
            // covariant, and it never drops a `T`; `AccessError` takes no
            // type args (W-TLS).
            Some(BuiltinTy::LocalKey) => return (Variance::Co, DropMode::None),
            Some(BuiltinTy::AccessError) => return (Variance::Inv, DropMode::Owned),
            // `RefMut<'b, T>` acts as `&'b mut T`, `Ref<'b, T>` as `&'b T`;
            // neither drops the `T` (W-STD-A).
            Some(BuiltinTy::RefMutGuard) => return (Variance::Inv, DropMode::None),
            Some(BuiltinTy::RefGuard) => return (Variance::Co, DropMode::None),
            // Interior mutability: `Cell<T>` and `RefCell<T>` are invariant.
            Some(BuiltinTy::Cell | BuiltinTy::RefCell) => return (Variance::Inv, DropMode::Owned),
            // `Arc<T>` and `sync::Weak<T>` are like `Rc` and `rc::Weak`;
            // the atomics take no type args (W-THREADS).
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::Arc | crate::ty::sync::SyncTy::ArcWeak)) => return (Variance::Co, DropMode::Owned),
            // `MutexGuard` and `RwLockWriteGuard` act as `&'b mut T`,
            // `RwLockReadGuard` as `&'b T` (its `NonNull<T>` is
            // covariant); none drops the `T`. `PoisonError<T>` owns its
            // `T`. The locks are invariant (`UnsafeCell`).
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::MutexGuard | crate::ty::sync::SyncTy::RwLockWriteGuard)) => return (Variance::Inv, DropMode::None),
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::RwLockReadGuard)) => return (Variance::Co, DropMode::None),
            Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::PoisonError)) => return (Variance::Co, DropMode::Owned),
            // The channel ends and join handles have std `Drop` impls with
            // no `#[may_dangle]`: their drop may read every `T` region.
            Some(BuiltinTy::Sync(
                crate::ty::sync::SyncTy::Sender
                | crate::ty::sync::SyncTy::SyncSender
                | crate::ty::sync::SyncTy::Receiver
                | crate::ty::sync::SyncTy::JoinHandle
                | crate::ty::sync::SyncTy::ScopedJoinHandle,
            )) => return (Variance::Inv, DropMode::All),
            // `ScopedJoinHandle<'scope, T>` owns its `T` (an `Arc` of a
            // packet with an `UnsafeCell`: invariant).
            Some(BuiltinTy::Sync(_)) => return (Variance::Inv, DropMode::Owned),
            None => {}
        }
        let v = self.variance.get(&def).and_then(|v| v.get(j)).copied().unwrap_or(Variance::Inv);
        let m = self.drop.get(&def).and_then(|d| d.get(j)).copied().unwrap_or(DropMode::All);
        (v, m)
    }
}

/// The number of region params an Adt type carries ahead of its type args:
/// a user Adt's declared lifetimes, or one for the builtin borrowing
/// iterators (`Chars`, `slice::Iter`, `slice::IterMut`) and the `RefCell`
/// guards (`Ref`, `RefMut`), whose erased types drop the lifetime.
fn adt_regions(p: &Program, tys: &impl TyIntern, t: Ty) -> u32 {
    use crate::ty::iter::IterKind;
    match tys.builtin_of(t) {
        Some(
            BuiltinTy::Chars
            | BuiltinTy::Iter(
                IterKind::SliceIter
                | IterKind::SliceIterMut
                | IterKind::RecvIter
                | IterKind::RecvTryIter
                | IterKind::Windows
                | IterKind::CharIndices
                | IterKind::VecDrain
                | IterKind::StringDrain,
            )
            | BuiltinTy::Iter(IterKind::StrSplit)
            | BuiltinTy::RefGuard
            | BuiltinTy::RefMutGuard,
        ) => return 1,
        // The borrowing hash iterators hold `&'a` (or `&'a mut`) of their table (W-STD-B).
        Some(BuiltinTy::Iter(k)) if k.is_hash() && !k.is_hash_owning() => return 1,
        // A Debug builder holds `&mut Formatter`, a map Entry `&mut` its
        // map (W-STD-B).
        Some(BuiltinTy::Fmt(k)) if k.is_builder() => return 1,
        // The lock guards borrow their lock (W-THREADS).
        Some(BuiltinTy::Sync(k)) if k.regions() > 0 => return k.regions(),
        Some(BuiltinTy::Hash(crate::ty::hash::HashTy::Entry)) => return 1,
        Some(_) => return 0,
        None => {}
    }
    match tys.kind(t) {
        TyKind::Adt(def, _) => p.gx.adt_lifetimes.get(&def).map_or(0, |v| v.len() as u32),
        _ => 0,
    }
}

/// The variance of a builtin type's region params: covariant, but for
/// `thread::Scope<'scope, 'env>`, invariant in both (std's
/// `PhantomData<&'scope mut &'scope ()>`), which pins a scoped spawn's
/// `'scope` to the scope closure's whole body.
fn builtin_region_variance(tys: &impl TyIntern, t: Ty) -> Variance {
    if crate::ty::sync::sync_kind(tys, t) == Some(crate::ty::sync::SyncTy::Scope) { Variance::Inv } else { Variance::Co }
}

/// True when a drop of a value of type `t` drops a `RefCell` or lock
/// guard, whose own drop uses its borrow (Rust's `BorrowRef` is `Drop`),
/// or a std type whose `Drop` reads its `T` (a channel end, a join
/// handle: no `#[may_dangle]`; W-THREADS).
fn drops_guard(tys: &impl TyIntern, t: Ty) -> bool {
    use crate::ty::sync::SyncTy as S;
    match tys.kind(t) {
        TyKind::Adt(_, args) => {
            tys.guard_elem(t).is_some()
                || matches!(crate::ty::sync::sync_kind(tys, t), Some(S::Sender | S::SyncSender | S::Receiver | S::JoinHandle | S::ScopedJoinHandle))
                || tys.builtin_of(t) == Some(BuiltinTy::Iter(crate::ty::iter::IterKind::RecvIntoIter))
                || (!matches!(tys.builtin_of(t), Some(BuiltinTy::Weak | BuiltinTy::Sync(crate::ty::sync::SyncTy::ArcWeak)))
                    && tys.args(args).iter().any(|g| g.as_ty().is_some_and(|e| drops_guard(tys, e))))
        }
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| drops_guard(tys, e)),
        TyKind::Array(e, _) => drops_guard(tys, e),
        TyKind::Closure(_, args) => closure_fields(tys, args).into_iter().any(|e| drops_guard(tys, e)),
        _ => false,
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
            // The object lifetime (`dyn Tr + 'o`).
            TyKind::Dyn(..) => 1,
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
            // A trait bounded by `'static` makes its object lifetime
            // `'static` whatever the default would be (rustc, ARCH 2.8).
            TyKind::Dyn(_, r) => out.push(if crate::check::object::dyn_is_static(self.p, self.tys, t) { Region::Static } else { r }),
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
                    let rv = if self.tys.builtin_of(t).is_some() { builtin_region_variance(self.tys, t) } else { self.p.regions.adts(self.p).region_modes(def, k as usize).0 };
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
            TyKind::Dyn(..) => {
                f(at, v.then(Variance::Co));
                at + 1
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
                    // A guard's drop gives its borrow back, so it uses it.
                    let rm = if self.tys.guard_elem(t).is_some() {
                        DropMode::All
                    } else if self.tys.builtin_of(t).is_some() {
                        DropMode::None
                    } else {
                        self.p.regions.adts(self.p).region_modes(def, k as usize).1
                    };
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
            // An owned dyn's unknown destructor may use what it borrows.
            TyKind::Dyn(..) => {
                out[at as usize] = m != DropMode::None;
                at + 1
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
    /// In a closure body, by universal: the requirement end it stands for
    /// (`'static`, a captured slot, a free argument slot, an output slot).
    /// Relations among the first three are its creator's to prove
    /// (`closure_requirements`), not errors here; the env reference and
    /// higher-ranked argument slots are None.
    pub ends: Vec<Option<End>>,
}

/// One end of a closure requirement (`closure_requirements`): `'static`,
/// a captured slot (in the closure type's slot order), a free argument
/// slot (in `closure_arg_slots` order), or an output slot (only as the
/// longer-lived side's target: what the output may hold).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum End {
    Static,
    Cap(u32),
    Arg(u32),
    Out(u32),
}

/// What a callee's `Fn*` bound makes of one closure argument slot
/// (`bound_slots`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BoundSlot {
    /// The call's instantiation of a type param: free in the closure.
    Free,
    /// An elided lifetime the bound writes: higher-ranked.
    Hr,
    /// A lifetime the bound names: this var (`'static` is 0).
    Tie(u32),
}

/// The fn whose body holds `f`: `f` itself, or a closure's enclosing fn.
fn root_fn(p: &Program, f: LocalDefId) -> LocalDefId {
    let mut root = f;
    while let Some(e) = p.gx.closure_fns.get(&root).and_then(|d| p.gx.closures.get(d)) {
        root = e.parent;
    }
    root
}

/// True when a call in `body` may pass a type param with a regioned `Fn`
/// bound (the fn holding it has one) or a fn item to a generic fn, which
/// proves the callee's bound from its signature (`entail_bound`) even in
/// a body with no loans.
pub(super) fn may_entail_bounds(p: &Program, body: &Body) -> bool {
    p.regions.body_sig(p, root_fn(p, body.fn_id)).is_some_and(|s| !s.fn_bounds.is_empty())
        || body.blocks.iter().any(|b| b.stmts.iter().any(|s| matches!(s.kind, StmtKind::Assign(_, Rvalue::FnValue(..)))))
}

/// What a region of a `Fn` signature is when one signature proves
/// another (`match_fn_sides`): a fixed var of this body, a binder of the
/// signature (each elided input lifetime of `Fn` sugar is its own,
/// numbered in order, and an elided output is the one input's; a fn
/// item's late-bound lifetime is one wherever it is written), or a region
/// nothing ties (a type param's instantiation).
#[derive(Clone, Copy, PartialEq)]
enum Side {
    Tie(u32),
    Binder(u32),
    Free,
}

/// The sides of a source signature's regions in order (`Side`): `F`'s
/// bound over this body's universals, or a fn item's (`early`: its
/// early-bound lifetimes, fresh vars of this use).
struct FnSides {
    item: Option<Vec<bool>>,
    early: FxMap<u32, u32>,
    n: u32,
}

impl FnSides {
    fn new(item: Option<Vec<bool>>) -> Self {
        FnSides { item, early: FxMap::default(), n: 0 }
    }

    fn side(&mut self, b: &mut Builder<'_, '_, '_>, r: Region, out: bool) -> Side {
        match (r, &self.item) {
            (Region::Static, _) => Side::Tie(0),
            (Region::Param(k), None) => Side::Tie(k + 1),
            (Region::Param(k), Some(e)) if e.get(k as usize) == Some(&true) => Side::Tie(*self.early.entry(k).or_insert_with(|| b.fresh())),
            (Region::Param(k), Some(_)) => Side::Binder(k),
            (Region::Bound(_), None) if out => Side::Binder(0),
            (Region::Bound(_), None) => {
                self.n += 1;
                Side::Binder(self.n - 1)
            }
            _ => Side::Free,
        }
    }
}

/// The type params a type names (indices), in order, repeats included.
fn type_params_in(tys: &impl TyIntern, t: Ty, out: &mut Vec<u32>) {
    match tys.kind(t) {
        TyKind::Param(j) => out.push(j.0),
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => type_params_in(tys, e, out),
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                type_params_in(tys, e, out);
            }
        }
        TyKind::Adt(_, a) | TyKind::Projection(_, a) => {
            for g in tys.args(a).to_vec() {
                if let GenericArg::Ty(e) = g {
                    type_params_in(tys, e, out);
                }
            }
        }
        _ => {}
    }
}

/// The pairs of regions at the same places of two regioned types (a
/// callee's bound and the argument's signature, `entail_bound`); a type
/// param or projection on either side (an instantiation) pairs nothing.
/// False when the shapes differ.
fn region_pairs(tys: &impl TyIntern, a: Ty, b: Ty, out: &mut Vec<(Region, Region)>) -> bool {
    match (tys.kind(a), tys.kind(b)) {
        (TyKind::Param(_) | TyKind::Projection(..), _) | (_, TyKind::Param(_) | TyKind::Projection(..)) => true,
        (TyKind::Ref(ra, ma, ia), TyKind::Ref(rb, mb, ib)) if ma == mb => {
            out.push((ra, rb));
            region_pairs(tys, ia, ib, out)
        }
        (TyKind::Adt(da, xa), TyKind::Adt(db, xb)) if da == db => {
            let (xa, xb) = (tys.args(xa).to_vec(), tys.args(xb).to_vec());
            xa.len() == xb.len()
                && xa.into_iter().zip(xb).all(|(x, y)| match (x, y) {
                    (GenericArg::Lifetime(r), GenericArg::Lifetime(s)) => {
                        out.push((r, s));
                        true
                    }
                    (GenericArg::Ty(x), GenericArg::Ty(y)) => region_pairs(tys, x, y, out),
                    (GenericArg::Const(_), GenericArg::Const(_)) => true,
                    _ => false,
                })
        }
        (TyKind::Tuple(x), TyKind::Tuple(y)) => {
            let (x, y) = (tys.tys_of(x).to_vec(), tys.tys_of(y).to_vec());
            x.len() == y.len() && x.into_iter().zip(y).all(|(x, y)| region_pairs(tys, x, y, out))
        }
        (TyKind::Array(x, _), TyKind::Array(y, _)) | (TyKind::Slice(x), TyKind::Slice(y)) => region_pairs(tys, x, y, out),
        (TyKind::Dyn(_, r), TyKind::Dyn(_, s)) => {
            out.push((r, s));
            true
        }
        _ => {
            let (mut x, mut y) = (Vec::new(), Vec::new());
            regions_of(tys, a, &mut x);
            regions_of(tys, b, &mut y);
            x.is_empty() && y.is_empty()
        }
    }
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
        let mut own = OwnSig { n_univ: 0, slots: Vec::new(), facts: Vec::new(), names: vec!["'static".into()], check, closure, ends: Vec::new() };
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
        // An `impl Trait` return captures every input region (edition
        // 2024), and callers assume its value lives no longer than any of
        // them (`call_opaque`): each region of the returned value must
        // outlive one fresh universal that every other universal outlives
        // (W-CHECK-G3).
        // An `impl Trait + 'static` return: every region of the returned
        // value is `'static` instead.
        if opaque_static_ret(p, p.ret_view(body.fn_id)) && !own.slots.is_empty() {
            own.slots[0].fill(0);
        } else if crate::check::opaque::mentions_opaque(&p.tys, p.ret_view(body.fn_id), None) && !own.slots.is_empty() {
            let ret: Vec<Univ> = own.slots[0].clone();
            let n = own.n_univ;
            for &r in &ret {
                for u in 1..=n {
                    if !ret.contains(&u) {
                        own.facts.push((u, r));
                    }
                }
            }
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
            // The object lifetime the signature names (or its default;
            // `'static` for a trait bounded by `'static`).
            (TyKind::Dyn(_, rr), TyKind::Dyn(..)) => {
                let rr = if crate::check::object::dyn_is_static(sc.p, tys, e) { Region::Static } else { rr };
                let mut fresh = || {
                    self.n_univ += 1;
                    self.n_univ
                };
                let u = univ_of(rr, &mut fresh);
                while self.names.len() < self.n_univ as usize + 1 {
                    self.names.push("an anonymous lifetime".into());
                }
                out.push(u);
                true
            }
            _ => r == e && sc.slots(e) == 0,
        }
    }

    /// A closure body's universals: one per slot of its env (the env
    /// reference's region, then each captured region), of its output, and
    /// of its inputs. The facts are the closure contract (`closure_roles`):
    /// every source (captured, or a free argument slot) outlives every
    /// other sink and every output slot. Relations among the captured
    /// slots, the free argument slots, and `'static` are not errors here:
    /// the creator adds what the body needs of them (`ends`,
    /// `closure_requirements`). Higher-ranked argument slots take no part.
    fn closure_sig<T: TyIntern>(&mut self, p: &Program, body: &Body, sc: &mut SlotCx<'_, '_, '_, T>) {
        let free = p.gx.closure_fns.get(&body.fn_id).and_then(|d| p.gx.closures.get(d)).and_then(|c| c.free_args.clone());
        let fresh = |own: &mut OwnSig, name: &str| -> Univ {
            own.n_univ += 1;
            own.names.push(name.into());
            own.n_univ
        };
        let mut env_caps: Vec<Univ> = Vec::new();
        let mut roles: Vec<(bool, bool)> = Vec::new();
        for l in 0..=body.arg_count {
            let t = body.locals[l].ty;
            let n = sc.slots(t) as usize;
            let mut out = Vec::with_capacity(n);
            if l == 0 {
                // A return annotation's `'static` slots are `'static`.
                let mut named: Vec<Region> = Vec::new();
                let entry = p.gx.closure_fns.get(&body.fn_id).and_then(|d| p.gx.closures.get(d));
                let paired = entry
                    .and_then(|c| c.output_region)
                    .is_some_and(|r| regioned_slots(sc, r, t, &mut named) && named.len() == n);
                for k in 0..n {
                    match named.get(k) {
                        Some(Region::Static) if paired => out.push(0),
                        _ => out.push(fresh(self, "the closure's return lifetime")),
                    }
                }
            } else if l == 1 {
                let cl = match sc.tys.kind(t) {
                    TyKind::Ref(_, _, inner) => {
                        out.push(fresh(self, "the closure environment's lifetime"));
                        inner
                    }
                    _ => t,
                };
                if let TyKind::Closure(_, args) = sc.tys.kind(cl) {
                    closure_roles(sc, args, &mut roles);
                }
                while out.len() < n {
                    let u = fresh(self, "a lifetime the closure captures");
                    env_caps.push(u);
                    out.push(u);
                }
            } else {
                for _ in 0..n {
                    out.push(fresh(self, "a closure argument's lifetime"));
                }
            }
            self.slots.push(out);
        }
        // The contract: every source (a captured one, a free argument
        // slot) outlives every other sink (a captured one, a free argument
        // slot behind `&mut`, the output). Higher-ranked argument slots
        // take no part.
        let inputs: Vec<Ty> = (2..=body.arg_count).map(|l| body.locals[l].ty).collect();
        let entry = p.gx.closure_fns.get(&body.fn_id).and_then(|d| p.gx.closures.get(d));
        let arg_roles: Vec<Option<(bool, bool)>> = match entry.map(|c| closure_arg_slots(sc, c)) {
            Some(Ok(slots)) => slots.into_iter().map(|(r, _)| r).collect(),
            // Unpaired annotations are the creator's error; every slot is
            // higher-ranked here.
            _ => {
                let mut v = Vec::new();
                closure_arg_roles(sc, &inputs, free.as_deref(), &mut v);
                v
            }
        };
        let args: Vec<Univ> = self.slots.iter().skip(2).flatten().copied().collect();
        let mut cap_srcs: Vec<Univ> = Vec::new();
        // Output slots pinned to `'static` (a return annotation) take no
        // contract facts: the body shows its result lives that long itself.
        let mut snks: Vec<Univ> = self.slots.first().map(|v| v.iter().copied().filter(|&u| u != 0).collect()).unwrap_or_default();
        for (i, &(src, snk)) in roles.iter().enumerate() {
            if let Some(&u) = env_caps.get(i) {
                if src {
                    cap_srcs.push(u);
                }
                if snk {
                    snks.push(u);
                }
            }
        }
        let mut arg_srcs: Vec<Univ> = Vec::new();
        let mut arg_snks: Vec<Univ> = Vec::new();
        for (i, r) in arg_roles.iter().enumerate() {
            if let (Some((src, snk)), Some(&u)) = (r, args.get(i)) {
                if *src {
                    arg_srcs.push(u);
                }
                if *snk {
                    arg_snks.push(u);
                }
            }
        }
        // Sources into sinks; an argument's regions do not flow into an
        // argument's `&mut` target (`closure_arg_vars` agrees).
        for &a in cap_srcs.iter().chain(&arg_srcs) {
            for &b in &snks {
                if a != b {
                    self.facts.push((a, b));
                }
            }
        }
        for &a in &cap_srcs {
            for &b in &arg_snks {
                self.facts.push((a, b));
            }
        }
        // `thread::scope`'s closure (W-THREADS): the scope is live for the
        // whole call, during which the closure's captures stay borrowed,
        // so every captured region (and the `Scope`'s `'env`) outlives the
        // `Scope`'s `'scope` (rustc: `'env: 'scope` from the scope type).
        if entry.is_some_and(|c| c.scope_body)
            && let Some(&[rf, sc, env]) = self.slots.get(2).map(|v| v.as_slice())
        {
            // `&'scope Scope<'scope, 'env>`: one region for both.
            self.facts.push((rf, sc));
            self.facts.push((sc, rf));
            for &u in env_caps.iter().chain(self.slots[1].first().filter(|_| self.slots[1].len() > env_caps.len())).chain([&env]) {
                self.facts.push((u, sc));
            }
        }
        self.ends = vec![None; self.n_univ as usize + 1];
        self.ends[0] = Some(End::Static);
        for (k, &u) in self.slots.first().cloned().unwrap_or_default().iter().enumerate() {
            if u != 0 {
                self.ends[u as usize] = Some(End::Out(k as u32));
            }
        }
        for (i, &u) in env_caps.iter().enumerate() {
            self.ends[u as usize] = Some(End::Cap(i as u32));
        }
        for (j, r) in arg_roles.iter().enumerate() {
            if r.is_some()
                && let Some(&u) = args.get(j)
            {
                self.ends[u as usize] = Some(End::Arg(j as u32));
            }
        }
        // A bound's higher-ranked output over its one elided input
        // lifetime (`F: Fn(&T) -> &U`): rustc gives the closure `for<'r>
        // fn(&'r T) -> &'r U`, so that argument slot (the only
        // higher-ranked one) outlives those output slots.
        if let Some(bo) = entry.and_then(|c| c.bound_output) {
            let mut named: Vec<Region> = Vec::new();
            let hr: Vec<usize> = (0..args.len()).filter(|&i| arg_roles.get(i).is_none_or(|r| r.is_none())).collect();
            if regioned_slots(sc, bo, body.locals[0].ty, &mut named)
                && let [j] = hr[..]
            {
                let outs = self.slots.first().cloned().unwrap_or_default();
                for (r, &o) in named.iter().zip(&outs) {
                    if matches!(r, Region::Bound(_)) && o != 0 {
                        self.facts.push((args[j], o));
                    }
                }
            }
        }
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

/// The region contract of a closure (W-BORROW, ARCH 5.2 closures): per
/// slot of its env field types, in slot order, whether the body may read
/// the region into other places (a source) and whether it may write a
/// region there (a sink). A shared capture `&'c T`: `'c` and `T`'s slots
/// are sources; a mutable one `&'c mut T`: `T`'s slots are sources and
/// sinks, `'c` neither (a captured `&mut` cannot escape); a by-value
/// field: its slots are sources and sinks. The body may make any source
/// outlive any sink and its output; the creator adds what the body needs
/// of that (`closure_reqs`), or every source-to-sink edge when the body
/// does not solve, and a call's result holds what the body returns.
pub(super) fn closure_roles<T: TyIntern>(sc: &mut SlotCx<'_, '_, '_, T>, args: ArgsId, out: &mut Vec<(bool, bool)>) {
    for f in closure_fields(sc.tys, args) {
        match sc.tys.kind(f) {
            TyKind::Ref(_, m, inner) => {
                let n = sc.slots(inner) as usize;
                if m.is_mut() {
                    out.push((false, false));
                    out.extend(std::iter::repeat_n((true, true), n));
                } else {
                    out.push((true, false));
                    out.extend(std::iter::repeat_n((true, false), n));
                }
            }
            _ => {
                let n = sc.slots(f) as usize;
                out.extend(std::iter::repeat_n((true, true), n));
            }
        }
    }
}

/// The roles of a closure's argument slots, in slot order: `None` for a
/// higher-ranked region; `Some((source, sink))` for a free one. With
/// `free` (`ClosureEntry::free_args`, an iterator method's closure) the
/// arguments are items: free, except the outer reference of an `&item`
/// argument; every free slot is a source, and one behind a `&mut` is a
/// sink too. Without it every argument region is higher-ranked.
pub(super) fn closure_arg_roles<T: TyIntern>(sc: &mut SlotCx<'_, '_, '_, T>, inputs: &[Ty], free: Option<&[bool]>, out: &mut Vec<Option<(bool, bool)>>) {
    for (i, &t) in inputs.iter().enumerate() {
        let Some(flags) = free else {
            let n = sc.slots(t) as usize;
            out.extend(std::iter::repeat_n(None, n));
            continue;
        };
        match sc.tys.kind(t) {
            TyKind::Ref(_, _, inner) if flags.get(i).copied().unwrap_or(false) => {
                out.push(None);
                arg_slot_roles(sc, inner, false, out);
            }
            _ => arg_slot_roles(sc, t, false, out),
        }
    }
}

/// The argument slots of a closure, in slot order: its role (`None`:
/// higher-ranked; see `closure_arg_roles`) and, for a slot its annotation
/// names (`|x: &'a T|`), the enclosing fn's region it is: such a slot is
/// free, and the creator ties it to that region. A `Region::Bound` slot
/// (an elided lifetime written on a closure with no expected signature)
/// is higher-ranked. `Err` when an annotated type does not pair with the
/// argument's erased type.
pub(super) fn closure_arg_slots<T: TyIntern>(
    sc: &mut SlotCx<'_, '_, '_, T>,
    c: &crate::check::generics::ClosureEntry,
) -> Result<Vec<(Option<(bool, bool)>, Option<Region>)>, ()> {
    let mut roles = Vec::new();
    closure_arg_roles(sc, &c.inputs, c.free_args.as_deref(), &mut roles);
    let mut free_roles = Vec::new();
    closure_arg_roles(sc, &c.inputs, Some(&vec![false; c.inputs.len()]), &mut free_roles);
    let mut named: Vec<Region> = Vec::with_capacity(roles.len());
    for (i, &e) in c.inputs.iter().enumerate() {
        let n = sc.slots(e) as usize;
        match c.input_regions.get(i).copied().flatten() {
            Some(r) => {
                let start = named.len();
                if !regioned_slots(sc, r, e, &mut named) || named.len() - start != n {
                    // An annotation that names no lifetime only marks
                    // its elided ones: unpaired, it counts as unwritten.
                    if names_region(sc.tys, r) {
                        return Err(());
                    }
                    named.truncate(start);
                    named.extend(std::iter::repeat_n(Region::Erased, n));
                }
            }
            None => named.extend(std::iter::repeat_n(Region::Erased, n)),
        }
    }
    Ok(roles
        .into_iter()
        .zip(free_roles)
        .zip(named)
        .map(|((r, fr), nr)| match nr {
            Region::Param(_) | Region::Static => (fr, Some(nr)),
            // An elided lifetime in an annotation of a closure with no
            // expected signature: the closure's own, higher-ranked.
            Region::Bound(_) => (None, None),
            _ => (r, None),
        })
        .collect())
}

/// True when regioned type `r` names a lifetime (`'static` or a param).
fn names_region(tys: &impl TyIntern, r: Ty) -> bool {
    let named = |x: Region| matches!(x, Region::Static | Region::Param(_));
    match tys.kind(r) {
        TyKind::Ref(x, _, inner) => named(x) || names_region(tys, inner),
        TyKind::Adt(_, args) => tys.args(args).iter().any(|g| match g {
            GenericArg::Ty(t) => names_region(tys, *t),
            GenericArg::Lifetime(x) => named(*x),
            _ => false,
        }),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&t| names_region(tys, t)),
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => names_region(tys, e),
        TyKind::Dyn(_, x) => named(x),
        _ => false,
    }
}

/// The region a regioned type `r` gives each slot of erased type `e`, in
/// slot order (`Erased` where `r` names none). False when they differ in
/// shape.
fn regioned_slots<T: TyIntern>(sc: &mut SlotCx<'_, '_, '_, T>, r: Ty, e: Ty, out: &mut Vec<Region>) -> bool {
    let tys = sc.tys;
    match (tys.kind(r), tys.kind(e)) {
        (TyKind::Ref(rr, rm, ri), TyKind::Ref(_, em, ei)) if rm == em => {
            out.push(rr);
            regioned_slots(sc, ri, ei, out)
        }
        (TyKind::Adt(rd, ra), TyKind::Adt(ed, ea)) if rd == ed => {
            let lts: Vec<Region> = tys.args(ra).iter().filter_map(|g| if let GenericArg::Lifetime(x) = g { Some(*x) } else { None }).collect();
            for k in 0..adt_regions(sc.p, tys, e) as usize {
                out.push(lts.get(k).copied().unwrap_or(Region::Erased));
            }
            let rargs: Vec<Ty> = tys.args(ra).iter().filter_map(|g| g.as_ty()).collect();
            let eargs: Vec<Ty> = tys.args(ea).iter().filter_map(|g| g.as_ty()).collect();
            rargs.len() == eargs.len() && rargs.into_iter().zip(eargs).all(|(x, y)| regioned_slots(sc, x, y, out))
        }
        (TyKind::Tuple(a), TyKind::Tuple(b)) => {
            let (xs, ys) = (tys.tys_of(a).to_vec(), tys.tys_of(b).to_vec());
            xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| regioned_slots(sc, x, y, out))
        }
        (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
            regioned_slots(sc, a, b, out)
        }
        (TyKind::Dyn(_, rr), TyKind::Dyn(..)) => {
            out.push(rr);
            true
        }
        // A bound's type param (`ClosureEntry::bound_output`): the call's
        // instantiation, no written regions.
        (TyKind::Param(_) | TyKind::Projection(..), _) => {
            let n = sc.slots(e) as usize;
            out.extend(std::iter::repeat_n(Region::Erased, n));
            true
        }
        _ => {
            let n = sc.slots(e) as usize;
            out.extend(std::iter::repeat_n(Region::Erased, n));
            r == e || n == 0
        }
    }
}

fn arg_slot_roles<T: TyIntern>(sc: &mut SlotCx<'_, '_, '_, T>, t: Ty, under_mut: bool, out: &mut Vec<Option<(bool, bool)>>) {
    match sc.tys.kind(t) {
        TyKind::Ref(_, m, inner) => {
            out.push(Some((true, under_mut)));
            arg_slot_roles(sc, inner, under_mut || m.is_mut(), out);
        }
        TyKind::Adt(_, args) => {
            let n = adt_regions(sc.p, sc.tys, t) as usize;
            out.extend(std::iter::repeat_n(Some((true, under_mut)), n));
            for g in sc.tys.args(args).to_vec() {
                if let GenericArg::Ty(e) = g {
                    arg_slot_roles(sc, e, under_mut, out);
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in sc.tys.tys_of(ts).to_vec() {
                arg_slot_roles(sc, e, under_mut, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => arg_slot_roles(sc, e, under_mut, out),
        _ => {
            let n = sc.slots(t) as usize;
            out.extend(std::iter::repeat_n(Some((true, under_mut)), n));
        }
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
        TyKind::Adt(def, args) => {
            let start = *at;
            for _ in 0..adt_regions(sc.p, sc.tys, t) {
                if let Some(&u) = us.get(*at) {
                    each(u, facts, outer);
                }
                *at += 1;
            }
            // The Adt's own outlives facts are implied by its use.
            for &(x, y) in sc.p.regions.adt_facts.get(&def).map_or(&[][..], |v| v.as_slice()) {
                let to = if y == crate::check::generics::STATIC_FACT { Some(0) } else { us.get(start + y as usize).copied() };
                if let (Some(&a), Some(b)) = (us.get(start + x as usize), to) {
                    facts.push((a, b));
                }
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
            // The closure contract: every source outlives every sink.
            let start = *at;
            for e in closure_fields(sc.tys, args) {
                implied_walk(sc, e, us, at, outer, facts);
            }
            let mut roles = Vec::new();
            closure_roles(sc, args, &mut roles);
            for (i, &(src, _)) in roles.iter().enumerate() {
                for (j, &(_, snk)) in roles.iter().enumerate() {
                    if src && snk && i != j
                        && let (Some(&a), Some(&b)) = (us.get(start + i), us.get(start + j))
                    {
                        facts.push((a, b));
                    }
                }
            }
        }
        // `&'r (dyn Tr + 'o)` gives `'o: 'r`.
        TyKind::Dyn(..) => {
            let Some(&u) = us.get(*at) else { return };
            each(u, facts, outer);
            *at += 1;
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
    /// In a closure body: every `a: b` between universals its constraints
    /// need (`closure_requirements`).
    pub reqs: Vec<(u32, u32)>,
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
    /// While a call through an `Fn*` bound instantiates it
    /// (`call_fn_bound`): the one fresh var its elided (higher-ranked)
    /// lifetime takes, so an output elided like an input ties to it.
    bound_var: Option<u32>,
    /// The argument slot vars of each closure created here whose
    /// arguments are free (`ClosureEntry::free_args`), by closure def.
    closure_args: FxMap<DefId, Vec<u32>>,
    /// The requirements of each closure created here (`closure_reqs`).
    closure_reqs: FxMap<DefId, Option<std::rc::Rc<Vec<(End, End)>>>>,
    /// The closures a call's `F: Fn*(..)` bounds linked (`link_bound_closure`).
    bound_linked: Vec<DefId>,
    /// While a call of a trait method instantiates its signature: the vars
    /// its first universals (the trait's lifetime params) take
    /// (`trait_lifetime_seeds`); empty otherwise.
    seed_univ: Vec<u32>,
    /// The closures `closure_created` has seen.
    created: FxMap<DefId, ()>,
    /// The last check of the fn whose closures `closure_reqs` lowers
    /// (None when it has errors), shared by its closures.
    root_check: Option<(LocalDefId, Option<crate::check::Checked<'p>>)>,
    /// While a call's signature is instantiated: the erased type each
    /// type param binds (`inst_walk`), for trait-selection checks.
    bind_tys: FxMap<u32, Ty>,
    /// The capture var of each local that may hold an `impl Trait` value
    /// (`Body::opaque_locals`): the regions the opaque type captures
    /// (edition 2024: every argument region of the defining call), which
    /// the revealed hidden type may have no slot for (`String` behind
    /// `impl Display`). Owned by the local and drop-live (`cap_flow`).
    cap_var: FxMap<Local, u32>,
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
            bound_var: None,
            closure_args: FxMap::default(),
            closure_reqs: FxMap::default(),
            bound_linked: Vec::new(),
            seed_univ: Vec::new(),
            created: FxMap::default(),
            root_check: None,
            bind_tys: FxMap::default(),
            cap_var: FxMap::default(),
        };
        // Vars 0..=n_univ: 'static and the universals.
        for _ in 0..=b.own.n_univ {
            b.owner.push(0);
            b.drop_slot.push(false);
        }
        let drops = !super::drop_heads(p).is_empty() || body.locals.iter().any(|d| drops_guard(&body.tys, d.ty));
        for (l, decl) in body.locals.iter().enumerate() {
            let n = b.local_slots(l as Local);
            let base = b.owner.len() as u32;
            b.local_base.push(base);
            let mut dl = vec![false; n as usize];
            if body.opaque_locals.contains(&(l as Local)) {
                // An `impl Trait` value's unknown destructor may use every
                // region it captures (W-CHECK-G3, `Body::opaque_locals`).
                dl = vec![true; n as usize];
            } else if drops && n > 0 && !fat_local(&body.tys, decl.ty) {
                b.sc.drop_slots(decl.ty, DropMode::Owned, 0, &mut dl);
            }
            for i in 0..n as usize {
                b.owner.push(l as u32 + 1);
                b.drop_slot.push(dl[i]);
            }
            if body.opaque_locals.contains(&(l as Local)) {
                b.cap_var.insert(l as Local, b.owner.len() as u32);
                b.owner.push(l as u32 + 1);
                b.drop_slot.push(true);
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
                    TyKind::Adt(..) if tys.guard_elem(ty).is_some() => {
                        // A `RefCell` guard derefs like the reference it
                        // stands for: its own region leads, then the value's.
                        let (inner, is_mut) = tys.guard_elem(ty).unwrap();
                        derefs.push((out[0], is_mut));
                        out.remove(0);
                        let n = self.sc.slots(inner) as usize;
                        out.truncate(n);
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
        // A value flowing into a place is a coercion site: rustc may
        // shorten the object lifetime of the outermost `&`/`&mut dyn`
        // (`&'r mut (dyn Tr + 'a)` to `&'r mut (dyn Tr + 'b)`, `'a: 'b`),
        // which plain `&mut` invariance would equate.
        if v == Variance::Co
            && let (TyKind::Ref(_, _, ai), TyKind::Ref(_, _, bi)) = (self.body.tys.kind(a), self.body.tys.kind(b))
            && matches!(self.body.tys.kind(ai), TyKind::Dyn(..))
            && matches!(self.body.tys.kind(bi), TyKind::Dyn(..))
            && av.len() == 2
            && bv.len() == 2
        {
            self.edge(av[0], bv[0]);
            self.edge(av[1], bv[1]);
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
                    let rv = if tys.builtin_of(a).is_some() { builtin_region_variance(tys, a) } else { self.p.regions.adts(self.p).region_modes(ad, k as usize).0 };
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
            (TyKind::Dyn(..), TyKind::Dyn(..)) => {
                let (Some(&x), Some(&y)) = (av.get(*ia), bv.get(*ib)) else { return false };
                self.edge_v(x, y, v.then(Variance::Co));
                *ia += 1;
                *ib += 1;
                true
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
            (TyKind::Dyn(_, rr), TyKind::Dyn(..)) => {
                out.push(if crate::check::object::dyn_is_static(self.p, et, e) { Region::Static } else { rr });
                true
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
            self.static_bound_edges(t, &inner, &mut 0);
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

    /// Carries the capture vars (`cap_var`) of the opaque locals `srcs`
    /// moves or copies into `dest`: into the dest local's capture var,
    /// or into every slot of a dest that has none (a reference to an
    /// opaque value, a `Box<dyn Tr>` made from one).
    fn cap_flow(&mut self, srcs: &[&Operand], dest: &Place) {
        let caps = self.caps_of(srcs.iter().copied());
        self.cap_into(&caps, dest);
    }

    /// The capture vars of the opaque locals the operands read.
    fn caps_of<'o>(&self, ops: impl Iterator<Item = &'o Operand>) -> Vec<u32> {
        ops.filter_map(|o| match o {
            Operand::Move(pl) | Operand::Copy(pl) => self.cap_var.get(&pl.local).copied(),
            _ => None,
        })
        .collect()
    }

    /// Makes the vars `caps` outlive what `dest` captures (`cap_flow`).
    fn cap_into(&mut self, caps: &[u32], dest: &Place) {
        if caps.is_empty() {
            return;
        }
        if let Some(&dc) = self.cap_var.get(&dest.local) {
            self.flow_all(caps, &[dc]);
            return;
        }
        let (mut dv, mut d) = (Vec::new(), Vec::new());
        self.place(dest, &mut dv, &mut d);
        self.flow_all(caps, &dv);
    }

    fn assign(&mut self, bi: usize, si: usize, dest: &Place, rv: &Rvalue) {
        if !self.cap_var.is_empty() {
            // Only the rvalues that move or copy a value into the result
            // carry its captures; a comparison or a format reads it.
            match rv {
                Rvalue::Use(o)
                | Rvalue::Cast(o, _)
                | Rvalue::Opt(_, Some(o))
                | Rvalue::Res(_, _, o)
                | Rvalue::MakeDyn { ptr: o, .. }
                | Rvalue::DynUpcast { ptr: o, .. }
                | Rvalue::DynData { ptr: o, .. }
                | Rvalue::VecRepeat(_, o, _)
                | Rvalue::ArrayRepeat(_, o, _) => self.cap_flow(&[o], dest),
                Rvalue::Aggregate(_, _, ops) | Rvalue::VecLit(_, ops) | Rvalue::TupleAgg(_, ops) | Rvalue::ArrayAgg(_, ops) => {
                    let ops: Vec<&Operand> = ops.iter().collect();
                    self.cap_flow(&ops, dest);
                }
                // A reference to an opaque value holds what it captures
                // (`&'r Opaque<'s>` needs `'s: 'r`).
                Rvalue::Ref(_, pl) => {
                    if let Some(&c) = self.cap_var.get(&pl.local) {
                        self.cap_into(&[c], dest);
                    }
                }
                _ => {}
            }
        }
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
                // A `ByNext` wrapper (W-STD-B): its item type is not a
                // field, so tie it here: the wrapped iterator's regions
                // outlive the item's.
                if let Some((crate::ty::iter::IterKind::ByNext, a)) = crate::ty::iter::iter_parts(&self.body.tys, *ty) {
                    self.place(dest, &mut dv, &mut d);
                    let own = adt_regions(self.p, &self.body.tys, *ty) as usize;
                    let n0 = self.sc.slots(a[0]) as usize;
                    let n1 = self.sc.slots(a[1]) as usize;
                    if let (Some(src), Some(item)) = (dv.get(own..own + n0), dv.get(own + n0..own + n0 + n1)) {
                        let (src, item) = (src.to_vec(), item.to_vec());
                        self.flow_all(&src, &item);
                    }
                }
                if let TyKind::Closure(def, args) = self.body.tys.kind(*ty) {
                    // The closure contract (`closure_roles`): its body may
                    // make any captured source outlive any captured sink.
                    // The creator adds what the body needs of it when the
                    // body solves (`closure_reqs`), else all of it.
                    self.place(dest, &mut dv, &mut d);
                    let mut roles = Vec::new();
                    closure_roles(&mut self.sc, args, &mut roles);
                    self.closure_created(def, &roles, &dv, true);
                }
            }
            Rvalue::ArrayAgg(_, ops) | Rvalue::VecLit(_, ops) => {
                for o in ops {
                    self.into_place(o, dest, &[Proj::Index(0)]);
                }
            }
            Rvalue::ArrayRepeat(_, o, _) | Rvalue::VecRepeat(_, o, _) => self.into_place(o, dest, &[Proj::Index(0)]),
            Rvalue::MakeDyn { ptr: o, .. } | Rvalue::DynUpcast { ptr: o, .. } => {
                // A dyn pointer from a thin one (or a narrower dyn). The
                // pointer's own region carries over (`&'p S` to `&'q dyn
                // Tr`: `'p: 'q`), and every region of the data outlives the
                // object lifetime (`S: 'o`, rustc's unsizing; an upcast
                // gives `'o1: 'o2`). An owning pointer (`Box<dyn Tr + 'o>`)
                // has only the object slot.
                let mut ov = Vec::new();
                let ot = self.operand(o, &mut ov);
                let dt = self.place(dest, &mut dv, &mut d);
                let refs = (matches!(self.body.tys.kind(ot), TyKind::Ref(..)), matches!(self.body.tys.kind(dt), TyKind::Ref(..)));
                let (data, obj): (Vec<u32>, Option<u32>) = match refs {
                    (true, true) => {
                        if let (Some(&x), Some(&y)) = (ov.first(), dv.first()) {
                            self.edge(x, y);
                        }
                        (ov.iter().skip(1).copied().collect(), dv.get(1).copied())
                    }
                    (false, false) => (ov.clone(), dv.first().copied()),
                    _ => (Vec::new(), None),
                };
                match obj {
                    Some(o) if dv.len() == if refs.1 { 2 } else { 1 } => {
                        for &x in &data {
                            self.edge(x, o);
                        }
                    }
                    _ => self.equate_all(&ov, &dv),
                }
                if let Rvalue::MakeDyn { src, dyn_ty, .. } = rv {
                    // A `'static` object lifetime (`Box<dyn Tr>` in a
                    // signature or field, `+ 'static`, a `'static` trait)
                    // may not be a slot of the place the object goes to:
                    // the data outlives `'static` here.
                    if crate::check::object::dyn_is_static(self.p, &self.body.tys, *dyn_ty) {
                        for &x in &data {
                            self.edge(x, 0);
                        }
                    }
                    self.dyn_fn_coercion(*src, *dyn_ty, &data);
                }
            }
            // A downcast (W-CHECK-G3): `&'p dyn Any` to `&'q T` needs
            // `'p: 'q`. T is `'static`; an owning pointer relates nothing.
            Rvalue::DynData { ptr: o, .. } => {
                let mut ov = Vec::new();
                self.operand(o, &mut ov);
                self.place(dest, &mut dv, &mut d);
                if let (Some(&x), Some(&y)) = (ov.first(), dv.first()) {
                    self.edge(x, y);
                }
            }
            _ => {}
        }
    }

    /// The inputs and output of a `dyn Fn*(I..) -> O` type, behind any
    /// references and smart pointers, in this body's types. None for any
    /// other type. Every region in them is elided (check rejects written
    /// ones, L0203), so late-bound: the `dyn Fn` rules below rely on it.
    fn dyn_fn_sig(&self, t: Ty) -> Option<(Vec<Ty>, Ty)> {
        let tys = &self.body.tys;
        let mut t = t;
        loop {
            match tys.kind(t) {
                TyKind::Ref(_, _, inner) => t = inner,
                _ => match tys.smart_elem(t) {
                    Some(inner) => t = inner,
                    None => break,
                },
            }
        }
        let lang = self.p.gx.lang;
        let pr = crate::check::object::principal_of(tys, t)?;
        if !lang.is_fn_family(pr.def) {
            return None;
        }
        let tuple = tys.args(pr.args).get(1).and_then(|g| g.as_ty())?;
        let ins = match tys.kind(tuple) {
            TyKind::Tuple(ts) => tys.tys_of(ts).to_vec(),
            TyKind::Unit => Vec::new(),
            _ => return None,
        };
        let out_def = lang.output_of(lang.fn_once)?;
        let out = tys.bindings(pr.bindings).iter().find(|(d, _)| *d == out_def).and_then(|(_, g)| g.as_ty()).unwrap_or(UNIT);
        Some((ins, out))
    }

    /// A call through a `dyn Fn*` value (`call_late_bound`, the receiver
    /// first). The receiver lends nothing to the result, and an argument
    /// reaches nothing else: whatever is behind the object takes any
    /// region there (`dyn_fn_coercion`).
    fn call_dyn_fn(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let Some((rt, _)) = avs.first() else { return false };
        let Some((ins, out)) = self.dyn_fn_sig(*rt) else { return false };
        self.call_late_bound(&ins, out, &avs[1..], dt, dv)
    }

    /// The region of each slot of a type inside a fn pointer type or `dyn
    /// Fn*` sugar: `'static` where written there (`Scope::static_refs`),
    /// else elided (`Erased`), so late-bound.
    fn sig_slot_regions(&mut self, t: Ty) -> Vec<Region> {
        let mut rs = Vec::new();
        regioned_slots(&mut self.sc, t, t, &mut rs);
        rs
    }

    /// A call of a signature whose regions are all elided, so late-bound,
    /// or written `'static` (a `dyn Fn*` value, a fn pointer: check rejects
    /// other written lifetimes there, L0203): each elided input slot is a
    /// fresh region of this call that the argument outlives, a `'static`
    /// one is `'static`, and each elided output slot is the one input
    /// slot's (elision; L0202 otherwise). False when the shapes do not
    /// pair or the output is not the one input's (the caller's rule then).
    fn call_late_bound(&mut self, ins: &[Ty], out: Ty, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        if ins.len() != avs.len() {
            return false;
        }
        let mut slots: Vec<u32> = Vec::new();
        for (i, &it) in ins.iter().enumerate() {
            let (at, av) = &avs[i];
            let pv: Vec<u32> = self.sig_slot_regions(it).into_iter().map(|r| if r == Region::Static { 0 } else { self.fresh() }).collect();
            if !av.is_empty() && !self.relate(*at, av, it, &pv, Variance::Co) {
                return false;
            }
            slots.extend(pv);
        }
        if dv.is_empty() {
            return true;
        }
        let outs = self.sig_slot_regions(out);
        let one = if let [one] = slots[..] { Some(one) } else { None };
        let Some(rv) = outs.iter().map(|&r| if r == Region::Static { Some(0) } else { one }).collect::<Option<Vec<u32>>>() else { return false };
        self.relate(out, &rv, dt, dv, Variance::Co)
    }

    /// A coercion to `dyn Fn*(I..) -> O`, whose regions are all
    /// late-bound (`dyn_fn_sig`): the source must take any region in each
    /// input slot and return the one input's in each output slot, as
    /// rustc proves `for<'r> Fn(&'r I) -> &'r O` of it. A closure with a
    /// free argument slot (a `let` closure, a named annotation) is not
    /// general enough (L0735), and what it returns from its captures
    /// (`data`, the env's slots) must be `'static`; a type param or a fn
    /// item is checked by its signature (`entail_dyn`).
    fn dyn_fn_coercion(&mut self, src: Ty, dyn_ty: Ty, data: &[u32]) {
        let p = self.p;
        let Some((ins, out)) = self.dyn_fn_sig(dyn_ty) else { return };
        let n_out = self.sc.slots(out) as usize;
        match self.body.tys.kind(src) {
            TyKind::Closure(def, args) => {
                let Some(c) = p.gx.closures.get(&def) else { return };
                // A free argument slot (a `let` closure, a named or
                // `'static` annotation, or the target's own `&'static`)
                // takes one region: only where the target writes `'static`
                // does it serve, and it is `'static` then.
                let mut targets: Vec<Region> = Vec::new();
                for &it in &ins {
                    targets.extend(self.sig_slot_regions(it));
                }
                if let Ok(cs) = closure_arg_slots(&mut self.sc, c) {
                    let vars = self.closure_args.get(&def).cloned().unwrap_or_default();
                    for (i, (r, link)) in cs.iter().enumerate() {
                        if r.is_none() {
                            continue;
                        }
                        if targets.get(i) != Some(&Region::Static) || cs.len() != targets.len() {
                            self.not_general_enough();
                            return;
                        }
                        if link.is_none()
                            && let Some(&v) = vars.get(i)
                        {
                            self.edge(v, 0);
                            self.edge(0, v);
                        }
                    }
                }
                if n_out == 0 {
                    return;
                }
                let mut roles = Vec::new();
                closure_roles(&mut self.sc, args, &mut roles);
                match self.closure_reqs(def, &roles) {
                    Some(reqs) => {
                        for &(x, y) in reqs.iter() {
                            if let (End::Cap(i), End::Out(_)) = (x, y)
                                && let Some(&v) = data.get(i as usize)
                            {
                                self.edge(v, 0);
                            }
                        }
                    }
                    None => {
                        for (i, &(src, _)) in roles.iter().enumerate() {
                            if src && let Some(&v) = data.get(i) {
                                self.edge(v, 0);
                            }
                        }
                    }
                }
            }
            TyKind::Param(_) | TyKind::FnDef(..) => self.entail_dyn(src, &ins, out),
            _ => {}
        }
    }

    /// A callee's region signature: its own, its template's, or its trait
    /// method's (a stub, or a trait default body and its instances).
    fn callee(&self, f: LocalDefId) -> Callee<'p> {
        let p = self.p;
        if p.gx.closure_fns.contains_key(&f) {
            return Callee::Closure;
        }
        match p.regions.body_sig(p, f) {
            Some(s) => Callee::Sig(s),
            None => Callee::Opaque,
        }
    }

    /// The closure arguments of a call to `f` (not a call through a
    /// bound) whose param is a type param (`F`, `&F`, `&mut F`) with only
    /// `Fn*` bounds whose output has no type param: what the closure
    /// returns has the bound's regions (`tie_bound_output`), which the
    /// signature relates to the result, as rustc checks a call by its
    /// signature alone.
    fn output_tied(&self, f: LocalDefId, avs: &[(Ty, Vec<u32>)]) -> Vec<usize> {
        let p = self.p;
        if p.gx.fn_class.get(f.0 as usize) == Some(&crate::check::generics::FnClass::Stub) {
            return Vec::new();
        }
        let Callee::Sig(sig) = self.callee(f) else { return Vec::new() };
        let mut out = Vec::new();
        for (i, (t, _)) in avs.iter().enumerate() {
            let mut t = *t;
            while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
                t = inner;
            }
            if !matches!(self.body.tys.kind(t), TyKind::Closure(..)) {
                continue;
            }
            let Some(mut pt) = sig.params.get(i).copied() else { continue };
            while let TyKind::Ref(_, _, inner) = p.tys.kind(pt) {
                pt = inner;
            }
            let TyKind::Param(j) = p.tys.kind(pt) else { continue };
            let mut bounds = sig.fn_bounds.iter().filter(|b| b.param == j.0).peekable();
            if bounds.peek().is_some() && bounds.all(|b| b.output.is_none_or(|o| !p.tys.flags(o).contains_param())) {
                out.push(i);
            }
        }
        out
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
        // A call of an `impl Trait` fn: its value captures every argument
        // region. Any call carries the captures of the opaque values it
        // takes by value to an opaque result (`cap_var`).
        if let Some(&dc) = self.cap_var.get(&dest.local) {
            // A template callee (`lust check` makes no instances) keeps
            // its opaque return in `FnInfo::ret`.
            if let CallTarget::Fn(f) = target
                && (self.p.gx.opaque_ret_of.contains_key(&f) || crate::check::opaque::mentions_opaque(&self.p.tys, self.p.fn_info(f).ret, None))
            {
                let all: Vec<u32> = avs.iter().flat_map(|(_, v)| v.iter().copied()).collect();
                self.flow_all(&all, &[dc]);
            }
            let caps = self.caps_of(args.iter());
            self.flow_all(&caps, &[dc]);
        }
        // Free closure arguments first: a closure with no captures has no
        // creating statement, so its argument vars are made here. A builtin
        // links them to its other arguments; a generic fn through its bound
        // (`call_sig_with`), or like a builtin when its signature cannot
        // pair (below).
        for (t, v) in &avs {
            if let TyKind::Closure(def, args) = self.body.tys.kind(*t) {
                let mut roles = Vec::new();
                closure_roles(&mut self.sc, args, &mut roles);
                self.closure_arg_vars(def, &roles, v);
            }
        }
        if let CallTarget::Builtin(b) = target {
            self.link_closure_args(&avs, Some(b), &[]);
        }
        // A closure argument that returns borrows: whatever the callee
        // returns may hold the closure's captured sources and free
        // argument regions (its output), unless the callee's bounds give
        // its output every region (`output_tied`; then the signature
        // says what reaches the result).
        // `Box::new(x)` and `Rc::new(x)` hold `x` itself: its slots are
        // the result's, one to one (a closure's captures included).
        if let CallTarget::Builtin(crate::check::Builtin::BoxNew | crate::check::Builtin::RcNew) = target
            && let [(at, av)] = &avs[..]
            && let Some(inner) = self.body.tys.smart_elem(dt)
            && (av.is_empty() && dv.is_empty() || self.relate(*at, av, inner, &dv, Variance::Co))
        {
            return;
        }
        let tied = match target {
            CallTarget::Fn(f) => self.output_tied(f, &avs),
            _ => Vec::new(),
        };
        let mut srcs: Vec<u32> = Vec::new();
        for (i, (t, v)) in avs.iter().enumerate() {
            if !tied.contains(&i) {
                self.closure_sources(*t, v, &mut 0, &mut srcs);
            }
        }
        self.flow_all(&srcs, &dv);
        // `catch_unwind(f)` returns what `f` returns, or a `'static`
        // payload: the closure's borrows reach the result only through its
        // output (W-UNWIND).
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::CatchUnwind)) = target {
            return;
        }
        if matches!(target, CallTarget::Dyn(_)) && self.call_dyn_fn(&avs, dt, &dv) {
            return;
        }
        if let CallTarget::Indirect(l) = target
            && let TyKind::FnPtr(sig) = self.body.tys.kind(self.body.locals[l as usize].ty)
        {
            let s = self.body.tys.sig(sig).value;
            let ins: Vec<Ty> = self.body.tys.tys_of(s.inputs).to_vec();
            if self.call_late_bound(&ins, s.output, &avs, dt, &dv) {
                return;
            }
        }
        // `scope.spawn(f)` on `&Scope<'s, _>`: `F: 's` and `T: 's`, and the
        // handle's own region is `'s` (W-THREADS). The scope closure's
        // `&Scope` argument is higher-ranked, so `'s` covers its whole
        // body: two spawned closures borrowing one place both hold it
        // to the end, as rustc's `'scope`.
        // `'s` is the `Scope`'s own `'scope` slot (behind the receiver's
        // reborrow, whose region may be shorter).
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::ScopeSpawn)) = target
            && let Some(&r) = avs.first().and_then(|(_, v)| v.get(1))
        {
            for &x in avs.iter().skip(1).flat_map(|(_, v)| v).chain(&srcs).chain(dv.iter().skip(1)) {
                self.edge(x, r);
            }
            if let Some(&h) = dv.first() {
                self.edge(h, r);
                self.edge(r, h);
            }
            // `spawn(&'scope self)`: the receiver's borrow outlives
            // `'scope` (rustc E0521-style "lifetime may not live long
            // enough" for `fn f(s: &Scope)` with two elided lifetimes).
            if let Some(&b) = avs.first().and_then(|(_, v)| v.first()) {
                self.edge(b, r);
            }
            return;
        }
        // `mpsc::channel()`: both ends carry one `T` (W-THREADS).
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::Channel | crate::check::sync::SyncOp::SyncChannel)) = target {
            let n = dv.len() / 2;
            for i in 0..n {
                self.edge(dv[i], dv[n + i]);
                self.edge(dv[n + i], dv[i]);
            }
            return;
        }
        // `send(&self, t: T)`: the value flows into the channel's `T`; a
        // failed send's `SendError<T>` gives that `T` back.
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::ChanSend | crate::check::sync::SyncOp::OnceSet)) = target
            && let [(st, sv), (vt, vv)] = avs.as_slice()
            && let TyKind::Ref(_, _, s) = self.body.tys.kind(*st)
            && let Some(el) = self.body.tys.adt_first_ty_arg(s)
            && let Some(tv) = sv.get(1..)
        {
            let tv = tv.to_vec();
            if !self.relate(*vt, vv, el, &tv, Variance::Co) {
                self.flow_all(vv, &tv);
            }
            self.equate_all(&tv, &dv);
            return;
        }
        // `handle.join()`: the result's `Ok` is the thread's `T`; its `Err`
        // payload is `'static` and borrows nothing (W-UNWIND).
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::JoinHandleJoin)) = target
            && let Some((ht, hv)) = avs.first()
            && let Some(t) = self.body.tys.adt_first_ty_arg(*ht)
        {
            let k = self.sc.slots(t) as usize;
            if k <= hv.len() && k <= dv.len() {
                let hv = hv[hv.len() - k..].to_vec();
                self.equate_all(&hv, &dv[..k]);
            }
            return;
        }
        // `once.get_or_init(f)`: what `f` returns is the cell's `T`; the
        // result `&T` borrows the cell.
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::OnceGetOrInit)) = target
            && let Some((_, sv)) = avs.first()
            && let Some((&r, tv)) = sv.split_first()
            && dv.len() == sv.len()
        {
            let tv = tv.to_vec();
            self.flow_all(&srcs, &tv);
            self.edge(r, dv[0]);
            self.equate_all(&tv, &dv[1..]);
            return;
        }
        // `cv.wait(guard)` and `wait_while`: the guard comes back as is.
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::CondvarWait | crate::check::sync::SyncOp::CondvarWaitWhile)) = target
            && let Some((_, gv)) = avs.get(1)
            && dv.len() == 2 * gv.len()
        {
            let gv = gv.clone();
            self.equate_all(&gv, &dv[..gv.len()]);
            self.equate_all(&gv, &dv[gv.len()..]);
            return;
        }
        // `thread::spawn(f)`: `F: 'static` and `T: 'static` (W-THREADS).
        // Every region of the closure (its captured borrows) and of the
        // handle must be `'static`.
        if let CallTarget::Builtin(crate::check::Builtin::Sync(crate::check::sync::SyncOp::ThreadSpawn)) = target {
            for &x in avs.iter().flat_map(|(_, v)| v).chain(&srcs).chain(&dv) {
                self.edge(x, 0);
            }
            return;
        }
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
        if let CallTarget::Fn(f) = target
            && self.call_fn_bound(f, &avs, dt, &dv)
        {
            return;
        }
        let callee = match target {
            CallTarget::Fn(f) => Some((f, self.callee(f))),
            _ => None,
        };
        match callee {
            Some((f, Callee::Sig(sig))) => {
                self.bound_linked.clear();
                self.seed_univ = self.trait_lifetime_seeds(f, &avs);
                let ok = self.call_sig(f, sig, &avs, dt, &dv);
                self.seed_univ.clear();
                // An `Item = T` bound (`I: Iterator<Item = T>`, `I:
                // IntoIterator<Item = T>`) ties `T`'s regions to the
                // iterator's, which the signature pairing does not see:
                // `mk(v.iter())` returning `Vec<T>` borrows `v` (rustc
                // E0505 on a later move; this was a false accept, also
                // behind `collect` into a BTreeSet). Over-approximate:
                // every argument region may reach the result.
                if ok && self.item_bound(f) {
                    let all: Vec<u32> = avs.iter().flat_map(|(_, v)| v.iter().copied()).collect();
                    self.flow_all(&all, &dv);
                }
                if ok {
                    // Closures no bound paired: like the opaque rule.
                    let linked = std::mem::take(&mut self.bound_linked);
                    self.link_closure_args(&avs, None, &linked);
                } else {
                    let mut srcs: Vec<u32> = Vec::new();
                    for &i in &tied {
                        let (t, v) = &avs[i];
                        self.closure_sources(*t, v, &mut 0, &mut srcs);
                    }
                    self.flow_all(&srcs, &dv);
                    self.call_opaque(&avs, dt, &dv);
                    self.link_closure_args(&avs, None, &[]);
                }
                self.trait_view(f, &avs, dt, &dv);
            }
            Some((_, Callee::Closure)) => {
                // The result holds what the body returns: per output slot,
                // the captured and free argument slots its requirements
                // name (`closure_reqs`), else every captured source (the
                // contract). Higher-ranked inputs reach no output.
                if let Some((et, ev)) = avs.first() {
                    let (ct, skip) = match self.body.tys.kind(*et) {
                        TyKind::Ref(_, _, inner) => (inner, 1),
                        _ => (*et, 0),
                    };
                    if let TyKind::Closure(def, args) = self.body.tys.kind(ct) {
                        let mut roles = Vec::new();
                        closure_roles(&mut self.sc, args, &mut roles);
                        let caps: Vec<u32> = ev.iter().skip(skip).copied().collect();
                        let vars = self.closure_arg_vars(def, &roles, &caps);
                        let n_out = self.p.gx.closures.get(&def).map(|c| c.output).map(|t| self.sc.slots(t) as usize);
                        match self.closure_reqs(def, &roles) {
                            Some(reqs) if n_out == Some(dv.len()) => {
                                for &(x, y) in reqs.iter() {
                                    let End::Out(k) = y else { continue };
                                    let from = match x {
                                        End::Cap(i) => caps.get(i as usize).copied(),
                                        End::Arg(j) => vars.as_ref().and_then(|v| v.get(j as usize)).copied(),
                                        End::Static | End::Out(_) => None,
                                    };
                                    if let (Some(from), Some(&d)) = (from, dv.get(k as usize)) {
                                        self.edge(from, d);
                                    }
                                }
                            }
                            _ => {
                                for (i, &(src, _)) in roles.iter().enumerate() {
                                    if src && let Some(&x) = caps.get(i) {
                                        for &y in &dv {
                                            self.edge(x, y);
                                        }
                                    }
                                }
                            }
                        }
                        // Free argument slots (a named annotation): the
                        // call's arguments flow into them.
                        if let Some(vars) = vars
                            && let Some(inputs) = self.p.gx.closures.get(&def).map(|c| c.inputs.clone())
                        {
                            let mut at = 0usize;
                            for (k, it) in inputs.into_iter().enumerate() {
                                let n = self.sc.slots(it) as usize;
                                if let (Some((at_ty, av)), Some(pv)) = (avs.get(1 + k), vars.get(at..at + n)) {
                                    let pv = pv.to_vec();
                                    if !av.is_empty() {
                                        self.relate(*at_ty, av, it, &pv, Variance::Co);
                                    }
                                }
                                at += n;
                            }
                        }
                    }
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
            _ if matches!(target, CallTarget::Builtin(b) if item_builtin(b) && self.call_item(b, &avs, dt, &dv)) => {}
            _ if matches!(target, CallTarget::Builtin(b) if item_builtin(b)) => {
                // Items the receiver cannot name slot by slot (a `map`
                // closure makes them): an item (or a collection of items)
                // borrows what the iterator's sources borrow, not the
                // temporary `&mut` of the iterator; a closure that returns
                // borrows adds its sources. W-STD-A, ty/iter.rs.
                // An item that holds `&mut` (`iter_mut`) is invariant in
                // what it points to: the element regions equal the
                // iterator's, and only the loan regions flow into the
                // item's top-level references (else a write through the
                // item could store a shorter borrow, rustc E0597).
                let mutable = has_mut_ref(&self.body.tys, dt);
                let (mut from, mut loans): (Vec<u32>, Vec<u32>) = (Vec::new(), Vec::new());
                for (t, v) in &avs {
                    let (inner, vars) = match self.body.tys.kind(*t) {
                        TyKind::Ref(_, _, inner) if !v.is_empty() => (inner, &v[1..]),
                        _ => (*t, &v[..]),
                    };
                    if mutable {
                        self.iter_slot_split(inner, vars, &mut 0, &mut loans, &mut from);
                    } else {
                        self.non_closure_slots(inner, vars, &mut 0, &mut from);
                    }
                }
                if mutable {
                    let (mut tops, mut rest) = (Vec::new(), Vec::new());
                    self.item_slot_split(dt, &dv, &mut 0, &mut tops, &mut rest);
                    loans.extend(from.iter().copied());
                    self.flow_all(&loans, &tops);
                    from.append(&mut rest);
                    self.equate_all(&from, &[]);
                } else {
                    self.flow_all(&from, &dv);
                }
                // An item that can write through shared memory (`&RefCell`)
                // is its source's own regions, both ways.
                if has_interior(&self.body.tys, dt) {
                    self.flow_all(&dv, &from);
                }
            }
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::Clone)) && self.call_clone(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::ConvDeref | crate::check::Builtin::ConvRcInner))
                && self.call_conv_deref(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::MemReplace | crate::check::Builtin::MemSwap))
                && self.call_mem(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::IterFold)) && self.call_fold(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(b) if receiver_builtin(b)) && self.call_receiver(&avs, dt, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::Clone))
                && let [(at, av)] = avs.as_slice()
                && let TyKind::Ref(_, _, inner) = self.body.tys.kind(*at)
                && inner == dt
                && !av.is_empty()
                && self.relate(inner, &av[1..], dt, &dv, Variance::Co) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::HashIterNew)) && self.call_hash_iter(&avs, dt, &dv) => {}
            _ if let CallTarget::Builtin(b) = target
                && entry_builtin(b)
                && self.call_hash_entry(b, &avs, &dv) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::HashExtend)) && self.call_hash_extend(&avs) => {}
            _ if matches!(target, CallTarget::Builtin(crate::check::Builtin::CowToMut)) && self.call_cow_to_mut(&avs, &dv) => {}
            // A map or set lookup (W-STD-B) reads its `&Q` key during the
            // call only: the opaque rule over the receiver alone.
            _ if matches!(target, CallTarget::Builtin(b) if hash_lookup_builtin(b)) && !avs.is_empty() => {
                self.call_opaque(&avs[..1], dt, &dv)
            }
            _ if matches!(target, CallTarget::Builtin(_)) && matches!(self.body.tys.builtin_of(dt), Some(BuiltinTy::Iter(_))) => {
                self.call_adapter(&avs, dt, &dv);
            }
            // `Rc::downgrade(&Rc<T>) -> Weak<T>` and `Weak::upgrade(&Weak<T>)
            // -> Option<Rc<T>>` share `T`; the borrow of the argument is
            // not part of the result (rustc's signatures).
            _ if let CallTarget::Builtin(
                crate::check::Builtin::RcDowngrade
                | crate::check::Builtin::WeakUpgrade
                | crate::check::Builtin::Sync(crate::check::sync::SyncOp::ArcDowngrade | crate::check::sync::SyncOp::ArcWeakUpgrade),
            ) = target
                && let [(at, av)] = avs.as_slice()
                && let TyKind::Ref(_, _, inner) = self.body.tys.kind(*at)
                && let Some(el) = self.body.tys.rc_elem(inner).or_else(|| self.body.tys.weak_elem(inner)).or_else(|| self.body.tys.arc_weak_elem(inner))
                && let Some(rl) = self
                    .body
                    .tys
                    .weak_elem(dt)
                    .or_else(|| self.body.tys.arc_weak_elem(dt))
                    .or_else(|| self.body.tys.option_elem(dt).and_then(|o| self.body.tys.rc_elem(o)))
                && rl == el
                && !av.is_empty()
                && self.relate(el, &av[1..], rl, &dv, Variance::Co) => {}
            _ if let CallTarget::Builtin(b) = target
                && self.call_cell(b, &avs, dt, &dv) => {}
            _ if let CallTarget::Builtin(b) = target
                && self.call_tls(b, &avs, dt, &dv) => {}
            _ => {
                self.call_opaque(&avs, dt, &dv);
                if matches!(target, CallTarget::Fn(_)) {
                    self.link_closure_args(&avs, None, &[]);
                }
            }
        }
    }

    /// `fold(init, f)`: the result is the initial value or what the body
    /// returns (the closure's sources, which `call` added from its
    /// requirements); the iterator's own borrow reaches it only through
    /// the body. False when the closure's body does not solve.
    fn call_fold(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let [_, (it, iv), (ct, _)] = avs else { return false };
        let TyKind::Closure(def, args) = self.body.tys.kind(*ct) else { return false };
        let mut roles = Vec::new();
        closure_roles(&mut self.sc, args, &mut roles);
        self.closure_reqs(def, &roles).is_some() && (iv.is_empty() || self.relate(*it, iv, dt, dv, Variance::Co))
    }

    /// `as_ref`, `borrow`, and `deref` to a pointee (`ConvDeref`,
    /// `ConvRcInner`): `&'r C` to `&T`, where `C` is a `Box<T>`, an
    /// `Rc<T>`, or a `&'c T`. The result borrows the receiver for `'r`
    /// (and `'c`), and `T`'s own regions carry over; the opaque rule would
    /// tie the receiver's borrow to all of them, a box's `'static` object
    /// lifetime included. False when the shapes differ.
    fn call_conv_deref(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let [(t0, v0)] = avs else { return false };
        let (TyKind::Ref(_, _, c), TyKind::Ref(_, _, di)) = (self.body.tys.kind(*t0), self.body.tys.kind(dt)) else { return false };
        let (Some((&r, cv)), Some((&d0, dvi))) = (v0.split_first(), dv.split_first()) else { return false };
        let (inner, iv) = match self.body.tys.kind(c) {
            TyKind::Ref(_, _, i) => {
                let Some((&cr, rest)) = cv.split_first() else { return false };
                self.edge(cr, d0);
                (i, rest)
            }
            _ => match self.body.tys.smart_elem(c) {
                Some(i) if adt_regions(self.p, &self.body.tys, c) == 0 => (i, cv),
                _ => return false,
            },
        };
        self.edge(r, d0);
        (iv.is_empty() && dvi.is_empty()) || self.relate(inner, iv, di, dvi, Variance::Co)
    }

    /// `mem::replace(dest, src)` and `mem::swap(a, b)`: values trade places
    /// through the `&mut`, whose own region reaches neither. The old value
    /// (the pointee's regions) is the result, and the new one takes the
    /// pointee's regions. False when the shapes differ.
    fn call_mem(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        match avs {
            [(rt, rv), (st, sv)] if matches!(self.body.tys.kind(*st), TyKind::Ref(_, Mut::Mut, _)) => {
                // swap
                let (TyKind::Ref(_, _, a), TyKind::Ref(_, _, b)) = (self.body.tys.kind(*rt), self.body.tys.kind(*st)) else { return false };
                let (Some((_, av)), Some((_, bv))) = (rv.split_first(), sv.split_first()) else { return false };
                let (av, bv) = (av.to_vec(), bv.to_vec());
                (av.is_empty() && bv.is_empty()) || (self.relate(a, &av, b, &bv, Variance::Co) && self.relate(b, &bv, a, &av, Variance::Co))
            }
            [(rt, rv), (st, sv)] => {
                let TyKind::Ref(_, _, inner) = self.body.tys.kind(*rt) else { return false };
                let Some((_, pv)) = rv.split_first() else { return false };
                let pv = pv.to_vec();
                (sv.is_empty() || self.relate(*st, sv, inner, &pv, Variance::Co)) && (dv.is_empty() || self.relate(inner, &pv, dt, dv, Variance::Co))
            }
            _ => false,
        }
    }

    /// `Clone::clone(&self) -> Self` (derived and builtin clones): the
    /// result has the receiver's pointee type and its regions; the borrow
    /// of the receiver ends with the call. False when the shapes differ.
    fn call_clone(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let [(t0, v0)] = avs else { return false };
        let TyKind::Ref(_, _, x) = self.body.tys.kind(*t0) else { return false };
        !v0.is_empty() && self.relate(x, &v0[1..], dt, dv, Variance::Co)
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
            _ => tys
                .vec_elem(x)
                .or_else(|| tys.lock_elem(x).map(|l| l.1))
                .or_else(|| tys.poison_elem(x))
                .or_else(|| {
                    matches!(crate::ty::sync::sync_kind(tys, x), Some(crate::ty::sync::SyncTy::Receiver | crate::ty::sync::SyncTy::OnceLock))
                        .then(|| tys.adt_first_ty_arg(x))
                        .flatten()
                })
                .or_else(|| {
                    let (k, a) = crate::ty::iter::iter_parts(tys, x)?;
                    (k == crate::ty::iter::IterKind::VecDrain).then(|| a[0])
                }),
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

    /// The `Cell` and `RefCell` builtins on a `&Cell<T>` or `&RefCell<T>`
    /// receiver (W-STD-A). Interior mutability stores through a shared
    /// reference, so a stored value flows into the cell's `T` slots as
    /// through `&mut`; a read flows out of them; a guard's `T` is the
    /// cell's (`RefMut` invariantly) behind the guard's own region, which
    /// the borrow of the cell outlives. False for any other call (the
    /// caller goes on).
    fn call_cell(&mut self, b: crate::check::Builtin, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        use crate::check::Builtin as B;
        if !matches!(
            b,
            B::RefCellBorrow
                | B::RefCellBorrowMut
                | B::RefCellTryBorrow
                | B::RefCellTryBorrowMut
                | B::CellGet
                | B::CellSet
                | B::CellReplace
                | B::RefCellReplace
                | B::CellSwap
                | B::RefCellSwap
                | B::CellTake
                | B::RefCellTake
        ) {
            return false;
        }
        let tys = &self.body.tys;
        let Some((rt, rv)) = avs.first() else { return false };
        let TyKind::Ref(_, _, cell) = tys.kind(*rt) else { return false };
        let Some(elem) = tys.cell_elem(cell).or_else(|| tys.refcell_elem(cell)) else { return false };
        if rv.is_empty() {
            return false;
        }
        let tv = rv[1..].to_vec();
        match b {
            // A try form's `Result<Ref<T>, E>` starts with the guard's
            // slots; the error type has none.
            B::RefCellBorrow | B::RefCellBorrowMut | B::RefCellTryBorrow | B::RefCellTryBorrowMut => {
                let Some(&g) = dv.first() else { return true };
                self.edge(rv[0], g);
                let v = if matches!(b, B::RefCellBorrowMut | B::RefCellTryBorrowMut) { Variance::Inv } else { Variance::Co };
                if !self.relate(elem, &tv, elem, &dv[1..], v) {
                    self.equate_all(&tv, &dv[1..]);
                }
            }
            B::CellSwap | B::RefCellSwap => {
                if let Some((_, ov)) = avs.get(1)
                    && ov.len() == rv.len()
                    && !self.relate(elem, &tv, elem, &ov[1..], Variance::Inv)
                {
                    self.equate_all(&tv, &ov[1..]);
                }
            }
            _ => {
                // `set` and `replace` store their argument; `get`,
                // `replace`, and `take` hand back a value out of the cell.
                if let Some((xt, xv)) = avs.get(1)
                    && !self.relate(*xt, xv, elem, &tv, Variance::Co)
                {
                    self.flow_all(xv, &tv);
                }
                if !self.relate(elem, &tv, dt, dv, Variance::Co) {
                    self.flow_all(&tv, dv);
                }
            }
        }
        true
    }

    /// The `LocalKey` method builtins (W-TLS, check/tls.rs). A key's
    /// value type is a static's type, so each of its regions is
    /// `'static` (the erased type does not say so: pin them here). `set`
    /// and `replace` on a `Cell` or `RefCell` key move their argument
    /// into the thread's value, so it flows into those slots, as a store
    /// through `Cell::set` does (`call_cell`). The rest is the opaque
    /// rule. False for any other call (the caller goes on).
    fn call_tls(&mut self, b: crate::check::Builtin, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        use crate::check::Builtin as B;
        if !crate::lower::tls::is_key_method(b) {
            return false;
        }
        let tys = &self.body.tys;
        let Some((kt, kv)) = avs.first() else { return false };
        let TyKind::Ref(_, _, key) = tys.kind(*kt) else { return false };
        let Some(t) = tys.local_key_elem(key) else { return false };
        let u = tys.cell_elem(t).or_else(|| tys.refcell_elem(t));
        let tv = kv.get(1..).unwrap_or_default().to_vec();
        for &v in &tv {
            self.edge(v, 0);
        }
        // `Cell<U>` and `RefCell<U>` carry no regions of their own.
        if matches!(b, B::TlsSet | B::TlsReplace)
            && let Some(u) = u
            && let Some((xt, xv)) = avs.get(1)
            && !self.relate(*xt, xv, u, &tv, Variance::Co)
        {
            self.flow_all(xv, &tv);
        }
        self.call_opaque(avs, dt, dv);
        true
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
        // A fallback flow into an adapter that can write through shared
        // memory goes both ways (see `has_interior`).
        let interior = has_interior(&self.body.tys, dt);
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
                        if interior {
                            self.flow_all(dv, v);
                        }
                    }
                }
                None => {
                    self.flow_all(v, dv);
                    if interior {
                        self.flow_all(dv, v);
                    }
                }
            }
        }
    }

    /// The vars of the slots of `t` (laid out from `*at` in `vars`) that do
    /// not sit inside a closure type, plus the captured sources of the
    /// closures that return borrows.
    fn non_closure_slots(&mut self, t: Ty, vars: &[u32], at: &mut usize, out: &mut Vec<u32>) {
        let n = self.sc.slots(t) as usize;
        if let TyKind::Closure(..) = self.body.tys.kind(t) {
            // A closure that returns borrows: the items may hold its
            // captured sources (`map(|i| &v[i])`).
            self.closure_sources(t, vars, at, out);
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

    /// Closure `def` at its creating statement (`force`), or at its first
    /// use (a closure with no captures has no creating statement): makes
    /// its argument vars once, and adds its body's requirements over the
    /// captured slots `caps` (`closure_reqs`), else the contract edges.
    fn closure_created(&mut self, def: DefId, roles: &[(bool, bool)], caps: &[u32], force: bool) -> Option<Vec<u32>> {
        let first = self.created.insert(def, ()).is_none();
        if !first && !force {
            return self.closure_args.get(&def).cloned();
        }
        let reqs = self.closure_reqs(def, roles);
        if reqs.is_none() {
            self.contract_edges(roles, caps);
        }
        let vars = self.make_arg_vars(def, roles, caps, reqs.is_none());
        for &(a, b) in reqs.iter().flat_map(|r| r.iter()) {
            let var = |e: End| match e {
                End::Static => Some(0),
                End::Cap(i) => caps.get(i as usize).copied(),
                End::Arg(j) => vars.as_ref().and_then(|v| v.get(j as usize)).copied(),
                // What a call's result holds: the call's rule.
                End::Out(_) => None,
            };
            if let (Some(x), Some(y)) = (var(a), var(b)) {
                self.edge(x, y);
            }
        }
        vars
    }

    /// The argument slot vars of closure `def` (`closure_created` at its
    /// first sight). None for a closure whose arguments are higher-ranked.
    fn closure_arg_vars(&mut self, def: DefId, roles: &[(bool, bool)], caps: &[u32]) -> Option<Vec<u32>> {
        self.closure_created(def, roles, caps, false)
    }

    /// What the body of closure `def` needs between its captured and free
    /// argument regions and `'static` (rustc's closure requirements): the
    /// body solves on its own and does not report those relations; its
    /// creator adds them. None for a closure with no such region, or when
    /// the body does not check or lower (its own check reports that).
    fn closure_reqs(&mut self, def: DefId, roles: &[(bool, bool)]) -> Option<std::rc::Rc<Vec<(End, End)>>> {
        if let Some(r) = self.closure_reqs.get(&def) {
            return r.clone();
        }
        let c = self.p.gx.closures.get(&def)?;
        let free = matches!(closure_arg_slots(&mut self.sc, c), Ok(v) if v.iter().any(|(r, _)| r.is_some()));
        let r = if free || !roles.is_empty() {
            // `check_fn` of a closure is its enclosing fn's check.
            let cf = c.body_fn;
            let mut root = c.parent;
            while let Some(e) = self.p.gx.closure_fns.get(&root).and_then(|d| self.p.gx.closures.get(d)) {
                root = e.parent;
            }
            if self.root_check.as_ref().is_none_or(|(r, _)| *r != root) {
                let (checked, errs) = crate::check::check_fn(self.p, root);
                self.root_check = Some((root, (errs.is_empty() && !checked.poisoned).then_some(checked)));
            }
            match self.root_check.as_ref().and_then(|(_, c)| c.clone()) {
                Some(checked) => {
                    let body = crate::lower::lower(self.p, cf, checked);
                    super::closure_requirements(self.p, &body).map(std::rc::Rc::new)
                }
                None => None,
            }
        } else {
            None
        };
        self.closure_reqs.insert(def, r.clone());
        r
    }

    /// `map.iter()` and kin (W-STD-B): the iterator's own region is
    /// outlived by the map borrow, and its key and value regions follow
    /// the map's (the values invariantly for `iter_mut` and
    /// `values_mut`, which hand out `&mut V`). False (nothing added) for
    /// the by-value forms, which take the opaque rule.
    fn call_hash_iter(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        use crate::ty::iter::IterKind as K;
        let Some((t0, v0)) = avs.first() else { return false };
        let TyKind::Ref(_, _, map) = self.body.tys.kind(*t0) else { return false };
        let Some((ik, _)) = crate::ty::iter::iter_parts(&self.body.tys, dt) else { return false };
        let Some((_, margs)) = crate::ty::hash::hash_parts(&self.body.tys, map) else { return false };
        let (Some((&r, mv)), Some((&i, iv))) = (v0.split_first(), dv.split_first()) else { return false };
        let parts: Vec<(Ty, usize)> =
            margs.iter().take(if ik == K::SetIter { 1 } else { 2 }).map(|&t| (t, self.sc.slots(t) as usize)).collect();
        let n: usize = parts.iter().map(|p| p.1).sum();
        if mv.len() < n || iv.len() < n {
            return false;
        }
        self.edge(r, i);
        let mut at = 0;
        for (j, (t, n)) in parts.into_iter().enumerate() {
            let var = if j == 1 && matches!(ik, K::MapIterMut | K::MapValuesMut) { Variance::Inv } else { Variance::Co };
            let (a, b) = (mv[at..at + n].to_vec(), iv[at..at + n].to_vec());
            self.relate(t, &a, t, &b, var);
            at += n;
        }
        true
    }

    /// The Entry API (W-STD-B): `map.entry(k)` holds the `&'a mut` loan
    /// and the map's K and V regions (invariant: it can insert, and the
    /// probe key flows into K); the `&'a mut V` an Entry method returns
    /// is that loan's, with the map's V regions; `and_modify` gives the
    /// same Entry back. A stored value (`or_insert`'s argument) and a
    /// closure form's closure (all its regions) flow into V. The keys'
    /// regions never reach the loan.
    fn call_hash_entry(&mut self, b: crate::check::Builtin, avs: &[(Ty, Vec<u32>)], dv: &[u32]) -> bool {
        use crate::check::Builtin as B;
        use crate::ty::hash::hash_parts;
        let Some((t0, v0)) = avs.first() else { return false };
        // The Entry (or, for `entry`, the map behind its `&mut`) and its K, V.
        let (holder, entry_args) = if b == B::MapEntry {
            let TyKind::Ref(_, _, map) = self.body.tys.kind(*t0) else { return false };
            (map, hash_parts(&self.body.tys, map))
        } else {
            (*t0, hash_parts(&self.body.tys, *t0))
        };
        let _ = holder;
        let Some((_, ka)) = entry_args else { return false };
        let (Some(&kt), Some(&vt)) = (ka.first(), ka.get(1)) else { return false };
        let (nk, nv) = (self.sc.slots(kt) as usize, self.sc.slots(vt) as usize);
        let (Some((&own, hv)), Some((&dst, rv))) = (v0.split_first(), dv.split_first()) else { return false };
        if hv.len() < nk + nv {
            return false;
        }
        let (hk, hvv) = (hv[..nk].to_vec(), hv[nk..nk + nv].to_vec());
        self.edge(own, dst);
        match b {
            B::MapEntry | B::EntryAndModify => {
                if rv.len() < nk + nv {
                    return false;
                }
                let (rk, rvv) = (rv[..nk].to_vec(), rv[nk..nk + nv].to_vec());
                self.relate(kt, &hk, kt, &rk, Variance::Inv);
                self.relate(vt, &hvv, vt, &rvv, Variance::Inv);
                if b == B::MapEntry
                    && let Some((t1, v1)) = avs.get(1)
                {
                    self.relate(*t1, v1, kt, &rk, Variance::Co);
                }
            }
            _ => {
                if rv.len() < nv {
                    return false;
                }
                self.relate(vt, &hvv, vt, &rv[..nv], Variance::Inv);
                if let Some((t1, v1)) = avs.get(1) {
                    if b == B::EntryOrInsert {
                        self.relate(*t1, v1, vt, &hvv, Variance::Co);
                    } else {
                        self.flow_all(v1, &hvv);
                    }
                }
            }
        }
        if b == B::EntryAndModify
            && let Some((_, v1)) = avs.get(1)
        {
            self.flow_all(v1, &hvv);
        }
        true
    }

    /// `cow.to_mut()` (W-STD-B): `&'r mut Owned` from `&'x mut Cow<'a,
    /// B>`. The loan outlives the result, and the Owned value's regions
    /// are B's (one invariant class, as behind `&mut`). The Cow's own
    /// `'a` does not reach the result: after the call it is Owned and
    /// holds no borrow of `'a` data.
    fn call_cow_to_mut(&mut self, avs: &[(Ty, Vec<u32>)], dv: &[u32]) -> bool {
        let Some((_, v0)) = avs.first() else { return false };
        let (Some((&x, cv)), Some((&r, ov))) = (v0.split_first(), dv.split_first()) else { return false };
        let Some(b_slots) = cv.get(1..) else { return false };
        self.edge(x, r);
        let mut class = b_slots.to_vec();
        class.extend_from_slice(ov);
        self.equate_all(&class, &[]);
        true
    }

    /// `table.extend(iter)` (W-STD-B): the items' regions outlive the
    /// table's element regions; the iterator's own loans do not reach
    /// the table unless an item holds them. False (nothing added) when
    /// the item's regions cannot be read off the iterator type.
    fn call_hash_extend(&mut self, avs: &[(Ty, Vec<u32>)]) -> bool {
        let [(t0, v0), (it, iv)] = avs else { return false };
        let TyKind::Ref(_, _, table) = self.body.tys.kind(*t0) else { return false };
        let Some((kind, targs)) = crate::ty::hash::hash_parts(&self.body.tys, table) else { return false };
        let parts = if kind == crate::ty::hash::HashTy::HashMap { 2 } else { 1 };
        let n: usize = targs.iter().take(parts).map(|&t| self.sc.slots(t) as usize).sum();
        let Some(ev) = v0.get(1..1 + n) else { return false };
        let ev = ev.to_vec();
        // A Vec, array, slice, map, or set argument: its elements' slots
        // lead its own (after the borrow for `&C`, whose items are copied).
        let tys = &self.body.tys;
        let container = |c: Ty| {
            tys.vec_elem(c).is_some()
                || matches!(tys.kind(c), TyKind::Array(..) | TyKind::Slice(_))
                || crate::ty::hash::hash_parts(tys, c).is_some()
        };
        let skip = match tys.kind(*it) {
            TyKind::Ref(_, _, c) if container(c) => Some(1),
            _ if container(*it) => Some(0),
            _ => None,
        };
        if let Some(skip) = skip {
            let Some(part) = iv.get(skip..skip + n) else { return false };
            let part = part.to_vec();
            self.flow_all(&part, &ev);
            return true;
        }
        let Some(item_vars) = self.item_slots(*it, iv) else { return false };
        // `Extend<&T>` and `Extend<(&K, &V)>` copy the parts in: each part
        // has one more (leading) region, the borrow, which does not flow.
        let item_vars = if item_vars.len() == n + parts {
            let mut out = Vec::new();
            let mut at = 0;
            for &t in targs.iter().take(parts) {
                let k = self.sc.slots(t) as usize;
                let Some(part) = item_vars.get(at + 1..at + 1 + k) else { return false };
                out.extend_from_slice(part);
                at += 1 + k;
            }
            out
        } else {
            item_vars
        };
        self.flow_all(&item_vars, &ev);
        true
    }

    /// The region slots of an iterator type's item, read off the
    /// iterator's own slots (`vars`, in slot order), for the builtin
    /// kinds whose item is made of parts of the iterator type. None for
    /// the rest (`Chain` mixes two sources).
    fn item_slots(&mut self, t: Ty, vars: &[u32]) -> Option<Vec<u32>> {
        use crate::ty::iter::IterKind as K;
        if self.body.tys.is_chars_ty(t) {
            return Some(Vec::new());
        }
        let (k, a) = crate::ty::iter::iter_parts(&self.body.tys, t)?;
        let mut at = adt_regions(self.p, &self.body.tys, t) as usize;
        let own: Vec<u32> = vars.get(..at)?.to_vec();
        let mut args: Vec<Vec<u32>> = Vec::new();
        for &x in &a {
            let n = self.sc.slots(x) as usize;
            args.push(vars.get(at..at + n)?.to_vec());
            at += n;
        }
        let cat = |parts: &[&[u32]]| parts.concat();
        Some(match k {
            K::SliceIter | K::SliceIterMut | K::Windows => cat(&[&own, &args[0]]),
            K::VecIntoIter | K::Range | K::RangeInclusive | K::VecDrain => args[0].clone(),
            K::Map | K::FilterMap => args[2].clone(),
            K::Copied | K::Cloned => args[1].clone(),
            K::Filter | K::Rev | K::Take | K::Skip | K::TakeWhile | K::SkipWhile | K::StepBy | K::Peekable | K::Inspect | K::Enumerate => {
                self.item_slots(a[0], &args[0])?
            }
            K::Zip => {
                let x = self.item_slots(a[0], &args[0])?;
                let y = self.item_slots(a[1], &args[1])?;
                cat(&[&x, &y])
            }
            K::Chain => return None,
            K::MapIter | K::MapIterMut => cat(&[&own, &args[0], &own, &args[1]]),
            K::MapKeys | K::SetIter => cat(&[&own, &args[0]]),
            K::MapValues | K::MapValuesMut => cat(&[&own, &args[1]]),
            K::MapIntoIter => cat(&[&args[0], &args[1]]),
            K::MapIntoKeys | K::SetIntoIter | K::RepeatN | K::ArrayIntoIter => args[0].clone(),
            K::MapIntoValues | K::ByNext => args[1].clone(),
            // (usize, char): no regions.
            K::CharIndices | K::StringDrain => Vec::new(),
            // Range kinds that are `RangeBounds` values here, not iterators.
            K::RangeFrom | K::RangeTo | K::RangeFull | K::RangeToInclusive => return None,
            K::Flatten => self.item_slots(a[1], &args[1])?,
            K::OptionIntoIter => args[0].clone(),
            // `&'a str` of the haystack (W-STD-B).
            K::StrSplit => own,
            // An mpsc receiver's items are its `T` values (W-THREADS).
            K::RecvIter | K::RecvTryIter | K::RecvIntoIter => args[0].clone(),
        })
    }

    /// Splits an iterator argument's slots (in `non_closure_slots`
    /// order) into the loan regions of the builtin iterator structs in
    /// it (their `adt_regions` slots) and the element regions (every
    /// other slot). Closures are skipped.
    fn iter_slot_split(&mut self, t: Ty, vars: &[u32], at: &mut usize, loans: &mut Vec<u32>, elems: &mut Vec<u32>) {
        let TyKind::Adt(_, args) = self.body.tys.kind(t) else {
            return self.non_closure_slots(t, vars, at, elems);
        };
        if !crate::ty::iter::is_iter(&self.body.tys, t) {
            return self.non_closure_slots(t, vars, at, elems);
        }
        for _ in 0..adt_regions(self.p, &self.body.tys, t) {
            if let Some(&v) = vars.get(*at) {
                loans.push(v);
            }
            *at += 1;
        }
        for g in self.body.tys.args(args).to_vec() {
            if let GenericArg::Ty(e) = g {
                self.iter_slot_split(e, vars, at, loans, elems);
            }
        }
    }

    /// Splits a result type's slots into its top-level reference regions
    /// (references reached through tuples, arrays, and Adt args without
    /// passing another reference, and builtin structs' own regions) and
    /// the rest.
    fn item_slot_split(&mut self, t: Ty, vars: &[u32], at: &mut usize, tops: &mut Vec<u32>, rest: &mut Vec<u32>) {
        let take = |at: &mut usize, n: usize, out: &mut Vec<u32>| {
            out.extend(vars.iter().skip(*at).take(n).copied());
            *at += n;
        };
        match self.body.tys.kind(t) {
            TyKind::Ref(_, _, inner) => {
                take(at, 1, tops);
                let n = self.sc.slots(inner) as usize;
                take(at, n, rest);
            }
            TyKind::Adt(_, args) => {
                let n = adt_regions(self.p, &self.body.tys, t) as usize;
                take(at, n, tops);
                for g in self.body.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.item_slot_split(e, vars, at, tops, rest);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.body.tys.tys_of(ts).to_vec() {
                    self.item_slot_split(e, vars, at, tops, rest);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => self.item_slot_split(e, vars, at, tops, rest),
            _ => {
                let n = self.sc.slots(t) as usize;
                take(at, n, rest);
            }
        }
    }

    /// The argument slot vars of a closure with free arguments, made at
    /// its creation with the contract edges between them and the
    /// closure's captured slots (`caps`, roles `roles`; not when
    /// `contract` is false: the creator adds the body's requirements).
    /// None for a closure whose arguments are higher-ranked.
    fn make_arg_vars(&mut self, def: DefId, roles: &[(bool, bool)], caps: &[u32], contract: bool) -> Option<Vec<u32>> {
        if let Some(v) = self.closure_args.get(&def) {
            return Some(v.clone());
        }
        let c = self.p.gx.closures.get(&def)?;
        let slots = match closure_arg_slots(&mut self.sc, c) {
            Ok(s) => s,
            Err(()) => {
                self.errs.push(Diag::new(
                    "L0203",
                    self.span,
                    "an explicit lifetime in this closure parameter's annotation is not supported yet",
                    "Drop the lifetime from the annotation, or write `'_`.",
                ));
                return None;
            }
        };
        if slots.iter().all(|(r, _)| r.is_none()) {
            return None;
        }
        let arg_roles: Vec<Option<(bool, bool)>> = slots.iter().map(|&(r, _)| r).collect();
        let vars: Vec<u32> = arg_roles.iter().map(|_| self.fresh()).collect();
        // A slot the annotation names is that region of the creator; only
        // the creating body has those universals (another body that calls
        // the closure, an instance of a generic callee, ties nothing).
        let creator = c.parent == self.body.fn_id
            || self.p.gx.instances.get(&self.body.fn_id).and_then(|i| i.template_local) == Some(c.parent);
        for (i, &(_, link)) in slots.iter().enumerate() {
            let u = match link {
                Some(Region::Static) => Some(0),
                Some(Region::Param(k)) if creator && !self.own.closure && k < self.own.n_univ => Some(k + 1),
                // A generic callee's instance: the bound took this input from
                // a type param (check rejects a higher-ranked one), so the
                // creator's call already tied what flows in.
                Some(Region::Param(_)) if !creator && !self.own.closure => None,
                Some(_) => {
                    self.errs.push(Diag::new(
                        "L0203",
                        self.span,
                        "a named lifetime in a closure parameter inside a closure is not supported yet",
                        "Move the closure out of the enclosing closure, or drop the lifetime.",
                    ));
                    None
                }
                None => None,
            };
            if let Some(u) = u {
                self.edge(vars[i], u);
                self.edge(u, vars[i]);
            }
        }
        let mut srcs: Vec<u32> = Vec::new();
        let mut snks: Vec<u32> = Vec::new();
        for (i, r) in arg_roles.iter().enumerate() {
            if let Some((src, snk)) = r {
                if *src {
                    srcs.push(vars[i]);
                }
                if *snk {
                    snks.push(vars[i]);
                }
            }
        }
        let mut cap_srcs: Vec<u32> = Vec::new();
        let mut cap_snks: Vec<u32> = Vec::new();
        for (i, &(src, snk)) in roles.iter().enumerate() {
            if let Some(&v) = caps.get(i) {
                if src {
                    cap_srcs.push(v);
                }
                if snk {
                    cap_snks.push(v);
                }
            }
        }
        // Argument sources into the captured sinks, captured sources into
        // the argument sinks (capture-to-capture is `contract_edges`'; an
        // argument does not flow into an argument's `&mut` target). The
        // output is the call's: `closure_sources` covers it. Not when the
        // creator adds the body's requirements instead.
        if !contract {
            self.closure_args.insert(def, vars.clone());
            return Some(vars);
        }
        for &a in &srcs {
            for &b in &cap_snks {
                self.edge(a, b);
            }
        }
        for &a in &cap_srcs {
            for &b in &snks {
                self.edge(a, b);
            }
        }
        self.closure_args.insert(def, vars.clone());
        Some(vars)
    }

    /// A builtin taking a closure with free arguments (an iterator
    /// method): an input that is the receiver's item (or `&item`, whose
    /// outer reference is higher-ranked) takes exactly the item's regions
    /// (`iter_items`); any other free argument slot (`fold`'s accumulator,
    /// an item the receiver cannot name, `b` None for a generic fn that did
    /// not pair) may hold any region of the call's other arguments, and a
    /// sink slot writes back into them. Closures in `skip` are linked
    /// already (`link_bound_closure`).
    fn link_closure_args(&mut self, avs: &[(Ty, Vec<u32>)], b: Option<crate::check::Builtin>, skip: &[DefId]) {
        let mut cands: Vec<Vec<u32>> = Vec::new();
        if b.is_some()
            && let Some((t0, v0)) = avs.first()
        {
            let (it, iv) = match self.body.tys.kind(*t0) {
                TyKind::Ref(_, _, inner) if !v0.is_empty() => (inner, v0[1..].to_vec()),
                _ => (*t0, v0.clone()),
            };
            if !self.iter_items(it, &iv, &mut cands) {
                cands.clear();
            }
        }
        for (k, (t, v)) in avs.iter().enumerate() {
            let TyKind::Closure(def, args) = self.body.tys.kind(*t) else { continue };
            if skip.contains(&def) {
                continue;
            }
            let Some(c) = self.p.gx.closures.get(&def) else { continue };
            let Ok(slots) = closure_arg_slots(&mut self.sc, c) else { continue };
            let inputs = c.inputs.clone();
            let c_output = c.output;
            let mut roles = Vec::new();
            closure_roles(&mut self.sc, args, &mut roles);
            let Some(vars) = self.closure_arg_vars(def, &roles, v) else { continue };
            let arg_roles: Vec<Option<(bool, bool)>> = slots.into_iter().map(|(r, _)| r).collect();
            let mut items: Vec<u32> = Vec::new();
            let mut elems: Vec<u32> = Vec::new();
            for (j, (ot, ov)) in avs.iter().enumerate() {
                if j != k {
                    self.non_closure_slots(*ot, ov, &mut 0, &mut items);
                    self.elem_slots(*ot, ov, &mut 0, &mut elems);
                    self.closure_sources(*ot, ov, &mut 0, &mut elems);
                }
            }
            let mut at = 0usize;
            for (pi, &pt) in inputs.iter().enumerate() {
                let n = self.sc.slots(pt) as usize;
                let range = at..(at + n).min(vars.len());
                at += n;
                // `filter(|x| ..)` takes `&Self::Item`: the method's own
                // borrow, higher-ranked in its bound.
                if k > 0 && by_ref_item(b) && n > 0 && arg_roles.get(range.start).is_some_and(|r| r.is_some()) {
                    self.not_general_enough();
                    continue;
                }
                // `fold`'s accumulator: the initial value, then what the
                // body returns (`closure_reqs`), round after round.
                if k == 2
                    && pi == 0
                    && b == Some(crate::check::Builtin::IterFold)
                    && let Some((it0, iv0)) = avs.get(1)
                    && self.sc.slots(c_output) as usize == n
                    && let Some(reqs) = self.closure_reqs(def, &roles)
                {
                    let pv: Vec<u32> = vars.get(range.clone()).map(<[u32]>::to_vec).unwrap_or_default();
                    // A constant initial value (`""`) holds no loan.
                    if pv.len() == n && (iv0.is_empty() || self.relate(*it0, iv0, pt, &pv, Variance::Co)) {
                        for &(x, y) in reqs.iter() {
                            let End::Out(q) = y else { continue };
                            let from = match x {
                                End::Cap(i) => v.get(i as usize).copied(),
                                End::Arg(j) => vars.get(j as usize).copied(),
                                End::Static | End::Out(_) => None,
                            };
                            if let (Some(from), Some(&a)) = (from, pv.get(q as usize)) {
                                self.edge(from, a);
                            }
                        }
                        continue;
                    }
                }
                let item_param = k > 0 && !cands.is_empty() && !(b == Some(crate::check::Builtin::IterFold) && pi == 0);
                if item_param {
                    let want = cands[0].len();
                    let (ity, skip) = match self.body.tys.kind(pt) {
                        TyKind::Ref(_, _, inner) if n == want + 1 && arg_roles.get(range.start).is_some_and(|r| r.is_none()) => (inner, 1),
                        _ => (pt, 0),
                    };
                    let pv: Vec<u32> = vars.get(range.start + skip..range.end).map(<[u32]>::to_vec).unwrap_or_default();
                    if pv.len() + skip == n && cands.iter().all(|c| c.len() == pv.len()) {
                        for c in cands.clone() {
                            self.relate(ity, &c, ity, &pv, Variance::Co);
                        }
                        continue;
                    }
                }
                for i in range {
                    let (Some((_, snk)), Some(&a)) = (arg_roles.get(i).copied().flatten(), vars.get(i)) else { continue };
                    if snk {
                        // Behind an item's `&mut`: the source's element regions
                        // (invariant), never the iterator's own borrow.
                        for &s in &elems {
                            self.edge(s, a);
                            self.edge(a, s);
                        }
                    } else {
                        for &s in &items {
                            self.edge(s, a);
                        }
                    }
                }
            }
        }
    }

    /// The item slots of builtin iterator type `t` (its slot vars `vars`),
    /// one candidate per source of items (`chain` has two): Rust's
    /// `Iterator::Item` of `slice::Iter<'a, T>` is `&'a T`, an adapter's
    /// is its inner iterator's, `copied`'s drops the outer reference, a
    /// `map` closure's is what its body returns (`closure_reqs`). False
    /// when the layout does not pair or the closure's body does not solve.
    fn iter_items(&mut self, t: Ty, vars: &[u32], out: &mut Vec<Vec<u32>>) -> bool {
        use crate::ty::iter::IterKind as K;
        if matches!(self.body.tys.builtin_of(t), Some(BuiltinTy::Chars)) {
            out.push(Vec::new());
            return true;
        }
        let Some((k, a)) = crate::ty::iter::iter_parts(&self.body.tys, t) else { return false };
        // `string::Drain` yields owned `char`s, like `Chars`.
        if k == K::StringDrain {
            out.push(Vec::new());
            return true;
        }
        let Some(&a0) = a.first() else { return false };
        let n0 = self.sc.slots(a0) as usize;
        match k {
            // The item `&'a T` is the iterator's own slots, in order.
            K::SliceIter | K::SliceIterMut => {
                if vars.len() != 1 + n0 {
                    return false;
                }
                out.push(vars.to_vec());
                true
            }
            // `mpsc::Iter<'a, T>` holds `&'a Receiver<T>`: its own region,
            // then `T`'s slots; `IntoIter<T>` holds the receiver.
            K::RecvIter | K::RecvTryIter => match vars.get(1..1 + n0) {
                Some(v) => {
                    out.push(v.to_vec());
                    true
                }
                None => false,
            },
            K::VecIntoIter | K::Range | K::RangeInclusive | K::RecvIntoIter => match vars.get(..n0) {
                Some(v) => {
                    out.push(v.to_vec());
                    true
                }
                None => false,
            },
            // The item `T` is owned; the drain's own region slot (its
            // borrow of the Vec) comes first and is not part of it.
            K::VecDrain => match vars.get(1..1 + n0) {
                Some(v) => {
                    out.push(v.to_vec());
                    true
                }
                None => false,
            },
            K::StringDrain | K::RangeFrom | K::RangeTo | K::RangeFull | K::RangeToInclusive => false,
            K::Filter | K::Rev | K::Take | K::Skip | K::TakeWhile | K::SkipWhile | K::StepBy | K::Peekable | K::Inspect | K::Enumerate => {
                vars.get(..n0).is_some_and(|v| self.iter_items(a0, v, out))
            }
            K::Chain => {
                let Some(&a1) = a.get(1) else { return false };
                let n1 = self.sc.slots(a1) as usize;
                vars.get(..n0).is_some_and(|v| self.iter_items(a0, v, out))
                    && vars.get(n0..n0 + n1).is_some_and(|v| self.iter_items(a1, v, out))
            }
            K::Zip => {
                let Some(&a1) = a.get(1) else { return false };
                let n1 = self.sc.slots(a1) as usize;
                let (mut xs, mut ys) = (Vec::new(), Vec::new());
                if !(vars.get(..n0).is_some_and(|v| self.iter_items(a0, v, &mut xs))
                    && vars.get(n0..n0 + n1).is_some_and(|v| self.iter_items(a1, v, &mut ys)))
                {
                    return false;
                }
                for x in &xs {
                    for y in &ys {
                        out.push(x.iter().chain(y).copied().collect());
                    }
                }
                true
            }
            K::Copied | K::Cloned => {
                let mut xs = Vec::new();
                if !vars.get(..n0).is_some_and(|v| self.iter_items(a0, v, &mut xs)) || xs.iter().any(|x| x.is_empty()) {
                    return false;
                }
                out.extend(xs.into_iter().map(|x| x[1..].to_vec()));
                true
            }
            // The closure's output (`FilterMap`'s `Option<B>` has `B`'s
            // slots): what its body returns of its captured slots (laid
            // out after the inner iterator's) and its free arguments.
            K::Map | K::FilterMap => {
                let (Some(&f), Some(&bt)) = (a.get(1), a.get(2)) else { return false };
                let TyKind::Closure(def, cargs) = self.body.tys.kind(f) else { return false };
                let nf = self.sc.slots(f) as usize;
                let nb = self.sc.slots(bt) as usize;
                let Some(caps) = vars.get(n0..n0 + nf).map(<[u32]>::to_vec) else { return false };
                let mut roles = Vec::new();
                closure_roles(&mut self.sc, cargs, &mut roles);
                let Some(reqs) = self.closure_reqs(def, &roles) else { return false };
                let args = self.closure_args.get(&def).cloned().unwrap_or_default();
                let item: Vec<u32> = (0..nb).map(|_| self.fresh()).collect();
                for &(x, y) in reqs.iter() {
                    let End::Out(k) = y else { continue };
                    let from = match x {
                        End::Static => Some(0),
                        End::Cap(i) => caps.get(i as usize).copied(),
                        End::Arg(j) => args.get(j as usize).copied(),
                        End::Out(_) => None,
                    };
                    if let (Some(from), Some(&o)) = (from, item.get(k as usize)) {
                        self.edge(from, o);
                    }
                }
                out.push(item);
                true
            }
            // A user iterator through its `next` (W-STD-B): the item's own
            // slots, which its construction ties to the iterator's.
            K::ByNext => {
                let Some(&a1) = a.get(1) else { return false };
                let own = adt_regions(self.p, &self.body.tys, t) as usize;
                let n1 = self.sc.slots(a1) as usize;
                match vars.get(own + n0..own + n0 + n1) {
                    Some(v) => {
                        out.push(v.to_vec());
                        true
                    }
                    None => false,
                }
            }
            // A str split's item is `&'a str` of its haystack: the own
            // region (W-STD-B).
            K::StrSplit => match vars.first() {
                Some(&r) => {
                    out.push(vec![r]);
                    true
                }
                None => false,
            },
            // The other W-STD-B kinds (hash iterators, array::IntoIter,
            // repeat_n, Windows, CharIndices, Flatten, option::IntoIter): the
            // conservative item rule (`item_slots` for the hash forms).
            K::MapIter
            | K::MapIterMut
            | K::MapKeys
            | K::MapValues
            | K::MapValuesMut
            | K::MapIntoIter
            | K::MapIntoKeys
            | K::MapIntoValues
            | K::SetIter
            | K::SetIntoIter
            | K::ArrayIntoIter
            | K::RepeatN
            | K::Windows
            | K::CharIndices
            | K::Flatten
            | K::OptionIntoIter => false,
        }
    }

    /// An item call (`next`, `find`, `last`, `min`, `collect` into a `Vec`)
    /// over a receiver whose items `iter_items` names: the result's item
    /// takes exactly their regions, nothing of the iterator's own borrow
    /// beyond what the item holds. False (nothing added) otherwise.
    fn call_item(&mut self, b: crate::check::Builtin, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        if matches!(b, crate::check::Builtin::IterFindMap) {
            return false;
        }
        let Some((t0, v0)) = avs.first() else { return false };
        let (it, iv) = match self.body.tys.kind(*t0) {
            TyKind::Ref(_, _, inner) if !v0.is_empty() => (inner, v0[1..].to_vec()),
            _ => (*t0, v0.clone()),
        };
        use crate::ty::hash::HashTy;
        // The result's parts that hold the item: `Option<T>` and `Vec<T>`
        // hold `T`; a map or set from `collect` (W-STD-B) holds `(K, V)` or
        // `T`, and its hasher's slots (after them) are its own.
        if adt_regions(self.p, &self.body.tys, dt) != 0 {
            return false;
        }
        let Some((_, args)) = self.body.tys.adt_parts(dt) else { return false };
        let comps: Vec<Ty> = self.body.tys.args(args).iter().filter_map(|g| g.as_ty()).collect();
        let collect = b == crate::check::Builtin::IterCollect;
        let parts = match (self.body.tys.builtin_of(dt), &comps[..]) {
            (Some(BuiltinTy::Option | BuiltinTy::Vec), &[t]) => vec![t],
            (Some(BuiltinTy::Hash(HashTy::HashMap)), &[k, v, _]) if collect => vec![k, v],
            (Some(BuiltinTy::Hash(HashTy::HashSet)), &[t, _]) if collect => vec![t],
            _ => return false,
        };
        let n: usize = parts.iter().map(|&t| self.sc.slots(t) as usize).sum();
        let Some(dv) = dv.get(..n) else { return false };
        let mut cands = Vec::new();
        if !self.iter_items(it, &iv, &mut cands) || cands.is_empty() || cands.iter().any(|c| c.len() != n) {
            return false;
        }
        for c in cands {
            let mut at = 0;
            for &t in &parts {
                let k = self.sc.slots(t) as usize;
                self.relate(t, &c[at..at + k], t, &dv[at..at + k], Variance::Co);
                at += k;
            }
        }
        true
    }

    /// `non_closure_slots` without the Adts' own region slots (an
    /// iterator's borrow of its source): the regions of the elements.
    fn elem_slots(&mut self, t: Ty, vars: &[u32], at: &mut usize, out: &mut Vec<u32>) {
        let n = self.sc.slots(t) as usize;
        match self.body.tys.kind(t) {
            TyKind::Closure(..) => *at += n,
            TyKind::Ref(_, _, inner) => {
                if let Some(&v) = vars.get(*at) {
                    out.push(v);
                }
                *at += 1;
                self.elem_slots(inner, vars, at, out);
            }
            TyKind::Adt(_, args) => {
                *at += adt_regions(self.p, &self.body.tys, t) as usize;
                for g in self.body.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.elem_slots(e, vars, at, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.body.tys.tys_of(ts).to_vec() {
                    self.elem_slots(e, vars, at, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.elem_slots(e, vars, at, out),
            _ => {
                out.extend(vars.iter().skip(*at).take(n).copied());
                *at += n;
            }
        }
    }

    /// The closure contract over a closure value's slot vars: every
    /// source outlives every other sink.
    fn contract_edges(&mut self, roles: &[(bool, bool)], vars: &[u32]) {
        for (i, &(src, _)) in roles.iter().enumerate() {
            for (j, &(_, snk)) in roles.iter().enumerate() {
                if src && snk && i != j
                    && let (Some(&a), Some(&b)) = (vars.get(i), vars.get(j))
                {
                    self.edge(a, b);
                }
            }
        }
    }

    /// Whether closure `def` returns a value with regions (W-BORROW: its
    /// body's output may hold its captured sources).
    fn closure_returns_regions(&mut self, def: DefId) -> bool {
        match self.p.gx.closures.get(&def) {
            Some(c) => self.sc.slots(c.output) > 0,
            None => true,
        }
    }

    /// Adds the captured sources of each closure inside `t` (laid out from
    /// `*at` in `vars`) whose output has regions to `out`.
    fn closure_sources(&mut self, t: Ty, vars: &[u32], at: &mut usize, out: &mut Vec<u32>) {
        let n = self.sc.slots(t) as usize;
        match self.body.tys.kind(t) {
            TyKind::Closure(def, args) => {
                if self.closure_returns_regions(def) {
                    let mut roles = Vec::new();
                    closure_roles(&mut self.sc, args, &mut roles);
                    let av = self.closure_args.get(&def).cloned().unwrap_or_default();
                    match self.closure_reqs(def, &roles) {
                        // What its body returns (`closure_reqs`).
                        Some(reqs) => {
                            for &(x, y) in reqs.iter() {
                                if !matches!(y, End::Out(_)) {
                                    continue;
                                }
                                let v = match x {
                                    End::Cap(i) => vars.get(*at + i as usize).copied(),
                                    End::Arg(j) => av.get(j as usize).copied(),
                                    End::Static | End::Out(_) => None,
                                };
                                out.extend(v);
                            }
                        }
                        // Every captured source, and its free argument
                        // regions: the output may borrow from an argument
                        // (`opt.map(|e| &e.1)`).
                        None => {
                            for (i, &(src, _)) in roles.iter().enumerate() {
                                if src && let Some(&v) = vars.get(*at + i) {
                                    out.push(v);
                                }
                            }
                            out.extend(av);
                        }
                    }
                }
                *at += n;
            }
            TyKind::Ref(_, _, inner) => {
                *at += 1;
                self.closure_sources(inner, vars, at, out);
            }
            TyKind::Adt(_, args) => {
                *at += adt_regions(self.p, &self.body.tys, t) as usize;
                for g in self.body.tys.args(args).to_vec() {
                    if let GenericArg::Ty(e) = g {
                        self.closure_sources(e, vars, at, out);
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in self.body.tys.tys_of(ts).to_vec() {
                    self.closure_sources(e, vars, at, out);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.closure_sources(e, vars, at, out),
            _ => *at += n,
        }
    }

    /// The conservative call rule: the result may hold any argument's
    /// regions (equal to them when it holds a `&mut`), and each `&mut`
    /// argument's target may receive every other argument's regions.
    fn call_opaque(&mut self, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) {
        let all: Vec<u32> = avs.iter().flat_map(|(_, v)| v.iter().copied()).collect();
        if has_mut_ref(&self.body.tys, dt) || has_interior(&self.body.tys, dt) {
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
        // An `impl Trait` return captures every input region (edition
        // 2024): the call takes `call_opaque` (W-CHECK-G3).
        if p.gx.opaque_ret_of.contains_key(&f) {
            return false;
        }
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
        let mut univ: Vec<u32> = Vec::with_capacity(sig.n_univ as usize);
        for k in 0..sig.n_univ as usize {
            let v = match self.seed_univ.get(k) {
                Some(&v) => v,
                None => self.fresh(),
            };
            univ.push(v);
        }
        let mut binds: FxMap<u32, Vec<u32>> = FxMap::default();
        self.bind_tys.clear();
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
        // `T: Tr<'a>` for a trait with lifetime params: the type bound to
        // `T` implements `Tr` with exactly those lifetimes (trait args are
        // invariant), so its own (this body's bound on a type param, or the
        // selected impl's header) equal the call's `'a`; unknown ones are
        // `'static`, never free.
        for b in &sig.trait_bounds {
            let n = b.lifetimes.len();
            let want: Vec<u32> = b.lifetimes.iter().map(|&r| self.inst_region(r, &univ)).collect();
            let have = match (self.bind_tys.get(&b.param).copied(), binds.get(&b.param).cloned()) {
                (Some(t), Some(vs)) => self.trait_lts_for(b.trait_def, t, &vs, n),
                _ => None,
            }
            .unwrap_or_else(|| vec![0; n]);
            for (x, y) in want.into_iter().zip(have) {
                self.edge(x, y);
                self.edge(y, x);
            }
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
            // `P: Tr` proves more through trait selection: `Tr` (or a
            // supertrait) bounded by `'static` makes `P` `'static`, and the
            // impl selected for `P`'s type adds its own `X: 'static`
            // where-clauses on the parts of `P` they name.
            if let Predicate::Trait(b) = pred
                && b.count == 0
                && let Some(self_t) = self.p.tys.args(b.value.args).first().and_then(|g| g.as_ty())
                && let TyKind::Param(j) = self.p.tys.kind(self_t)
                && let Some(vs) = binds.get(&j.0).cloned()
            {
                if self.p.gx.dyn_infos.get(&b.value.def).is_some_and(|i| i.static_bound) {
                    for &v in &vs {
                        self.edge(v, 0);
                    }
                }
                if let Some(&actual) = self.bind_tys.get(&j.0) {
                    self.impl_static_edges(b.value.def, actual, &vs);
                }
            }
            // A closure passed for `F: Fn*(A..)`: an input that is a type
            // param there is that param's regions exactly (`&T`: past its
            // higher-ranked outer reference).
            if let Predicate::Trait(b) = pred
                && b.count == 0
                && self.p.gx.lang.is_fn_family(b.value.def)
            {
                self.link_bound_closure(b.value.args, &binds, sig, &univ);
                self.tie_bound_output(b.value.args, &binds, sig, &univ);
                self.entail_bound(b.value.args, sig, &univ);
                self.flow_bound_inputs(b.value.args, &binds, sig, &univ);
            }
        }
        ok
    }

    /// The vars a call takes for the lifetime params of the callee's trait
    /// (its universals `0..n`) when `f` is a method of a trait with
    /// lifetime params (a stub, or a default body and its instances):
    /// those of the receiver's type (`trait_lts_for`), else `'static`. Never
    /// fresh: a fresh trait lifetime would let the callee take a borrow for
    /// less than the trait promises. Empty for any other callee.
    fn trait_lifetime_seeds(&mut self, f: LocalDefId, avs: &[(Ty, Vec<u32>)]) -> Vec<u32> {
        let p = self.p;
        let trait_method = |g: LocalDefId| p.fn_defs.get(g.0 as usize).copied().filter(|d| p.regions.trait_methods.contains_key(d));
        let Some(m) = p
            .regions
            .stub_method(p, f)
            .or_else(|| trait_method(f))
            .or_else(|| trait_method(p.gx.instances.get(&f)?.template_local?))
        else {
            return Vec::new();
        };
        let Some(trait_def) = p.gx.index.trait_of_method(m) else { return Vec::new() };
        let n = p.gx.adt_lifetimes.get(&trait_def).map_or(0, |v| v.len());
        if n == 0 {
            return Vec::new();
        }
        let has_self = p.gx.trait_methods.get(&m).is_some_and(|t| t.self_kind.is_some());
        if has_self && let Some((rt, rv)) = avs.first() {
            let (mut t, mut skip) = (*rt, 0usize);
            while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
                t = inner;
                skip += 1;
            }
            let vars: Vec<u32> = rv.iter().skip(skip).copied().collect();
            if let Some(seeds) = self.trait_lts_for(trait_def, t, &vars, n) {
                return seeds;
            }
        }
        vec![0; n]
    }

    /// The vars of the `n` lifetime params of `trait_def` that Self type `t`
    /// (erased, slot vars `vars`) implements it with: through this body's
    /// bound on a type param (`Self` in the trait's own default body: the
    /// trait's lifetimes), or through the one impl whose header matches
    /// (`impl Tr<'static> for S`: `'static`; `impl<'d> Tr<'d> for S<'d>`:
    /// `S`'s region; a lifetime the Self type does not name is free).
    /// None when neither tells, or when the impl has where-clauses that
    /// would need a replay of their own.
    fn trait_lts_for(&mut self, trait_def: DefId, t: Ty, vars: &[u32], n: usize) -> Option<Vec<u32>> {
        self.trait_lts_at(trait_def, t, vars, n, 0)
    }

    fn trait_lts_at(&mut self, trait_def: DefId, t: Ty, vars: &[u32], n: usize, depth: u32) -> Option<Vec<u32>> {
        let p = self.p;
        if self.own.closure || depth > 8 {
            return None;
        }
        if let TyKind::Param(j) = self.body.tys.kind(t) {
            let sig = p.regions.body_sig(p, self.body.fn_id)?;
            if let Some(b) = sig.trait_bounds.iter().find(|b| b.param == j.0 && b.trait_def == trait_def) {
                return Some(b.lifetimes.iter().map(|&r| if let Region::Param(k) = r { k + 1 } else { 0 }).collect());
            }
            let own_trait = p.fn_defs.get(self.body.fn_id.0 as usize).and_then(|&d| p.gx.index.trait_of_method(d));
            if j.0 == 0 && own_trait == Some(trait_def) && sig.n_univ as usize >= n {
                return Some((1..=n as u32).collect());
            }
            return None;
        }
        let mut found: Option<Vec<u32>> = None;
        for &id in p.gx.index.impls_of_trait(trait_def) {
            let rec = p.gx.index.get(id);
            let Some(pat) = p.tys.args(rec.trait_ref.args).first().and_then(|g| g.as_ty()) else { continue };
            let mut parts: FxMap<u32, Vec<u32>> = FxMap::default();
            if !self.match_impl_self(pat, t, vars, &mut 0, &mut parts) {
                continue;
            }
            let head = p.regions.impl_heads.get(&rec.def)?;
            // Every where-clause on a lifetime trait must be one the head
            // kept (on a type param), else nothing tells its lifetimes.
            let nested = rec.generics.predicates.iter().filter(|pr| self.lifetime_trait_pred(pr)).count();
            if found.is_some() || nested != head.where_lts.len() {
                return None;
            }
            let mut lts: FxMap<u32, u32> = FxMap::default();
            self.match_impl_lifetimes(head.self_ty, t, vars, &mut 0, &mut lts);
            // The impl's own `T: Tr2<'x>` bounds: the part of Self that `T`
            // matched implements `Tr2` with lifetimes equal to the impl's
            // `'x` (replayed the same way, a bounded number of levels).
            if !head.where_lts.is_empty() {
                let mut part_tys: FxMap<u32, Ty> = FxMap::default();
                self.impl_param_tys(pat, t, &mut part_tys);
                for w in head.where_lts.clone() {
                    let pt = *part_tys.get(&w.param)?;
                    let pv = parts.get(&w.param).cloned().unwrap_or_default();
                    let inner = self.trait_lts_at(w.trait_def, pt, &pv, w.lifetimes.len(), depth + 1)?;
                    for (r, v) in w.lifetimes.iter().zip(inner) {
                        let x = match *r {
                            Region::Param(m) => match lts.get(&m) {
                                Some(&x) => x,
                                None => {
                                    let x = self.fresh();
                                    lts.insert(m, x);
                                    x
                                }
                            },
                            _ => 0,
                        };
                        self.edge(x, v);
                        self.edge(v, x);
                    }
                }
            }
            let mut out = Vec::with_capacity(n);
            for &r in &head.trait_lifetimes {
                let v = match r {
                    Region::Param(m) => match lts.get(&m) {
                        Some(&v) => v,
                        None => self.fresh(),
                    },
                    _ => 0,
                };
                out.push(v);
            }
            found = Some(out);
        }
        found.filter(|v| v.len() == n)
    }

    /// The erased part of `actual` each type param of an impl's Self
    /// pattern `pat` matches.
    fn impl_param_tys(&self, pat: Ty, actual: Ty, out: &mut FxMap<u32, Ty>) {
        let tys = &self.body.tys;
        match (tys.kind(pat), tys.kind(actual)) {
            (TyKind::Param(k), _) => {
                out.entry(k.0).or_insert(actual);
            }
            (TyKind::Ref(_, _, pi), TyKind::Ref(_, _, ai)) => self.impl_param_tys(pi, ai, out),
            (TyKind::Adt(pd, pa), TyKind::Adt(ad, aa)) if pd == ad => {
                let (xs, ys): (Vec<Ty>, Vec<Ty>) =
                    (tys.args(pa).iter().filter_map(|g| g.as_ty()).collect(), tys.args(aa).iter().filter_map(|g| g.as_ty()).collect());
                for (x, y) in xs.into_iter().zip(ys) {
                    self.impl_param_tys(x, y, out);
                }
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                for (x, y) in tys.tys_of(a).to_vec().into_iter().zip(tys.tys_of(b).to_vec()) {
                    self.impl_param_tys(x, y, out);
                }
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.impl_param_tys(a, b, out)
            }
            _ => {}
        }
    }

    /// True for a predicate on a trait with lifetime params.
    fn lifetime_trait_pred(&self, pr: &Predicate) -> bool {
        matches!(pr, Predicate::Trait(b) if self.p.gx.adt_lifetimes.get(&b.value.def).is_some_and(|v| !v.is_empty()))
    }

    /// Matches an impl's regioned Self type against an erased type whose
    /// slots are `vars` from `*at`, collecting the var of each impl
    /// lifetime param it names (`Region::Param(k)`).
    fn match_impl_lifetimes(&mut self, pat: Ty, actual: Ty, vars: &[u32], at: &mut usize, out: &mut FxMap<u32, u32>) {
        let tys = &self.body.tys;
        match (tys.kind(pat), tys.kind(actual)) {
            (TyKind::Ref(r, pm, pi), TyKind::Ref(_, am, ai)) if pm == am => {
                if let (Region::Param(k), Some(&v)) = (r, vars.get(*at)) {
                    out.entry(k).or_insert(v);
                }
                *at += 1;
                self.match_impl_lifetimes(pi, ai, vars, at, out);
            }
            (TyKind::Adt(pd, pa), TyKind::Adt(ad, aa)) if pd == ad => {
                let lts: Vec<Region> = tys.args(pa).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g { Some(*r) } else { None }).collect();
                let n = adt_regions(self.p, tys, actual) as usize;
                for (i, r) in lts.into_iter().enumerate().take(n) {
                    if let (Region::Param(k), Some(&v)) = (r, vars.get(*at + i)) {
                        out.entry(k).or_insert(v);
                    }
                }
                *at += n;
                let (xs, ys): (Vec<Ty>, Vec<Ty>) =
                    (tys.args(pa).iter().filter_map(|g| g.as_ty()).collect(), tys.args(aa).iter().filter_map(|g| g.as_ty()).collect());
                for (x, y) in xs.into_iter().zip(ys) {
                    self.match_impl_lifetimes(x, y, vars, at, out);
                }
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                for (x, y) in tys.tys_of(a).to_vec().into_iter().zip(tys.tys_of(b).to_vec()) {
                    self.match_impl_lifetimes(x, y, vars, at, out);
                }
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.match_impl_lifetimes(a, b, vars, at, out)
            }
            _ => *at += self.sc.slots(actual) as usize,
        }
    }

    /// A call through the `Fn*` bound of a type param of this body
    /// (`(self.f)(x)`: the callee is the bound's `call`, `call_mut`, or
    /// `call_once` stub, the receiver `F`, `&F`, or `&mut F`), with the
    /// bound from this fn's region signature (the fn's own, its impl's,
    /// or its trait's): the arguments flow into the bound's inputs and its
    /// output into the destination; a lifetime the bound writes is this
    /// fn's own, an elided one a fresh region of this call (higher-ranked).
    /// False when no regioned bound pairs: the caller then takes the
    /// conservative rule, which ties the result to the receiver too.
    /// True when `f`'s template bounds an `Item` of `Iterator` or
    /// `IntoIterator` to a type (`call`'s over-approximation, W-STD-C).
    fn item_bound(&self, f: LocalDefId) -> bool {
        let p = self.p;
        let src = p.gx.instances.get(&f).and_then(|i| i.template_local).unwrap_or(f);
        let Some(Some(t)) = p.gx.fn_templates.get(src.0 as usize) else { return false };
        let items: Vec<DefId> = [p.gx.lang.iterator, p.gx.lang.into_iterator]
            .iter()
            .filter_map(|&tr| p.gx.index.trait_record(tr))
            .flat_map(|r| r.assoc_items.iter().filter(|a| p.interner.get(a.1) == "Item").map(|a| a.0).collect::<Vec<_>>())
            .collect();
        t.generics.predicates.iter().any(|pr| match pr {
            Predicate::AssocEq(b) => items.contains(&b.value.assoc),
            Predicate::Trait(b) => p.tys.bindings(b.value.bindings).iter().any(|(d, _)| items.contains(d)),
            _ => false,
        })
    }

    fn call_fn_bound(&mut self, f: LocalDefId, avs: &[(Ty, Vec<u32>)], dt: Ty, dv: &[u32]) -> bool {
        let p = self.p;
        if p.gx.fn_class.get(f.0 as usize) != Some(&crate::check::generics::FnClass::Stub) {
            return false;
        }
        let Some(m) = p.regions.stub_method(p, f) else { return false };
        let lang = p.gx.lang;
        let is_call = [(lang.fn_, "call"), (lang.fn_mut, "call_mut"), (lang.fn_once, "call_once")]
            .iter()
            .any(|&(tr, name)| p.gx.index.trait_record(tr).and_then(|r| r.method_by_name(p.interner.intern(name))) == Some(m));
        let Some((rt, _)) = avs.first() else { return false };
        let mut t = *rt;
        while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
            t = inner;
        }
        let TyKind::Param(j) = self.body.tys.kind(t) else { return false };
        // A closure body calls through its enclosing fn's bound; the
        // fn's lifetimes are not universals there, so only a bound that
        // names none (`'static` and elided ones) takes this rule.
        let Some(sig) = p.regions.body_sig(p, root_fn(p, self.body.fn_id)) else { return false };
        let Some(b) = sig.fn_bounds.iter().find(|b| b.param == j.0 && b.inputs.len() + 1 == avs.len()).cloned() else { return false };
        if !is_call {
            return false;
        }
        if self.own.closure {
            let named = |ts: &[Ty]| {
                let mut rs = Vec::new();
                for &t in ts {
                    regions_of(&p.tys, t, &mut rs);
                }
                rs.iter().any(|r| matches!(r, Region::Param(_)))
            };
            // An input that must live for the fn's lifetime cannot be
            // proved here; an output that does takes the conservative rule.
            if named(&b.inputs) {
                self.errs.push(Diag::new(
                    "L0203",
                    self.span,
                    "a call inside a closure through an `Fn` bound whose argument names a lifetime of the enclosing fn is not supported yet",
                    "Make the call outside the closure, or write the bound with an elided lifetime.",
                ));
                return false;
            }
            if b.output.is_some_and(|o| named(&[o])) {
                return false;
            }
        }
        let univ: Vec<u32> = if self.own.closure { Vec::new() } else { (1..=sig.n_univ).collect() };
        let bv = self.fresh();
        self.bound_var = Some(bv);
        let mut binds: FxMap<u32, Vec<u32>> = FxMap::default();
        self.bind_tys.clear();
        let mut ok = true;
        for (i, &it) in b.inputs.iter().enumerate() {
            let (at, av) = &avs[i + 1];
            let mut pv = Vec::new();
            ok &= self.inst(it, *at, &univ, &mut binds, &mut pv);
            if !av.is_empty() {
                ok &= self.relate(*at, av, *at, &pv, Variance::Co);
            }
        }
        if let Some(ot) = b.output {
            let mut rv = Vec::new();
            ok &= self.inst(ot, dt, &univ, &mut binds, &mut rv);
            if !dv.is_empty() {
                ok &= self.relate(dt, &rv, dt, dv, Variance::Co);
            }
        } else {
            ok &= dv.is_empty();
        }
        self.bound_var = None;
        ok
    }

    /// The free argument slots of the closure bound to `F` in a call's
    /// `F: Fn*(A..)` bound (`trait_args`; found through the type `F` binds,
    /// so a mono instance pairs like its template), equated with the
    /// call's instantiation of each input that is a type param of the
    /// callee (`binds`; `&T`: past its higher-ranked outer reference).
    /// Records the closure in `bound_linked` when every free slot paired;
    /// `call` links any other closure conservatively.
    fn link_bound_closure(&mut self, trait_args: ArgsId, binds: &FxMap<u32, Vec<u32>>, sig: &RegionSig, univ: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let TyKind::Param(jf) = p.tys.kind(self_t) else { return };
        let Some(&ft) = self.bind_tys.get(&jf.0) else { return };
        let TyKind::Closure(def, _) = self.body.tys.kind(ft) else { return };
        let Some(vars) = self.closure_args.get(&def).cloned() else { return };
        let TyKind::Tuple(ts) = p.tys.kind(tuple) else { return };
        let inputs_tmpl: Vec<Ty> = p.tys.tys_of(ts).to_vec();
        let Some(c) = p.gx.closures.get(&def) else { return };
        let Ok(slots) = closure_arg_slots(&mut self.sc, c) else { return };
        let inputs = c.inputs.clone();
        // A reference the bound writes with an elided lifetime is
        // higher-ranked there: the callee may pass a borrow of its own
        // data, so the closure must take any region in that slot (rustc:
        // "not general enough"). A written one (`&'static Message`, the
        // callee's `'a`) ties the slot to that region. The regioned inputs
        // come from the callee's signature; without them every written
        // reference counts as higher-ranked.
        let regioned: Option<Vec<Ty>> =
            sig.fn_bounds.iter().find(|b| b.param == jf.0 && b.inputs.len() == inputs_tmpl.len()).map(|b| b.inputs.clone());
        let tmpl = regioned.unwrap_or_else(|| inputs_tmpl.clone());
        let mut kinds: Vec<BoundSlot> = Vec::with_capacity(slots.len());
        for (i, &it) in inputs.iter().enumerate() {
            match tmpl.get(i) {
                Some(&t) => self.bound_slots(t, it, univ, &mut kinds),
                None => kinds.extend(std::iter::repeat_n(BoundSlot::Free, self.sc.slots(it) as usize)),
            }
        }
        if kinds.iter().zip(&slots).any(|(k, (r, link))| *k == BoundSlot::Hr && (r.is_some() || link.is_some())) {
            self.not_general_enough();
            return;
        }
        // A tied slot is paired: the bound says exactly what flows in.
        let mut paired = vec![false; vars.len()];
        for (idx, k) in kinds.iter().enumerate() {
            if let BoundSlot::Tie(u) = *k
                && slots.get(idx).is_some_and(|(r, _)| r.is_some())
                && let Some(&v) = vars.get(idx)
            {
                self.edge(v, u);
                self.edge(u, v);
                paired[idx] = true;
            }
        }
        let mut at_slot = 0usize;
        for (i, &it) in inputs.iter().enumerate() {
            let n = self.sc.slots(it) as usize;
            let (skip, param) = match inputs_tmpl.get(i).map(|&t| p.tys.kind(t)) {
                Some(TyKind::Param(j)) => (0, Some(j.0)),
                Some(TyKind::Ref(_, _, inner)) => match p.tys.kind(inner) {
                    TyKind::Param(j) => (1, Some(j.0)),
                    _ => (0, None),
                },
                _ => (0, None),
            };
            if let Some(j) = param
                && let Some(bv) = binds.get(&j)
                && n >= skip
                && bv.len() == n - skip
            {
                for (q, &b) in bv.iter().enumerate() {
                    let idx = at_slot + skip + q;
                    if slots.get(idx).is_some_and(|(r, _)| r.is_some())
                        && let Some(&v) = vars.get(idx)
                    {
                        self.edge(v, b);
                        self.edge(b, v);
                        paired[idx] = true;
                    }
                }
            }
            at_slot += n;
        }
        if slots.iter().enumerate().all(|(i, (r, _))| r.is_none() || paired.get(i) == Some(&true)) {
            self.bound_linked.push(def);
        }
    }

    /// A closure passed for `F: Fn*(..) -> R` whose regioned output names
    /// a lifetime (`-> &'static str`, the callee's `'a`) or is
    /// higher-ranked (`Fn(&u8) -> &u8`): rustc gives the closure that
    /// return type, so what the body returns from its captured or free
    /// argument slots (`closure_reqs`, else every captured source) must
    /// outlive that region, `'static` for a higher-ranked one (the callee
    /// picks it). Higher-ranked arguments take no part: the body itself
    /// checks those.
    fn tie_bound_output(&mut self, trait_args: ArgsId, binds: &FxMap<u32, Vec<u32>>, sig: &RegionSig, univ: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let (TyKind::Param(jf), TyKind::Tuple(ts)) = (p.tys.kind(self_t), p.tys.kind(tuple)) else { return };
        let n_in = p.tys.tys_of(ts).len();
        let Some(out_t) = sig.fn_bounds.iter().find(|b| b.param == jf.0 && b.inputs.len() == n_in).and_then(|b| b.output) else { return };
        let Some(&ft) = self.bind_tys.get(&jf.0) else { return };
        let TyKind::Closure(def, args) = self.body.tys.kind(ft) else { return };
        let Some(c_out) = p.gx.closures.get(&def).map(|c| c.output) else { return };
        let mut outs: Vec<BoundSlot> = Vec::new();
        self.bound_slots(out_t, c_out, univ, &mut outs);
        let target = |k: BoundSlot| match k {
            BoundSlot::Tie(u) => Some(u),
            BoundSlot::Hr => Some(0),
            BoundSlot::Free => None,
        };
        if outs.iter().all(|&k| target(k).is_none()) {
            return;
        }
        let caps = binds.get(&jf.0).cloned().unwrap_or_default();
        let mut roles = Vec::new();
        closure_roles(&mut self.sc, args, &mut roles);
        match self.closure_reqs(def, &roles) {
            Some(reqs) => {
                let vars = self.closure_args.get(&def).cloned().unwrap_or_default();
                for &(x, y) in reqs.iter() {
                    let End::Out(k) = y else { continue };
                    let Some(u) = outs.get(k as usize).and_then(|&k| target(k)) else { continue };
                    let from = match x {
                        End::Cap(i) => caps.get(i as usize),
                        End::Arg(j) => vars.get(j as usize),
                        End::Static | End::Out(_) => None,
                    };
                    if let Some(&v) = from {
                        self.edge(v, u);
                    }
                }
            }
            None => {
                let us: Vec<u32> = outs.iter().filter_map(|&k| target(k)).collect();
                for (i, &(src, _)) in roles.iter().enumerate() {
                    if src && let Some(&v) = caps.get(i) {
                        for &u in &us {
                            self.edge(v, u);
                        }
                    }
                }
            }
        }
    }

    /// A type param `F` of this body or a fn item (also behind `&`)
    /// passed for the callee's `G: Fn*(..)` bound: its regioned signature
    /// (`F`'s own bound, the fn's signature) must prove `G`'s, as rustc
    /// selects the `Fn*` impl and equates the signatures (trait args are
    /// invariant). Per pair of places: lifetimes both write are one
    /// region; a binder of the argument (an elided lifetime of `F`'s
    /// bound, a late-bound lifetime of the fn) takes the lifetime `G`
    /// writes there, or stays higher-ranked where `G`'s is (not both); a
    /// higher-ranked `G` input needs a binder (L0735); outputs must agree
    /// the same way (L0733). A fn's early-bound lifetimes are fresh here.
    /// Type params are the call's instantiation. In a closure body the
    /// enclosing fn's lifetimes are not universals: L0203 where `F`'s
    /// bound names one.
    fn entail_bound(&mut self, trait_args: ArgsId, sig: &RegionSig, univ: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let (TyKind::Param(jg), TyKind::Tuple(ts)) = (p.tys.kind(self_t), p.tys.kind(tuple)) else { return };
        let n_in = p.tys.tys_of(ts).len();
        let Some(g) = sig.fn_bounds.iter().find(|b| b.param == jg.0 && b.inputs.len() == n_in).cloned() else { return };
        let Some(&ft) = self.bind_tys.get(&jg.0) else { return };
        let Some(src) = self.source_fn_sig(ft, n_in) else { return };
        let Some((inputs, output, item)) = src else { return self.unproved_bound(&g) };
        let mut ins: Vec<(Region, Region)> = Vec::new();
        let mut outs: Vec<(Region, Region)> = Vec::new();
        let paired = g.inputs.iter().zip(&inputs).all(|(&a, &b)| region_pairs(&p.tys, a, b, &mut ins))
            && match (g.output, output) {
                (Some(a), Some(b)) => region_pairs(&p.tys, a, b, &mut outs),
                (None, None) => true,
                // No output is `()`: it pairs with an output without regions.
                (Some(t), None) | (None, Some(t)) => {
                    let mut rs = Vec::new();
                    regions_of(&p.tys, t, &mut rs);
                    rs.is_empty()
                }
            };
        if !paired {
            return self.unproved_bound(&g);
        }
        if item.is_none() && self.own.closure && ins.iter().chain(&outs).any(|&(_, b)| matches!(b, Region::Param(_))) {
            return self.closure_param_bound_cut();
        }
        let gside = |r: Region, n: &mut u32, out: bool| match r {
            Region::Static => Side::Tie(0),
            Region::Param(k) => univ.get(k as usize).map_or(Side::Free, |&u| Side::Tie(u)),
            Region::Bound(_) if out => Side::Binder(0),
            Region::Bound(_) => {
                *n += 1;
                Side::Binder(*n - 1)
            }
            _ => Side::Free,
        };
        let mut sides = FnSides::new(item);
        let mut gn = 0u32;
        let ins: Vec<(Side, Side)> = ins.iter().map(|&(a, b)| (gside(a, &mut gn, false), sides.side(self, b, false))).collect();
        let outs: Vec<(Side, Side)> = outs.iter().map(|&(a, b)| (gside(a, &mut gn, true), sides.side(self, b, true))).collect();
        self.match_fn_sides(&ins, &outs);
    }

    /// A source that is not a closure (a fn item, a constructor, a fn
    /// pointer, a type param) passed for the callee's `G: Fn*(..) -> R`
    /// bound: what it returns may hold what it takes, so the regions bound
    /// to the type params in `G`'s inputs, and the lifetimes `G` writes
    /// there, flow into the regions bound to the type params in its output
    /// (rustc instantiates the source's signature with the call's types;
    /// a closure's sources flow through `closure_sources`).
    fn flow_bound_inputs(&mut self, trait_args: ArgsId, binds: &FxMap<u32, Vec<u32>>, sig: &RegionSig, univ: &[u32]) {
        let p = self.p;
        let targs: Vec<GenericArg> = p.tys.args(trait_args).to_vec();
        let (Some(self_t), Some(tuple)) = (targs.first().and_then(|g| g.as_ty()), targs.get(1).and_then(|g| g.as_ty())) else { return };
        let (TyKind::Param(jg), TyKind::Tuple(ts)) = (p.tys.kind(self_t), p.tys.kind(tuple)) else { return };
        let n_in = p.tys.tys_of(ts).len();
        let Some(&ft) = self.bind_tys.get(&jg.0) else { return };
        let mut t = ft;
        while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
            t = inner;
        }
        if matches!(self.body.tys.kind(t), TyKind::Closure(..)) {
            return;
        }
        let Some(g) = sig.fn_bounds.iter().find(|b| b.param == jg.0 && b.inputs.len() == n_in) else { return };
        let Some(out) = g.output else { return };
        // Bare type params in and out (`Fn(T, U) -> R`): the source's own
        // signature, where it has one, says exactly which input reaches R.
        let bare = |t: Ty| match p.tys.kind(t) {
            TyKind::Param(j) => Some(j.0),
            _ => None,
        };
        if let (Some(ins), Some(r)) = (g.inputs.iter().map(|&t| bare(t)).collect::<Option<Vec<u32>>>(), bare(out))
            && self.flow_by_signature(t, &ins, r, binds)
        {
            return;
        }
        let (mut outs, mut ins) = (Vec::new(), Vec::new());
        type_params_in(&p.tys, out, &mut outs);
        let dsts: Vec<u32> = outs.iter().filter_map(|j| binds.get(j)).flatten().copied().collect();
        if dsts.is_empty() {
            return;
        }
        let mut srcs: Vec<u32> = Vec::new();
        for &it in &g.inputs {
            type_params_in(&p.tys, it, &mut ins);
            let mut rs = Vec::new();
            regions_of(&p.tys, it, &mut rs);
            srcs.extend(rs.into_iter().filter_map(|r| match r {
                Region::Param(k) => univ.get(k as usize).copied(),
                _ => None,
            }));
        }
        srcs.extend(ins.iter().filter_map(|j| binds.get(j)).flatten().copied());
        self.flow_all(&srcs, &dsts);
    }

    /// `flow_bound_inputs` through the source's own regioned signature
    /// (a fn item's, or a type param's `Fn` bound outside a closure body),
    /// instantiated at this use: its universals are fresh vars, its
    /// late-bound regions one var of the use, and each input `ins[i]` and
    /// the output `out` take exactly the regions of the type params the
    /// call binds there. False when there is no such signature or it does
    /// not pair (the conservative flow then).
    fn flow_by_signature(&mut self, src: Ty, ins: &[u32], out: u32, binds: &FxMap<u32, Vec<u32>>) -> bool {
        let p = self.p;
        let root = root_fn(p, self.body.fn_id);
        let (s_ins, s_out, univ): (Vec<Ty>, Ty, Vec<u32>) = match self.body.tys.kind(src) {
            TyKind::FnDef(def, _) => {
                let Some(fs) = p.local_def(def.hash).and_then(|l| p.regions.body_sig(p, l)) else { return false };
                let univ: Vec<u32> = (0..fs.n_univ).map(|_| self.fresh()).collect();
                (fs.params.clone(), fs.ret, univ)
            }
            TyKind::Param(jf) if !self.own.closure => {
                let Some(rs) = p.regions.body_sig(p, root) else { return false };
                let Some(f) = rs.fn_bounds.iter().find(|b| b.param == jf.0 && b.inputs.len() == ins.len()) else { return false };
                let Some(o) = f.output else { return false };
                (f.inputs.clone(), o, (1..=rs.n_univ).collect())
            }
            _ => return false,
        };
        if s_ins.len() != ins.len() {
            return false;
        }
        let bv = self.fresh();
        self.bound_var = Some(bv);
        let mut ok = true;
        for (&st, &j) in s_ins.iter().zip(ins).chain(std::iter::once((&s_out, &out))) {
            let (Some(&at), Some(bvs)) = (self.bind_tys.get(&j), binds.get(&j)) else {
                ok = false;
                break;
            };
            let (mut pv, mut own) = (Vec::new(), FxMap::default());
            if !self.inst(st, at, &univ, &mut own, &mut pv) || pv.len() != bvs.len() {
                ok = false;
                break;
            }
            for (&a, &b) in pv.iter().zip(bvs) {
                self.edge(a, b);
                self.edge(b, a);
            }
        }
        self.bound_var = None;
        ok
    }

    /// The regioned signature of a type param `F` of this body's fn (its
    /// `Fn` bound with `n_in` inputs) or of a fn item (also behind `&`),
    /// passed where a `Fn*` bound or a `dyn Fn` is expected: inputs,
    /// output, and for a fn item which of its lifetimes are early-bound.
    /// `Some(None)` for such a source without a signature that pairs;
    /// None for any other type (closures have their own rules).
    #[allow(clippy::type_complexity)]
    fn source_fn_sig(&self, t: Ty, n_in: usize) -> Option<Option<(Vec<Ty>, Option<Ty>, Option<Vec<bool>>)>> {
        let p = self.p;
        let mut t = t;
        while let TyKind::Ref(_, _, inner) = self.body.tys.kind(t) {
            t = inner;
        }
        Some(match self.body.tys.kind(t) {
            TyKind::Param(jf) => p
                .regions
                .body_sig(p, root_fn(p, self.body.fn_id))
                .and_then(|s| s.fn_bounds.iter().find(|b| b.param == jf.0 && b.inputs.len() == n_in).cloned())
                .map(|f| (f.inputs, f.output, None)),
            TyKind::FnDef(def, _) => match p.local_def(def.hash).and_then(|l| p.regions.body_sig(p, l)) {
                Some(fs) if fs.params.len() == n_in => Some((fs.params.clone(), Some(fs.ret), Some(fs.early.clone()))),
                _ => None,
            },
            _ => return None,
        })
    }

    /// `entail_bound` for a coercion to `dyn Fn*(I..) -> O` (`dyn_fn_sig`):
    /// every input slot there is its own binder, and every output slot
    /// the one input slot's. A source whose signature does not pair takes
    /// the conservative answer (L0733 when the target has regions).
    fn entail_dyn(&mut self, src: Ty, ins: &[Ty], out: Ty) {
        let p = self.p;
        let Some(src) = self.source_fn_sig(src, ins.len()) else { return };
        let n_slots: Vec<usize> = ins.iter().map(|&t| self.sc.slots(t) as usize).collect();
        let n_out = self.sc.slots(out) as usize;
        let unproved = |this: &mut Self| {
            if n_slots.iter().sum::<usize>() + n_out > 0 {
                this.bound_mismatch();
            }
        };
        let Some((f_ins, f_out, item)) = src else { return unproved(self) };
        let mut f_in_regions: Vec<Region> = Vec::new();
        for (&t, &n) in f_ins.iter().zip(&n_slots) {
            let mut rs = Vec::new();
            regions_of(&p.tys, t, &mut rs);
            if rs.len() != n {
                return unproved(self);
            }
            f_in_regions.extend(rs);
        }
        let mut f_out_regions: Vec<Region> = Vec::new();
        if let Some(o) = f_out {
            regions_of(&p.tys, o, &mut f_out_regions);
        }
        // The target's slots: a written `'static` is `'static`, each
        // elided input its own binder, an elided output the one input's.
        let mut t_in: Vec<Region> = Vec::new();
        for &it in ins {
            t_in.extend(self.sig_slot_regions(it));
        }
        let t_out = self.sig_slot_regions(out);
        let tside = |i: usize, r: Region| if r == Region::Static { Side::Tie(0) } else { Side::Binder(i as u32) };
        let t_outs: Option<Vec<Side>> = t_out
            .iter()
            .map(|&r| match (r, &t_in[..]) {
                (Region::Static, _) => Some(Side::Tie(0)),
                (_, [one]) => Some(tside(0, *one)),
                _ => None,
            })
            .collect();
        let Some(t_outs) = t_outs else { return unproved(self) };
        if f_out_regions.len() != n_out || t_in.len() != f_in_regions.len() {
            return unproved(self);
        }
        if item.is_none() && self.own.closure && f_in_regions.iter().chain(&f_out_regions).any(|r| matches!(r, Region::Param(_))) {
            return self.closure_param_bound_cut();
        }
        let mut sides = FnSides::new(item);
        let ins: Vec<(Side, Side)> = t_in.iter().zip(&f_in_regions).enumerate().map(|(i, (&t, &r))| (tside(i, t), sides.side(self, r, false))).collect();
        let outs: Vec<(Side, Side)> = t_outs.into_iter().zip(&f_out_regions).map(|(t, &r)| (t, sides.side(self, r, true))).collect();
        self.match_fn_sides(&ins, &outs);
    }

    /// L0203: inside a closure, a type param whose `Fn` bound names a
    /// lifetime of the enclosing fn, passed on (the closure body cannot
    /// name that lifetime).
    fn closure_param_bound_cut(&mut self) {
        self.errs.push(Diag::new(
            "L0203",
            self.span,
            "a type param whose `Fn` bound names a lifetime of the enclosing fn, passed to a generic fn inside a closure, is not supported yet",
            "Make the call outside the closure, or pass a closure written in place.",
        ));
    }

    /// Proves a target `Fn` signature (the left side of each pair) from a
    /// source's (the right), place by place in the inputs, then the
    /// outputs. A source binder takes either one target binder, where the
    /// target is higher-ranked, or the one lifetime the target writes there
    /// (trait args are invariant); a target binder needs a source binder
    /// (L0735); outputs agree the same way (L0733).
    fn match_fn_sides(&mut self, ins: &[(Side, Side)], outs: &[(Side, Side)]) {
        let mut takes: FxMap<u32, u32> = FxMap::default();
        let mut inst: FxMap<u32, u32> = FxMap::default();
        for &(ga, fb) in ins {
            match (ga, fb) {
                (Side::Binder(gi), Side::Binder(k)) => {
                    if inst.contains_key(&k) || takes.get(&k).is_some_and(|&gj| gj != gi) {
                        return self.not_general_enough_param();
                    }
                    takes.insert(k, gi);
                }
                (Side::Binder(_), Side::Tie(_)) => return self.not_general_enough_param(),
                (Side::Tie(u), Side::Binder(k)) => {
                    if takes.contains_key(&k) {
                        return self.not_general_enough_param();
                    }
                    match inst.get(&k) {
                        Some(&v) => {
                            self.edge(u, v);
                            self.edge(v, u);
                        }
                        None => {
                            inst.insert(k, u);
                        }
                    }
                }
                (Side::Tie(u), Side::Tie(v)) => {
                    self.edge(u, v);
                    self.edge(v, u);
                }
                _ => {}
            }
        }
        for &(ga, fb) in outs {
            match (ga, fb) {
                (Side::Binder(gi), Side::Binder(k)) if takes.get(&k) == Some(&gi) => {}
                (Side::Tie(u), Side::Binder(k)) if inst.contains_key(&k) => {
                    let v = inst[&k];
                    self.edge(u, v);
                    self.edge(v, u);
                }
                (Side::Tie(u), Side::Tie(v)) => {
                    self.edge(u, v);
                    self.edge(v, u);
                }
                (Side::Free, _) | (_, Side::Free) => {}
                _ => return self.bound_mismatch(),
            }
        }
    }

    /// An argument whose signature does not pair with the callee's `G:
    /// Fn*` bound (check selected the impl some other way): only a bound
    /// without lifetimes is proved (L0733).
    fn unproved_bound(&mut self, g: &FnBound) {
        let mut rs = Vec::new();
        for &it in &g.inputs {
            regions_of(&self.p.tys, it, &mut rs);
        }
        if let Some(o) = g.output {
            regions_of(&self.p.tys, o, &mut rs);
        }
        if rs.into_iter().any(|r| matches!(r, Region::Param(_) | Region::Static | Region::Bound(_))) {
            self.bound_mismatch();
        }
    }

    /// L0735 for a type param's `Fn` bound or a fn item that fixes an
    /// argument lifetime where the callee's bound is higher-ranked (rustc
    /// E0277, "not general enough").
    fn not_general_enough_param(&mut self) {
        self.errs.push(Diag::new(
            "L0735",
            self.span,
            "this argument is not general enough for the callee's `Fn` bound: it fixes an argument lifetime, but the callee may pass a borrow of its own data",
            "Give that argument an elided lifetime (`F: Fn(&T)`, `fn f(x: &T)`).",
        ));
    }

    /// L0733 for a type param's `Fn` bound or a fn item whose signature
    /// does not prove the callee's bound (rustc E0308).
    fn bound_mismatch(&mut self) {
        self.errs.push(Diag::new(
            "L0733",
            self.span,
            "lifetime may not live long enough: this argument's signature does not prove the callee's `Fn` bound (their lifetimes differ)",
            "Write the same lifetimes in both signatures.",
        ));
    }

    /// Per slot of a closure input's erased type `t`, what the bound's
    /// input type `tmpl` (over the callee's params; regioned when the
    /// signature has it) makes of it: a type param or projection is the
    /// call's instantiation (free); an elided lifetime (`Region::Bound`,
    /// or any region in an erased bound) is higher-ranked; `'static` and
    /// the callee's lifetime `k` tie the slot to `'static` and `univ[k]`.
    fn bound_slots(&mut self, tmpl: Ty, t: Ty, univ: &[u32], out: &mut Vec<BoundSlot>) {
        let p = self.p;
        let n = self.sc.slots(t) as usize;
        let kind = |r: Region| match r {
            Region::Static => BoundSlot::Tie(0),
            Region::Param(k) => univ.get(k as usize).map_or(BoundSlot::Hr, |&u| BoundSlot::Tie(u)),
            _ => BoundSlot::Hr,
        };
        match (p.tys.kind(tmpl), self.body.tys.kind(t)) {
            (TyKind::Param(_) | TyKind::Projection(..), _) => out.extend(std::iter::repeat_n(BoundSlot::Free, n)),
            (TyKind::Ref(r, _, ti), TyKind::Ref(_, _, ei)) => {
                out.push(kind(r));
                self.bound_slots(ti, ei, univ, out);
            }
            (TyKind::Adt(_, ta), TyKind::Adt(_, ea)) => {
                let lts: Vec<Region> = p.tys.args(ta).iter().filter_map(|g| if let GenericArg::Lifetime(r) = g { Some(*r) } else { None }).collect();
                let nr = adt_regions(p, &self.body.tys, t) as usize;
                for i in 0..nr {
                    out.push(lts.get(i).map_or(BoundSlot::Hr, |&r| kind(r)));
                }
                let ta_tys: Vec<Ty> = p.tys.args(ta).iter().filter_map(|g| g.as_ty()).collect();
                let ea_tys: Vec<Ty> = self.body.tys.args(ea).iter().filter_map(|g| g.as_ty()).collect();
                if ta_tys.len() == ea_tys.len() {
                    for (a, b) in ta_tys.into_iter().zip(ea_tys) {
                        self.bound_slots(a, b, univ, out);
                    }
                } else {
                    out.extend(std::iter::repeat_n(BoundSlot::Hr, n - nr));
                }
            }
            (TyKind::Tuple(ta), TyKind::Tuple(ea)) if p.tys.tys_of(ta).len() == self.body.tys.tys_of(ea).len() => {
                let pairs: Vec<(Ty, Ty)> = p.tys.tys_of(ta).iter().copied().zip(self.body.tys.tys_of(ea).iter().copied()).collect();
                for (a, b) in pairs {
                    self.bound_slots(a, b, univ, out);
                }
            }
            (TyKind::Array(a, _) | TyKind::Slice(a), TyKind::Array(b, _) | TyKind::Slice(b)) => self.bound_slots(a, b, univ, out),
            (TyKind::Dyn(_, r), TyKind::Dyn(..)) => out.push(kind(r)),
            _ => out.extend(std::iter::repeat_n(BoundSlot::Hr, n)),
        }
    }

    /// L0735: a closure whose argument lifetime is free (inferred, or named
    /// by an annotation) where the callee's bound is higher-ranked.
    fn not_general_enough(&mut self) {
        self.errs.push(Diag::new(
            "L0735",
            self.span,
            "this closure is not general enough for the bound it is passed to: its argument lifetime is fixed, but the callee may pass a borrow of its own data",
            "Annotate the parameter with an elided lifetime (`|x: &T|`), or pass the closure where it is written.",
        ));
    }

    /// The `X: 'static` where-clauses of the impls of `trait_def` whose Self
    /// pattern matches `actual` (laid out in `vars`): each region of the part
    /// `X` matches outlives `'static`.
    fn impl_static_edges(&mut self, trait_def: DefId, actual: Ty, vars: &[u32]) {
        let p = self.p;
        for (id, statics) in p.regions.static_impls(p, trait_def).to_vec() {
            let rec = p.gx.index.get(id);
            let Some(pat) = p.tys.args(rec.trait_ref.args).first().and_then(|g| g.as_ty()) else { continue };
            let mut parts: FxMap<u32, Vec<u32>> = FxMap::default();
            if !self.match_impl_self(pat, actual, vars, &mut 0, &mut parts) {
                continue;
            }
            for k in statics {
                for &v in parts.get(&k).map(|x| x.as_slice()).unwrap_or(&[]) {
                    self.edge(v, 0);
                }
            }
        }
    }

    /// Matches an impl's Self pattern (over its params) against an erased
    /// type whose slots are `vars` from `*at`, collecting each param's
    /// slot vars. False when the shapes differ.
    fn match_impl_self(&mut self, pat: Ty, actual: Ty, vars: &[u32], at: &mut usize, out: &mut FxMap<u32, Vec<u32>>) -> bool {
        let tys = &self.body.tys;
        match (tys.kind(pat), tys.kind(actual)) {
            (TyKind::Param(k), _) => {
                let n = self.sc.slots(actual) as usize;
                out.entry(k.0).or_default().extend(vars.iter().skip(*at).take(n).copied());
                *at += n;
                true
            }
            (TyKind::Ref(_, pm, pi), TyKind::Ref(_, am, ai)) if pm == am => {
                *at += 1;
                self.match_impl_self(pi, ai, vars, at, out)
            }
            (TyKind::Adt(pd, pa), TyKind::Adt(ad, aa)) if pd == ad => {
                *at += adt_regions(self.p, tys, actual) as usize;
                let (xs, ys): (Vec<Ty>, Vec<Ty>) =
                    (tys.args(pa).iter().filter_map(|g| g.as_ty()).collect(), tys.args(aa).iter().filter_map(|g| g.as_ty()).collect());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.match_impl_self(x, y, vars, at, out))
            }
            (TyKind::Tuple(a), TyKind::Tuple(b)) => {
                let (xs, ys) = (tys.tys_of(a).to_vec(), tys.tys_of(b).to_vec());
                xs.len() == ys.len() && xs.into_iter().zip(ys).all(|(x, y)| self.match_impl_self(x, y, vars, at, out))
            }
            (TyKind::Array(a, _), TyKind::Array(b, _)) | (TyKind::Slice(a), TyKind::Slice(b)) | (TyKind::RawPtr(_, a), TyKind::RawPtr(_, b)) => {
                self.match_impl_self(a, b, vars, at, out)
            }
            _ => {
                *at += self.sc.slots(actual) as usize;
                pat == actual
            }
        }
    }

    fn inst_region(&mut self, r: Region, univ: &[u32]) -> u32 {
        match r {
            Region::Static => 0,
            Region::Param(k) => univ.get(k as usize).copied().unwrap_or_else(|| self.fresh()),
            Region::Bound(_) if let Some(v) = self.bound_var => v,
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
                        self.bind_tys.insert(j.0, e);
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
            (TyKind::Dyn(_, rr), TyKind::Dyn(..)) => {
                let rr = if crate::check::object::dyn_is_static(self.p, et, e) { Region::Static } else { rr };
                let v = self.inst_region(rr, univ);
                out.push(v);
                true
            }
            _ => self.sc.slots(e) == 0,
        }
    }

    /// Edges for the `T: 'static` bounds of the user Adts inside a type
    /// (rustc's well-formedness: `S<&'a i32>` with `struct S<T: 'static>`
    /// needs `'a: 'static`): every slot of such an argument outlives
    /// `'static`. `at` walks the slots in order.
    fn static_bound_edges(&mut self, t: Ty, vars: &[u32], at: &mut usize) {
        let tys = &self.body.tys;
        match tys.kind(t) {
            TyKind::Ref(_, _, inner) => {
                *at += 1;
                self.static_bound_edges(inner, vars, at);
            }
            TyKind::Adt(def, args) => {
                *at += adt_regions(self.p, tys, t) as usize;
                let statics: Vec<u32> = match self.p.adt_by_def(def).and_then(|a| self.p.gx.adt_generics.get(a.0 as usize)) {
                    Some(g) => g
                        .predicates
                        .iter()
                        .filter_map(|pr| match pr {
                            Predicate::TypeOutlives(x, Region::Static) => match self.p.tys.kind(*x) {
                                TyKind::Param(j) => Some(j.0),
                                _ => None,
                            },
                            _ => None,
                        })
                        .collect(),
                    None => Vec::new(),
                };
                for (j, g) in tys.args(args).to_vec().into_iter().enumerate() {
                    if let GenericArg::Ty(e) = g {
                        let start = *at;
                        self.static_bound_edges(e, vars, at);
                        if statics.contains(&(j as u32)) {
                            for &v in vars.get(start..*at).unwrap_or(&[]) {
                                self.edge(v, 0);
                            }
                        }
                    }
                }
            }
            TyKind::Tuple(ts) => {
                for e in tys.tys_of(ts).to_vec() {
                    self.static_bound_edges(e, vars, at);
                }
            }
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => self.static_bound_edges(e, vars, at),
            _ => *at += self.sc.slots(t) as usize,
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
            TyKind::Adt(def, args) => {
                let start = *at;
                for _ in 0..adt_regions(self.p, tys, t) {
                    if let Some(&v) = vars.get(*at) {
                        for &o in refs.iter() {
                            self.edge(v, o);
                        }
                    }
                    *at += 1;
                }
                // The Adt's own outlives facts: every value of the type
                // meets them (`struct H<'a, 'b: 'a>`).
                for &(x, y) in self.p.regions.adt_facts.get(&def).map_or(&[][..], |v| v.as_slice()) {
                    let to = if y == crate::check::generics::STATIC_FACT { Some(0) } else { vars.get(start + y as usize).copied() };
                    if let (Some(&a), Some(b)) = (vars.get(start + x as usize), to) {
                        self.edge(a, b);
                    }
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
            TyKind::Dyn(..) => {
                if let Some(&v) = vars.get(*at) {
                    for &o in refs.iter() {
                        self.edge(v, o);
                    }
                }
                *at += 1;
            }
            _ => {}
        }
    }
}

/// True when `ret` is an `impl Trait` type with a `'static` bound.
fn opaque_static_ret(p: &Program, ret: Ty) -> bool {
    let TyKind::Opaque(od, _) = p.tys.kind(ret) else { return false };
    p.gx.opaques.get(&od).is_some_and(|o| o.bounds.iter().any(|b| matches!(b, Predicate::TypeOutlives(_, Region::Static))))
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
            | B::SliceToVec
            | B::Sync(
                crate::check::sync::SyncOp::MutexLock
                    | crate::check::sync::SyncOp::RwLockRead
                    | crate::check::sync::SyncOp::RwLockWrite
                    | crate::check::sync::SyncOp::LockGetMut
                    | crate::check::sync::SyncOp::PoisonGetRef
                    | crate::check::sync::SyncOp::PoisonGetMut
                    | crate::check::sync::SyncOp::ChanRecv
                    | crate::check::sync::SyncOp::ChanTryRecv
                    | crate::check::sync::SyncOp::OnceGet
                    | crate::check::sync::SyncOp::OnceGetMut
                    | crate::check::sync::SyncOp::OnceTake
                    | crate::check::sync::SyncOp::TryLock(_)
                    | crate::check::sync::SyncOp::RecvMakeIter(0 | 1)
            )
            | B::VecDrain
            | B::StringDrain
            | B::VecDrainAsSlice
            | B::StrDrainAsStr
    )
}

/// The iterator methods whose closure takes `&Self::Item` (check/iter.rs
/// `fn_mut_param_ref`): its outer reference is higher-ranked.
fn by_ref_item(b: Option<crate::check::Builtin>) -> bool {
    use crate::check::Builtin as B;
    matches!(b, Some(B::IterFilter | B::IterTakeWhile | B::IterSkipWhile | B::IterInspect | B::IterFind | B::IterMinByKey | B::IterMaxByKey))
}

/// The map and set lookups by `&Q` (W-STD-B): the key is not stored or
/// returned.
fn hash_lookup_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(b, B::MapGet | B::MapGetMut | B::MapContainsKey | B::MapRemove | B::SetContains | B::SetRemove | B::SetGet)
}

/// `map.entry(k)` and the Entry methods that return the value or the
/// Entry (W-STD-B, `call_hash_entry`).
fn entry_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(
        b,
        B::MapEntry | B::EntryOrInsert | B::EntryOrDefault | B::EntryOrInsertWith | B::EntryOrInsertWithKey | B::EntryAndModify
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
            | B::DlEntries
            | B::DmEntries
            | B::DmKey
            | B::DmValue
    )
}

/// The builtin iterator calls whose result is an item (or a collection
/// of items): their regions come from the iterator's sources.
fn item_builtin(b: crate::check::Builtin) -> bool {
    use crate::check::Builtin as B;
    matches!(
        b,
        B::IterNext
            | B::IterNextBack
            | B::IterNth
            | B::IterFind
            | B::IterFindMap
            | B::IterLast
            | B::IterMin
            | B::IterMax
            | B::IterMinByKey
            | B::IterMaxByKey
            | B::IterCollect
    )
}

/// True when a type holds a `&mut` reference somewhere.
/// True when a value of type `t` can reach a `Cell`, `RefCell`, or
/// `RefCell` guard: memory shared values can write through. A builtin
/// result of such a type may alias its source (an `Rc` clone shares the
/// cell), so its regions are the source's, not just outlived by them.
fn has_interior(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(_, _, inner) | TyKind::Array(inner, _) | TyKind::Slice(inner) => has_interior(tys, inner),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| has_interior(tys, e)),
        TyKind::Adt(_, a) => {
            matches!(tys.builtin_of(t), Some(BuiltinTy::Cell | BuiltinTy::RefCell | BuiltinTy::RefGuard | BuiltinTy::RefMutGuard))
                || tys.guard_elem(t).is_some()
                || tys.lock_elem(t).is_some()
                || tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| has_interior(tys, e)))
        }
        TyKind::Closure(_, a) => closure_fields(tys, a).into_iter().any(|e| has_interior(tys, e)),
        _ => false,
    }
}

fn has_mut_ref(tys: &impl TyIntern, t: Ty) -> bool {
    // A map Entry holds `&'a mut HashMap<K, V>` (W-STD-B).
    if let Some(BuiltinTy::Hash(crate::ty::hash::HashTy::Entry)) = tys.builtin_of(t) {
        return true;
    }
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
            reqs: Vec::new(),
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
        if self.own.closure {
            for u in 1..nu {
                let c = scc[u] as usize;
                for v in bit_iter(&univ[c * wu..(c + 1) * wu]) {
                    if v != u && v < nu {
                        sol.reqs.push((u as u32, v as u32));
                    }
                }
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
                    // A closure's creator proves relations between its
                    // captured and free argument regions (`closure_reqs`).
                    if matches!(self.own.ends.get(u), Some(Some(End::Cap(_) | End::Arg(_))))
                        && matches!(self.own.ends.get(v), Some(Some(End::Static | End::Cap(_) | End::Arg(_))))
                    {
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
    // A trait's own lifetime params (the trait method's first universals)
    // are what the impl header gives them: `'static` (`impl Tr<'static>`),
    // or the impl's lifetime passed for them (`impl<'d> Tr<'d>`), which
    // stays a placeholder of the contract.
    let impl_def = p.fn_defs.get(f.0 as usize).and_then(|&d| p.defs.get(d)).and_then(|d| d.parent);
    let trait_lts = impl_def.and_then(|d| p.regions.impl_heads.get(&d)).map(|h| h.trait_lifetimes.clone()).unwrap_or_default();
    let mut cx = Contract { p, nt, trait_lts, edges: Vec::new() };
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
    /// The impl-side region of each of the trait's own lifetime params.
    trait_lts: Vec<Region>,
    edges: Vec<(usize, usize)>,
}

impl Contract<'_, '_> {
    /// The node of region `r` on the trait side or the impl side.
    fn node(&self, r: Region, trait_side: bool) -> Option<usize> {
        match r {
            Region::Static => Some(0),
            // A trait lifetime the header fixes to `'static` is `'static`.
            Region::Param(k) if trait_side && self.trait_lts.get(k as usize) == Some(&Region::Static) => Some(0),
            Region::Param(k) if trait_side => Some(1 + k as usize),
            // An impl lifetime the header passes as the trait's `k`-th
            // lifetime is that one, a placeholder of the contract.
            Region::Param(m) if let Some(k) = self.trait_lts.iter().position(|&x| x == Region::Param(m)) => Some(1 + k),
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
            (TyKind::Dyn(_, ra), TyKind::Dyn(_, rb)) => self.slot(ra, rb, v.then(Variance::Co), a_trait),
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
        TyKind::Dyn(_, r) => note(r, outer, out),
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
                continue;
            }
            // A fn pointer type's regions are its own (late-bound) or a
            // written `&'static` (`Scope::static_refs`): an input the fn
            // needs `'static` where the pointer takes any is less general
            // than the pointer, and so is an output the pointer promises
            // `'static` where the fn returns a borrow (rustc E0308).
            let TyKind::FnPtr(ps) = body.tys.kind(*ty) else { continue };
            let ps = body.tys.sig(ps).value;
            let (p_ins, p_out) = (body.tys.tys_of(ps.inputs).to_vec(), ps.output);
            let (mut ins, mut outs) = (Vec::new(), Vec::new());
            if let Some(s) = sig {
                for (&it, &pt) in s.params.iter().zip(&p_ins) {
                    ptr_region_pairs(&p.tys, &body.tys, it, pt, &mut ins);
                }
                ptr_region_pairs(&p.tys, &body.tys, s.ret, p_out, &mut outs);
            }
            if outs.iter().any(|&(f, t)| t == Region::Static && f != Region::Static) {
                out.push(Diag::new(
                    "L0110",
                    s.span,
                    format!("`{}` returns a borrow of its argument, so it cannot become a fn pointer that returns `'static`", p.display_name(p.fn_info(*f).name)),
                    "Return `'static` data from the fn, or elide the pointer's output lifetime.",
                ));
                continue;
            }
            if ins.iter().any(|&(f, t)| f == Region::Static && t != Region::Static) {
                out.push(Diag::new(
                    "L0110",
                    s.span,
                    format!(
                        "`{}` takes a `'static` borrow, so it cannot become a fn pointer that accepts any lifetime",
                        p.display_name(p.fn_info(*f).name)
                    ),
                    "Call the fn directly, or take the parameter with an elided lifetime.",
                ));
            }
        }
    }
    out
}

/// The pairs of regions at the same places of a fn's regioned param or
/// return type `f` (in `ftys`) and a fn pointer's erased one `t` (in
/// `ptys`, `'static` kept where written): an Adt's lifetime slots pair
/// with `Erased` (a fn pointer type writes none there).
fn ptr_region_pairs(ftys: &impl TyIntern, ptys: &impl TyIntern, f: Ty, t: Ty, out: &mut Vec<(Region, Region)>) {
    match (ftys.kind(f), ptys.kind(t)) {
        (TyKind::Ref(a, _, fi), TyKind::Ref(b, _, ti)) => {
            out.push((a, b));
            ptr_region_pairs(ftys, ptys, fi, ti, out);
        }
        (TyKind::Adt(_, fa), TyKind::Adt(_, ta)) => {
            let ta: Vec<Ty> = ptys.args(ta).iter().filter_map(|g| g.as_ty()).collect();
            let mut tj = ta.into_iter();
            for g in ftys.args(fa).to_vec() {
                match g {
                    GenericArg::Lifetime(r) => out.push((r, Region::Erased)),
                    GenericArg::Ty(e) => {
                        if let Some(te) = tj.next() {
                            ptr_region_pairs(ftys, ptys, e, te, out);
                        }
                    }
                    GenericArg::Const(_) => {}
                }
            }
        }
        (TyKind::Tuple(a), TyKind::Tuple(b)) => {
            for (x, y) in ftys.tys_of(a).to_vec().into_iter().zip(ptys.tys_of(b).to_vec()) {
                ptr_region_pairs(ftys, ptys, x, y, out);
            }
        }
        (TyKind::Slice(x), TyKind::Slice(y)) | (TyKind::Array(x, _), TyKind::Array(y, _)) => ptr_region_pairs(ftys, ptys, x, y, out),
        _ => {}
    }
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
