// Generic-program reuse across daemon requests (docs/ARCH.md section 8;
// W-PERF wave B). Collect checks every template once against its bounds
// (`generics::template_check`) and runs instance discovery over every
// plain fn and every instance it makes (`generics::materialize`). This
// cache keeps both results per stable def across the requests of one
// daemon session, so collect checks only the bodies an edit touched and
// replays the rest in the cold order.
//
// A stored result depends on three things, and holds while all three do:
// - the trait system: trait items, impl items of lang and foreign
//   traits, inherent impls with an associated const or a `dyn` Self,
//   type alias and const items, and derive lists (`trait_key`).
//   Collect drops every entry when their fingerprint changes
//   (`GenReuse::gate`), and the driver also drops them on a const fn
//   body edit, a nested static, or a slot renumber (`compile.rs`,
//   "generic reuse"). Impls of user traits are not in the key:
//   selection records an `ImplSet` read of the bucket it searched
//   (driver/graph.rs), so an added, removed, or edited user trait impl
//   rechecks only the bodies that read its bucket. Other inherent impls
//   are not in it either: method probes and inherent table lookups
//   record `MethodSet` reads (`Program::inherent_reads`).
// - the source: the body and head hash of the AST fn whose text the
//   body checks, and what the body takes from other checks in this
//   collect. An instance's source is its template's source plus the
//   template check's outputs it replays (picks, closure call kinds and
//   shapes): its own reads miss the probes that chose those picks. A
//   closure body fn's source is its parent's plus the closure record the
//   parent's check made. A trait default method's text is part of its
//   trait item, under the first key.
// - everything else the check read (section 8.2 `Reads`: bindings,
//   method sets, signatures with generics and bounds, layouts). An entry
//   made under another item-level environment replays its reads against
//   this program first.
use crate::ast::ExprId;
use crate::check::closure::ClosureKind;
use crate::check::collect::Program;
use crate::check::generics::{CaptureShape, FnClass, OwnedArg, OwnedClosure, OwnedTy};
use crate::check::picks::TraitPick;
use crate::def::{DefId, LocalDefId};
use crate::driver::graph::{Read, ReadKey, Reads};
use crate::intern::{FxHasher, FxMap};
use std::hash::{Hash, Hasher};

/// One passing template check of a body with no closure expressions:
/// its trait picks and closure call kinds, by expression offset from
/// the template body's first expression (`ExprId`s move when the merged
/// Ast is rebuilt; offsets inside one body do not).
struct TemplateEntry {
    src: u64,
    /// The item-level environment the entry last held under.
    env: u64,
    reads: Reads,
    n_exprs: u32,
    picks: Vec<(u32, TraitPick)>,
    calls: Vec<(u32, ClosureKind)>,
}

/// One clean discovery check: the Adt types the body names, its
/// instance requests (template def, owned args), its closures, and its
/// vtable requests (concrete type, dyn type), in check order.
struct DiscoveryEntry {
    src: u64,
    env: u64,
    reads: Reads,
    adt_tys: Vec<OwnedTy>,
    requests: Vec<(DefId, Vec<OwnedArg>)>,
    closures: Vec<OwnedClosure>,
    vtables: Vec<(OwnedTy, OwnedTy)>,
}

/// A copy of one stored discovery output (`GenReuse::out_copy`).
pub(crate) struct OutCopy {
    adt_tys: Vec<OwnedTy>,
    requests: Vec<(DefId, Vec<OwnedArg>)>,
    closures: Vec<OwnedClosure>,
    vtables: Vec<(OwnedTy, OwnedTy)>,
}

impl OutCopy {
    /// True when fn `f`'s new discovery output `out` equals this copy
    /// where it can make anything: the closures, vtables, and the types
    /// that can name an Adt instance, in order. Collect then makes the
    /// same closures, instances, vtables, and glue from it (the other
    /// types only enter the global store; the caller interns them). A
    /// check walks no instance requests, so they must match only for a
    /// build (`walk_instances`).
    pub(crate) fn same(&self, p: &Program, out: &Discovered, walk_instances: bool) -> bool {
        let (adt_tys, requests, closures, vtables) = out;
        let makers = |ts: &[OwnedTy]| ts.iter().filter(|t| crate::check::generics::may_make_instances(t)).cloned().collect::<Vec<_>>();
        self.closures == *closures
            && makers(&self.adt_tys) == makers(adt_tys)
            && self.vtables == *vtables
            && (!walk_instances
                || self.requests.len() == requests.len()
                    && self.requests.iter().zip(requests).all(|((d, a), (t, b))| *d == p.def_id(*t) && a == b))
    }
}

/// What one stored discovery check replays: Adt types, requests with
/// templates as this program's local ids, closures to register, and
/// vtable requests.
pub(crate) type Discovered = (Vec<OwnedTy>, Vec<(LocalDefId, Vec<OwnedArg>)>, Vec<OwnedClosure>, Vec<(OwnedTy, OwnedTy)>);

/// The session's generic reuse cache. `collect_reuse` moves it into
/// `GenTables::reuse` for one collect and back out after.
#[derive(Default)]
pub struct GenReuse {
    /// False: every lookup misses and nothing is stored (one-shot
    /// sessions, and `collect` callers outside the driver).
    pub on: bool,
    /// Source fingerprint of each AST fn, in `LocalDefId` order (body
    /// and head hash), set by the driver before collect.
    pub ast_src: Vec<u64>,
    /// This request's item-level environment (item-scan hash and AST fn
    /// count), set by the driver before collect.
    pub env: u64,
    templates: FxMap<DefId, TemplateEntry>,
    discovery: FxMap<DefId, DiscoveryEntry>,
    /// Defs whose last discovery check stored nothing (a body error), so
    /// their entry, if any, is older than what that collect used.
    unstored: FxMap<DefId, ()>,
    /// Node answers of this collect's program, for read replays.
    memo: FxMap<ReadKey, Read>,
    /// This collect's template check outputs that instances replay, by
    /// template, and its closure records, by closure def (fingerprints;
    /// see `src_of`).
    tpl_out: FxMap<LocalDefId, u64>,
    closure_out: FxMap<DefId, u64>,
    /// This collect's work, for the stats line: checks run and reused.
    pub templates_checked: usize,
    pub templates_reused: usize,
    pub discovery_checked: usize,
    pub discovery_reused: usize,
    /// Errors this collect's template checks reported (body errors).
    pub template_errors: usize,
    /// The trait-system key of the last collect that reached its body
    /// checks (`gate`).
    trait_key: Option<u64>,
    /// True unless this collect's trait-system key equals the last one;
    /// then every entry was dropped, and the driver rechecks every body.
    pub trait_changed: bool,
}

impl GenReuse {
    /// Drops every entry: the trait system they were made under changed.
    pub fn clear(&mut self) {
        self.templates.clear();
        self.discovery.clear();
        self.unstored.clear();
    }

    /// Notes that a fresh discovery check of `f` stored nothing.
    pub fn note_unstored(&mut self, p: &Program, f: LocalDefId) {
        self.unstored.insert(p.def_id(f), ());
    }

    /// Drops every entry when the trait-system key moved since the last
    /// collect. Collect calls it once the impl index is built, before any
    /// template check or discovery runs.
    pub fn gate(&mut self, key: u64) {
        self.trait_changed = self.trait_key != Some(key);
        if self.trait_changed {
            self.clear();
        }
        self.trait_key = Some(key);
    }

    /// Resets the per-collect state before a collect runs.
    pub fn begin(&mut self) {
        self.trait_changed = true;
        self.memo.clear();
        self.tpl_out.clear();
        self.closure_out.clear();
        self.templates_checked = 0;
        self.templates_reused = 0;
        self.discovery_checked = 0;
        self.discovery_reused = 0;
        self.template_errors = 0;
    }

    /// Resets this request's work counters when the daemon's kept program
    /// stands in for collect (driver/patch.rs): no collect ran, so no
    /// template check, and the trait system stands.
    pub fn begin_kept(&mut self) {
        self.trait_changed = false;
        self.templates_checked = 0;
        self.templates_reused = 0;
        self.discovery_checked = 0;
        self.discovery_reused = 0;
        self.template_errors = 0;
    }

    /// The source fingerprint of one fn of `p` (see the module docs),
    /// or None for a fn with no checked body of its own (a trait method
    /// stub) or whose upstream check output is not known yet.
    pub fn src_of(&self, p: &Program, f: LocalDefId) -> Option<u64> {
        self.src_depth(p, f, 0)
    }

    fn src_depth(&self, p: &Program, f: LocalDefId, depth: u32) -> Option<u64> {
        if let Some(&h) = self.ast_src.get(f.0 as usize) {
            return Some(h);
        }
        if depth > 64 {
            return None;
        }
        let mix = |a: u64, b: u64| {
            let mut h = FxHasher::default();
            (a, b).hash(&mut h);
            h.finish()
        };
        match p.gx.fn_class.get(f.0 as usize)? {
            FnClass::Instance => {
                let t = p.gx.instances.get(&f)?.template_local?;
                Some(mix(self.src_depth(p, t, depth + 1)?, *self.tpl_out.get(&t)?))
            }
            FnClass::Closure | FnClass::TemplateClosure => {
                let def = *p.gx.closure_fns.get(&f)?;
                let parent = p.gx.closures.get(&def)?.parent;
                Some(mix(self.src_depth(p, parent, depth + 1)?, *self.closure_out.get(&def)?))
            }
            // A trait default body: its text is in the trait item, which
            // the trait-system key covers.
            FnClass::Template => Some(0),
            FnClass::Plain | FnClass::Stub => None,
        }
    }

    /// Records the outputs of template `t`'s check (fresh or reused)
    /// that its instances replay, as one fingerprint over expression
    /// offsets from the body's first expression.
    pub fn note_template_out(
        &mut self,
        p: &Program,
        t: LocalDefId,
        picks: &[(ExprId, TraitPick)],
        calls: &[(ExprId, ClosureKind)],
        shapes: &[(ExprId, ClosureKind, Vec<CaptureShape>)],
    ) {
        let lo = p.fn_def(t).exprs.0;
        let off = |e: ExprId| e.0.wrapping_sub(lo);
        let mut picks: Vec<(u32, u64, u8, u8, Option<u32>)> = picks
            .iter()
            .map(|(e, k)| {
                let form = match k.form {
                    crate::driver::graph::ReceiverForm::Value => 0u8,
                    crate::driver::graph::ReceiverForm::Ref => 1,
                    crate::driver::graph::ReceiverForm::RefMut => 2,
                };
                (off(*e), k.trait_def.hash.0, k.derefs, form, k.env_pred)
            })
            .collect();
        picks.sort_unstable();
        let mut calls: Vec<(u32, ClosureKind)> = calls.iter().map(|(e, k)| (off(*e), *k)).collect();
        calls.sort_unstable();
        let mut h = FxHasher::default();
        "tpl-out-v1".hash(&mut h);
        picks.hash(&mut h);
        calls.hash(&mut h);
        (shapes.len() as u64).hash(&mut h);
        for (e, kind, caps) in shapes {
            (off(*e), kind).hash(&mut h);
            (caps.len() as u64).hash(&mut h);
            for (root, projs, mode) in caps {
                (root, mode).hash(&mut h);
                (projs.len() as u64).hash(&mut h);
                for pr in projs {
                    match pr {
                        crate::ir::Proj::Deref => 0u8.hash(&mut h),
                        crate::ir::Proj::Field(i) => (1u8, i).hash(&mut h),
                        crate::ir::Proj::Downcast(i) => (2u8, i).hash(&mut h),
                        crate::ir::Proj::Index(l) => (3u8, l).hash(&mut h),
                    }
                }
            }
        }
        self.tpl_out.insert(t, h.finish());
    }

    /// Records the closures one discovery check registers, by def (the
    /// first record of a def wins, as in `register_closures`).
    pub fn note_closures(&mut self, closures: &[OwnedClosure]) {
        for oc in closures {
            let mut h = FxHasher::default();
            "closure-out-v1".hash(&mut h);
            oc.kind.hash(&mut h);
            hash_owned_ty(&mut h, &oc.env);
            (oc.inputs.len() as u64).hash(&mut h);
            for t in &oc.inputs {
                hash_owned_ty(&mut h, t);
            }
            hash_owned_ty(&mut h, &oc.output);
            self.closure_out.entry(oc.def).or_insert(h.finish());
        }
    }

    /// The fn whose source text one fn of `p` checks: an AST fn, or a
    /// trait default method template (whose text is in its trait item).
    /// None for a trait method stub.
    pub fn source(&self, p: &Program, f: LocalDefId) -> Option<LocalDefId> {
        let mut f = f;
        // Instances and closure body fns chain to a template or parent
        // made earlier, so the walk ends; the bound only guards it.
        for _ in 0..64 {
            if (f.0 as usize) < self.ast_src.len() {
                return Some(f);
            }
            f = match p.gx.fn_class.get(f.0 as usize)? {
                FnClass::Instance => p.gx.instances.get(&f)?.template_local?,
                FnClass::Closure | FnClass::TemplateClosure => p.gx.closures.get(p.gx.closure_fns.get(&f)?)?.parent,
                FnClass::Template => return Some(f),
                FnClass::Plain | FnClass::Stub => return None,
            };
        }
        None
    }

    /// True when an entry made under `env` with `reads` still holds in
    /// this program: same environment, or every read answers the same.
    fn reads_hold(memo: &mut FxMap<ReadKey, Read>, this_env: u64, p: &Program, env: u64, reads: &Reads) -> bool {
        env == this_env || p.reads_dirty_memo(reads, memo) == 0
    }

    /// The stored picks and closure call kinds of template `t`, rebased
    /// onto its current body, if its stored check still holds.
    #[allow(clippy::type_complexity)]
    pub fn template(&mut self, p: &Program, t: LocalDefId) -> Option<(Vec<(ExprId, TraitPick)>, Vec<(ExprId, ClosureKind)>)> {
        if !self.on {
            return None;
        }
        let src = self.src_of(p, t)?;
        let (lo, hi) = p.fn_def(t).exprs;
        let e = self.templates.get_mut(&p.def_id(t))?;
        if e.src != src || e.n_exprs != hi - lo || !Self::reads_hold(&mut self.memo, self.env, p, e.env, &e.reads) {
            return None;
        }
        e.env = self.env;
        self.templates_reused += 1;
        let picks = e.picks.iter().map(|&(off, pick)| (ExprId(lo + off), pick)).collect();
        let calls = e.calls.iter().map(|&(off, k)| (ExprId(lo + off), k)).collect();
        Some((picks, calls))
    }

    /// Stores one passing template check (the caller passes only bodies
    /// with no closure expressions).
    pub fn store_template(&mut self, p: &Program, t: LocalDefId, reads: &Reads, picks: &[(ExprId, TraitPick)], calls: &[(ExprId, ClosureKind)]) {
        if !self.on {
            return;
        }
        let Some(src) = self.src_of(p, t) else { return };
        let (lo, hi) = p.fn_def(t).exprs;
        let inside = |e: ExprId| e.0 >= lo && e.0 < hi;
        if !picks.iter().all(|(e, _)| inside(*e)) || !calls.iter().all(|(e, _)| inside(*e)) {
            return;
        }
        let picks = picks.iter().map(|&(e, pick)| (e.0 - lo, pick)).collect();
        let calls = calls.iter().map(|&(e, k)| (e.0 - lo, k)).collect();
        let entry = TemplateEntry { src, env: self.env, reads: with_own_sig(p, t, reads), n_exprs: hi - lo, picks, calls };
        self.templates.insert(p.def_id(t), entry);
    }

    /// Drops this program's node answers: a signature delta changed the
    /// program they describe (driver/kept_delta.rs).
    pub fn forget_answers(&mut self) {
        self.memo.clear();
    }

    /// Whether template `t`'s stored check still holds; None when none
    /// is stored (`template` without the copy).
    pub fn template_holds(&mut self, p: &Program, t: LocalDefId) -> Option<bool> {
        let src = self.src_of(p, t)?;
        let (lo, hi) = p.fn_def(t).exprs;
        let e = self.templates.get(&p.def_id(t))?;
        Some(self.on && e.src == src && e.n_exprs == hi - lo && Self::reads_hold(&mut self.memo, self.env, p, e.env, &e.reads))
    }

    /// True when fn `f`'s stored discovery output still holds
    /// (`discovered` without the copy).
    pub fn discovery_holds(&mut self, p: &Program, f: LocalDefId) -> bool {
        let Some(src) = self.src_of(p, f).filter(|_| self.on) else { return false };
        let Some(e) = self.discovery.get(&p.def_id(f)) else { return false };
        e.src == src && Self::reads_hold(&mut self.memo, self.env, p, e.env, &e.reads)
    }

    /// The stored discovery output of fn `f`, if it still holds.
    pub fn discovered(&mut self, p: &Program, f: LocalDefId) -> Option<Discovered> {
        if !self.on {
            return None;
        }
        let src = self.src_of(p, f)?;
        let e = self.discovery.get_mut(&p.def_id(f))?;
        if e.src != src || !Self::reads_hold(&mut self.memo, self.env, p, e.env, &e.reads) {
            return None;
        }
        let mut requests = Vec::with_capacity(e.requests.len());
        for (def, args) in &e.requests {
            let l = p.local_def(def.hash).filter(|&l| p.def_id(l) == *def)?;
            requests.push((l, args.clone()));
        }
        e.env = self.env;
        self.discovery_reused += 1;
        Some((e.adt_tys.clone(), requests, e.closures.clone(), e.vtables.clone()))
    }

    /// True when a stored check read the body of one of `defs`: a
    /// `Checked` read, which a check records for each const fn its const
    /// evaluation ran. The driver's const fn edit asks (compile.rs).
    pub(crate) fn reads_checked(&self, defs: &[DefId]) -> bool {
        let stored = self.templates.values().map(|e| &e.reads).chain(self.discovery.values().map(|e| &e.reads));
        stored.into_iter().any(|r| defs.iter().any(|&d| r.contains(&ReadKey::Checked(d))))
    }

    /// A copy of the stored discovery output of the fn with def `def`,
    /// unless its last discovery check stored nothing: what collect used
    /// for that body. The daemon's kept programs take one per edited fn
    /// at the patch (driver/patch.rs).
    pub(crate) fn out_copy(&self, def: DefId) -> Option<OutCopy> {
        if self.unstored.contains_key(&def) {
            return None;
        }
        let e = self.discovery.get(&def)?;
        Some(OutCopy { adt_tys: e.adt_tys.clone(), requests: e.requests.clone(), closures: e.closures.clone(), vtables: e.vtables.clone() })
    }

    /// Stores the output of one clean discovery check of fn `f`.
    #[allow(clippy::too_many_arguments)]
    pub fn store_discovered(
        &mut self,
        p: &Program,
        f: LocalDefId,
        reads: &Reads,
        adt_tys: &[OwnedTy],
        requests: &[(LocalDefId, Vec<OwnedArg>)],
        closures: &[OwnedClosure],
        vtables: &[(OwnedTy, OwnedTy)],
    ) {
        if !self.on {
            return;
        }
        let Some(src) = self.src_of(p, f) else { return };
        let requests = requests.iter().map(|(t, args)| (p.def_id(*t), args.clone())).collect();
        let reads = with_own_sig(p, f, reads);
        let entry = DiscoveryEntry {
            src,
            env: self.env,
            reads,
            adt_tys: adt_tys.to_vec(),
            requests,
            closures: closures.to_vec(),
            vtables: vtables.to_vec(),
        };
        self.unstored.remove(&p.def_id(f));
        self.discovery.insert(p.def_id(f), entry);
    }
}

/// The trait-system key (see the module docs): trait items (default
/// bodies included), impl items (headers, method heads, associated
/// items), type alias and const items (an impl header or a bound can
/// reach a type through them), and the derive list of each Adt that has
/// one. An impl of a trait whose impls `ImplSet` reads cover
/// (`Program::impls_read_covered`; `impl_traits` gives each trait impl's
/// trait by item index) is left out, and so is an inherent impl with no
/// associated const or type and no `dyn` Self: method probes and every
/// direct inherent table lookup record `MethodSet` reads
/// (`Program::inherent_reads`), whose fingerprints cover each method's
/// signature.
pub fn trait_key(p: &Program, impl_traits: &FxMap<usize, DefId>) -> u64 {
    use crate::ast::{ItemKind, TyExpr};
    let user_trait = |d: &DefId| p.impls_read_covered(*d);
    let plain_inherent = |imp: &crate::ast::ImplDef| {
        imp.trait_ref.is_none() && imp.consts.is_empty() && imp.types.is_empty() && !matches!(p.ast.ty(imp.self_ty), TyExpr::Dyn { .. })
    };
    let mut h = FxHasher::default();
    "trait-system-v2".hash(&mut h);
    for (i, item) in p.ast.items.iter().enumerate() {
        let derives = match &item.kind {
            ItemKind::Impl(imp) if imp.trait_ref.is_some() && impl_traits.get(&i).is_some_and(user_trait) => continue,
            ItemKind::Impl(imp) if plain_inherent(imp) => continue,
            ItemKind::Trait(_) | ItemKind::Impl(_) | ItemKind::Type(_) | ItemKind::Const(_) => {
                (0u8, crate::driver::ast_hash::item_hash(&p.ast, item)).hash(&mut h);
                continue;
            }
            ItemKind::Struct(s) => (s.name, &s.derives),
            ItemKind::Enum(e) => (e.name, &e.derives),
            _ => continue,
        };
        // An Adt with no derives adds no impl: a new plain struct
        // keeps the key.
        if derives.1.is_empty() {
            continue;
        }
        1u8.hash(&mut h);
        p.interner.get(derives.0).hash(&mut h);
        (derives.1.len() as u64).hash(&mut h);
        for (d, _) in derives.1 {
            p.interner.get(*d).hash(&mut h);
        }
    }
    h.finish()
}

/// A check's read set plus a `Sig` read of the checked fn itself: a body
/// reads its own signature (parameter and return types, deep) through
/// the compat `FnInfo` path, which records nothing, and its field
/// accesses record nothing either. The driver adds the same read to
/// each slot's stored set.
fn with_own_sig(p: &Program, f: LocalDefId, reads: &Reads) -> Reads {
    let mut reads = reads.clone();
    let _ = p.sig_of(&mut reads, p.def_id(f));
    reads
}

/// Hashes one owned type snapshot by its stable content: defs, kinds,
/// regions, and consts; a fn pointer's session-local signature ids are
/// skipped (its inputs and output are hashed from the snapshot).
fn hash_owned_ty(h: &mut FxHasher, t: &OwnedTy) {
    match t {
        OwnedTy::Leaf(k) => (0u8, k).hash(h),
        OwnedTy::Ref(r, m, e) => {
            (1u8, r, m).hash(h);
            hash_owned_ty(h, e);
        }
        OwnedTy::RawPtr(m, e) => {
            (2u8, m).hash(h);
            hash_owned_ty(h, e);
        }
        OwnedTy::Slice(e) => {
            3u8.hash(h);
            hash_owned_ty(h, e);
        }
        OwnedTy::Array(e, n) => {
            (4u8, n).hash(h);
            hash_owned_ty(h, e);
        }
        OwnedTy::Tuple(es) => {
            (5u8, es.len() as u64).hash(h);
            for e in es {
                hash_owned_ty(h, e);
            }
        }
        OwnedTy::Adt(d, a) | OwnedTy::FnDef(d, a) | OwnedTy::Closure(d, a) | OwnedTy::Opaque(d, a) => {
            let tag = match t {
                OwnedTy::Adt(..) => 6u8,
                OwnedTy::FnDef(..) => 7,
                OwnedTy::Closure(..) => 8,
                _ => 9,
            };
            (tag, d).hash(h);
            hash_owned_args(h, a);
        }
        OwnedTy::Projection(d, a) => {
            (10u8, d.0).hash(h);
            hash_owned_args(h, a);
        }
        OwnedTy::FnPtr(b, inputs, output) => {
            (11u8, b.count, b.value.is_unsafe, b.value.extern_c, inputs.len() as u64).hash(h);
            for e in inputs {
                hash_owned_ty(h, e);
            }
            hash_owned_ty(h, output);
        }
        OwnedTy::Dyn(principal, auto, r) => {
            (12u8, auto, r).hash(h);
            match principal {
                Some((d, a, bs)) => {
                    (1u8, d).hash(h);
                    hash_owned_args(h, a);
                    (bs.len() as u64).hash(h);
                    for (bd, g) in bs {
                        bd.hash(h);
                        hash_owned_args(h, std::slice::from_ref(g));
                    }
                }
                None => 0u8.hash(h),
            }
        }
    }
}

fn hash_owned_args(h: &mut FxHasher, args: &[OwnedArg]) {
    (args.len() as u64).hash(h);
    for a in args {
        match a {
            OwnedArg::Ty(t) => {
                0u8.hash(h);
                hash_owned_ty(h, t);
            }
            OwnedArg::Lifetime(r) => (1u8, r).hash(h),
            OwnedArg::Const(c) => (2u8, c).hash(h),
        }
    }
}
