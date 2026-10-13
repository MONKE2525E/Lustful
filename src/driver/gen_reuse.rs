// Generic-program reuse across daemon requests (docs/ARCH.md section 8;
// W-PERF wave B). Collect checks every template once against its bounds
// (`generics::template_check`) and runs instance discovery over every
// plain fn and every instance it makes (`generics::materialize`). This
// cache keeps both results per stable def across the requests of one
// daemon session, so collect checks only the bodies an edit touched and
// replays the rest in the cold order.
//
// A stored result depends on three things, and holds while all three do:
// - the trait system: trait items, impl items, and derive lists. The
//   driver clears the cache when their fingerprint changes (and on a
//   const fn body edit, a nested static, or a slot renumber; see
//   `compile.rs`, "generic reuse"). No read records trait selection,
//   so this is the only key for it.
// - the source: the body and head hash of the AST fn whose text the
//   body checks. A closure body fn's source is its parent's, an
//   instance's source is its template's, and a trait default method's
//   text is part of its trait item, under the first key.
// - everything else the check read (section 8.2 `Reads`: bindings,
//   method sets, signatures with generics and bounds, layouts). An entry
//   made under another item-level environment replays its reads against
//   this program first. Instance entries do not: an instance check
//   replays its template's picks without probing, so its reads miss the
//   probes that chose them; after an item edit, instances recheck.
use crate::ast::ExprId;
use crate::check::closure::ClosureKind;
use crate::check::collect::Program;
use crate::check::generics::{FnClass, OwnedArg, OwnedClosure, OwnedTy};
use crate::check::picks::TraitPick;
use crate::def::{DefId, LocalDefId};
use crate::driver::graph::{Read, ReadKey, Reads};
use crate::intern::FxMap;

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
/// instance requests (template def, owned args), and its closures, in
/// check order.
struct DiscoveryEntry {
    src: u64,
    env: u64,
    reads: Reads,
    adt_tys: Vec<OwnedTy>,
    requests: Vec<(DefId, Vec<OwnedArg>)>,
    closures: Vec<OwnedClosure>,
}

/// What one stored discovery check replays: Adt types, requests with
/// templates as this program's local ids, and closures to register.
pub(crate) type Discovered = (Vec<OwnedTy>, Vec<(LocalDefId, Vec<OwnedArg>)>, Vec<OwnedClosure>);

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
    /// Node answers of this collect's program, for read replays.
    memo: FxMap<ReadKey, Read>,
    /// This collect's work, for the stats line: checks run and reused.
    pub templates_checked: usize,
    pub templates_reused: usize,
    pub discovery_checked: usize,
    pub discovery_reused: usize,
}

impl GenReuse {
    /// Drops every entry: the trait system they were made under changed.
    pub fn clear(&mut self) {
        self.templates.clear();
        self.discovery.clear();
    }

    /// Resets the per-collect state before a collect runs.
    pub fn begin(&mut self) {
        self.memo.clear();
        self.templates_checked = 0;
        self.templates_reused = 0;
        self.discovery_checked = 0;
        self.discovery_reused = 0;
    }

    /// The source fingerprint of one fn of `p`, or None for a fn with no
    /// checked body of its own (a trait method stub).
    pub fn src_of(&self, p: &Program, f: LocalDefId) -> Option<u64> {
        let s = self.source(p, f)?;
        // A trait default body: its text is in the trait item, which
        // the trait-system key covers.
        Some(self.ast_src.get(s.0 as usize).copied().unwrap_or(0))
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
        let (lo, hi) = p.fn_info(t).def.exprs;
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
        let (lo, hi) = p.fn_info(t).def.exprs;
        let inside = |e: ExprId| e.0 >= lo && e.0 < hi;
        if !picks.iter().all(|(e, _)| inside(*e)) || !calls.iter().all(|(e, _)| inside(*e)) {
            return;
        }
        let picks = picks.iter().map(|&(e, pick)| (e.0 - lo, pick)).collect();
        let calls = calls.iter().map(|&(e, k)| (e.0 - lo, k)).collect();
        let entry = TemplateEntry { src, env: self.env, reads: with_own_sig(p, t, reads), n_exprs: hi - lo, picks, calls };
        self.templates.insert(p.def_id(t), entry);
    }

    /// The stored discovery output of fn `f`, if it still holds.
    pub fn discovered(&mut self, p: &Program, f: LocalDefId) -> Option<Discovered> {
        if !self.on {
            return None;
        }
        let src = self.src_of(p, f)?;
        let instance = p.gx.fn_class.get(f.0 as usize) == Some(&FnClass::Instance);
        let e = self.discovery.get_mut(&p.def_id(f))?;
        if e.src != src || (instance && e.env != self.env) || !Self::reads_hold(&mut self.memo, self.env, p, e.env, &e.reads) {
            return None;
        }
        let mut requests = Vec::with_capacity(e.requests.len());
        for (def, args) in &e.requests {
            let l = p.local_def(def.hash).filter(|&l| p.def_id(l) == *def)?;
            requests.push((l, args.clone()));
        }
        e.env = self.env;
        self.discovery_reused += 1;
        Some((e.adt_tys.clone(), requests, e.closures.clone()))
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
    ) {
        if !self.on {
            return;
        }
        let Some(src) = self.src_of(p, f) else { return };
        let requests = requests.iter().map(|(t, args)| (p.def_id(*t), args.clone())).collect();
        let reads = with_own_sig(p, f, reads);
        let entry = DiscoveryEntry { src, env: self.env, reads, adt_tys: adt_tys.to_vec(), requests, closures: closures.to_vec() };
        self.discovery.insert(p.def_id(f), entry);
    }
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
