// Generic-program reuse across daemon requests (docs/ARCH.md section 8;
// W-PERF wave B). Collect checks every template once against its bounds
// (`generics::template_check`) and runs instance discovery over every
// plain fn and every instance it makes (`generics::materialize`). Both
// results are functions of the checked body's source text and the
// program's item-level environment. This cache keeps them per stable
// def across the requests of one daemon session, so collect checks only
// the bodies an edit touched and replays the rest in the cold order.
//
// The driver owns the environment half of the key: it clears the cache
// whenever anything item-level changed, a const fn body changed, or the
// program has a nested static (see `compile.rs`, "generic reuse"). Under
// an unchanged environment, an entry holds while its source fingerprint
// holds: the body hash of the AST fn whose text the body checks. A
// closure body fn's source is its parent's, an instance's source is its
// template's, and a trait default method's text is part of the trait
// item, which the environment covers.
use crate::ast::ExprId;
use crate::check::closure::ClosureKind;
use crate::check::collect::Program;
use crate::check::generics::{FnClass, OwnedArg, OwnedClosure, OwnedTy};
use crate::check::picks::TraitPick;
use crate::def::{DefId, LocalDefId};
use crate::intern::FxMap;

/// One passing template check of a body with no closure expressions:
/// its trait picks and closure call kinds, by expression offset from
/// the template body's first expression (`ExprId`s move when the merged
/// Ast is rebuilt; offsets inside one body do not).
struct TemplateEntry {
    src: u64,
    n_exprs: u32,
    picks: Vec<(u32, TraitPick)>,
    calls: Vec<(u32, ClosureKind)>,
}

/// One clean discovery check: the Adt types the body names, its
/// instance requests (template def, owned args), and its closures, in
/// check order.
struct DiscoveryEntry {
    src: u64,
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
    /// Source fingerprint of each AST fn, in `LocalDefId` order (the
    /// driver's scan body hash), set by the driver before collect.
    pub ast_src: Vec<u64>,
    templates: FxMap<DefId, TemplateEntry>,
    discovery: FxMap<DefId, DiscoveryEntry>,
    /// This collect's work, for the stats line: checks run and reused.
    pub templates_checked: usize,
    pub templates_reused: usize,
    pub discovery_checked: usize,
    pub discovery_reused: usize,
}

impl GenReuse {
    /// Drops every entry: the environment they were made under changed.
    pub fn clear(&mut self) {
        self.templates.clear();
        self.discovery.clear();
    }

    /// Resets the per-collect counters before a collect runs.
    pub fn begin(&mut self) {
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
        // the environment half of the key covers.
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

    /// The stored picks and closure call kinds of template `t`, rebased
    /// onto its current body, if its stored check still holds.
    #[allow(clippy::type_complexity)]
    pub fn template(&mut self, p: &Program, t: LocalDefId) -> Option<(Vec<(ExprId, TraitPick)>, Vec<(ExprId, ClosureKind)>)> {
        if !self.on {
            return None;
        }
        let src = self.src_of(p, t)?;
        let (lo, hi) = p.fn_info(t).def.exprs;
        let e = self.templates.get(&p.def_id(t))?;
        if e.src != src || e.n_exprs != hi - lo {
            return None;
        }
        self.templates_reused += 1;
        let picks = e.picks.iter().map(|&(off, pick)| (ExprId(lo + off), pick)).collect();
        let calls = e.calls.iter().map(|&(off, k)| (ExprId(lo + off), k)).collect();
        Some((picks, calls))
    }

    /// Stores one passing template check (the caller passes only bodies
    /// with no closure expressions).
    pub fn store_template(&mut self, p: &Program, t: LocalDefId, picks: &[(ExprId, TraitPick)], calls: &[(ExprId, ClosureKind)]) {
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
        self.templates.insert(p.def_id(t), TemplateEntry { src, n_exprs: hi - lo, picks, calls });
    }

    /// The stored discovery output of fn `f`, if it still holds.
    pub fn discovered(&mut self, p: &Program, f: LocalDefId) -> Option<Discovered> {
        if !self.on {
            return None;
        }
        let src = self.src_of(p, f)?;
        let e = self.discovery.get(&p.def_id(f))?;
        if e.src != src {
            return None;
        }
        let mut requests = Vec::with_capacity(e.requests.len());
        for (def, args) in &e.requests {
            let l = p.local_def(def.hash).filter(|&l| p.def_id(l) == *def)?;
            requests.push((l, args.clone()));
        }
        self.discovery_reused += 1;
        Some((e.adt_tys.clone(), requests, e.closures.clone()))
    }

    /// Stores the output of one clean discovery check of fn `f`.
    pub fn store_discovered(
        &mut self,
        p: &Program,
        f: LocalDefId,
        adt_tys: &[OwnedTy],
        requests: &[(LocalDefId, Vec<OwnedArg>)],
        closures: &[OwnedClosure],
    ) {
        if !self.on {
            return;
        }
        let Some(src) = self.src_of(p, f) else { return };
        let requests = requests.iter().map(|(t, args)| (p.def_id(*t), args.clone())).collect();
        self.discovery.insert(p.def_id(f), DiscoveryEntry { src, adt_tys: adt_tys.to_vec(), requests, closures: closures.to_vec() });
    }
}
