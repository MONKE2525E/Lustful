// The fn signature delta (sigedit PLAN, P2.2-3): header edits of plain
// fns applied to the daemon's kept program in place of a full collect.
// The item patch (driver/patch.rs) has already put the new items in the
// Ast, moved the program's spans, and attached this request's Ast and
// resolver tables. `apply_headers` then does for each edited fn what
// collect does for it, and refuses whatever it cannot prove equal to a
// cold collect:
//
// - the record and the signature checks collect runs, for this fn only
//   (`delta_audit::redo_sig`); an `impl Trait` return of the fn reveals
//   again from its body and its hidden type must stand (`delta_audit::reveal_again`);
// - mono's body checks that read the signature: every plain body whose
//   stored discovery no longer holds checks again and must make the same
//   instances, closures, and vtables. A template whose stored check no
//   longer holds, or that stores none and names an edited fn, checks
//   again in a check (no diagnostic, same hidden type) and refuses in a
//   build.
//   The check and build programs share the stored checks; one stored
//   after the kept program's `reuse_stamp` (by the other mode's request)
//   refuses, since this program may not hold that output.
//
// Also refused (the caller collects in full): a fn whose class moves (a
// template keeps its parameter kinds), and a template in a build or in a
// program with generic associated consts (its instances would keep their
// old signatures); const fns and any fn const evaluation may reach
// through const fn bodies (`ConstReach`, transitive); trait methods and
// trait impl methods; methods of inherent impls with associated items
// (the trait-system key hashes their heads); lang and shipped std fns;
// main and #[test] fns; an `impl Trait` return that comes or goes; a fn
// that a template body revealing an opaque type names (a plain one reveals
// again, and its hidden type must stand: then the auto traits callers read
// through it, and any opaque type that names it, stand too); a header with a `dyn` or macro type (eager vtables scan the Ast
// for `dyn`); programs without user generics (collect's whole-Ast flag
// scans may turn them on); and any diagnostic. The full path answers
// then. A refusal before any write, or a diagnostic of a new signature
// (its old records go back, `delta_audit::undo`), leaves the program as
// it was: `reuse_kept` keeps it for the next request (sigedit R9).
//
// check/delta_audit.rs lists what the delta does with each Program field.
use super::const_reach::ConstReach;
use super::session::{Caches, Front};
use crate::check::collect::{FnLoc, Program};
use crate::check::generics::{self, FnClass};
use crate::def::LocalDefId;
use crate::diag::Diag;
use crate::driver::graph::{BindingRes, ReadKey};

/// One header edit: the edited AST fn (its `LocalDefId` index) and its
/// old body's expression range (a template's picks key on it).
#[derive(Clone, Copy)]
#[allow(dead_code)] // The item patch (sigedit P1.3) builds these in `reuse_kept`.
pub(crate) struct HeaderEdit {
    pub(crate) fn_index: usize,
    pub(crate) old_exprs: (u32, u32),
}

/// Applies header edits to the kept program `p`. `reach` is the patch
/// base's const reach, if it has one. Err names the first condition that
/// failed (the `kept=` of `lust-visits:`), and says whether `p` is as it
/// was (a refusal before any write, or a diagnostic of a new signature,
/// whose records go back: the caller may keep it for the next request,
/// sigedit R9) or half edited (it must be dropped).
#[allow(dead_code)] // The item patch (sigedit P1.3) calls it from `reuse_kept`.
pub(crate) fn apply_headers(
    p: &mut Program,
    front: &Front,
    caches: &mut Caches,
    reach: Option<&ConstReach>,
    edits: &[HeaderEdit],
    walk_instances: bool,
) -> Result<(), (&'static str, bool)> {
    let fns = untouched_refusals(p, front, reach, edits, walk_instances).map_err(|e| (e, true))?;
    let opaque_idents = opaque_body_idents(p);
    let namers = rpit_namers(p, &opaque_idents, &fns).map_err(|e| (e, true))?;
    super::laps::mark("collect/delta refusals");
    // The node answers of the last collect describe the old signatures.
    caches.gen_reuse.forget_answers();
    // Every new signature first: a body checked below may call any of them.
    let mut errs: Vec<Diag> = Vec::new();
    let mut old_rets = Vec::with_capacity(fns.len());
    let mut undos = Vec::with_capacity(fns.len());
    for &i in &fns {
        let f = LocalDefId(i as u32);
        let rpit = p.gx.opaques.contains_key(&generics::opaque_def(p.def_id(f)));
        old_rets.push((rpit, p.fns[i].ret));
        undos.push(crate::check::delta_audit::sig_undo(p, f));
        let out = crate::check::delta_audit::redo_sig(p, f, rpit, &mut errs);
        if let Err(why) = out.and_then(|()| if errs.is_empty() { Ok(()) } else { Err("sig diag") }) {
            undos.into_iter().rev().for_each(|u| crate::check::delta_audit::undo(p, u));
            return Err((why, true));
        }
    }
    let half = |e: &'static str| (e, false);
    super::laps::mark("collect/delta redo");
    for (&i, &(rpit, old_ret)) in fns.iter().zip(&old_rets) {
        let f = LocalDefId(i as u32);
        if p.gx.fn_class[i] == FnClass::Template {
            let ranges: Vec<(u32, u32)> = edits.iter().filter(|e| e.fn_index == i).map(|e| e.old_exprs).collect();
            recheck_template(p, f, &ranges, caches).map_err(half)?;
        } else if rpit {
            crate::check::delta_audit::reveal_again(p, f, old_ret).map_err(half)?;
        }
    }
    // A plain fn that reveals an opaque type and names an edited fn: its
    // hidden type (and so the auto traits callers read through it) must
    // stand under the new signatures. Then the opaque types that name it
    // see no change either.
    for g in namers {
        let (record_reads, unwind) = (p.record_reads, p.unwind);
        (p.record_reads, p.unwind) = (true, false);
        let stands = crate::check::opaque::hidden_stands(p, g);
        (p.record_reads, p.unwind) = (record_reads, unwind);
        if !stands {
            return Err(half("hidden type"));
        }
    }
    super::laps::mark("collect/delta reveal");
    let out = replay_bodies(p, front, caches, &fns, walk_instances).map_err(half);
    super::laps::mark("collect/delta replay");
    out
}

/// The edited fns of `edits`, sorted, or the first refusal that needs no
/// write to the program (`refusal` and the const reach).
fn untouched_refusals(
    p: &Program,
    front: &Front,
    reach: Option<&ConstReach>,
    edits: &[HeaderEdit],
    walk_instances: bool,
) -> Result<Vec<usize>, &'static str> {
    if !p.gx.user_generics {
        return Err("sig flags");
    }
    let built;
    let reach = match reach {
        Some(r) => r,
        None => {
            built = ConstReach::build(front);
            &built
        }
    };
    let mut fns: Vec<usize> = edits.iter().map(|e| e.fn_index).collect();
    fns.sort_unstable();
    fns.dedup();
    for &i in &fns {
        if i >= front.fn_loc.len() {
            return Err("sig class");
        }
        refusal(p, LocalDefId(i as u32), walk_instances)?;
        if reach.reaches(front, i) {
            return Err("sig const");
        }
    }
    Ok(fns)
}

/// An edited template checks again as collect's template check does
/// (`reuse_kept` does the same for a body edit): its old picks and
/// closure call kinds go, the check records new ones. Its closures must be
/// the registered ones, and its own `impl Trait` must keep its hidden type.
fn recheck_template(p: &mut Program, f: LocalDefId, old: &[(u32, u32)], caches: &mut Caches) -> Result<(), &'static str> {
    if !generics::template_closures_stand(p, f) {
        return Err("closures");
    }
    p.gx.trait_picks.retain(|x, _| !old.iter().any(|r| x.0 >= r.0 && x.0 < r.1));
    p.gx.template_closures.retain(|k, _| k.0 != f);
    p.gx.template_calls.retain(|k, _| k.0 != f);
    // Collect's template check runs before mono.
    let (counts, mono_done) = (p.gx.mono_counts, std::mem::replace(&mut p.gx.mono_done, false));
    let od = generics::opaque_def(p.def_id(f));
    let hidden = p.gx.opaque_hidden.get(&od).copied();
    let errs = generics::check_template(p, f, &mut caches.gen_reuse);
    (p.gx.mono_counts, p.gx.mono_done) = (counts, mono_done);
    if !errs.is_empty() {
        return Err("sig diag");
    }
    if p.gx.opaque_hidden.get(&od).copied() != hidden {
        return Err("hidden type");
    }
    Ok(())
}

/// The identifier sets of the bodies that define an opaque type, by
/// owner def (`refusal` reads them).
fn opaque_body_idents(p: &Program) -> Vec<(crate::def::DefId, Vec<crate::intern::Sym>)> {
    p.gx.opaques
        .values()
        .map(|o| {
            let ids = p.local_def(o.owner.hash).map(|g| super::ast_hash::body_scan(&p.ast, p.fn_def(g), None).1);
            (o.owner, ids.unwrap_or_default())
        })
        .collect()
}

/// Why fn `f` cannot take a header delta, if anything (see the module
/// docs; `apply_headers` adds the const reach and `rpit_namers`). Reads
/// the new Ast and the old program.
fn refusal(p: &Program, f: LocalDefId, walk_instances: bool) -> Result<(), &'static str> {
    let i = f.0 as usize;
    // A template's instances keep their old signatures: only a check that
    // walks none (no build, no generic associated consts) takes it.
    match p.gx.fn_class.get(i) {
        Some(FnClass::Plain) => {}
        Some(FnClass::Template) if !walk_instances && p.gx.assoc_const_tmpls.is_empty() => {}
        _ => return Err("sig class"),
    }
    let info = p.fn_info(f);
    let def = info.def(&p.ast);
    match info.loc {
        FnLoc::Item(_) => {}
        // An inherent method of a local Adt (`inherent_self_pats`); trait
        // impl methods answer to their trait's signature.
        FnLoc::Impl(item, _) if p.gx.inherent_self_pats.contains_key(&f) && p.impl_parents.contains_key(&item) => {}
        _ => return Err("sig loc"),
    }
    // The trait-system key hashes the method heads of an inherent impl
    // with associated items (`gen_reuse::trait_key`); the delta keeps the key.
    if let FnLoc::Impl(item, _) = info.loc
        && let crate::ast::ItemKind::Impl(imp) = &p.ast.items[item as usize].kind
        && (!imp.consts.is_empty() || !imp.types.is_empty())
    {
        return Err("sig trait key");
    }
    if p.is_lang_method(f) || p.fn_shipped_crate(f).is_some() || p.std_source_span(def.name_span) {
        return Err("sig std");
    }
    if p.main == Some(f) || def.name == p.known.main || def.is_test {
        return Err("sig main");
    }
    if info.is_const || def.qual.is_const {
        return Err("sig const");
    }
    if p.gx.static_dyn_fns.contains(&f) || p.gx.dyn_inherent.values().any(|&g| g == f) {
        return Err("sig dyn");
    }
    // An `impl Trait` return of the fn itself reveals again from its body
    // (`delta_audit::reveal_again`, or the template check); the new header
    // must keep one (`redo_sig`). Other bodies that reveal one and name
    // the fn: `rpit_namers`.
    // Collect's eager vtables scan every written `dyn` type.
    if let Some(body) = def.body {
        let (lo, hi, file) = (def.name_span.lo, p.ast.blocks[body.0 as usize].span.lo, def.name_span.file);
        let dyn_in_header = p.ast.tys.iter().zip(&p.ast.ty_spans).any(|(t, s)| {
            s.file == file && s.lo >= lo && s.hi <= hi && matches!(t, crate::ast::TyExpr::Dyn { .. } | crate::ast::TyExpr::MacroCall(_))
        });
        if dyn_in_header {
            return Err("sig dyn");
        }
    } else {
        return Err("sig loc");
    }
    Ok(())
}

/// The plain fns whose bodies reveal an opaque type and name one of the
/// edited fns `fns` (by identifier, as `body_scan` sees the rewritten
/// body), not counting the edited fns themselves: `apply_headers` reveals
/// each again. Refuses when such a body is a template's (its hidden type
/// comes from the template check) or when an opaque owner has no local
/// body to scan.
fn rpit_namers(
    p: &Program,
    opaque_idents: &[(crate::def::DefId, Vec<crate::intern::Sym>)],
    fns: &[usize],
) -> Result<Vec<LocalDefId>, &'static str> {
    let names: Vec<crate::intern::Sym> = fns.iter().map(|&i| p.fn_def(LocalDefId(i as u32)).name).collect();
    let mut out = Vec::new();
    for (owner, ids) in opaque_idents {
        let Some(g) = p.local_def(owner.hash) else { return Err("sig rpit") };
        if fns.contains(&(g.0 as usize)) || !ids.iter().any(|s| names.contains(s)) {
            continue;
        }
        if p.gx.fn_class.get(g.0 as usize) != Some(&FnClass::Plain) || !p.gx.opaque_ret_of.contains_key(&g) {
            return Err("sig rpit");
        }
        out.push(g);
    }
    out.sort_unstable_by_key(|g| g.0);
    out.dedup();
    Ok(out)
}

/// Mono's body checks that read the edited signatures, as a collect with
/// generic reuse runs them (`materialize`, `template_check`): a stored
/// result that no longer holds checks again, and a plain body must give
/// the discovery output collect built the program with.
fn replay_bodies(p: &mut Program, front: &Front, caches: &mut Caches, fns: &[usize], walk_instances: bool) -> Result<(), &'static str> {
    let names: Vec<crate::intern::Sym> = fns.iter().map(|&i| p.fn_def(LocalDefId(i as u32)).name).collect();
    let idents = &front.chunks[0].scan.body_idents;
    let fn_count = front.fn_loc.len();
    // The nodes the delta can move: the edited fns' signatures, and the
    // bindings and method sets whose answers hash them (graph.rs
    // `binding_fingerprint`, `method_set_fingerprint`). No other node
    // reads an edited fn's record (every other fn keeps its signature and
    // hidden type). A `Checked` read never holds by fingerprint.
    let defs: Vec<crate::def::DefId> = fns.iter().map(|&i| p.def_id(LocalDefId(i as u32))).collect();
    let mut seen: crate::intern::FxMap<ReadKey, bool> = Default::default();
    let mut touched = |p: &Program, k: &ReadKey| -> bool {
        *seen.entry(*k).or_insert_with(|| match k {
            ReadKey::Sig(d) => defs.contains(d),
            ReadKey::MethodSet(m) => names.contains(&m.name),
            ReadKey::Binding(b) => {
                names.contains(&b.name) || matches!(p.binding_res(b.module, b.ns, b.name), BindingRes::Def(d) if defs.contains(&d))
            }
            ReadKey::Checked(_) => true,
            ReadKey::ImplSet(_) | ReadKey::Layout(_) | ReadKey::TraitInScope(..) | ReadKey::Derives(_) => false,
        })
    };
    let (record_reads, unwind) = (p.record_reads, p.unwind);
    (p.record_reads, p.unwind) = (true, false);
    let out = (|| {
        let reuse = &mut caches.gen_reuse;
        let mut again = Vec::new();
        for t in (0..fn_count as u32).map(LocalDefId) {
            if p.gx.fn_class.get(t.0 as usize) != Some(&FnClass::Template) || p.is_lang_method(t) || fns.contains(&(t.0 as usize)) {
                continue;
            }
            if p.check_skips(t) && !p.gx.opaques.contains_key(&generics::opaque_def(p.def_id(t))) {
                continue;
            }
            // The other mode's program stored this check: this one may
            // hold another.
            if reuse.newer(p, t, p.reuse_stamp) {
                return Err("sig mode");
            }
            // Every entry no newer than the program held for it.
            if reuse.untouched(p, t, &mut |k| touched(p, k)) {
                continue;
            }
            // A template with no stored check (one with closures) stands
            // while its body does not name an edited fn.
            let named = idents.get(t.0 as usize).is_none_or(|ids| ids.iter().any(|s| names.contains(s)));
            if !reuse.template_holds(p, t).unwrap_or(!named) {
                again.push(t);
            }
        }
        // A template whose check no longer holds checks again, as collect
        // does, in a check only: a build's instances of it would keep
        // their old checks.
        if !again.is_empty() && walk_instances {
            return Err("sig template");
        }
        for t in again {
            let (lo, hi) = p.fn_def(t).exprs;
            recheck_template(p, t, &[(lo, hi)], caches)?;
        }
        super::laps::mark("collect/delta replay templates");
        let reuse = &mut caches.gen_reuse;
        for g in (0..fn_count as u32).map(LocalDefId) {
            if p.gx.fn_class.get(g.0 as usize) != Some(&FnClass::Plain) || p.check_skips(g) {
                continue;
            }
            // A holding entry stands for this program's output only when
            // this program stored or replayed it (`Program::reuse_stamp`).
            if reuse.newer(p, g, p.reuse_stamp) {
                return Err("sig mode");
            }
            if reuse.untouched(p, g, &mut |k| touched(p, k)) || reuse.discovery_holds(p, g) {
                continue;
            }
            let base = reuse.out_copy(p.def_id(g)).ok_or("discovery")?;
            let (checked, discarded) = crate::check::check_fn(p, g);
            if checked.closure_map_pending {
                return Err("discovery");
            }
            let out = generics::discovery_out(p, &checked, &discarded);
            if !base.same(p, &out, walk_instances) {
                return Err("discovery");
            }
            if discarded.is_empty() {
                let (adt_tys, reqs, closures, vts) = &out;
                reuse.store_discovered(p, g, &checked.reads, adt_tys, reqs, closures, vts);
            } else {
                reuse.note_unstored(p, g);
            }
            reuse.discovery_checked += 1;
            drop((checked, discarded));
            // Every body type enters the global store, as discovery does.
            for t in out.0.iter().chain(out.3.iter().flat_map(|(a, b)| [a, b])) {
                generics::build_owned_ty(p, t);
            }
        }
        Ok(())
    })();
    (p.record_reads, p.unwind) = (record_reads, unwind);
    out
}

/// The header delta's answer for every user fn of `p` (a census for
/// `LUST_SIGDELTA_SELFTEST=v`): the number of fns per refusal reason, and
/// "ok" for those it takes. Const reach is not counted (it needs the
/// patch base); std and lang fns are left out.
pub(crate) fn census(p: &Program) -> Vec<(&'static str, usize)> {
    let opaque_idents = opaque_body_idents(p);
    let mut out: Vec<(&'static str, usize)> = Vec::new();
    for i in 0..p.fns.len() {
        let f = LocalDefId(i as u32);
        if !matches!(p.gx.fn_class[i], FnClass::Plain | FnClass::Template)
            || p.gx.closure_fns.contains_key(&f)
            || p.is_lang_method(f)
            || p.fn_shipped_crate(f).is_some()
            || p.std_source_span(p.fn_def(f).name_span)
        {
            continue;
        }
        let why = refusal(p, f, false).and_then(|()| rpit_namers(p, &opaque_idents, &[i]).map(drop)).err().unwrap_or("ok");
        match out.iter_mut().find(|e| e.0 == why) {
            Some(e) => e.1 += 1,
            None => out.push((why, 1)),
        }
    }
    out.sort_by(|a, b| b.1.cmp(&a.1));
    out
}
