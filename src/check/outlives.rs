// Outlives requirements of written types (rustc E0309, E0310, E0491; L0617).
//
// A type is well-formed only when what it borrows outlives the borrow:
// `&'a T` needs `T: 'a`, `&'a &'b ()` needs `'b: 'a`, `S<'a, T>` needs what
// the fields of `S` need (rustc's inferred outlives, `infer_adts`). An item
// may assume these requirements for the types it takes and gives (implied
// bounds): a fn's params and return, an impl's header, an Adt's fields.
// The types its bounds name (where clauses, param bounds, assoc bindings,
// `impl Trait` args), an impl's assoc type values, and the bounds of a
// trait or an Adt get no such help: their requirements must follow from
// the implied ones, the declared `'a: 'b` facts, and `T: 'static` bounds.
// lust rejects a written `T: 'a` bound (L0203), so a type param outlives a
// named lifetime only through implied bounds or `'static`.
//
// Collect records each item (`wanted`) with its types resolved in
// `RegionMode::Keep` (`Region::Param` for the item's lifetimes, `'static`
// as `Region::Static`). A region bound by a `for<..>` or `Fn` sugar
// (`Region::Bound`) and an erased one put no requirement.

use crate::check::collect::Program;
use crate::check::generics::STATIC_FACT;
use crate::def::DefId;
use crate::diag::{Diag, Span};
use crate::ty::*;

/// What the walks read from the program: the Adt tables and the traits.
struct Cx<'a> {
    regions: &'a crate::borrowck::RegionTables,
    index: &'a crate::traits::index::ImplIndex,
}

/// One requirement `subject: region`; the subject is a type or a region.
type Req = (GenericArg, Region);

/// What a type's outlives requirement splits into (rustc's outlives
/// components): its regions, its type params, its projections.
#[derive(Clone, Copy, PartialEq)]
enum Comp {
    Re(Region),
    Param(Ty),
    Proj(Ty),
}

/// The known outlives facts of one item: `x: r` between regions, and a
/// type param or projection that outlives a region.
#[derive(Default)]
struct Env {
    re: Vec<(Region, Region)>,
    ty: Vec<(Ty, Region)>,
    statics: Vec<Ty>,
}

/// One item's types for the check (see the file comment), recorded at
/// collect (`wanted`) and checked once every Adt has its fields
/// (`check_all`). `facts` are the declared `'a: 'b` facts by universal
/// index (`STATIC_FACT` is `'static`), `statics` the type params with a
/// `T: 'static` bound.
#[derive(Clone, Debug)]
pub struct Item {
    pub implied: Vec<Ty>,
    pub required: Vec<Ty>,
    pub facts: Vec<(u32, u32)>,
    pub statics: Vec<Ty>,
    pub span: Span,
}

/// Whether to record an item in `RegionTables::outlives_items`: not when
/// it requires nothing or is shipped source (std, core, alloc, and the
/// platform crate are valid as written). Callers push it themselves, so
/// a borrow of the AST may stay live.
pub fn wanted(p: &Program, item: &Item) -> bool {
    !item.required.is_empty() && !p.in_lang_methods(item.span) && p.shipped_crate_at(item.span).is_none()
}

/// The type params with a `T: 'static` bound among `preds`.
pub fn statics_of(preds: &[Predicate]) -> Vec<Ty> {
    preds.iter().filter_map(|q| if let Predicate::TypeOutlives(x, Region::Static) = q { Some(*x) } else { None }).collect()
}

/// Infers the Adt tables, then checks every recorded item. The first
/// requirement of an item that does not hold is its error.
pub fn check_all(p: &mut Program, errs: &mut Vec<Diag>) {
    let items = std::mem::take(&mut p.regions.outlives_items);
    // Body annotations read the Adt tables too (`check_body_ty`).
    infer_adts(p);
    for it in items {
        if let Some(d) = check_item(p, &it) {
            errs.push(d);
        }
    }
}

fn check_item(p: &mut Program, it: &Item) -> Option<Diag> {
    let cx = Cx { regions: &p.regions, index: &p.gx.index };
    let env = implied_env(&cx, &mut p.tys, &it.implied, &it.facts, &it.statics);
    let bad = unmet(&cx, &mut p.tys, &env, &it.required);
    bad.map(|(g, r)| diag(p, g, r, it.span))
}

/// The facts an item knows: declared ones, `T: 'static` bounds, and the
/// requirements of its implied types.
fn implied_env(cx: &Cx, tys: &mut impl TyIntern, implied: &[Ty], facts: &[(u32, u32)], statics: &[Ty]) -> Env {
    let mut env = Env { statics: statics.to_vec(), ..Env::default() };
    for &(a, b) in facts {
        env.re.push((Region::Param(a), if b == STATIC_FACT { Region::Static } else { Region::Param(b) }));
    }
    for &t in implied {
        let mut reqs = Vec::new();
        wf(cx, tys, t, &mut reqs);
        for (g, r) in reqs {
            assume(tys, &mut env, g, r);
        }
    }
    env
}

/// The first requirement of the `required` types that `env` does not prove.
fn unmet(cx: &Cx, tys: &mut impl TyIntern, env: &Env, required: &[Ty]) -> Option<Req> {
    for &t in required {
        let mut reqs = Vec::new();
        wf(cx, tys, t, &mut reqs);
        if let Some(bad) = reqs.into_iter().find(|&(g, r)| !holds(cx, tys, env, g, r)) {
            return Some(bad);
        }
    }
    None
}

/// Checks a type written in the body of a fn with region signature
/// `sig` (a `let` annotation) under the fn's implied bounds and its
/// `T: 'static` bounds in `preds`. The error, if a requirement fails.
pub fn check_body_ty(p: &Program, tys: &mut impl TyIntern, sig: &crate::borrowck::RegionSig, preds: &[Predicate], t: Ty, span: Span) -> Option<Diag> {
    let mut implied: Vec<Ty> = sig.params.iter().copied().chain([sig.ret]).collect();
    implied.extend(sig.header.iter().copied());
    let facts: Vec<(u32, u32)> = sig
        .facts
        .iter()
        .filter_map(|&(a, b)| match (a, b) {
            (Region::Param(x), Region::Param(y)) => Some((x, y)),
            (Region::Param(x), Region::Static) => Some((x, STATIC_FACT)),
            _ => None,
        })
        .collect();
    let cx = Cx { regions: &p.regions, index: &p.gx.index };
    let env = implied_env(&cx, tys, &implied, &facts, &statics_of(preds));
    unmet(&cx, tys, &env, &[t]).map(|(g, r)| diag_in(p, tys, g, r, span))
}

/// The diagnostic for a requirement `g: r` that does not hold.
/// What a fn knows of its type params' lifetimes: `(param index,
/// region)` for each bound its signature implies (region signature
/// `sig`) or its env `preds` states as `T: 'static`. Borrowck's dyn
/// coercions read it (`OwnSig::param_univs`).
pub fn param_bounds(p: &Program, sig: Option<&crate::borrowck::RegionSig>, preds: &[Predicate]) -> Vec<(u32, Region)> {
    let mut out: Vec<(u32, Region)> = Vec::new();
    let mut tys = crate::ty::Tys::new(&p.tys);
    for t in statics_of(preds) {
        if let TyKind::Param(j) = tys.kind(t) {
            out.push((j.0, Region::Static));
        }
    }
    let Some(sig) = sig else { return out };
    let mut implied: Vec<Ty> = sig.params.iter().copied().chain([sig.ret]).collect();
    implied.extend(sig.header.iter().copied());
    let cx = Cx { regions: &p.regions, index: &p.gx.index };
    let env = implied_env(&cx, &mut tys, &implied, &[], &[]);
    for (t, r) in env.ty {
        if let TyKind::Param(j) = tys.kind(t) {
            out.push((j.0, r));
        }
    }
    out
}

fn diag(p: &Program, g: GenericArg, r: Region, span: Span) -> Diag {
    diag_in(p, &p.tys, g, r, span)
}

fn diag_in(p: &Program, tys: &impl TyIntern, g: GenericArg, r: Region, span: Span) -> Diag {
    let what = match g {
        GenericArg::Ty(t) => format!("the type `{}`", crate::check::collect::ty_name(p, tys, t)),
        _ => "a lifetime in this type".to_string(),
    };
    let (life, fix) = if r == Region::Static {
        ("`'static`", "Add a `'static` bound to the type parameter, or change the type.")
    } else {
        ("a lifetime this type names", "Take a parameter of this type (an implied bound), add a `'a: 'b` bound, or change the type.")
    };
    Diag::new("L0617", span, format!("{what} may not live long enough: a type here needs it to outlive {life}"), fix)
}

/// Records the requirements of an implied type as facts.
fn assume(tys: &impl TyIntern, env: &mut Env, g: GenericArg, r: Region) {
    match g {
        GenericArg::Lifetime(x) => env.re.push((x, r)),
        GenericArg::Ty(t) => {
            let mut cs = Vec::new();
            components(tys, t, &mut cs);
            for c in cs {
                match c {
                    Comp::Re(x) => env.re.push((x, r)),
                    Comp::Param(x) | Comp::Proj(x) => env.ty.push((x, r)),
                }
            }
        }
        GenericArg::Const(_) => {}
    }
}

/// True when `r` is a region the item names: a lifetime param or `'static`.
fn named(r: Region) -> bool {
    matches!(r, Region::Param(_) | Region::Static)
}

/// Whether `g: r` follows from the env.
fn holds(cx: &Cx, tys: &impl TyIntern, env: &Env, g: GenericArg, r: Region) -> bool {
    if !named(r) {
        return true;
    }
    match g {
        GenericArg::Lifetime(x) => region_holds(env, x, r),
        GenericArg::Ty(t) => ty_holds(cx, tys, env, t, r),
        GenericArg::Const(_) => true,
    }
}

fn ty_holds(cx: &Cx, tys: &impl TyIntern, env: &Env, t: Ty, r: Region) -> bool {
    let mut cs = Vec::new();
    components(tys, t, &mut cs);
    cs.into_iter().all(|c| match c {
        Comp::Re(x) => region_holds(env, x, r),
        Comp::Param(x) => env.statics.contains(&x) || env.ty.iter().any(|&(y, s)| y == x && region_holds(env, s, r)),
        Comp::Proj(x) => {
            env.ty.iter().any(|&(y, s)| y == x && region_holds(env, s, r))
                || assoc_is_static(cx, tys, x)
                || match tys.kind(x) {
                    TyKind::Projection(_, a) => tys.args(a).to_vec().into_iter().all(|g| holds(cx, tys, env, g, r)),
                    _ => true,
                }
        }
    })
}

/// `<T as Tr>::A` where the trait declares `type A: 'static`.
fn assoc_is_static(cx: &Cx, tys: &impl TyIntern, t: Ty) -> bool {
    let TyKind::Projection(assoc, _) = tys.kind(t) else { return false };
    let Some(rec) = cx.index.trait_of_assoc(assoc.0).and_then(|d| cx.index.trait_record(d)) else { return false };
    rec.generics.predicates.iter().any(|q| match q {
        Predicate::TypeOutlives(x, Region::Static) => matches!(tys.kind(*x), TyKind::Projection(b, _) if b == assoc),
        _ => false,
    })
}

/// `x: r` for regions, through the facts (reflexive and transitive;
/// `'static` outlives every region, and an unnamed region is not checked).
fn region_holds(env: &Env, x: Region, r: Region) -> bool {
    if x == r || x == Region::Static || !named(x) || !named(r) {
        return true;
    }
    let mut seen = vec![x];
    let mut i = 0;
    while i < seen.len() {
        let a = seen[i];
        i += 1;
        for &(u, v) in &env.re {
            if u == a && !seen.contains(&v) {
                if v == r || v == Region::Static {
                    return true;
                }
                seen.push(v);
            }
        }
    }
    false
}

/// The outlives components of `t` (rustc's `compute_components`): every
/// region, type param, and projection in it. A projection is one
/// component; `ty_holds` splits it further when no fact names it.
fn components(tys: &impl TyIntern, t: Ty, out: &mut Vec<Comp>) {
    match tys.kind(t) {
        TyKind::Ref(r, _, e) => {
            out.push(Comp::Re(r));
            components(tys, e, out);
        }
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) => args_components(tys, a, out),
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                components(tys, e, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => components(tys, e, out),
        TyKind::FnPtr(sig) => {
            let b = tys.sig(sig);
            for e in tys.tys_of(b.value.inputs).to_vec() {
                components(tys, e, out);
            }
            components(tys, b.value.output, out);
        }
        TyKind::Dyn(b, r) => {
            out.push(Comp::Re(r));
            for tr in dyn_refs(tys, b) {
                trait_ref_components(tys, tr, out);
            }
        }
        TyKind::Param(_) => out.push(Comp::Param(t)),
        TyKind::Projection(..) => out.push(Comp::Proj(t)),
        _ => {}
    }
}

fn args_components(tys: &impl TyIntern, a: ArgsId, out: &mut Vec<Comp>) {
    for g in tys.args(a).to_vec() {
        match g {
            GenericArg::Ty(e) => components(tys, e, out),
            GenericArg::Lifetime(r) => out.push(Comp::Re(r)),
            GenericArg::Const(_) => {}
        }
    }
}

/// A trait ref's parts past `Self`: its args and bound types.
fn trait_ref_components(tys: &impl TyIntern, tr: TraitRef, out: &mut Vec<Comp>) {
    for g in tys.args(tr.args).iter().skip(1).copied().collect::<Vec<_>>() {
        match g {
            GenericArg::Ty(e) => components(tys, e, out),
            GenericArg::Lifetime(r) => out.push(Comp::Re(r)),
            GenericArg::Const(_) => {}
        }
    }
    for (_, g) in tys.bindings(tr.bindings).to_vec() {
        if let GenericArg::Ty(e) = g {
            components(tys, e, out);
        }
    }
}

/// The trait refs of a `dyn` type: its principal and written supertraits.
fn dyn_refs(tys: &impl TyIntern, b: BoundsId) -> Vec<TraitRef> {
    let d = tys.dyn_bounds(b);
    d.principal.iter().chain(d.supertraits.iter()).map(|tr| tr.value).collect()
}

/// The outlives requirements of `t` being well-formed (rustc's WF
/// obligations, outlives part): `&'r X` needs `X: 'r`, an Adt needs
/// its inferred outlives under its args, and so on into every part.
fn wf(cx: &Cx, tys: &mut impl TyIntern, t: Ty, out: &mut Vec<Req>) {
    match tys.kind(t) {
        TyKind::Ref(r, _, e) => {
            out.push((GenericArg::Ty(e), r));
            wf(cx, tys, e, out);
        }
        TyKind::Adt(d, a) => {
            let argv: Vec<GenericArg> = tys.args(a).to_vec();
            adt_reqs(cx, tys, d, &argv, out);
            for g in argv {
                if let GenericArg::Ty(e) = g {
                    wf(cx, tys, e, out);
                }
            }
        }
        TyKind::Tuple(ts) => {
            for e in tys.tys_of(ts).to_vec() {
                wf(cx, tys, e, out);
            }
        }
        TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::RawPtr(_, e) => wf(cx, tys, e, out),
        TyKind::FnPtr(sig) => {
            let b = tys.sig(sig);
            for e in tys.tys_of(b.value.inputs).to_vec() {
                wf(cx, tys, e, out);
            }
            wf(cx, tys, b.value.output, out);
        }
        TyKind::Dyn(b, _) => {
            for tr in dyn_refs(tys, b) {
                trait_ref_wf(cx, tys, tr, out);
            }
        }
        TyKind::Projection(_, a) => {
            for g in tys.args(a).to_vec() {
                if let GenericArg::Ty(e) = g {
                    wf(cx, tys, e, out);
                }
            }
        }
        _ => {}
    }
}

/// `wf` of a trait ref's types (a bound, or a `dyn` principal): its
/// args and bound types.
pub(crate) fn trait_ref_wf_tys(tys: &impl TyIntern, tr: TraitRef, out: &mut Vec<Ty>) {
    for g in tys.args(tr.args).to_vec() {
        if let GenericArg::Ty(e) = g {
            out.push(e);
        }
    }
    for (_, g) in tys.bindings(tr.bindings).to_vec() {
        if let GenericArg::Ty(e) = g {
            out.push(e);
        }
    }
}

fn trait_ref_wf(cx: &Cx, tys: &mut impl TyIntern, tr: TraitRef, out: &mut Vec<Req>) {
    let mut ts = Vec::new();
    trait_ref_wf_tys(tys, tr, &mut ts);
    // `Self` of a `dyn` principal is a placeholder.
    for e in ts.into_iter().filter(|&e| e != DYN_SELF) {
        wf(cx, tys, e, out);
    }
}

/// The requirements of one Adt use with region-kept args (lifetimes
/// first, then types and consts): its inferred outlives table under
/// these args; a builtin Adt with no table needs each type arg to
/// outlive each lifetime arg (`slice::Iter<'a, T>`, `Ref<'b, T>`).
fn adt_reqs(cx: &Cx, tys: &mut impl TyIntern, d: DefId, argv: &[GenericArg], out: &mut Vec<Req>) {
    let lts: Vec<Region> = argv.iter().filter_map(|g| if let GenericArg::Lifetime(r) = g { Some(*r) } else { None }).collect();
    let rest: Vec<GenericArg> = argv.iter().copied().filter(|g| !matches!(g, GenericArg::Lifetime(_))).collect();
    let Some(table) = cx.regions.adt_outlives.get(&d).cloned() else {
        if cx.regions.adt_fields.contains_key(&d) {
            return;
        }
        for &r in &lts {
            for g in &rest {
                if let GenericArg::Ty(e) = g {
                    out.push((GenericArg::Ty(*e), r));
                }
            }
        }
        return;
    };
    let re = |r: Region| match r {
        Region::Param(k) => lts.get(k as usize).copied().unwrap_or(Region::Erased),
        r => r,
    };
    for (g, r) in table {
        let g = match g {
            GenericArg::Lifetime(x) => GenericArg::Lifetime(re(x)),
            GenericArg::Ty(t) => GenericArg::Ty(subst(tys, t, &rest)),
            c => c,
        };
        out.push((g, re(r)));
    }
}

/// Fills `RegionTables::adt_outlives`: per user Adt, the requirements
/// over its own params that its fields put (rustc's inferred outlives),
/// its declared `'a: 'b` facts, and its `T: 'static` bounds. Nested Adts
/// pass theirs up; the table iterates to a fixpoint.
fn infer_adts(p: &mut Program) {
    p.regions.adt_outlives.clear();
    let mut defs: Vec<DefId> = p.regions.adt_fields.keys().copied().collect();
    defs.sort_by_key(|d| (d.krate.0, d.hash.0));
    let statics: Vec<(DefId, Vec<Ty>)> = defs
        .iter()
        .filter_map(|&d| {
            let a = p.adt_by_def(d)?;
            let s: Vec<Ty> = p.gx.adt_generics[a.0 as usize]
                .predicates
                .iter()
                .filter_map(|q| if let Predicate::TypeOutlives(x, Region::Static) = q { Some(*x) } else { None })
                .collect();
            Some((d, s))
        })
        .collect();
    for _ in 0..16 {
        let mut changed = false;
        for &d in &defs {
            let fields: Vec<Ty> = p.regions.adt_fields[&d].iter().flatten().copied().collect();
            let facts = p.regions.adt_facts.get(&d).cloned().unwrap_or_default();
            let cx = Cx { regions: &p.regions, index: &p.gx.index };
            let env = implied_env(&cx, &mut p.tys, &fields, &facts, &[]);
            let mut table: Vec<Req> = Vec::new();
            for &(x, r) in &env.re {
                if matches!(x, Region::Param(_)) && named(r) && x != r && !table.contains(&(GenericArg::Lifetime(x), r)) {
                    table.push((GenericArg::Lifetime(x), r));
                }
            }
            for &(x, r) in &env.ty {
                if named(r) && !table.contains(&(GenericArg::Ty(x), r)) {
                    table.push((GenericArg::Ty(x), r));
                }
            }
            for (_, s) in statics.iter().filter(|(e, _)| *e == d) {
                for &x in s {
                    if !table.contains(&(GenericArg::Ty(x), Region::Static)) {
                        table.push((GenericArg::Ty(x), Region::Static));
                    }
                }
            }
            if table.is_empty() {
                continue;
            }
            if p.regions.adt_outlives.get(&d) != Some(&table) {
                p.regions.adt_outlives.insert(d, table);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}
