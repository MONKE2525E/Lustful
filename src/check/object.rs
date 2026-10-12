// `dyn Trait` (docs/ARCH.md section 2.8): dyn compatibility, the vtable
// layout of each user trait, object method lookup for dyn receivers
// (section 2.10), and the slot paths of trait upcasting.
//
// One `DynInfo` per user trait is computed after the trait tables
// exist (`compute_dyn_infos`, from `finish_collect`). Everything else
// reads it: the dyn type checks at signature and body sites, the
// method probe for dyn receivers, the coercion checks, mono's vtable
// builder, lowering (slot paths), and codegen (vtable statics).
//
// Vtable layout, one array of pointer-sized words per (concrete type,
// principal trait ref):
//
//   [0]  drop glue for the concrete type, or 0 when it needs none
//   [1]  size of the concrete type (Rust layout)
//   [2]  align of the concrete type
//   [3 .. 3+S)  one vtable pointer per direct supertrait that has a
//               vtable, in declaration order (the `super_N` slots)
//   [3+S ..)    one entry per vtable method, in declaration order
//
// A method entry is a per-vtable shim that forwards through
// `lust_fns[slot]`, never a body address, so a daemon overlay that
// swaps a method body cannot leave a stale entry (ARCH 4.5). A
// supertrait method is reached through its `super_N` chain, which is
// also the upcast path: upcasting `&dyn Sub` to `&dyn Super` loads one
// super slot per level, fixed at compile time.
use crate::check::collect::Program;
use crate::def::{DefId, LocalDefId};
use crate::diag::{Diag, Span};
use crate::intern::{FxMap, Sym};
use crate::ty::*;

/// Words before the first super slot: drop, size, align.
pub const VT_HEADER: u32 = 3;

/// How a vtable method takes its receiver.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DynRecv {
    Ref,
    RefMut,
}

/// One vtable method of a trait.
#[derive(Clone, Debug)]
pub struct DynMethod {
    pub def: DefId,
    pub name: Sym,
    pub recv: DynRecv,
}

/// The dyn view of one user trait.
#[derive(Clone, Debug, Default)]
pub struct DynInfo {
    /// Why the trait is not dyn compatible (rustc E0038), first reason
    /// found: the message tail and the offending item's span.
    pub violation: Option<(String, Span)>,
    /// A dyn form the subset cannot build a vtable for yet.
    pub unsupported: Option<String>,
    /// Direct supertraits with a vtable, in declaration order, as trait
    /// refs over this trait's params (Self is `Param(0)`).
    pub supers: Vec<TraitRef>,
    /// Auto traits the trait requires through its supertraits.
    pub auto: AutoTraits,
    /// Vtable methods in declaration order.
    pub methods: Vec<DynMethod>,
    /// Methods that exist but cannot be called through dyn: the name,
    /// its def, and why.
    pub uncallable: Vec<(Sym, DefId, &'static str)>,
}

impl DynInfo {
    /// The word index of super slot `i`.
    pub fn super_slot(&self, i: usize) -> u32 {
        VT_HEADER + i as u32
    }
    /// The word index of vtable method `j`.
    pub fn method_slot(&self, j: usize) -> u32 {
        VT_HEADER + self.supers.len() as u32 + j as u32
    }
}

/// One materialized vtable (built by mono, emitted by codegen).
#[derive(Clone, Debug)]
pub struct VtableData {
    /// The concrete type behind the pointer (global store).
    pub self_ty: Ty,
    /// The existential principal trait ref (global store).
    pub principal: TraitRef,
    /// The callable fn for each vtable method, in `DynInfo::methods` order.
    pub methods: Vec<LocalDefId>,
    /// The vtable for each super slot, in `DynInfo::supers` order.
    pub supers: Vec<u32>,
}

/// The dyn info of every user trait. Runs once trait tables exist.
pub fn compute_dyn_infos(p: &Program) -> FxMap<DefId, DynInfo> {
    let mut memo: FxMap<DefId, DynInfo> = FxMap::default();
    let mut defs: Vec<DefId> = p.gx.trait_names.values().copied().collect();
    defs.sort_by_key(|d| d.hash.0);
    for d in defs {
        info_of(p, d, &mut memo, &mut Vec::new());
    }
    memo
}

/// Lang traits whose definition requires `Self: Sized` in std.
fn lang_requires_sized(p: &Program, def: DefId) -> bool {
    let l = &p.gx.lang;
    [l.sized, l.copy, l.clone, l.default, l.from, l.into, l.from_iterator].contains(&def)
}

/// True when a trait predicate on `Self` implies `Self: Sized`, through
/// lang facts and user supertraits.
fn implies_sized(p: &Program, def: DefId, seen: &mut Vec<DefId>) -> bool {
    if lang_requires_sized(p, def) {
        return true;
    }
    if seen.contains(&def) {
        return false;
    }
    seen.push(def);
    let Some(rec) = p.gx.index.trait_record(def) else { return false };
    if !rec.local {
        return false;
    }
    rec.generics.predicates.iter().any(|pred| match pred {
        Predicate::Trait(b) => is_self(&p.tys, p.tys.args(b.value.args)[0]) && implies_sized(p, b.value.def, seen),
        _ => false,
    })
}

fn is_self(tys: &impl TyIntern, g: GenericArg) -> bool {
    g.as_ty().is_some_and(|t| matches!(tys.kind(t), TyKind::Param(ParamId(0))))
}

/// True when `Self` (`Param(0)`) occurs in `t` outside the Self slot of
/// a projection (`Self::Assoc` names the erased type's binding, which a
/// dyn type would supply).
fn mentions_self(tys: &impl TyIntern, t: Ty) -> bool {
    if !tys.flags(t).contains_param() {
        return false;
    }
    let args_mention = |a: ArgsId, skip_self: bool| {
        tys.args(a).iter().enumerate().any(|(i, g)| match g.as_ty() {
            Some(e) => !(skip_self && i == 0 && is_self(tys, *g)) && mentions_self(tys, e),
            None => false,
        })
    };
    match tys.kind(t) {
        TyKind::Param(q) => q.0 == 0,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => mentions_self(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| mentions_self(tys, e)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) => args_mention(a, false),
        TyKind::Projection(_, a) => args_mention(a, true),
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            mentions_self(tys, s.output) || tys.tys_of(s.inputs).iter().any(|&e| mentions_self(tys, e))
        }
        TyKind::Dyn(b, _) => tys.dyn_bounds(b).principal.is_some_and(|pr| args_mention(pr.value.args, true)),
        _ => false,
    }
}

/// Fills `memo[def]`. Supertraits are computed first, so their
/// violations, unsupported forms, and auto traits fold into this one.
fn info_of(p: &Program, def: DefId, memo: &mut FxMap<DefId, DynInfo>, stack: &mut Vec<DefId>) {
    if memo.contains_key(&def) || stack.contains(&def) {
        return;
    }
    stack.push(def);
    let mut info = DynInfo::default();
    let Some(rec) = p.gx.index.trait_record(def).cloned() else {
        stack.pop();
        return;
    };
    let tname = p.name(rec.name).to_string();
    let lang = &p.gx.lang;
    // Trait-level facts: supertraits and `Self: Sized`.
    for pred in &rec.generics.predicates {
        let Predicate::Trait(b) = pred else { continue };
        let args = p.tys.args(b.value.args).to_vec();
        if !is_self(&p.tys, args[0]) {
            continue;
        }
        let sup = b.value.def;
        if implies_sized(p, sup, &mut Vec::new()) {
            info.violation.get_or_insert((format!("it requires `Self: Sized`, which a `dyn {tname}` value is not"), rec.span));
            continue;
        }
        if args[1..].iter().any(|g| g.as_ty().is_some_and(|t| mentions_self(&p.tys, t))) {
            info.violation.get_or_insert((format!("a supertrait of `{tname}` uses `Self` as a type parameter"), rec.span));
            continue;
        }
        if lang.is_auto(sup) {
            if sup == lang.send {
                info.auto.send = true;
            } else if sup == lang.sync {
                info.auto.sync = true;
            } else {
                info.auto.unpin = true;
            }
            continue;
        }
        let Some(srec) = p.gx.index.trait_record(sup) else { continue };
        if !srec.local {
            info.unsupported.get_or_insert(format!("`dyn {tname}` with the std supertrait `{}`", p.name(srec.name)));
            continue;
        }
        info_of(p, sup, memo, stack);
        if let Some(si) = memo.get(&sup) {
            if let Some((why, _)) = &si.violation {
                info.violation.get_or_insert((format!("its supertrait `{}` is not dyn compatible: {why}", p.name(srec.name)), rec.span));
            }
            if let Some(u) = &si.unsupported {
                info.unsupported.get_or_insert(u.clone());
            }
            info.auto.send |= si.auto.send;
            info.auto.sync |= si.auto.sync;
            info.auto.unpin |= si.auto.unpin;
        }
        if !info.supers.iter().any(|s| *s == b.value) {
            info.supers.push(b.value);
        }
    }
    for (_, aname, is_type) in &rec.assoc_items {
        if *is_type {
            info.unsupported.get_or_insert(format!("`dyn {tname}` with the associated type `{}`", p.name(*aname)));
        } else {
            info.violation.get_or_insert((format!("it contains the associated const `{}`", p.name(*aname)), rec.span));
        }
    }
    // Methods: dispatchable ones get vtable entries; `where Self:
    // Sized` ones are skipped, as in rustc.
    let n_params = rec.generics.params.len();
    let n_preds = rec.generics.predicates.len();
    for &(mdef, mname) in &rec.methods {
        let Some(tm) = p.gx.trait_methods.get(&mdef) else { continue };
        let span = tm.def.name_span;
        let mn = p.name(mname).to_string();
        let own_preds = tm.generics.predicates.get(n_preds..).unwrap_or(&[]);
        let exempt = own_preds.iter().any(|pred| match pred {
            Predicate::Trait(b) => is_self(&p.tys, p.tys.args(b.value.args)[0]) && implies_sized(p, b.value.def, &mut Vec::new()),
            _ => false,
        });
        if exempt {
            info.uncallable.push((mname, mdef, "it requires `Self: Sized`"));
            continue;
        }
        let bad = |why: String| Some((why, span));
        let mut v: Option<(String, Span)> = None;
        let recv = match tm.self_kind {
            None => {
                v = v.or(bad(format!("associated function `{mn}` has no `self` parameter")));
                None
            }
            Some(_) => match p.tys.kind(tm.params[0]) {
                TyKind::Param(ParamId(0)) => None,
                TyKind::Ref(_, m, inner) if matches!(p.tys.kind(inner), TyKind::Param(ParamId(0))) => {
                    Some(if m.is_mut() { DynRecv::RefMut } else { DynRecv::Ref })
                }
                _ => {
                    info.unsupported.get_or_insert(format!("calls through `dyn {tname}` to the receiver form of `{mn}`"));
                    None
                }
            },
        };
        if tm.generics.params.len() > n_params {
            v = v.or(bad(format!("method `{mn}` has generic type parameters")));
        }
        if tm.params.iter().skip(1).any(|&t| mentions_self(&p.tys, t)) {
            v = v.or(bad(format!("method `{mn}` references the `Self` type in a parameter")));
        }
        if mentions_self(&p.tys, tm.ret) {
            v = v.or(bad(format!("method `{mn}` references the `Self` type in its return type")));
        }
        let pred_mentions = |pred: &Predicate| match pred {
            Predicate::Trait(b) => p.tys.args(b.value.args).iter().any(|g| g.as_ty().is_some_and(|t| mentions_self(&p.tys, t))),
            Predicate::AssocEq(b) => {
                mentions_self(&p.tys, b.value.ty)
                    || p.tys.args(b.value.trait_args).iter().any(|g| g.as_ty().is_some_and(|t| mentions_self(&p.tys, t)))
            }
            Predicate::TypeOutlives(t, _) => mentions_self(&p.tys, *t),
            Predicate::Outlives(..) => false,
        };
        if own_preds.iter().any(pred_mentions) {
            v = v.or(bad(format!("method `{mn}` references the `Self` type in its `where` clause")));
        }
        if let Some(v) = v {
            info.violation.get_or_insert(v);
            continue;
        }
        match recv {
            Some(recv) => info.methods.push(DynMethod { def: mdef, name: mname, recv }),
            None if tm.self_kind.is_some() => info.uncallable.push((mname, mdef, "it takes `self` by value, and a `dyn` value has no size")),
            None => {}
        }
    }
    stack.pop();
    memo.insert(def, info);
}

/// The trait name for messages.
pub fn trait_name(p: &Program, def: DefId) -> String {
    p.gx.index.trait_record(def).map_or_else(|| "?".to_string(), |r| p.name(r.name).to_string())
}

/// The principal trait ref of a dyn type, if `t` is one.
pub fn principal_of(tys: &impl TyIntern, t: Ty) -> Option<TraitRef> {
    match tys.kind(t) {
        TyKind::Dyn(b, _) => tys.dyn_bounds(b).principal.map(|pr| pr.value),
        _ => None,
    }
}

/// The auto traits a dyn type has: written bits plus the ones its
/// principal's supertraits require.
pub fn dyn_auto(p: &Program, tys: &impl TyIntern, t: Ty) -> AutoTraits {
    let TyKind::Dyn(b, _) = tys.kind(t) else { return AutoTraits::default() };
    let b = tys.dyn_bounds(b);
    let implied = b.principal.and_then(|pr| p.gx.dyn_infos.get(&pr.value.def)).map(|i| i.auto).unwrap_or_default();
    AutoTraits { send: b.auto.send || implied.send, sync: b.auto.sync || implied.sync, unpin: b.auto.unpin || implied.unpin }
}

/// The problem with the first dyn type inside `t`, as a diagnostic at
/// `span`: not dyn compatible (L0701) or not supported yet (L0702).
pub fn dyn_type_diag(p: &Program, tys: &impl TyIntern, t: Ty, span: Span) -> Option<Diag> {
    match tys.kind(t) {
        TyKind::Dyn(b, _) => {
            let pr = tys.dyn_bounds(b).principal?.value;
            if let Some(d) = tys.args(pr.args)[1..].iter().find_map(|g| g.as_ty().and_then(|e| dyn_type_diag(p, tys, e, span))) {
                return Some(d);
            }
            let info = p.gx.dyn_infos.get(&pr.def)?;
            let name = trait_name(p, pr.def);
            if let Some((why, item)) = &info.violation {
                return Some(
                    Diag::new(
                        "L0701",
                        span,
                        format!("the trait `{name}` is not dyn compatible: {why}"),
                        "Add `where Self: Sized` to the offending method to keep it out of the vtable, or use generics instead of `dyn`.",
                    )
                    .with_label(*item, "this item makes the trait not dyn compatible"),
                );
            }
            info.unsupported.as_ref().map(|u| crate::check::generics::dyn_not_yet(span, u))
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => dyn_type_diag(p, tys, e, span),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().find_map(|&e| dyn_type_diag(p, tys, e, span)),
        TyKind::Adt(_, a) | TyKind::Projection(_, a) | TyKind::FnDef(_, a) | TyKind::Opaque(_, a) => {
            tys.args(a).iter().find_map(|g| g.as_ty().and_then(|e| dyn_type_diag(p, tys, e, span)))
        }
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            tys.tys_of(s.inputs).iter().chain(std::iter::once(&s.output)).find_map(|&e| dyn_type_diag(p, tys, e, span))
        }
        _ => None,
    }
}

/// True when trait `want` is `principal` or one of its supertraits
/// (by def; the object type implements each of them).
fn implied_by_principal(p: &Program, principal: DefId, want: DefId, seen: &mut Vec<DefId>) -> bool {
    if principal == want {
        return true;
    }
    if seen.contains(&principal) {
        return false;
    }
    seen.push(principal);
    let Some(info) = p.gx.dyn_infos.get(&principal) else { return false };
    info.supers.iter().any(|s| implied_by_principal(p, s.def, want, seen))
}

/// True when the AST type contains a `dyn` anywhere.
fn ast_has_dyn(ast: &crate::ast::Ast, id: crate::ast::TyId) -> bool {
    use crate::ast::{GenericArg as AstArg, GenericArgs, TyExpr};
    match ast.ty(id) {
        TyExpr::Dyn { .. } => true,
        TyExpr::Ref { inner, .. } | TyExpr::Ptr { inner, .. } | TyExpr::Slice(inner) | TyExpr::Paren(inner) => ast_has_dyn(ast, *inner),
        TyExpr::Array { inner, .. } => ast_has_dyn(ast, *inner),
        TyExpr::Tuple(elems) => elems.iter().any(|&e| ast_has_dyn(ast, e)),
        TyExpr::Path(segs) => segs.iter().any(|s| match &s.args {
            GenericArgs::Angle(args) => args.iter().any(|a| matches!(a, AstArg::Type(t) if ast_has_dyn(ast, *t))),
            _ => false,
        }),
        _ => false,
    }
}

/// The dyn type checks over every signature collect resolved: fn and
/// method signatures (trait methods included), fields, impl headers,
/// and `impl dyn Trait` blocks. Const and static item types with a dyn
/// type are not supported yet (their values would need vtables at
/// compile time). Body types are checked as they resolve.
pub fn check_signatures(p: &Program, errs: &mut Vec<Diag>) {
    use crate::check::generics::FnClass;
    // Every dyn type that resolves names a user trait, so a crate
    // without traits has none to check.
    if p.gx.trait_names.is_empty() {
        return;
    }
    let mut push = |d: Option<Diag>| {
        if let Some(d) = d
            && !errs.iter().any(|e| e.span == d.span && e.code == d.code)
        {
            errs.push(d);
        }
    };
    let sig_diag = |params: &[Ty], ret: Ty, def: &crate::ast::FnDef, push: &mut dyn FnMut(Option<Diag>)| {
        let skip = usize::from(def.self_param.is_some());
        for (i, param) in def.params.iter().enumerate() {
            if let Some(&t) = params.get(i + skip) {
                push(dyn_type_diag(p, &p.tys, t, p.ast.ty_span(param.ty)));
            }
        }
        let rspan = def.ret.map_or(def.name_span, |t| p.ast.ty_span(t));
        push(dyn_type_diag(p, &p.tys, ret, rspan));
    };
    for (i, f) in p.fns.iter().enumerate() {
        let class = p.gx.fn_class.get(i).copied().unwrap_or_default();
        if !matches!(class, FnClass::Plain | FnClass::Template) || p.gx.trait_methods.contains_key(&p.fn_defs[i]) {
            continue;
        }
        sig_diag(&f.params, f.ret, f.def, &mut push);
    }
    let mut methods: Vec<_> = p.gx.trait_methods.values().collect();
    methods.sort_by_key(|m| m.def.name_span.lo);
    for tm in methods {
        sig_diag(&tm.params, tm.ret, tm.def, &mut push);
    }
    for (a, adt) in p.adts.iter().enumerate() {
        if p.gx.adt_instance_of.get(a).is_some_and(|i| i.is_some()) {
            continue;
        }
        for v in &adt.variants {
            for f in &v.fields {
                push(dyn_type_diag(p, &p.tys, f.ty, adt.span));
            }
        }
    }
    for (_, rec) in p.gx.index.all_impls() {
        if rec.local && rec.synthetic == crate::traits::index::Synthetic::None {
            for g in p.tys.args(rec.trait_ref.args) {
                if let Some(t) = g.as_ty() {
                    push(dyn_type_diag(p, &p.tys, t, rec.span));
                }
            }
            // rustc E0371: `dyn Tr` already implements `Tr` and every
            // supertrait of `Tr`; a written impl would overlap it.
            let self_ty = rec.self_ty(&p.tys);
            if let Some(pr) = principal_of(&p.tys, self_ty)
                && implied_by_principal(p, pr.def, rec.trait_def, &mut Vec::new())
            {
                let (tn, dn) = (trait_name(p, rec.trait_def), trait_name(p, pr.def));
                push(Some(Diag::new(
                    "L0704",
                    rec.span,
                    format!("`dyn {dn}` implements `{tn}` already: the object type implements its trait and every supertrait"),
                    "Remove this impl; calls through the dyn type use the vtable.",
                )));
            }
        }
    }
    for &(t, span) in &p.gx.dyn_impl_sites {
        push(dyn_type_diag(p, &p.tys, t, span));
    }
    for item in &p.ast.items {
        let ty = match &item.kind {
            crate::ast::ItemKind::Const(c) => c.ty,
            crate::ast::ItemKind::Static(s) => s.ty,
            _ => continue,
        };
        if ast_has_dyn(p.ast, ty) {
            push(Some(crate::check::generics::dyn_not_yet(p.ast.ty_span(ty), "a `dyn` type in a const or static item")));
        }
    }
}

/// One object method candidate for a dyn receiver: the trait that owns
/// the method (existential ref, Self is `DYN_SELF`), and either its
/// vtable word index and receiver form, or why it cannot be called.
#[derive(Clone, Debug)]
pub struct ObjectCand {
    pub owner: TraitRef,
    pub def: DefId,
    pub call: Result<(u32, DynRecv), &'static str>,
}

/// The object method candidates named `name` across the principal and
/// its supertraits, each owning trait once (a diamond reaches one trait
/// twice), principal first then supertraits depth-first in declaration
/// order.
pub fn object_cands(p: &Program, tys: &mut impl TyIntern, principal: TraitRef, name: Sym) -> Vec<ObjectCand> {
    let mut out: Vec<ObjectCand> = Vec::new();
    let mut seen: Vec<TraitRef> = Vec::new();
    let mut work = vec![principal];
    while let Some(tr) = work.pop() {
        if seen.contains(&tr) {
            continue;
        }
        seen.push(tr);
        let Some(info) = p.gx.dyn_infos.get(&tr.def) else { continue };
        if let Some(j) = info.methods.iter().position(|m| m.name == name) {
            let m = &info.methods[j];
            out.push(ObjectCand { owner: tr, def: m.def, call: Ok((info.method_slot(j), m.recv)) });
        } else if let Some(&(_, def, why)) = info.uncallable.iter().find(|u| u.0 == name) {
            out.push(ObjectCand { owner: tr, def, call: Err(why) });
        }
        let args: Vec<GenericArg> = tys.args(tr.args).to_vec();
        let supers: Vec<TraitRef> = info.supers.iter().map(|s| crate::traits::index::subst_trait_ref_pub(tys, *s, &args)).collect();
        for s in supers.into_iter().rev() {
            work.push(s);
        }
    }
    out
}

/// The super-slot word indexes from a vtable of `from` to one of `to`
/// (a supertrait reached by upcasting), outermost first. Empty when
/// they are the same trait ref; None when `to` is not a supertrait.
pub fn upcast_path(p: &Program, tys: &mut impl TyIntern, from: TraitRef, to: TraitRef) -> Option<Vec<u32>> {
    fn go(p: &Program, tys: &mut impl TyIntern, from: TraitRef, to: TraitRef, depth: u32) -> Option<Vec<u32>> {
        if from == to {
            return Some(Vec::new());
        }
        if depth > 64 {
            return None;
        }
        let info = p.gx.dyn_infos.get(&from.def)?;
        let args: Vec<GenericArg> = tys.args(from.args).to_vec();
        let supers: Vec<TraitRef> = info.supers.iter().map(|s| crate::traits::index::subst_trait_ref_pub(tys, *s, &args)).collect();
        for (i, s) in supers.into_iter().enumerate() {
            if let Some(mut rest) = go(p, tys, s, to, depth + 1) {
                rest.insert(0, info.super_slot(i));
                return Some(rest);
            }
        }
        None
    }
    go(p, tys, from, to, 0)
}

/// A dyn type with its region erased: the key form for inherent
/// methods and vtables (a `'static` bound changes no method set).
pub fn erase_dyn_region(tys: &mut impl TyIntern, t: Ty) -> Ty {
    match tys.kind(t) {
        TyKind::Dyn(b, Region::Static) => tys.intern(TyKind::Dyn(b, Region::Erased)),
        _ => t,
    }
}

/// The full trait ref a dyn principal stands for at one concrete Self.
pub fn with_self(tys: &mut impl TyIntern, tr: TraitRef, self_ty: Ty) -> TraitRef {
    let mut args: Vec<GenericArg> = tys.args(tr.args).to_vec();
    args[0] = GenericArg::Ty(self_ty);
    let args = tys.intern_args(&args);
    TraitRef { args, ..tr }
}
