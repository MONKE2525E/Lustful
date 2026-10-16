// Type and borrow checking of const and static initializers.
//
// The const evaluator (ty/consteval.rs) runs initializers on the AST, so no
// IR existed for them and borrowck never saw them: `const C: (S, S) = { let
// s = S { x: 1 }; (s, s) };` was accepted (rustc E0382). The parser makes
// each initializer a fn body too (`ast::ConstDef::init_fn`: no parameters,
// a block whose tail is the value). After collect, `check_all` gives every
// such body a transient fn entry that returns the item's type (under its
// impl's or trait's generics for an associated const), runs the body
// checker, lowering and borrowck on it, and removes the entries again, so
// nothing after collect (mono, the driver, codegen) sees them.
//
// Lowering knows these bodies by their location (`FnLoc::is_const_init`):
// the temporaries the value extends (`&Vec::new()`, `&S { .. }`) live in
// static storage, as rustc's do in a const initializer, so a borrow of one
// may be the item's value. The const-specific checks (no `&mut` or
// interior mutability in the final value, no destructor runs, const fn
// calls only) stay with the evaluator.

use super::collect::{FnInfo, FnLoc, ParentGen, Program, apply_stmt_overlay};
use super::generics::{self, FnClass, FnScope, FnTemplate};
use crate::ast::{self, ItemKind};
use crate::def::{DefId, LocalDefId};
use crate::diag::{Diag, Span};
use crate::ty::defs::{DefData, DefKind, ModuleId, SigData, Vis};
use crate::ty::{AdtId, GenericArg, Region, Ty, TyIntern, TyKind};

/// One initializer to check: where its body is, the written type, the
/// generics and scope it is checked under, and its item's span.
struct Site {
    loc: FnLoc,
    ty: ast::TyId,
    parent: ParentGen,
    owner: Option<AdtId>,
    /// The trait of a trait default: the body may use `Self: Trait`.
    trait_def: Option<DefId>,
    span: Span,
}

/// Type- and borrow-checks every const and static initializer of the
/// program (the module comment). Runs at the end of collect, when the
/// program has no errors yet; diagnostics go to `errs`.
pub fn check_all(p: &mut Program, errs: &mut Vec<Diag>) {
    p.const_body_reads.clear();
    check_sites(p, errs, &|_| true);
}

/// `check_all` for a kept program after a header or derive delta: only
/// the bodies whose stored reads moved check again (all of them when the
/// program records no reads).
pub fn check_dirty(p: &mut Program, errs: &mut Vec<Diag>) {
    if !p.record_reads {
        return check_all(p, errs);
    }
    let mut memo = crate::intern::FxMap::default();
    let reads = std::mem::take(&mut p.const_body_reads);
    let (dirty, clean): (Vec<_>, Vec<_>) = reads.into_iter().partition(|(_, r)| p.reads_dirty_memo(r, &mut memo) != 0);
    p.const_body_reads = clean;
    let dirty: Vec<FnLoc> = dirty.into_iter().map(|(l, _)| l).collect();
    if !dirty.is_empty() {
        check_sites(p, errs, &|l| dirty.contains(&l));
    }
}

/// Checks the initializer bodies `keep` selects and stores their reads.
fn check_sites(p: &mut Program, errs: &mut Vec<Diag>, keep: &dyn Fn(FnLoc) -> bool) {
    let mut sites = sites(p);
    sites.retain(|s| keep(s.loc));
    if sites.is_empty() {
        return;
    }
    let base = (p.fns.len(), p.fn_defs.len(), p.defs.len());
    let ids: Vec<LocalDefId> = sites.into_iter().filter_map(|s| install(p, s)).collect();
    let prog: &Program = p;
    let results = crate::pool::par_map(&ids, |&f| {
        let (ck, mut e) = super::check_fn(prog, f);
        let mut reads = if e.is_empty() {
            // Lowering and borrowck read derive lists too (Copy operands).
            let ((mut reads, be), noted) = super::derive_delta::scoped(prog.record_reads, || {
                let body = crate::lower::lower(prog, f, ck);
                let be = crate::borrowck::borrowck(prog, &body);
                (body.reads, be)
            });
            super::derive_delta::record(prog, &mut reads, &noted);
            e.extend(be);
            reads
        } else {
            if !may_borrow(prog, f) {
                // The evaluator took a value the body checker does not
                // type (a std item the checker lacks, a hoisted `LazyLock`
                // init): with no binding, borrow, or static read, the
                // value holds no borrow error, so the checker's limit is
                // no reason to reject.
                e.clear();
            }
            ck.reads
        };
        (prog.fns[f.0 as usize].loc, e, reads)
    });
    p.fns.truncate(base.0);
    p.fn_defs.truncate(base.1);
    p.defs.truncate(base.2);
    p.gx.fn_templates.truncate(base.0);
    p.gx.fn_scopes.truncate(base.0);
    p.gx.fn_class.truncate(base.0);
    for &f in &ids {
        p.fn_siblings.remove(&f);
        p.regions.fns.remove(&f);
    }
    for (loc, e, reads) in results {
        errs.extend(e);
        if p.record_reads {
            p.const_body_reads.push((loc, reads));
        }
    }
}

/// The module whose names an initializer body sees: its item's (the
/// resolver records it by item span), or for a const inside a fn body,
/// the innermost fn around it. None for any other fn.
pub fn module_of(p: &Program, f: LocalDefId) -> Option<ModuleId> {
    let info = p.fns.get(f.0 as usize)?;
    if !info.loc.is_const_init() {
        return None;
    }
    let tables = p.resolved.as_deref()?;
    let root = Some(crate::ty::defs::ROOT_MODULE);
    let span = match info.loc {
        FnLoc::ConstItem(i) => item_span(&p.ast.items[i as usize])?,
        FnLoc::ImplConst(i, k) => match &p.ast.items[i as usize].kind {
            ItemKind::Impl(imp) => imp.consts[k as usize].span,
            _ => return root,
        },
        FnLoc::TraitConst(i, k) => match &p.ast.items[i as usize].kind {
            ItemKind::Trait(t) => t.consts[k as usize].span,
            _ => return root,
        },
        FnLoc::NestedConst(i) => item_span(&p.ast.stmt_items[i as usize])?,
        _ => return None,
    };
    if let Some(&m) = tables.const_init_module.get(&span) {
        return Some(m);
    }
    // A const in a fn body: the module of the smallest fn whose
    // expressions hold it.
    let at = info.def(&p.ast).exprs.0;
    let mut best: Option<(u32, ModuleId)> = None;
    for (i, g) in p.fns.iter().enumerate().take(tables.fn_module.len()) {
        let (lo, hi) = g.def(&p.ast).exprs;
        if at >= lo && at < hi && best.is_none_or(|(b, _)| hi - lo < b) {
            let m = super::collect::def_module_of_fn(p, i).unwrap_or(tables.fn_module[i]);
            best = Some((hi - lo, m));
        }
    }
    best.map(|(_, m)| m).or(root)
}

/// True when initializer body `f` has a form that can hold a borrow
/// error: a pattern binding (a `let`, a match arm, a closure parameter),
/// a borrow, a deref, an assignment, a method call on a receiver other
/// than a literal (it may be borrowed), a closure, or a path that names a
/// static (a read may move
/// out of it). The scan covers the body's expression and pattern ranges.
fn may_borrow(p: &Program, f: LocalDefId) -> bool {
    use crate::ast::{Expr, Pat};
    let def = p.fn_def(f);
    let statics = |segs: &[ast::PathSeg]| segs.last().is_some_and(|s| p.static_names.contains_key(&s.name) || p.statics.iter().any(|st| st.name == s.name));
    (def.pats.0..def.pats.1).any(|i| matches!(p.ast.pat(ast::PatId(i)), Pat::Binding { .. } | Pat::At { .. }))
        || (def.exprs.0..def.exprs.1).any(|i| match p.ast.expr(ast::ExprId(i)) {
            Expr::Ref { .. } | Expr::Deref(_) | Expr::Assign { .. } | Expr::AssignOp { .. } | Expr::Closure { .. } => true,
            // A literal receiver is a constant: a borrow of it is promoted.
            Expr::MethodCall { recv, .. } => !matches!(p.ast.expr(*recv), Expr::Int(..) | Expr::Float(_) | Expr::Bool(_) | Expr::Char(_) | Expr::Str(_)),
            Expr::Path(segs) => statics(segs),
            _ => false,
        })
}

/// The span of a const or static item as the resolver keys it.
fn item_span(item: &ast::Item) -> Option<Span> {
    match &item.kind {
        ItemKind::Const(c) => Some(c.span),
        ItemKind::Static(s) => Some(s.span),
        _ => None,
    }
}

/// Every initializer body of the program, outside shipped std source.
/// A `thread_local!` static's value is a path to its init fn, which is
/// checked as a fn already.
fn sites(p: &Program) -> Vec<Site> {
    let ast = &*p.ast;
    let plain = |loc, ty, span| Site { loc, ty, parent: ParentGen::default(), owner: None, trait_def: None, span };
    let tls = |item: &ast::Item| super::tls::key_form(&item.attrs, &p.interner).is_some();
    let mut out = Vec::new();
    for (i, item) in ast.items.iter().enumerate() {
        let i = i as u32;
        match &item.kind {
            ItemKind::Const(c) if c.init_fn.is_some() => out.push(plain(FnLoc::ConstItem(i), c.ty, c.span)),
            ItemKind::Static(s) if s.init_fn.is_some() && !tls(item) => out.push(plain(FnLoc::ConstItem(i), s.ty, s.span)),
            ItemKind::Impl(imp) if !imp.consts.is_empty() => {
                let Some(parent) = p.impl_parents.get(&i) else { continue };
                let owner = parent.scope.self_ty.and_then(|t| p.tys.local_adt(t));
                for (k, c) in imp.consts.iter().enumerate().filter(|(_, c)| c.init_fn.is_some()) {
                    let loc = FnLoc::ImplConst(i, k as u32);
                    out.push(Site { loc, ty: c.ty, parent: parent.clone(), owner, trait_def: None, span: c.span });
                }
            }
            ItemKind::Trait(t) if t.consts.iter().any(|c| c.init_fn.is_some()) => {
                let Some(&td) = p.gx.trait_names.get(&t.name) else { continue };
                let (Some(rec), Some(scope)) = (p.gx.index.trait_record(td), p.gx.trait_scopes.get(&td)) else { continue };
                let parent = ParentGen { generics: rec.generics.clone(), scope: scope.clone(), impl_item: None };
                for (k, c) in t.consts.iter().enumerate().filter(|(_, c)| c.init_fn.is_some()) {
                    let loc = FnLoc::TraitConst(i, k as u32);
                    out.push(Site { loc, ty: c.ty, parent: parent.clone(), owner: None, trait_def: Some(td), span: c.span });
                }
            }
            _ => {}
        }
    }
    for (i, item) in ast.stmt_items.iter().enumerate() {
        let loc = FnLoc::NestedConst(i as u32);
        let mut site = match &item.kind {
            ItemKind::Const(c) if c.init_fn.is_some() => plain(loc, c.ty, c.span),
            ItemKind::Static(s) if s.init_fn.is_some() && !tls(item) => plain(loc, s.ty, s.span),
            _ => continue,
        };
        apply_stmt_overlay(p, &mut site.parent.scope, item.span);
        out.push(site);
    }
    out.retain(|s| p.shipped_crate_at(s.span).is_none() && !p.in_lang_methods(s.span));
    out
}

/// Adds the transient fn entry of one initializer body. None when its
/// written type does not resolve here (the evaluator reports that).
fn install(p: &mut Program, site: Site) -> Option<LocalDefId> {
    let Site { loc, ty, parent, owner, trait_def, .. } = site;
    let scope = parent.scope;
    let ret = {
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        let t = generics::resolve_scoped(&p.ast, &p.interner, &p.known, &cx, &mut p.tys, ty, &scope).ok()?;
        generics::normalize_item_ty(p, t)
    };
    // Every region in a const's or static's type is `'static` (an impl
    // lifetime in an associated const's type is taken as `'static` too):
    // the region signature says so, the fn entry holds the erased type.
    let regioned = all_static(&mut p.tys, ret);
    let ret = crate::borrowck::erase(&mut p.tys, ret);
    let generics = parent.generics;
    let mut preds = generics.predicates.clone();
    if let Some(td) = trait_def {
        // A trait default's body may use the trait's own items on Self.
        let own: Vec<GenericArg> = generics
            .params
            .iter()
            .enumerate()
            .map(|(i, d)| match d.kind {
                crate::ty::ParamKind::Const(_) => GenericArg::Const(p.tys.intern_const(crate::ty::ConstKind::Param(i as u32))),
                crate::ty::ParamKind::Lifetime => GenericArg::Lifetime(crate::ty::Region::Erased),
                crate::ty::ParamKind::Type => GenericArg::Ty(p.tys.intern(TyKind::Param(crate::ty::ParamId(i as u32)))),
            })
            .collect();
        let args = p.tys.intern_args(&own);
        let tr = crate::ty::TraitRef { def: td, args, bindings: crate::ty::EMPTY_BINDINGS };
        preds.push(crate::ty::Predicate::Trait(crate::ty::Binder::plain(tr)));
    }
    let env = generics::body_env(&mut p.tys, &p.gx.index, &preds);
    let is_template = !generics.params.is_empty();
    let mut body_scope = scope;
    if !is_template {
        body_scope.type_params.clear();
        body_scope.const_params.clear();
    }
    let id = LocalDefId(p.fns.len() as u32);
    let def = DefId { krate: p.krate, hash: crate::def::item_hash(p.stable_crate, &["<const init>"], crate::def::DefKind::Fn, "", id.0) };
    let name = loc.def(&p.ast).name;
    let mut data = DefData::skeleton(DefKind::Fn, generics.parent, name, Vis::Priv, loc.def(&p.ast).name_span);
    data.generics = generics.clone();
    data.sig = SigData::Fn { params: Vec::new(), ret };
    p.defs.insert(def, data);
    p.fn_defs.push(def);
    p.fns.push(FnInfo { name, loc, owner, self_kind: None, params: Vec::new(), ret, ret_borrows_from: None, is_const: false });
    p.gx.fn_templates.push(is_template.then(|| FnTemplate { generics, env: env.clone() }));
    p.gx.fn_scopes.push(FnScope { env, scope: body_scope });
    p.gx.fn_class.push(if is_template { FnClass::Template } else { FnClass::Plain });
    let sig = crate::borrowck::RegionSig::const_value(regioned);
    p.regions.fns.insert(id, sig);
    // A const in a fn body names its block's items and the enclosing
    // blocks' items, as a nested fn does.
    if let FnLoc::NestedConst(i) = loc
        && let Some(sibs) = p.scope_of_stmt.get(&i).cloned()
    {
        p.fn_siblings.insert(id, sibs);
    }
    Some(id)
}

/// `t` with every region `'static`: references, dyn object lifetimes,
/// and lifetime args, through every type it contains.
pub(crate) fn all_static(tys: &mut impl TyIntern, t: Ty) -> Ty {
    let arg = |tys: &mut _, g: GenericArg| match g {
        GenericArg::Ty(e) => GenericArg::Ty(all_static(tys, e)),
        GenericArg::Lifetime(_) => GenericArg::Lifetime(Region::Static),
        g => g,
    };
    match tys.kind(t) {
        TyKind::Ref(_, m, inner) => {
            let i = all_static(tys, inner);
            tys.intern(TyKind::Ref(Region::Static, m, i))
        }
        TyKind::Dyn(b, _) => tys.intern(TyKind::Dyn(b, Region::Static)),
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = tys.tys_of(ts).to_vec().into_iter().map(|e| all_static(tys, e)).collect();
            let id = tys.intern_tys(&elems);
            tys.intern(TyKind::Tuple(id))
        }
        TyKind::Array(e, n) => {
            let e = all_static(tys, e);
            tys.intern(TyKind::Array(e, n))
        }
        TyKind::Slice(e) => {
            let e = all_static(tys, e);
            tys.intern(TyKind::Slice(e))
        }
        TyKind::Adt(d, a) => {
            let args: Vec<GenericArg> = tys.args(a).to_vec().into_iter().map(|g| arg(tys, g)).collect();
            tys.mk_adt(d, &args)
        }
        _ => t,
    }
}
