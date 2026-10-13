// Method resolution for generic and trait receivers
// (docs/ARCH.md section 2.10; W-TRAITS-CORE in wave A,
// W-CHECK-G after). The builtin and plain inherent dispatch stays
// in `check/mod.rs`; this module is the candidate search used when
// a receiver is a generic Adt application, an abstract opaque, a
// projection, or a dyn type, and for every trait method.
//
// Probe order is section 2.10 step 2, interleaved with the
// inherent probes `method_call` already makes. It follows rustc:
// candidates match by receiver type, not by Self type. For each
// autoderef step `U` (builtin derefs only in this wave:
// references) the by-value probe takes every method whose
// receiver type is `U`: the by-value methods of `U` itself, and,
// when `U` is `&T` or `&mut T`, the `&self` or `&mut self`
// methods of `T`. Autoref probes (`&U`, then `&mut U`) come
// after. Inherent candidates win over trait candidates in one
// probe; two trait hits in one probe are ambiguous. Every probe
// records its candidate-set reads: inherent probes go through
// the `MethodSet` query, trait probes record `ImplSet` reads
// inside selection.
use super::*;
use crate::ast::{ExprId, SelfKind};
use crate::check::generics::TraitMethodTemplate;
use crate::def::DefId;
use crate::traits::solve::Selection;

/// What a generic method probe found at one receiver form.
pub(super) enum Probe {
    /// The call is resolved; the payload is its return type.
    Hit(Ty),
    /// No candidate in this probe.
    Miss,
    /// The call failed (an error was reported).
    Failed,
}

/// The receiver type a probe form presents to a method whose
/// Self type at this autoderef step is `step`.
fn receiver_for_form(cx: &mut Ctx, step: Ty, form: ReceiverForm) -> Ty {
    match form {
        ReceiverForm::Value => step,
        ReceiverForm::Ref => cx.tys.mk_ref(false, step),
        ReceiverForm::RefMut => cx.tys.mk_ref(true, step),
    }
}

fn autoref_of(form: ReceiverForm) -> Autoref {
    match form {
        ReceiverForm::Value => Autoref::None,
        ReceiverForm::Ref => Autoref::Ref,
        ReceiverForm::RefMut => Autoref::RefMut,
    }
}

/// One receiver-type probe variant at one autoderef step: the
/// Self type whose inherent impls and trait impls are probed,
/// the receiver type a matching method must have, the
/// adjustment lowering applies after the step's derefs, and
/// the `self` form filter for candidate sets. The by-value
/// probe at a reference step has two variants: Self = the step
/// type (by-value methods) and Self = the pointee (`&self`
/// methods, whose receiver type is the step type itself). A
/// pointee hit records one extra deref plus autoref, so the
/// receiver is reborrowed (`&mut *r`), never moved.
#[derive(Clone, Copy)]
pub(super) struct RcvProbe {
    pub self_ty: Ty,
    pub recv_ty: Ty,
    pub autoref: Autoref,
    pub extra_derefs: u8,
    pub filter: ReceiverForm,
}

impl RcvProbe {
    /// The primary variant at one autoderef step and form.
    pub(super) fn at(cx: &mut Ctx, step: Ty, form: ReceiverForm) -> RcvProbe {
        RcvProbe { self_ty: step, recv_ty: receiver_for_form(cx, step, form), autoref: autoref_of(form), extra_derefs: 0, filter: form }
    }
}

/// True when a trait is in scope for method calls here: a local
/// trait (defined in this file), a std prelude trait, or a trait
/// named by a bound in the current param env.
pub(super) fn trait_in_scope_pub(cx: &Ctx, trait_def: DefId) -> bool {
    trait_in_scope(cx, trait_def)
}

fn trait_in_scope(cx: &Ctx, trait_def: DefId) -> bool {
    let p = cx.p;
    if p.gx.trait_names.values().any(|&d| d == trait_def) {
        return true;
    }
    let lang = &p.gx.lang;
    if [
        lang.copy,
        lang.clone,
        lang.debug,
        lang.display,
        lang.partial_eq,
        lang.eq,
        lang.partial_ord,
        lang.ord,
        lang.hash,
        lang.default,
        lang.drop,
        lang.iterator,
        lang.into_iterator,
        lang.from_iterator,
        lang.from,
        lang.into,
        lang.deref,
        lang.deref_mut,
        lang.index,
        lang.index_mut,
    ]
    .contains(&trait_def)
    {
        return true;
    }
    cx.env().iter().any(|pred| matches!(pred, Predicate::Trait(b) if b.value.def == trait_def))
}

/// Confirms one method candidate (inherent template, impl
/// template, or trait default template) at a call site:
/// instantiate it, unify the receiver, check the args, and
/// record the resolution. `prefix` are the already-known leading
/// generic args (impl or trait args from selection); `explicit`
/// are the method's own turbofish args.
#[allow(clippy::too_many_arguments)]
fn confirm_method(
    cx: &mut Ctx,
    e: ExprId,
    template: LocalDefId,
    generics: &Generics,
    prefix: &[GenericArg],
    explicit: &[Option<GenericArg>],
    probe: RcvProbe,
    derefs: u8,
    args: &[ExprId],
    name_span: Span,
) -> Option<Ty> {
    let snap_vars = cx.snapshot_vars();
    let obl_len = cx.obl_len();
    let sites_len = cx.generic_sites.len();
    let mut full_explicit: Vec<Option<GenericArg>> = prefix.iter().map(|&g| Some(g)).collect();
    full_explicit.extend_from_slice(explicit);
    let (params, ret, _) = cx.instantiate_template(e, template, generics, &full_explicit, name_span);
    let want_recv = *params.first()?;
    if !cx.unify(want_recv, probe.recv_ty) {
        cx.rollback_vars(snap_vars);
        cx.obl_truncate(obl_len);
        cx.generic_sites.truncate(sites_len);
        return None;
    }
    cx.set_res(e, Res::Method { f: template, derefs: derefs + probe.extra_derefs, autoref: probe.autoref });
    cx.check_args(&params[1.min(params.len())..], args, name_span);
    Some(cx.normalize_here(ret))
}

/// Probes inherent method templates of one probe variant's Self
/// type. Plain inherent methods are `plain_inherent_probe`;
/// this covers the generic ones that path would
/// mis-instantiate. Every registered template is tried: the
/// receiver unify in `confirm_method` keeps only the ones whose
/// impl Self pattern matches this receiver.
#[allow(clippy::too_many_arguments)]
pub(super) fn inherent_template_probe(
    cx: &mut Ctx,
    e: ExprId,
    probe: RcvProbe,
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
) -> Probe {
    let p = cx.p;
    let Some((adt_def, _)) = cx.tys.adt_parts(probe.self_ty) else { return Probe::Miss };
    let Some(templates) = p.gx.inherent_methods.get(&(adt_def, name)).cloned() else { return Probe::Miss };
    for template in templates {
        let Some(Some(tmpl)) = p.gx.fn_templates.get(template.0 as usize).cloned() else { continue };
        if let Some(ret) = confirm_method(cx, e, template, &tmpl.generics.clone(), &[], explicit, probe, derefs, args, name_span) {
            return Probe::Hit(ret);
        }
    }
    Probe::Miss
}

/// Probes trait methods for one receiver-type probe group (the
/// variants of one autoderef step that share a receiver type).
/// Hits are counted across the whole group, as rustc counts
/// candidates in one probe.
#[allow(clippy::too_many_arguments)]
pub(super) fn trait_method_probe(
    cx: &mut Ctx,
    e: ExprId,
    probes: &[RcvProbe],
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
) -> Probe {
    let p = cx.p;
    let Some(traits) = p.gx.traits_by_method.get(&name).cloned() else { return Probe::Miss };
    // First pass: probe every in-scope trait by selection, with
    // rollback, and count the hits at this form.
    // A hit: trait, its method template, the impl method (or
    // default) local, the instantiation prefix, and the trait
    // input types a trial argument check inferred (when plain
    // selection with fresh inputs was ambiguous).
    let mut hits: Vec<(DefId, Option<TraitMethodTemplate>, LocalDefId, Vec<GenericArg>, Option<Vec<Ty>>, RcvProbe)> = Vec::new();
    for trait_def in traits {
        if !trait_in_scope(cx, trait_def) {
            continue;
        }
        let Some(rec) = p.gx.index.trait_record(trait_def).cloned() else { continue };
        let Some(method_def) = rec.method_by_name(name) else { continue };
        // Lang traits have no method templates: the receiver
        // form and signature come from the impl method itself
        // once selection picks it (below).
        let tmpl = p.gx.trait_methods.get(&method_def).cloned();
        if tmpl.as_ref().is_some_and(|t| t.self_kind.is_none()) {
            continue;
        }
        for &probe in probes {
            let step = probe.self_ty;
            let form = probe.filter;
            // Receiver-form pre-filter for plain receivers; typed
            // receivers are decided by unification in confirm.
            match tmpl.as_ref().and_then(|t| t.self_kind) {
                Some(SelfKind::Value) if form != ReceiverForm::Value => continue,
                Some(SelfKind::Ref) if form != ReceiverForm::Ref => continue,
                Some(SelfKind::RefMut) if form != ReceiverForm::RefMut => continue,
                _ => {}
            }
            let n_inputs = rec.generics.params.len().saturating_sub(1);
            let snap = cx.snapshot_vars();
            let obl_len = cx.obl_len();
            let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(step)];
            for _ in 0..n_inputs {
                tr_args.push(GenericArg::Ty(cx.new_var(false)));
            }
            let args_id = cx.tys.intern_args(&tr_args);
            let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
            let sel = cx.select_obligation(tr);
            let ambiguous = matches!(sel, Selection::Ambiguous);
            let found: Option<(LocalDefId, Vec<GenericArg>)> = match sel {
                Selection::Impl { id, args: impl_args, .. } => {
                    let rec_impl = p.gx.index.get(id);
                    let by_name = rec_impl.items.iter().copied().find(|&d| p.local_def(d.hash).is_some_and(|l| p.fn_info(l).name == name));
                    match by_name {
                        Some(d) => p.local_def(d.hash).map(|l| (l, impl_args.clone())),
                        None => {
                            // The trait default body, as a template.
                            p.local_def(method_def.hash).map(|l| {
                                let raw: Vec<GenericArg> = cx.tys.args(tr.args).to_vec();
                                let deep_args: Vec<GenericArg> = raw
                                    .iter()
                                    .map(|&g| match g {
                                        GenericArg::Ty(t) => GenericArg::Ty(cx.deep(t)),
                                        other => other,
                                    })
                                    .collect();
                                (l, deep_args)
                            })
                        }
                    }
                }
                _ => None,
            };
            // Roll the probe back either way; the winner re-selects.
            cx.rollback_vars(snap);
            cx.obl_truncate(obl_len);
            if let Some((local, prefix)) = found {
                hits.push((trait_def, tmpl.clone(), local, prefix, None, probe));
                continue;
            }
            // Ambiguous selection with fresh trait inputs is common
            // with one impl per input (`Convert<u8>` and
            // `Convert<u16>` for one Self): the written arguments
            // fix the inputs through the trait method's own
            // signature. Trial-check the arguments against that
            // signature (rolled back in full), then select again
            // with the inferred inputs.
            if ambiguous && let Some(t) = &tmpl {
                let snap = cx.snapshot_vars();
                let obl_len = cx.obl_len();
                let err_len = cx.errs.len();
                let sites_len = cx.generic_sites.len();
                let csites_len = cx.closure_sites.len();
                let mut input_vars: Vec<Ty> = Vec::new();
                let mut full: Vec<GenericArg> = vec![GenericArg::Ty(step)];
                for _ in 0..n_inputs {
                    let v = cx.new_var(false);
                    input_vars.push(v);
                    full.push(GenericArg::Ty(v));
                }
                let n_trait_params = rec.generics.params.len();
                for (i, param) in t.generics.params.iter().enumerate().skip(n_trait_params) {
                    let given = explicit.get(i - n_trait_params).copied().flatten();
                    full.push(match (given, &param.kind) {
                        (Some(g), _) => g,
                        (None, ParamKind::Type) => GenericArg::Ty(cx.new_var(false)),
                        (None, ParamKind::Lifetime) => GenericArg::Lifetime(Region::Erased),
                        (None, ParamKind::Const(_)) => GenericArg::Const(cx.fresh_const_var()),
                    });
                }
                let params: Vec<Ty> = t.params.iter().map(|&pt| subst(&mut cx.tys, pt, &full)).collect();
                let want_form = probe.recv_ty;
                let zonked: Option<Vec<Ty>> = if !params.is_empty() && cx.unify(params[0], want_form) {
                    cx.check_args(&params[1..], args, name_span);
                    Some(input_vars.iter().map(|&v| cx.deep(v)).collect())
                } else {
                    None
                };
                cx.rollback_vars(snap);
                cx.obl_truncate(obl_len);
                cx.errs.truncate(err_len);
                cx.generic_sites.truncate(sites_len);
                cx.closure_sites.truncate(csites_len);
                if let Some(inputs) = zonked {
                    let snap = cx.snapshot_vars();
                    let obl_len = cx.obl_len();
                    let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(step)];
                    tr_args.extend(inputs.iter().map(|&t| GenericArg::Ty(t)));
                    let args_id = cx.tys.intern_args(&tr_args);
                    let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
                    let found: Option<(LocalDefId, Vec<GenericArg>)> = match cx.select_obligation(tr) {
                        Selection::Impl { id, args: impl_args, .. } => {
                            let rec_impl = p.gx.index.get(id);
                            let by_name =
                                rec_impl.items.iter().copied().find(|&d| p.local_def(d.hash).is_some_and(|l| p.fn_info(l).name == name));
                            match by_name {
                                Some(d) => p.local_def(d.hash).map(|l| (l, impl_args.clone())),
                                None => p.local_def(method_def.hash).map(|l| (l, tr_args.clone())),
                            }
                        }
                        _ => None,
                    };
                    cx.rollback_vars(snap);
                    cx.obl_truncate(obl_len);
                    if let Some((local, prefix)) = found {
                        hits.push((trait_def, tmpl.clone(), local, prefix, Some(inputs), probe));
                    }
                }
            }
        }
    }
    match hits.len() {
        0 => Probe::Miss,
        1 => {
            let (trait_def, _tmpl, local, prefix, zonked, probe) = hits.into_iter().next().unwrap();
            let step = probe.self_ty;
            // Re-select to commit the selection bindings and get
            // the confirmed instantiation prefix.
            let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(step)];
            match &zonked {
                Some(inputs) => tr_args.extend(inputs.iter().map(|&t| GenericArg::Ty(t))),
                None => {
                    let n_inputs = prefix.len().saturating_sub(1);
                    for _ in 0..n_inputs {
                        tr_args.push(GenericArg::Ty(cx.new_var(false)));
                    }
                }
            }
            let args_id = cx.tys.intern_args(&tr_args);
            let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
            let prefix: Vec<GenericArg> = match cx.select_obligation(tr) {
                Selection::Impl { args: impl_args, .. } => {
                    // Impl methods take impl args; trait defaults
                    // take the trait ref args.
                    if p.gx.index.impls_of_trait(trait_def).iter().any(|_| true) && local_is_impl_method(p, local, name) {
                        impl_args
                    } else {
                        let raw: Vec<GenericArg> = cx.tys.args(tr.args).to_vec();
                        raw.iter()
                            .map(|&g| match g {
                                GenericArg::Ty(t) => GenericArg::Ty(cx.deep(t)),
                                other => other,
                            })
                            .collect()
                    }
                }
                _ => prefix,
            };
            let generics = match p.gx.fn_templates.get(local.0 as usize).cloned() {
                Some(Some(t)) => t.generics.clone(),
                _ => {
                    // A plain (non-generic) impl method.
                    let (params, ret) = {
                        let info = p.fn_info(local);
                        (info.params.clone(), info.ret)
                    };
                    let want_recv = params[0];
                    if !cx.unify(want_recv, probe.recv_ty) {
                        return Probe::Miss;
                    }
                    cx.set_res(e, Res::Method { f: local, derefs: derefs + probe.extra_derefs, autoref: probe.autoref });
                    cx.check_args(&params[1..], args, name_span);
                    return Probe::Hit(cx.normalize_here(ret));
                }
            };
            match confirm_method(cx, e, local, &generics, &prefix, explicit, probe, derefs, args, name_span) {
                Some(ret) => Probe::Hit(ret),
                None => Probe::Miss,
            }
        }
        _ => {
            cx.err(
                "L0720",
                name_span,
                format!("multiple trait methods named `{}` apply here", cx.name(name)),
                "Call the method with a fully qualified path, such as `<Type as Trait>::method(...)`.",
            );
            for &a in args {
                cx.expr(a, None);
            }
            Probe::Failed
        }
    }
}

/// True when `local` is a method written in an impl (not a trait
/// default template): its template, if any, is keyed by impl
/// generics, not trait generics.
fn local_is_impl_method(p: &Program, local: LocalDefId, _name: Sym) -> bool {
    let def = p.def_id(local);
    p.gx.index.all_impls().any(|(_, rec)| rec.items.contains(&def))
}

/// The plain inherent probe of one variant, through the
/// recorded `MethodSet` query (as `method_call` makes it), for
/// non-template inherent methods. Every candidate in the set is
/// tried; templates are left to `inherent_template_probe`, and
/// associated fns (no `self`) never match here (the fallback in
/// `method_call` reports them when nothing else applies).
#[allow(clippy::too_many_arguments)]
pub(super) fn plain_inherent_probe(
    cx: &mut Ctx,
    e: ExprId,
    probe: RcvProbe,
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
) -> Probe {
    let p = cx.p;
    let head = Head::of(&cx.tys, probe.self_ty);
    let set = p.method_set(&mut cx.out.reads, head, name, probe.filter);
    for c in set.candidates {
        let Some(f) = p.local_def(c.def.hash) else { continue };
        if c.receiver.is_none() {
            continue;
        }
        if p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
            continue; // the template probe handles it
        }
        let (params, ret) = match p.sig_of(&mut cx.out.reads, c.def) {
            SigOf::Fn(info) => (info.params.clone(), info.ret),
            _ => continue,
        };
        // The candidate set is keyed by the reference-peeled head
        // and by the template Adt, so it also surfaces methods
        // whose receiver type or impl Self pattern does not match
        // this receiver (a `&self` method of `S` at a `&S` step
        // under form `Ref`, where lowering would pass `&&S`, or a
        // method of `impl W<u8>` for a `W<u32>` receiver). Unify
        // the method's receiver type with what this variant
        // presents (as `confirm_method` does) and probe on when
        // they differ.
        let snap_vars = cx.snapshot_vars();
        let obl_len = cx.obl_len();
        let want_recv = params.first().copied();
        if want_recv.is_none_or(|want| !cx.unify(want, probe.recv_ty)) {
            cx.rollback_vars(snap_vars);
            cx.obl_truncate(obl_len);
            continue;
        }
        cx.set_res(e, Res::Method { f, derefs: derefs + probe.extra_derefs, autoref: probe.autoref });
        cx.check_args(&params[1.min(params.len())..], args, name_span);
        return Probe::Hit(ret);
    }
    Probe::Miss
}

/// The full generic method search over autoderef steps, in
/// rustc's receiver-type probe order. Returns Hit/Miss/Failed
/// like a single probe.
pub(super) fn generic_method_search(
    cx: &mut Ctx,
    e: ExprId,
    recv_ty: Ty,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
) -> Probe {
    // Autoderef steps through references (the builtin derefs of
    // this wave), each with its deref count for lowering.
    let mut steps: Vec<(Ty, u8)> = Vec::new();
    let mut cur = cx.resolve(recv_ty);
    for derefs in 0..32u8 {
        steps.push((cur, derefs));
        match cx.tys.kind(cur) {
            TyKind::Ref(_, _, inner) => cur = cx.resolve(inner),
            _ => break,
        }
    }
    for (step, derefs) in steps {
        // One group per receiver type, in probe order: by value
        // (the step type itself; at a reference step this group
        // also has the pointee variant), then `&step`, then
        // `&mut step`. Inherent probes run for every variant of
        // the group before the group's trait probe.
        let mut by_value = vec![RcvProbe::at(cx, step, ReceiverForm::Value)];
        if let TyKind::Ref(_, m, inner) = cx.tys.kind(step) {
            by_value.push(RcvProbe {
                self_ty: cx.resolve(inner),
                recv_ty: step,
                autoref: if m == Mut::Mut { Autoref::RefMut } else { Autoref::Ref },
                extra_derefs: 1,
                filter: if m == Mut::Mut { ReceiverForm::RefMut } else { ReceiverForm::Ref },
            });
        }
        let groups = [by_value, vec![RcvProbe::at(cx, step, ReceiverForm::Ref)], vec![RcvProbe::at(cx, step, ReceiverForm::RefMut)]];
        for group in &groups {
            for &probe in group {
                match plain_inherent_probe(cx, e, probe, derefs, name, name_span, args) {
                    Probe::Miss => {}
                    hit => return hit,
                }
                match inherent_template_probe(cx, e, probe, derefs, name, name_span, args, explicit) {
                    Probe::Miss => {}
                    hit => return hit,
                }
            }
            match trait_method_probe(cx, e, group, derefs, name, name_span, args, explicit) {
                Probe::Miss => {}
                hit => return hit,
            }
        }
    }
    Probe::Miss
}
