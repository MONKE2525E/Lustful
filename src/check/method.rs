// Method resolution for generic and trait receivers
// (docs/ARCH.md section 2.10; W-TRAITS-CORE in wave A,
// W-CHECK-G after). The builtin and plain inherent dispatch stays
// in `check/mod.rs`; this module is the candidate search used when
// a receiver is a generic Adt application, an abstract opaque, a
// projection, or a dyn type, and for every trait method.
//
// Probe order is section 2.10 step 2, interleaved with the
// inherent probes `method_call` already makes: for each autoderef
// step (builtin derefs only in this wave: references), for each
// receiver form (by value, then `&`, then `&mut`), inherent first,
// then traits in scope. Two trait hits in one probe are ambiguous.
// Every probe records its candidate-set reads: inherent probes go
// through the `MethodSet` query in `method_call`, trait probes
// record `ImplSet` reads inside selection.
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
    step: Ty,
    form: ReceiverForm,
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
    let got_recv = receiver_for_form(cx, step, form);
    if !cx.unify(want_recv, got_recv) {
        cx.rollback_vars(snap_vars);
        cx.obl_truncate(obl_len);
        cx.generic_sites.truncate(sites_len);
        return None;
    }
    cx.set_res(e, Res::Method { f: template, derefs, autoref: autoref_of(form) });
    cx.check_args(&params[1.min(params.len())..], args, name_span);
    Some(cx.normalize_here(ret))
}

/// Probes inherent method templates of one Adt step type at one
/// receiver form. Plain inherent methods are the existing
/// `method_set` path in `method_call`; this covers the generic
/// ones that path would mis-instantiate.
#[allow(clippy::too_many_arguments)]
pub(super) fn inherent_template_probe(
    cx: &mut Ctx,
    e: ExprId,
    step: Ty,
    form: ReceiverForm,
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
) -> Probe {
    let p = cx.p;
    let Some((adt_def, _)) = cx.tys.adt_parts(step) else { return Probe::Miss };
    let Some(&template) = p.gx.inherent_methods.get(&(adt_def, name)) else { return Probe::Miss };
    let Some(Some(tmpl)) = p.gx.fn_templates.get(template.0 as usize).cloned() else { return Probe::Miss };
    // The receiver form must be able to match at all; the unify
    // in confirm_method decides the rest.
    match confirm_method(cx, e, template, &tmpl.generics.clone(), &[], explicit, step, form, derefs, args, name_span) {
        Some(ret) => Probe::Hit(ret),
        None => Probe::Miss,
    }
}

/// Probes trait methods at one autoderef step and receiver form.
#[allow(clippy::too_many_arguments)]
pub(super) fn trait_method_probe(
    cx: &mut Ctx,
    e: ExprId,
    step: Ty,
    form: ReceiverForm,
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
    let mut hits: Vec<(DefId, Option<TraitMethodTemplate>, LocalDefId, Vec<GenericArg>, Option<Vec<Ty>>)> = Vec::new();
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
            hits.push((trait_def, tmpl, local, prefix, None));
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
            let want_form = receiver_for_form(cx, step, form);
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
                    hits.push((trait_def, tmpl.clone(), local, prefix, Some(inputs)));
                }
            }
        }
    }
    match hits.len() {
        0 => Probe::Miss,
        1 => {
            let (trait_def, _tmpl, local, prefix, zonked) = hits.into_iter().next().unwrap();
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
                    let got_recv2 = receiver_for_form(cx, step, form);
                    if !cx.unify(want_recv, got_recv2) {
                        return Probe::Miss;
                    }
                    cx.set_res(e, Res::Method { f: local, derefs, autoref: autoref_of(form) });
                    cx.check_args(&params[1..], args, name_span);
                    return Probe::Hit(cx.normalize_here(ret));
                }
            };
            match confirm_method(cx, e, local, &generics, &prefix, explicit, step, form, derefs, args, name_span) {
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

/// The full generic method search over autoderef steps, used
/// when the plain inherent probe and the builtin table both miss
/// (and interleaved per form for generic inherent templates via
/// `inherent_template_probe`). Returns Hit/Miss/Failed like a
/// single probe.
#[allow(clippy::too_many_arguments)]
/// The plain inherent probe of one step+form, through the
/// recorded `MethodSet` query (as `method_call` makes it), for
/// non-template inherent methods.
#[allow(clippy::too_many_arguments)]
pub(super) fn plain_inherent_probe(
    cx: &mut Ctx,
    e: ExprId,
    step: Ty,
    form: ReceiverForm,
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
) -> Probe {
    let p = cx.p;
    let head = Head::of(&cx.tys, step);
    let set = p.method_set(&mut cx.out.reads, head, name, form);
    let Some(c) = set.first() else { return Probe::Miss };
    let Some(f) = p.local_def(c.def.hash) else { return Probe::Miss };
    if p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
        return Probe::Miss; // the template probe handles it
    }
    let Some(rcv_form) = c.receiver else {
        cx.err("L0104", name_span, format!("`{}` is an associated function, not a method", cx.name(name)), "Call it as `Type::name(...)`.");
        return Probe::Failed;
    };
    let _ = rcv_form;
    let (params, ret) = match p.sig_of(&mut cx.out.reads, c.def) {
        SigOf::Fn(info) => (info.params.clone(), info.ret),
        _ => return Probe::Miss,
    };
    cx.set_res(e, Res::Method { f, derefs, autoref: autoref_of(form) });
    cx.check_args(&params[1.min(params.len())..], args, name_span);
    Probe::Hit(ret)
}

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
        for form in ReceiverForm::PROBE_ORDER {
            match plain_inherent_probe(cx, e, step, form, derefs, name, name_span, args) {
                Probe::Miss => {}
                hit => return hit,
            }
            match inherent_template_probe(cx, e, step, form, derefs, name, name_span, args, explicit) {
                Probe::Miss => {}
                hit => return hit,
            }
            match trait_method_probe(cx, e, step, form, derefs, name, name_span, args, explicit) {
                Probe::Miss => {}
                hit => return hit,
            }
        }
    }
    Probe::Miss
}
