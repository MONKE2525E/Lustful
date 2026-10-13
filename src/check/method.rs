// Method resolution for generic and trait receivers
// (docs/ARCH.md section 2.10; W-TRAITS-CORE in wave A,
// W-CHECK-G after). The builtin and plain inherent dispatch stays
// in `check/mod.rs`; this module is the candidate search used when
// a receiver is a generic Adt application, a type parameter, a
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

/// True when a trait is in scope for method calls here: a std
/// prelude trait, a trait defined in or imported into the
/// current fn's module (per the resolver tables), or a trait
/// named by a bound in the current param env. Without resolver
/// tables (collect-only test paths) every local trait counts
/// as in scope, as before.
pub(super) fn trait_in_scope_pub(cx: &Ctx, trait_def: DefId) -> bool {
    trait_in_scope(cx, trait_def)
}

fn trait_in_scope(cx: &Ctx, trait_def: DefId) -> bool {
    let p = cx.p;
    if p.gx.trait_names.values().any(|&d| d == trait_def) {
        match &p.resolved {
            Some(res) => match res.def_info.get(&trait_def) {
                Some(info) => {
                    if info.module == cx.module {
                        return true;
                    }
                    // Imported into this module under any name
                    // (including `as _`): a type-namespace
                    // binding here targets the trait.
                    use crate::resolve::imports::{BindState, ns_index};
                    let imported = res
                        .maps
                        .get(cx.module.0 as usize)
                        .is_some_and(|maps| {
                            maps[ns_index(Namespace::Type)]
                                .values()
                                .any(|s| matches!(s, BindState::One(b) if res.target_def(b.target) == trait_def))
                        });
                    if imported {
                        return true;
                    }
                }
                None => return true,
            },
            None => return true,
        }
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
        // The operator traits are not in rustc's prelude (a method
        // call needs the trait in scope), but no record of
        // `use std::ops::..` reaches check today, and bounds and
        // impl headers already resolve these traits by flat name
        // (`trait_by_name`), with or without the use. Method calls
        // follow the same flat rule until resolver use-scope for
        // lang traits lands (W-RESOLVE).
        lang.add,
        lang.sub,
        lang.mul,
        lang.div,
        lang.rem,
        lang.neg,
        lang.not,
        lang.bit_and,
        lang.bit_or,
        lang.bit_xor,
        lang.shl,
        lang.shr,
        lang.add_assign,
        lang.sub_assign,
        lang.mul_assign,
        lang.div_assign,
        lang.rem_assign,
        lang.bit_and_assign,
        lang.bit_or_assign,
        lang.bit_xor_assign,
        lang.shl_assign,
        lang.shr_assign,
    ]
    .contains(&trait_def)
    {
        return true;
    }
    let in_env = |preds: &[Predicate]| preds.iter().any(|pred| matches!(pred, Predicate::Trait(b) if b.value.def == trait_def));
    if in_env(cx.env()) {
        return true;
    }
    // An instance body re-checks its template with concrete
    // types and an empty env; the template's bounds are what
    // made the call legal, so they still speak for scope here.
    if let Some(info) = p.gx.instances.get(&cx.fid)
        && let Some(tl) = info.template_local
        && let Some(fs) = p.gx.fn_scopes.get(tl.0 as usize)
    {
        return in_env(&fs.env);
    }
    false
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
    let err_len = cx.errs.len();
    let mut full_explicit: Vec<Option<GenericArg>> = prefix.iter().map(|&g| Some(g)).collect();
    full_explicit.extend_from_slice(explicit);
    let (params, ret, _) = cx.instantiate_template(e, template, generics, &full_explicit, name_span);
    let want_recv = *params.first()?;
    if !cx.unify(want_recv, probe.recv_ty) {
        cx.rollback_vars(snap_vars);
        cx.obl_truncate(obl_len);
        cx.generic_sites.truncate(sites_len);
        cx.errs.truncate(err_len);
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
/// candidates in one probe. `expected` is the call's expected
/// result type, when the context gives one: it fixes the input
/// of `Into` (whose method returns that input) and breaks
/// selection ties the way a return-type annotation does in
/// rustc.
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
    expected: Option<Ty>,
) -> Probe {
    trait_probe_for(cx, e, None, probes, derefs, name, name_span, args, explicit, expected)
}

/// `trait_method_probe` over every trait in scope, or over `only`
/// when a template pick or a where clause already fixed the trait
/// (scope was decided there). A confirmed hit is recorded as a
/// template pick (see `picks.rs`).
#[allow(clippy::too_many_arguments)]
pub(super) fn trait_probe_for(
    cx: &mut Ctx,
    e: ExprId,
    only: Option<DefId>,
    probes: &[RcvProbe],
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
    expected: Option<Ty>,
) -> Probe {
    let p = cx.p;
    let traits: Vec<DefId> = match only {
        Some(t) => vec![t],
        None => match p.gx.traits_by_method.get(&name) {
            Some(t) => t.clone(),
            None => return Probe::Miss,
        },
    };
    // First pass: probe every in-scope trait by selection, with
    // rollback, and count the hits at this form.
    // A hit: trait, its method template, the impl method (or
    // default) local, the instantiation prefix, the trait
    // input types selection fixed, the probe variant, and a
    // bridge pair when the selected impl is core's blanket
    // `Into` (the real method is the `From` impl's `from`; the
    // pair is that trait ref's Self and input types).
    #[allow(clippy::type_complexity)]
    let mut hits: Vec<(DefId, Option<TraitMethodTemplate>, LocalDefId, Vec<GenericArg>, Option<Vec<Ty>>, RcvProbe, Option<(Ty, Ty)>)> =
        Vec::new();
    // Traits whose selection stays ambiguous after the argument
    // trial: (trait, method template, inferred inputs, variant).
    let mut deferred: Vec<(DefId, TraitMethodTemplate, Vec<Ty>, RcvProbe)> = Vec::new();
    // Lang traits selection picks an impl for but that have no
    // impl method fn to call (a derived or synthetic impl, or a
    // core default method like `PartialOrd::lt`): rustc counts
    // them as candidates all the same, so they still make a call
    // ambiguous next to a real hit. Alone they stay a miss (the
    // builtin dispatch or the no-method error answers).
    let mut lang_hits: Vec<DefId> = Vec::new();
    for trait_def in traits {
        if only.is_none() && !trait_in_scope(cx, trait_def) {
            continue;
        }
        let Some(rec) = p.gx.index.trait_record(trait_def).cloned() else { continue };
        let Some(method_def) = rec.method_by_name(name) else { continue };
        // Lang traits have no method templates: the receiver
        // form comes from the lang signature table instead, and
        // the signature from the impl method itself once
        // selection picks it (below).
        let tmpl = p.gx.trait_methods.get(&method_def).cloned();
        if tmpl.as_ref().is_some_and(|t| t.self_kind.is_none()) {
            continue;
        }
        let lang_self_kind = if tmpl.is_none() {
            match p.gx.lang_method_sigs.get(&method_def) {
                Some(sig) => {
                    if sig.self_kind.is_none() {
                        continue;
                    }
                    sig.self_kind
                }
                None => None,
            }
        } else {
            None
        };
        for &probe in probes {
            let step = probe.self_ty;
            let form = probe.filter;
            // Receiver-form pre-filter for plain receivers; typed
            // receivers are decided by unification in confirm.
            match tmpl.as_ref().and_then(|t| t.self_kind).or(lang_self_kind) {
                Some(SelfKind::Value) if form != ReceiverForm::Value => continue,
                Some(SelfKind::Ref) if form != ReceiverForm::Ref => continue,
                Some(SelfKind::RefMut) if form != ReceiverForm::RefMut => continue,
                _ => {}
            }
            let n_inputs = rec.generics.params.len().saturating_sub(1);
            let snap = cx.snapshot_vars();
            let obl_len = cx.obl_len();
            let mut input_vars: Vec<Ty> = Vec::new();
            let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(step)];
            for i in 0..n_inputs {
                // `Into::into` returns the trait input itself,
                // so an expected result type is that input.
                let t = if trait_def == p.gx.lang.into && i == 0 {
                    expected.unwrap_or_else(|| cx.new_var(false))
                } else {
                    cx.new_var(false)
                };
                input_vars.push(t);
                tr_args.push(GenericArg::Ty(t));
            }
            let args_id = cx.tys.intern_args(&tr_args);
            let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
            let sel = cx.select_obligation(tr);
            let ambiguous = matches!(sel, Selection::Ambiguous);
            let was_impl = matches!(sel, Selection::Impl { .. });
            let found: Option<(LocalDefId, Vec<GenericArg>, Option<(Ty, Ty)>)> = match sel {
                Selection::Impl { id, args: impl_args, .. } => {
                    let rec_impl = p.gx.index.get(id);
                    let by_name = rec_impl.items.iter().copied().find(|&d| p.local_def(d.hash).is_some_and(|l| p.fn_info(l).name == name));
                    match by_name {
                        Some(d) => p.local_def(d.hash).map(|l| (l, impl_args.clone(), None)),
                        None => {
                            // Core's blanket `Into` has no method
                            // of its own: the call is the selected
                            // `From` impl's `from`, with the
                            // receiver as its argument.
                            let bridged = if trait_def == p.gx.lang.into && input_vars.len() == 1 {
                                let u = cx.deep(input_vars[0]);
                                let fargs = cx.tys.intern_args(&[GenericArg::Ty(u), GenericArg::Ty(step)]);
                                let ftr = TraitRef { def: p.gx.lang.from, args: fargs, bindings: EMPTY_BINDINGS };
                                match cx.select_obligation(ftr) {
                                    Selection::Impl { id: id2, args: args2, .. } => {
                                        let rec2 = p.gx.index.get(id2);
                                        let fname = p
                                            .gx
                                            .index
                                            .trait_record(p.gx.lang.from)
                                            .and_then(|r| r.methods.first().map(|m| m.1));
                                        fname
                                            .and_then(|fname| {
                                                rec2.items
                                                    .iter()
                                                    .copied()
                                                    .find(|&d| p.local_def(d.hash).is_some_and(|l| p.fn_info(l).name == fname))
                                            })
                                            .and_then(|d| p.local_def(d.hash))
                                            .map(|l| (l, args2.clone(), Some((u, cx.deep(step)))))
                                    }
                                    _ => None,
                                }
                            } else {
                                None
                            };
                            bridged.or_else(|| {
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
                                    (l, deep_args, None)
                                })
                            })
                        }
                    }
                }
                Selection::ParamEvidence(_) => param_env_hit(cx, method_def, tr).map(|(l, a)| (l, a, None)),
                _ => None,
            };
            let zonked_inputs: Option<Vec<Ty>> = if found.is_some() && !input_vars.is_empty() {
                Some(input_vars.iter().map(|&v| cx.deep(v)).collect())
            } else {
                None
            };
            // Roll the probe back either way; the winner re-selects.
            cx.rollback_vars(snap);
            cx.obl_truncate(obl_len);
            if let Some((local, prefix, bridge)) = found {
                hits.push((trait_def, tmpl.clone(), local, prefix, zonked_inputs, probe, bridge));
                continue;
            }
            if was_impl
                && !rec.local
                && trait_def != p.gx.lang.into
                && !matches!(trait_def, d if d == p.gx.lang.fn_ || d == p.gx.lang.fn_mut || d == p.gx.lang.fn_once)
                && p.gx.lang_method_sigs.get(&method_def).is_some_and(|s| s.self_kind.is_some())
                && !lang_hits.contains(&trait_def)
            {
                lang_hits.push(trait_def);
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
                let picks_len = cx.out.trait_picks.len();
                let dmeth_len = cx.deferred_methods.len();
                // Closures checked in the trial are checked again for
                // real below: drop their records and parameter locals.
                let closures_len = cx.closures.len();
                let calls_len = cx.out.closure_calls.len();
                let locals_len = cx.out.locals.len();
                let binops_len = cx.deferred_binops.len();
                let open_len = cx.open_binops.len();
                let fmt_len = cx.deferred_fmt.len();
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
                    // A known expected type fixes inputs that
                    // only the return type mentions. A return
                    // type that is still a projection cannot be
                    // unified yet and does not count against
                    // the trial.
                    let ret_ok = match expected {
                        Some(exp) => {
                            let r = subst(&mut cx.tys, t.ret, &full);
                            let r = cx.normalize_here(r);
                            let is_proj = {
                                let d = cx.deep(r);
                                cx.tys.flags(d).contains_projection()
                            };
                            is_proj || cx.unify(r, exp)
                        }
                        None => true,
                    };
                    if ret_ok { Some(input_vars.iter().map(|&v| cx.deep(v)).collect()) } else { None }
                } else {
                    None
                };
                cx.rollback_vars(snap);
                cx.obl_truncate(obl_len);
                cx.errs.truncate(err_len);
                cx.generic_sites.truncate(sites_len);
                cx.out.trait_picks.truncate(picks_len);
                cx.deferred_methods.truncate(dmeth_len);
                cx.closures.truncate(closures_len);
                cx.out.closure_calls.truncate(calls_len);
                cx.out.locals.truncate(locals_len);
                cx.deferred_binops.truncate(binops_len);
                cx.open_binops.truncate(open_len);
                cx.deferred_fmt.truncate(fmt_len);
                if let Some(inputs) = zonked {
                    let snap = cx.snapshot_vars();
                    let obl_len = cx.obl_len();
                    let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(step)];
                    tr_args.extend(inputs.iter().map(|&t| GenericArg::Ty(t)));
                    let args_id = cx.tys.intern_args(&tr_args);
                    let tr = TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS };
                    let sel = cx.select_obligation(tr);
                    let still_ambiguous = sel == Selection::Ambiguous;
                    let found: Option<(LocalDefId, Vec<GenericArg>)> = match sel {
                        Selection::Impl { id, args: impl_args, .. } => {
                            let rec_impl = p.gx.index.get(id);
                            let by_name =
                                rec_impl.items.iter().copied().find(|&d| p.local_def(d.hash).is_some_and(|l| p.fn_info(l).name == name));
                            match by_name {
                                Some(d) => p.local_def(d.hash).map(|l| (l, impl_args.clone())),
                                None => p.local_def(method_def.hash).map(|l| (l, tr_args.clone())),
                            }
                        }
                        Selection::ParamEvidence(_) => param_env_hit(cx, method_def, tr),
                        _ => None,
                    };
                    cx.rollback_vars(snap);
                    cx.obl_truncate(obl_len);
                    if let Some((local, prefix)) = found {
                        hits.push((trait_def, tmpl.clone(), local, prefix, Some(inputs), probe, None));
                    } else if still_ambiguous {
                        deferred.push((trait_def, t.clone(), inputs, probe));
                    }
                }
            }
        }
    }
    // A lang candidate with no callable method fn still ties
    // with a real hit or a deferred call (rustc E0034).
    let lang_only: Vec<DefId> =
        lang_hits.iter().copied().filter(|d| !hits.iter().any(|h| h.0 == *d) && !deferred.iter().any(|h| h.0 == *d)).collect();
    if !lang_only.is_empty() && hits.len() + deferred.len() >= 1 {
        cx.err(
            "L0720",
            name_span,
            format!("multiple trait methods named `{}` apply here", cx.name(name)),
            "Call the method with a fully qualified path, such as `<Type as Trait>::method(...)`.",
        );
        for &a in args {
            cx.expr(a, None);
        }
        return Probe::Failed;
    }
    // Only ambiguous traits: one is the call (its impl is picked at
    // body end), two are ambiguous between traits (rustc E0034).
    if hits.is_empty() && deferred.len() == 1 {
        let (trait_def, t, inputs, probe) = deferred.pop().unwrap();
        return confirm_deferred(cx, e, trait_def, &t, &inputs, probe, derefs, name_span, args, explicit);
    }
    if hits.is_empty() && deferred.len() > 1 {
        cx.err(
            "L0720",
            name_span,
            format!("multiple trait methods named `{}` apply here", cx.name(name)),
            "Call the method with a fully qualified path, such as `<Type as Trait>::method(...)`.",
        );
        for &a in args {
            cx.expr(a, None);
        }
        return Probe::Failed;
    }
    match hits.len() {
        0 => Probe::Miss,
        1 => {
            let (trait_def, _tmpl, local, prefix, zonked, probe, bridge) = hits.into_iter().next().unwrap();
            // `Drop::drop` may not be called by hand (rustc
            // E0040); the drop glue calls it, never a method
            // call. A user trait method also named `drop` is a
            // different trait and stays callable.
            if trait_def == p.gx.lang.drop {
                cx.err(
                    "L0110",
                    name_span,
                    "the `drop` method cannot be called directly",
                    "Let the value go out of scope instead.",
                );
                for &a in args {
                    cx.expr(a, None);
                }
                return Probe::Failed;
            }
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
            let prefix: Vec<GenericArg> = if let Some((u, from_step)) = bridge {
                // Bookkeep the `Into` obligation, then take the
                // instantiation prefix from the `From` impl whose
                // `from` method this call really is.
                let _ = cx.select_obligation(tr);
                let fargs = cx.tys.intern_args(&[GenericArg::Ty(u), GenericArg::Ty(from_step)]);
                let ftr = TraitRef { def: p.gx.lang.from, args: fargs, bindings: EMPTY_BINDINGS };
                match cx.select_obligation(ftr) {
                    Selection::Impl { args: args2, .. } => args2,
                    _ => prefix,
                }
            } else {
                match cx.select_obligation(tr) {
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
                }
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
                    cx.record_pick(e, trait_def, derefs + probe.extra_derefs, probe.filter);
                    return Probe::Hit(cx.normalize_here(ret));
                }
            };
            match confirm_method(cx, e, local, &generics, &prefix, explicit, probe, derefs, args, name_span) {
                Some(ret) => {
                    cx.record_pick(e, trait_def, derefs + probe.extra_derefs, probe.filter);
                    Probe::Hit(ret)
                }
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

/// A trait method call whose impl selection was still ambiguous at
/// the call: body end selects the impl and sets the resolution.
pub(super) struct DeferredMethod {
    e: ExprId,
    tr: TraitRef,
    name: Sym,
    /// The method's own generic args, after the trait's.
    own: Vec<GenericArg>,
    derefs: u8,
    autoref: Autoref,
}

/// Confirms a trait method whose impl is still ambiguous (an input
/// type only an argument or the expected type fixes, or a literal Self
/// with several numeric impls), as rustc does: the call is typed by the
/// trait's method signature, the trait obligation stays queued (the
/// literal fallback can settle it), and `finish_deferred_methods`
/// selects the impl at body end.
#[allow(clippy::too_many_arguments)]
fn confirm_deferred(
    cx: &mut Ctx,
    e: ExprId,
    trait_def: DefId,
    t: &TraitMethodTemplate,
    inputs: &[Ty],
    probe: RcvProbe,
    derefs: u8,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
) -> Probe {
    let n_trait = 1 + inputs.len();
    let snap = cx.snapshot_vars();
    let obl_len = cx.obl_len();
    let mut full: Vec<GenericArg> = vec![GenericArg::Ty(probe.self_ty)];
    full.extend(inputs.iter().map(|&i| GenericArg::Ty(i)));
    for (i, param) in t.generics.params.iter().enumerate().skip(n_trait) {
        let given = explicit.get(i - n_trait).copied().flatten();
        full.push(match (given, &param.kind) {
            (Some(g), _) => g,
            (None, ParamKind::Type) => GenericArg::Ty(cx.new_var(false)),
            (None, ParamKind::Lifetime) => GenericArg::Lifetime(Region::Erased),
            (None, ParamKind::Const(_)) => GenericArg::Const(cx.fresh_const_var()),
        });
    }
    let params: Vec<Ty> = t.params.iter().map(|&pt| subst(&mut cx.tys, pt, &full)).collect();
    let ret = subst(&mut cx.tys, t.ret, &full);
    if params.is_empty() || !cx.unify(params[0], probe.recv_ty) {
        cx.rollback_vars(snap);
        cx.obl_truncate(obl_len);
        return Probe::Miss;
    }
    let preds = t.generics.predicates.clone();
    cx.push_predicates(&preds, &full, name_span);
    let tr_args = cx.tys.intern_args(&full[..n_trait]);
    let tr = TraitRef { def: trait_def, args: tr_args, bindings: EMPTY_BINDINGS };
    cx.obl.push_trait_at(tr, name_span, 0);
    let derefs = derefs + probe.extra_derefs;
    cx.deferred_methods.push(DeferredMethod { e, tr, name: t.name, own: full[n_trait..].to_vec(), derefs, autoref: probe.autoref });
    cx.record_pick(e, trait_def, derefs, probe.filter);
    cx.check_args(&params[1..], args, name_span);
    Probe::Hit(cx.normalize_here(ret))
}

/// Body end for `confirm_deferred` calls: after the hard obligation
/// run, select each trait ref and point the call at the impl method
/// (or the trait default), with its generic site for mono. A trait
/// ref that still does not select was already reported by that run.
pub(super) fn finish_deferred_methods(cx: &mut Ctx) {
    let p = cx.p;
    for d in std::mem::take(&mut cx.deferred_methods) {
        let Selection::Impl { id, args: impl_args, .. } = cx.select_obligation(d.tr) else { continue };
        let rec = p.gx.index.get(id);
        let target = match rec.items.iter().copied().find_map(|x| p.local_def(x.hash).filter(|&l| p.fn_info(l).name == d.name)) {
            Some(l) => Some((l, impl_args)),
            None => p.gx.index.trait_record(d.tr.def).and_then(|r| r.method_by_name(d.name)).and_then(|m| p.local_def(m.hash)).map(|l| {
                let raw: Vec<GenericArg> = cx.tys.args(d.tr.args).to_vec();
                (l, raw.iter().map(|&g| if let GenericArg::Ty(t) = g { GenericArg::Ty(cx.deep(t)) } else { g }).collect())
            }),
        };
        let Some((local, mut prefix)) = target else { continue };
        if p.gx.fn_templates.get(local.0 as usize).is_some_and(|t| t.is_some()) {
            prefix.extend(d.own.iter().copied());
            let ei = cx.ei(d.e);
            cx.generic_sites.push((ei, local, prefix));
        }
        cx.set_res(d.e, Res::Method { f: local, derefs: d.derefs, autoref: d.autoref });
    }
}

/// A call the param env proves (a template check: `t.m()` with
/// `T: Tr` in the bounds): the trait method's signature stub, with
/// the trait ref's args (resolved after selection) as its prefix.
fn param_env_hit(cx: &mut Ctx, method_def: DefId, tr: TraitRef) -> Option<(LocalDefId, Vec<GenericArg>)> {
    let stub = *cx.p.gx.trait_method_stubs.get(&method_def)?;
    let raw: Vec<GenericArg> = cx.tys.args(tr.args).to_vec();
    let prefix = raw
        .iter()
        .map(|&g| match g {
            GenericArg::Ty(t) => GenericArg::Ty(cx.deep(t)),
            other => other,
        })
        .collect();
    Some((stub, prefix))
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
        // A mono instance of an inherent template: the template probe
        // handles the call too, so the template's bounds are proved at
        // every call (`lust build` checks after mono made the instance).
        if p.gx.fn_class.get(f.0 as usize) == Some(&crate::check::generics::FnClass::Instance) {
            continue;
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

/// The inherent probe of a dyn step (ARCH 2.8, 2.10): methods of
/// `impl dyn Trait` blocks and the object candidates (methods of the
/// principal and its supertraits, which need no import) are both
/// inherent here, as in rustc, so two of them at one receiver form are
/// ambiguous (rustc E0034). An object method calls through the vtable.
/// With `only`, a replayed template pick: just the object candidates of
/// that trait, as the generic body resolved `<T as Tr>::m` (picks.rs).
#[allow(clippy::too_many_arguments)]
pub(super) fn dyn_probe(
    cx: &mut Ctx,
    e: ExprId,
    probe: RcvProbe,
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    only: Option<DefId>,
) -> Probe {
    use crate::check::object::{self, DynRecv};
    let p = cx.p;
    // At step `&dyn P` the by-value group's pointee variant probes
    // `dyn P` for `&self` methods, ahead of any trait method that needs
    // an autoref there (a blanket `impl<T: ?Sized> Tr for &T`), as in
    // rustc; the call reborrows through the step.
    let (step, form, derefs) = (probe.self_ty, probe.filter, derefs + probe.extra_derefs);
    let Some(principal) = object::principal_of(&cx.tys, step) else { return Probe::Miss };
    let form_of = |k: Option<SelfKind>| match k {
        Some(SelfKind::Value) | Some(SelfKind::Typed) => Some(ReceiverForm::Value),
        Some(SelfKind::Ref) => Some(ReceiverForm::Ref),
        Some(SelfKind::RefMut) => Some(ReceiverForm::RefMut),
        None => None,
    };
    let key = object::erase_dyn_region(&mut cx.tys, step);
    let inherent = if only.is_some() { None } else { p.gx.dyn_inherent.get(&(key, name)).copied() };
    if let Some(f) = inherent
        && form_of(p.fn_info(f).self_kind).is_none()
    {
        if form == ReceiverForm::Value {
            cx.err(
                "L0104",
                name_span,
                format!("`{}` is an associated function, not a method", cx.name(name)),
                "Call it as `<dyn Trait>::name(...)`.",
            );
            return Probe::Failed;
        }
        return Probe::Miss;
    }
    let inherent = inherent.filter(|&f| form_of(p.fn_info(f).self_kind) == Some(form));
    let cands: Vec<(usize, object::ObjectCand)> = object::object_cands(p, &mut cx.tys, principal, name)
        .into_iter()
        .enumerate()
        .filter(|(_, c)| only.is_none_or(|t| c.owner.def == t))
        .filter(|(_, c)| match c.call {
            Ok((_, DynRecv::Ref)) => form == ReceiverForm::Ref,
            Ok((_, DynRecv::RefMut)) => form == ReceiverForm::RefMut,
            Err(_) => p.gx.trait_methods.get(&c.def).and_then(|t| form_of(t.self_kind)) == Some(form),
        })
        .collect();
    if inherent.is_some() as usize + cands.len() > 1 {
        cx.err(
            "L0720",
            name_span,
            format!("multiple applicable items named `{}` are in scope for this `dyn` receiver", cx.name(name)),
            "Call the method with a fully qualified path, such as `Trait::method(receiver)`.",
        );
        for &a in args {
            cx.expr(a, None);
        }
        return Probe::Failed;
    }
    if let Some(f) = inherent {
        if p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
            cx.errs.push(crate::check::generics::dyn_not_yet(name_span, "generic methods in `impl dyn Trait` blocks"));
            return Probe::Failed;
        }
        cx.check_dyn_method_vis(f, name_span);
        let (params, ret) = {
            let info = p.fn_info(f);
            (info.params.clone(), info.ret)
        };
        cx.set_res(e, Res::Method { f, derefs, autoref: probe.autoref });
        cx.check_args(&params[1.min(params.len())..], args, name_span);
        return Probe::Hit(ret);
    }
    let Some((ci, c)) = cands.into_iter().next() else { return Probe::Miss };
    let slot = match c.call {
        Ok((slot, _)) => slot,
        Err(why) => {
            let tn = cx.tn(step);
            cx.err(
                "L0703",
                name_span,
                format!("the method `{}` cannot be called on `{tn}`: {why}", cx.name(name)),
                "Call it on a concrete type, or on a generic parameter bounded by the trait.",
            );
            for &a in args {
                cx.expr(a, None);
            }
            return Probe::Failed;
        }
    };
    let Some(tm) = p.gx.trait_methods.get(&c.def) else { return Probe::Miss };
    let (tparams, tret) = (tm.params.clone(), tm.ret);
    // The method's signature with Self as the dyn type and the owner
    // trait's params from the receiver's principal.
    let mut sargs: Vec<GenericArg> = cx.tys.args(c.owner.args).to_vec();
    sargs[0] = GenericArg::Ty(step);
    let params: Vec<Ty> = tparams.iter().map(|&t| subst(&mut cx.tys, t, &sargs)).collect();
    let ret = subst(&mut cx.tys, tret, &sargs);
    let cand = u8::try_from(ci).expect("at most 256 object candidates");
    cx.set_res(e, Res::DynMethod { owner: c.owner.def, cand, slot, derefs, autoref: probe.autoref });
    if c.needs_static && !object::dyn_is_static(p, &cx.tys, step) {
        cx.obl.push(crate::check::obligations::Obligation::DynStatic { span: name_span });
    }
    cx.check_args(&params[1.min(params.len())..], args, name_span);
    Probe::Hit(cx.normalize_here(ret))
}

/// The full generic method search over autoderef steps, in
/// rustc's receiver-type probe order. Returns Hit/Miss/Failed
/// like a single probe.
#[allow(clippy::too_many_arguments)]
pub(super) fn generic_method_search(
    cx: &mut Ctx,
    e: ExprId,
    recv_ty: Ty,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
    expected: Option<Ty>,
) -> Probe {
    // Autoderef steps through references and `Box` (the builtin
    // derefs of this wave), each with its deref count for lowering.
    let mut steps: Vec<(Ty, u8)> = Vec::new();
    let mut cur = cx.resolve(recv_ty);
    for derefs in 0..32u8 {
        steps.push((cur, derefs));
        match cx.tys.kind(cur) {
            TyKind::Ref(_, _, inner) => cur = cx.resolve(inner),
            _ => match cx.tys.smart_elem(cur) {
                Some(inner) => cur = cx.resolve(inner),
                None => break,
            },
        }
    }
    for (step, derefs) in steps {
        // One group per receiver type, in probe order: by value
        // (the step type itself; at a reference step this group
        // also has the pointee variant), then `&step`, then
        // `&mut step`. Inherent probes run for every variant of
        // the group before the group's trait probe.
        let mut by_value = vec![RcvProbe::at(cx, step, ReceiverForm::Value)];
        if let Some(elem) = cx.tys.smart_elem(step) {
            // Typed receivers on the pointee's impls (`self:
            // Box<Self>`, `self: &Rc<Self>`, kin) match by
            // receiver type at this step (ARCH 2.10 step 3).
            // They bucket as Value, so the filter stays Value
            // while the receiver type carries the real form.
            let elem = cx.resolve(elem);
            by_value.push(RcvProbe { self_ty: elem, recv_ty: step, autoref: Autoref::None, extra_derefs: 0, filter: ReceiverForm::Value });
            by_value.push(RcvProbe {
                self_ty: elem,
                recv_ty: cx.tys.mk_ref(false, step),
                autoref: Autoref::Ref,
                extra_derefs: 0,
                filter: ReceiverForm::Value,
            });
            by_value.push(RcvProbe {
                self_ty: elem,
                recv_ty: cx.tys.mk_ref(true, step),
                autoref: Autoref::RefMut,
                extra_derefs: 0,
                filter: ReceiverForm::Value,
            });
        }
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
                match dyn_probe(cx, e, probe, derefs, name, name_span, args, None) {
                    Probe::Miss => {}
                    hit => return hit,
                }
                match plain_inherent_probe(cx, e, probe, derefs, name, name_span, args) {
                    Probe::Miss => {}
                    hit => return hit,
                }
                match inherent_template_probe(cx, e, probe, derefs, name, name_span, args, explicit) {
                    Probe::Miss => {}
                    hit => return hit,
                }
                match super::picks::where_clause_probe(cx, e, probe, derefs, name, name_span, args, explicit, expected) {
                    Probe::Miss => {}
                    hit => return hit,
                }
            }
            match trait_method_probe(cx, e, group, derefs, name, name_span, args, explicit, expected) {
                Probe::Miss => {}
                hit => return hit,
            }
        }
    }
    Probe::Miss
}
