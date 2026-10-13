// Template call picks (docs/ARCH.md section 4.1, `CallTrait`). A
// template body is checked once against its bounds (the template
// check, mono's canonical abstract instance). Every call there that
// resolves through a trait method records a pick: the trait, and
// where the Self type sits relative to the receiver. Every other
// check of the same body (concrete instances, closure instances, and
// abstract instances made for other templates' calls) replays the
// pick: the trait is fixed, and selection on the Self type there
// picks the impl. Method lookup never runs again for those calls, so
// an instance cannot see the inherent methods, builtin std methods,
// or other traits of a concrete type that the template could not
// see (rustc also resolves methods once per generic body).
//
// The template check also needs rustc's rule that the methods of a
// type parameter's where clauses are inherent candidates
// (`where_clause_probe`): they win over a blanket impl of another
// trait at the same probe, and they match by receiver type, so a
// by-value probe at `&T` takes a `&self` bound method of `T`.
use super::method::{self, Probe, RcvProbe};
use super::*;
use crate::def::DefId;
use crate::traits::index::Synthetic;

/// One call a template check resolved through a trait method.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TraitPick {
    pub trait_def: DefId,
    /// Method calls: autoderefs from the receiver to the Self type.
    /// Zero for path calls (`T::f(..)`).
    pub derefs: u8,
    /// Method calls: the method's receiver form on Self.
    pub form: ReceiverForm,
}

impl Ctx<'_, '_> {
    /// True when this body is a template check, whose picks are
    /// recorded rather than replayed.
    fn is_template_check(&self) -> bool {
        self.p.gx.template_checks.contains_key(&self.fid)
    }

    /// The pick a template check recorded for one call, when this
    /// body is any other check of that template's body.
    pub(super) fn replay_pick(&self, e: ExprId) -> Option<TraitPick> {
        if self.is_template_check() {
            return None;
        }
        self.p.gx.trait_picks.get(&e).copied()
    }

    /// Records one confirmed trait call in a template check.
    pub(super) fn record_pick(&mut self, e: ExprId, trait_def: DefId, derefs: u8, form: ReceiverForm) {
        if self.is_template_check() {
            self.out.trait_picks.push((e, TraitPick { trait_def, derefs, form }));
        }
    }

    /// The traits of the where clauses on one type parameter that
    /// declare a method `name` with a template. A `Param` Self reads
    /// this body's env. In a template check over opaques, each bound
    /// is made true by an `Abstract` synthetic impl for the opaque, so
    /// those records are its where clauses. Both envs are elaborated,
    /// so supertraits count.
    pub(super) fn bound_traits_with(&self, self_ty: Ty, name: Sym) -> Vec<DefId> {
        let p = self.p;
        let Some(traits) = p.gx.traits_by_method.get(&name) else { return Vec::new() };
        let self_ty = self.resolve(self_ty);
        let is_bound: Box<dyn Fn(DefId) -> bool + '_> = match self.tys.kind(self_ty) {
            TyKind::Param(_) => Box::new(move |t: DefId| {
                self.env().iter().any(|pred| {
                    matches!(pred, Predicate::Trait(b) if b.count == 0 && b.value.def == t
                        && self.tys.args(b.value.args).first().and_then(|g| g.as_ty()) == Some(self_ty))
                })
            }),
            _ => {
                let Some(a) = self.tys.local_adt(self_ty) else { return Vec::new() };
                if !p.gx.param_opaques.contains_key(&a) {
                    return Vec::new();
                }
                Box::new(move |t: DefId| {
                    p.gx.index.impls_of_trait(t).iter().any(|&id| {
                        let r = p.gx.index.get(id);
                        r.synthetic == Synthetic::Abstract
                            && p.tys.args(r.trait_ref.args).first().and_then(|g| g.as_ty()).and_then(|s| p.tys.local_adt(s)) == Some(a)
                    })
                })
            }
        };
        let mut out: Vec<DefId> = Vec::new();
        for &t in traits {
            let templated = p.gx.index.trait_record(t).and_then(|r| r.method_by_name(name)).is_some_and(|m| p.gx.trait_methods.contains_key(&m));
            if templated && !out.contains(&t) && is_bound(t) {
                out.push(t);
            }
        }
        out
    }
}

/// The receiver form a trait's method `name` takes on Self, from its
/// template. None for associated fns, typed receivers, and lang
/// trait methods (no template).
fn method_form(cx: &Ctx, trait_def: DefId, name: Sym) -> Option<ReceiverForm> {
    let p = cx.p;
    let m = p.gx.index.trait_record(trait_def)?.method_by_name(name)?;
    match p.gx.trait_methods.get(&m)?.self_kind? {
        ast::SelfKind::Value => Some(ReceiverForm::Value),
        ast::SelfKind::Ref => Some(ReceiverForm::Ref),
        ast::SelfKind::RefMut => Some(ReceiverForm::RefMut),
        ast::SelfKind::Typed => None,
    }
}

/// The where-clause probe of one receiver-type probe variant
/// (rustc's inherent candidates from the param env): the methods of
/// the bounds on the variant's Self type whose receiver form is the
/// variant's form. The pointee variant of a by-value probe at `&T`
/// covers a `&self` bound method of `T`. Two bound traits with a
/// matching method are ambiguous (rustc E0034).
#[allow(clippy::too_many_arguments)]
pub(super) fn where_clause_probe(
    cx: &mut Ctx,
    e: ExprId,
    probe: RcvProbe,
    derefs: u8,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
    expected: Option<Ty>,
) -> Probe {
    let traits: Vec<DefId> =
        cx.bound_traits_with(probe.self_ty, name).into_iter().filter(|&t| method_form(cx, t, name) == Some(probe.filter)).collect();
    match traits.len() {
        0 => Probe::Miss,
        1 => method::trait_probe_for(cx, e, Some(traits[0]), &[probe], derefs, name, name_span, args, explicit, expected),
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

/// Replays one recorded pick at a method call: Self sits
/// `pick.derefs` derefs into the receiver, and only the picked trait
/// is probed, at the recorded form. Selection on this body's Self
/// type picks the impl. A lang trait impl with no method fn (a builtin
/// type, a derive) has a builtin body: None tells the caller to use
/// the builtin dispatch only, never an inherent method. Any other miss
/// means the bound did not hold where the instance was requested
/// (that call site already reported it), or that the template check
/// and this check disagree: either way it is the no-impl error.
#[allow(clippy::too_many_arguments)]
pub(super) fn replay_method(
    cx: &mut Ctx,
    e: ExprId,
    recv_ty: Ty,
    pick: TraitPick,
    name: Sym,
    name_span: Span,
    args: &[ExprId],
    explicit: &[Option<GenericArg>],
    expected: Option<Ty>,
) -> Option<Ty> {
    let mut step = cx.resolve(recv_ty);
    let mut ok = true;
    for _ in 0..pick.derefs {
        match cx.tys.kind(step) {
            TyKind::Ref(_, _, inner) => step = cx.resolve(inner),
            _ => ok = false,
        }
    }
    if ok {
        let probe = RcvProbe::at(cx, step, pick.form);
        match method::trait_probe_for(cx, e, Some(pick.trait_def), &[probe], pick.derefs, name, name_span, args, explicit, expected) {
            Probe::Hit(ret) => return Some(ret),
            Probe::Failed => return Some(ERROR),
            Probe::Miss => {}
        }
    }
    let p = cx.p;
    let templated =
        p.gx.index.trait_record(pick.trait_def).and_then(|r| r.method_by_name(name)).is_some_and(|m| p.gx.trait_methods.contains_key(&m));
    if ok && !templated {
        return None;
    }
    for &a in args {
        cx.expr(a, None);
    }
    if cx.kind(step) != TyKind::Error {
        let tn = cx.tn(step);
        let tr_name = cx.trait_name(pick.trait_def);
        cx.err("L0612", name_span, format!("no impl of `{tr_name}` for `{tn}`"), "Add the impl, or change the bound.");
    }
    Some(ERROR)
}

#[cfg(test)]
mod tests {
    use crate::check::collect::{self, Program};
    use crate::def::{CrateIds, LOCAL_CRATE};
    use crate::diag::FileId;
    use crate::intern::{Interner, Known};
    use crate::{lexer, parser};

    /// Collects one sample file, then runs `run` on the program.
    fn with_program(src: &str, run: impl FnOnce(&Interner, &Program)) {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(&ast, &interner, &known, ids).unwrap();
        run(&interner, &program);
    }

    /// The template check records the call through the bound with the
    /// bound's trait and Self one deref into `&T`, by `&self`.
    #[test]
    fn template_check_records_the_bound_trait() {
        let src = "struct S;\nimpl S { fn get(&self) -> u8 { 1 } }\ntrait G { fn get(&self) -> u8; }\n\
                   impl G for S { fn get(&self) -> u8 { 2 } }\nfn via<T: G>(t: &T) -> u8 { t.get() }\n\
                   fn main() { println!(\"{}\", via(&S)); }\n";
        with_program(src, |interner, p| {
            let g = p.gx.trait_names[&interner.intern("G")];
            let picks: Vec<_> = p.gx.trait_picks.values().collect();
            assert_eq!(picks.len(), 1);
            assert_eq!(picks[0].trait_def, g);
            assert_eq!((picks[0].derefs, picks[0].form), (1, super::ReceiverForm::Ref));
        });
    }
}
