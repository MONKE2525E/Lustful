// Template call picks (docs/ARCH.md section 4.1, `CallTrait`). A
// template body is checked once against its bounds (the template
// check, `generics::template_check`). Every call there that
// resolves through a trait method records a pick: the trait, and
// where the Self type sits relative to the receiver. Every other
// check of the same body (concrete instances and closure instances)
// replays the pick: the trait is fixed, and selection on the Self
// type there picks the impl. Method lookup never runs again for those calls, so
// an instance cannot see the inherent methods, builtin std methods,
// or other traits of a concrete type that the template could not
// see (rustc also resolves methods once per generic body).
//
// The template check also needs rustc's rule that the methods of a
// type parameter's where clauses are inherent candidates
// (`where_clause_probe`): they win over a blanket impl of another
// trait at the same probe, and they match by receiver type, so a
// by-value probe at `&T` takes a `&self` bound method of `T`.
//
// Operators (`a + b`, `-a`, `a += b`) and `for` loops record no
// pick: their instance checks re-select, and that is equal by
// construction. An operator names exactly one lang trait, so
// selection in an instance can only find the one impl coherence
// allows for the operand types (or the builtin scalar path, whose
// `Output`/`Rhs` are core's own scalar impls); a bound that fixes
// `Output` is checked again at the call site, so an instance
// whose impl disagrees with the bound never gets built. A `for`
// loop is the same shape through `IntoIterator`: the blanket
// `impl<I: Iterator> IntoIterator for I` overlaps any direct
// impl, so the template proof and the instance selection name
// the same impl. The tests `operator_pick_*` and
// `for_loop_pick_*` in tests/pass pin both shapes.
use super::method::{self, Probe, RcvProbe};
use super::*;
use crate::def::DefId;

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
    pub(super) fn is_template_check(&self) -> bool {
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

    /// The traits of the where clauses on one type parameter (or
    /// projection) that declare a method `name` with a template, from
    /// this body's env. The env is elaborated, so supertraits count.
    pub(super) fn bound_traits_with(&self, self_ty: Ty, name: Sym) -> Vec<DefId> {
        let p = self.p;
        let Some(traits) = p.gx.traits_by_method.get(&name) else { return Vec::new() };
        let self_ty = self.resolve(self_ty);
        if !matches!(self.tys.kind(self_ty), TyKind::Param(_) | TyKind::Projection(..)) {
            return Vec::new();
        }
        let is_bound = |t: DefId| {
            self.env().iter().any(|pred| {
                matches!(pred, Predicate::Trait(b) if b.count == 0 && b.value.def == t
                    && self.tys.args(b.value.args).first().and_then(|g| g.as_ty()) == Some(self_ty))
            })
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
    // The same autoderef steps as the template's search: references,
    // then `Box` and `Rc` (`method::generic_method_search`).
    let mut step = cx.resolve(recv_ty);
    let mut ok = true;
    for _ in 0..pick.derefs {
        match cx.tys.kind(step) {
            TyKind::Ref(_, _, inner) => step = cx.resolve(inner),
            _ => match cx.tys.smart_elem(step) {
                Some(inner) => step = cx.resolve(inner),
                None => ok = false,
            },
        }
    }
    if ok {
        let probe = RcvProbe::at(cx, step, pick.form);
        // A `?Sized` param instantiated at a dyn type whose principal (or
        // a supertrait of it) is the picked trait: the object candidate,
        // through the vtable (ARCH 2.8), never an `impl dyn` method.
        if matches!(cx.tys.kind(step), TyKind::Dyn(..)) {
            match method::dyn_probe(cx, e, probe, pick.derefs, name, name_span, args, Some(pick.trait_def)) {
                Probe::Hit(ret) => return Some(ret),
                Probe::Failed => return Some(ERROR),
                Probe::Miss => {}
            }
        }
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

    /// Collects one sample file in build (`walk` true) or check mode,
    /// then runs `run` on the program.
    fn with_mode(src: &str, walk: bool, run: impl FnOnce(&Interner, &Program)) {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = CrateIds { local: LOCAL_CRATE, stable: crate::def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect_mode(&ast, &interner, &known, ids, walk).unwrap();
        run(&interner, &program);
    }

    /// `with_mode` for a build.
    fn with_program(src: &str, run: impl FnOnce(&Interner, &Program)) {
        with_mode(src, true, run);
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

    /// The lang signature table is built from the lang trait
    /// records: `PartialOrd::partial_cmp` exists with an
    /// `Option<Ordering>` return, the comparison defaults exist,
    /// and methods a bound cannot call (`Hash::hash`,
    /// `Debug::fmt`) have no entry.
    #[test]
    fn lang_sigs_come_from_the_records() {
        use crate::ty::TyIntern as _;
        let src = "fn main() { println!(\"x\"); }\n";
        with_program(src, |interner, p| {
            let lang = &p.gx.lang;
            let sig_of = |trait_def, name: &str| {
                let rec = p.gx.index.trait_record(trait_def).expect("lang record");
                let m = rec.method_by_name(interner.intern(name)).expect("record method");
                p.gx.lang_method_sigs.get(&m)
            };
            let pc = sig_of(lang.partial_ord, "partial_cmp").expect("partial_cmp sig");
            assert_eq!(pc.self_kind, Some(crate::ast::SelfKind::Ref));
            let elem = p.tys.option_elem(pc.ret).expect("Option return");
            assert_eq!(p.tys.adt_parts(elem).map(|(d, _)| d), Some(crate::check::generics::ordering_def()));
            assert!(sig_of(lang.partial_ord, "lt").is_some());
            assert!(sig_of(lang.ord, "cmp").is_some());
            assert!(sig_of(lang.add, "add").is_some());
            assert!(sig_of(lang.add_assign, "add_assign").is_some());
            assert!(sig_of(lang.hash, "hash").is_none());
            assert!(sig_of(lang.debug, "fmt").is_none());
            assert!(sig_of(lang.drop, "drop").is_none());
        });
    }

    /// `lust check` makes closure body fns (they check closure bodies)
    /// but no generic fn instances; a build makes both (ARCH 4.1).
    #[test]
    fn check_mode_makes_no_generic_fn_instances() {
        use crate::check::generics::FnClass;
        let src = "fn id<T>(t: T) -> T { t }\nfn main() { let f = |x: u8| x + 1; println!(\"{} {}\", id(5u8), f(1)); }\n";
        let count = |p: &Program, k: FnClass| p.gx.fn_class.iter().filter(|&&c| c == k).count();
        with_mode(src, true, |_, p| assert_eq!((count(p, FnClass::Instance), count(p, FnClass::Closure)), (1, 1)));
        with_mode(src, false, |_, p| assert_eq!((count(p, FnClass::Instance), count(p, FnClass::Closure)), (0, 1)));
    }
}
