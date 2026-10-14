// `core::any` (W-CHECK-G3): the `Any` trait, `TypeId`, and downcasts.
//
// `Any` is a lang trait with one synthetic blanket impl for every type
// (`impl<T: 'static + ?Sized> Any for T`, `generics::add_synthetic_impls`);
// selection ignores the `'static` part, as rustc's method probe does, and
// the checks here and in the borrow checker prove it. `TypeId` is a
// synthetic struct of two `u64` words (`generics::type_id_def`): a 128-bit
// hash of the type's structure with regions erased (`type_id_words`), the
// same in every body and every daemon build of one program.
//
// A `dyn Any` vtable stores the value's type id after its header
// (`object::VT_ANY_ID`); a user trait with `Any` as a supertrait reaches
// it through its super slot. This file types the calls; lowering builds
// them (lower/any.rs):
//
// - `x.type_id()` (with `Any` in scope, or on a dyn receiver whose
//   principal has `Any` as a supertrait): Self follows rustc's probe
//   order (a reference step's pointee first, then the step itself under
//   an autoref), so `Box<dyn Any>` in scope answers for the box.
// - `is`, `downcast_ref`, `downcast_mut` on `dyn Any`, `dyn Any + Send`,
//   and `dyn Any + Send + Sync` (std's inherent impls), through
//   references, `Box`, and `Rc`.
// - `Box<dyn Any ..>::downcast` and `Rc<dyn Any>::downcast` by value.
// - `TypeId::of::<T>()`.
//
// The tested type is `Checked::generic_args[e][0]` (the Self type for a
// static `type_id`). It must be known at the call (a turbofish or the
// expected type), sized, and `'static`. lust does not track the regions
// of non-dyn references, so a reference in it passes only where its
// region can be `'static` without a check (written in a turbofish
// without a named lifetime, and not behind `downcast_mut`).
use super::*;
use std::hash::Hasher;

/// Which `core::any` operation a `Res::Any` is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AnyOp {
    /// `x.type_id()` with a static Self (`generic_args[e][0]`).
    TypeId,
    /// `x.type_id()` on a dyn receiver: the id in its vtable.
    DynTypeId,
    Is,
    DowncastRef,
    DowncastMut,
    /// `Box<dyn Any>::downcast` or `Rc<dyn Any>::downcast` (by the
    /// receiver type).
    Downcast,
    /// `TypeId::of::<T>()`, on the callee path.
    TypeIdOf,
}

/// The two words of the type id of `t` (a concrete type, in any store):
/// a 128-bit hash of its structure, with defs in stable form and regions
/// erased. Lowering builds `TypeId` values from it and codegen writes it
/// into `dyn Any` vtables, so both must see equal types.
pub fn type_id_words(p: &Program, tys: &impl TyIntern, t: Ty) -> (u64, u64) {
    let mut bytes: Vec<u8> = Vec::new();
    encode_ty(p, tys, t, &mut bytes);
    // std's `DefaultHasher::new()` is SipHash with fixed keys: the same
    // in every run of one lust binary.
    let word = |salt: u8| {
        let mut h = std::hash::DefaultHasher::new();
        h.write(&[salt]);
        h.write(&bytes);
        h.finish()
    };
    (word(1), word(2))
}

/// The canonical byte form of a type for `type_id_words`.
fn encode_ty(p: &Program, tys: &impl TyIntern, t: Ty, out: &mut Vec<u8>) {
    let def = |out: &mut Vec<u8>, d: crate::def::DefId| {
        out.extend(crate::driver::graph::def_crate_hash(p, d).to_le_bytes());
        out.extend(d.hash.0.to_le_bytes());
    };
    let args = |out: &mut Vec<u8>, a: ArgsId| {
        for g in tys.args(a) {
            match *g {
                GenericArg::Ty(e) => {
                    out.push(b'T');
                    encode_ty(p, tys, e, out);
                }
                GenericArg::Const(c) => {
                    out.push(b'C');
                    out.extend(format!("{:?}", tys.const_kind(c)).bytes());
                }
                // Lifetimes are not part of a type id.
                GenericArg::Lifetime(_) => {}
            }
        }
        out.push(b'.');
    };
    match tys.kind(t) {
        TyKind::Unit => out.push(1),
        TyKind::Bool => out.push(2),
        TyKind::Char => out.push(3),
        TyKind::Never => out.push(4),
        TyKind::Int(i) => {
            out.push(5);
            out.extend(i.name().bytes());
        }
        TyKind::Float(f) => {
            out.push(6);
            out.extend(f.name().bytes());
        }
        TyKind::Str => out.push(7),
        TyKind::Ref(_, m, e) => {
            out.push(if m.is_mut() { 9 } else { 8 });
            encode_ty(p, tys, e, out);
        }
        TyKind::RawPtr(m, e) => {
            out.push(if m.is_mut() { 11 } else { 10 });
            encode_ty(p, tys, e, out);
        }
        TyKind::Slice(e) => {
            out.push(12);
            encode_ty(p, tys, e, out);
        }
        TyKind::Array(e, n) => {
            out.push(13);
            encode_ty(p, tys, e, out);
            out.extend(format!("{:?}", tys.const_kind(n)).bytes());
        }
        TyKind::Tuple(ts) => {
            out.push(14);
            for &e in tys.tys_of(ts) {
                encode_ty(p, tys, e, out);
            }
            out.push(b'.');
        }
        TyKind::Adt(d, a) => {
            out.push(15);
            def(out, d);
            args(out, a);
        }
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            out.push(16);
            out.extend([s.is_unsafe as u8, s.extern_c as u8]);
            for &e in tys.tys_of(s.inputs) {
                encode_ty(p, tys, e, out);
            }
            out.push(b'>');
            encode_ty(p, tys, s.output, out);
        }
        TyKind::FnDef(d, a) => {
            out.push(17);
            def(out, d);
            args(out, a);
        }
        TyKind::Closure(d, a) => {
            out.push(18);
            def(out, d);
            args(out, a);
        }
        TyKind::Dyn(b, _) => {
            out.push(19);
            let b = tys.dyn_bounds(b);
            if let Some(pr) = b.principal {
                def(out, pr.value.def);
                args(out, pr.value.args);
                for &(assoc, g) in tys.bindings(pr.value.bindings) {
                    def(out, assoc);
                    if let GenericArg::Ty(e) = g {
                        encode_ty(p, tys, e, out);
                    }
                }
            }
            out.extend([b.auto.send as u8, b.auto.sync as u8, b.auto.unpin as u8]);
        }
        // Never in a checked concrete type (`any_type_ok` rejects them);
        // a template's placeholder answer is never generated.
        TyKind::Error | TyKind::Opaque(..) | TyKind::Param(_) | TyKind::Projection(..) | TyKind::Infer(_) => out.push(0),
    }
}

/// True when the dyn type `t` can answer `type_id` through its vtable:
/// its principal is `Any` or has `Any` as a supertrait.
pub fn dyn_reaches_any(p: &Program, tys: &mut impl TyIntern, t: Ty) -> bool {
    let Some(pr) = object::principal_of(tys, t) else { return false };
    let any = p.gx.lang.any;
    if pr.def == any {
        return true;
    }
    let args = tys.intern_args(&[GenericArg::Ty(DYN_SELF)]);
    object::upcast_path(p, tys, pr, TraitRef { def: any, args, bindings: EMPTY_BINDINGS }).is_some()
}

/// True for `dyn Any`, `dyn Any + Send`, and `dyn Any + Send + Sync`:
/// the dyn types std gives `is` and the downcast methods.
fn is_downcast_dyn(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    let TyKind::Dyn(b, _) = tys.kind(t) else { return false };
    let b = tys.dyn_bounds(b);
    b.principal.is_some_and(|pr| pr.value.def == p.gx.lang.any) && !b.auto.unpin && (b.auto.send || !b.auto.sync)
}

impl<'p, 'a> Ctx<'p, 'a> {
    /// The `core::any` methods (see the file comment). None when the call
    /// is not one of them, or when a user method of the name could apply
    /// (then the ordinary probes answer).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn any_method(
        &mut self,
        e: ExprId,
        rt: Ty,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        explicit: &[Option<GenericArg>],
        expected: Option<Ty>,
    ) -> Option<Ty> {
        let p = self.p;
        let n = self.name(name);
        if !matches!(n, "type_id" | "is" | "downcast_ref" | "downcast_mut" | "downcast") {
            return None;
        }
        if p.gx.traits_by_method.get(&name).is_some_and(|ts| ts.iter().any(|t| p.gx.index.trait_record(*t).is_some_and(|r| r.local))) {
            return None;
        }
        if n == "type_id" {
            if !turbofish.is_empty() || p.methods.keys().any(|(_, m)| *m == name) {
                return None;
            }
            return self.type_id_method(e, rt, name_span, args);
        }
        // The steps of the receiver through references, `Box`, and `Rc`.
        let mut steps: Vec<(Ty, u8)> = Vec::new();
        let mut cur = self.resolve(rt);
        for derefs in 0..32u8 {
            steps.push((cur, derefs));
            cur = match self.tys.kind(cur) {
                TyKind::Ref(_, _, inner) => self.resolve(inner),
                _ => match self.tys.smart_elem(cur) {
                    Some(inner) => self.resolve(inner),
                    None => break,
                },
            };
        }
        if n == "downcast" {
            // By value, at the receiver itself (a `Box` behind a
            // reference would move out of the borrow).
            let (t0, _) = steps[0];
            let elem = self.tys.smart_elem(t0).map(|t| self.resolve(t))?;
            let boxed = self.tys.boxed_elem(t0).is_some();
            let ok = if boxed {
                is_downcast_dyn(p, &self.tys, elem)
            } else {
                object::principal_of(&self.tys, elem).is_some_and(|pr| pr.def == p.gx.lang.any)
                    && object::dyn_auto(p, &self.tys, elem) == AutoTraits::default()
            };
            if !ok {
                return None;
            }
            let want = expected.and_then(|x| {
                let x = self.resolve(x);
                let (okt, _) = self.tys.result_args(x)?;
                let okt = self.resolve(okt);
                self.tys.smart_elem(okt)
            });
            let Some(t) = self.any_target(e, explicit, turbofish, want, name_span, true) else { return Some(self.any_fail(args)) };
            self.check_args(&[], args, name_span);
            self.set_res(e, Res::Any { op: AnyOp::Downcast, derefs: 0, autoref: Autoref::None });
            let owned = if boxed { self.tys.mk_boxed(t) } else { self.tys.mk_rc(t) };
            return Some(self.tys.mk_result(owned, t0));
        }
        let (_, derefs) = steps.iter().copied().find(|&(t, _)| is_downcast_dyn(p, &self.tys, t))?;
        let (op, mutable) = match n {
            "is" => (AnyOp::Is, false),
            "downcast_ref" => (AnyOp::DowncastRef, false),
            _ => (AnyOp::DowncastMut, true),
        };
        let want = match op {
            AnyOp::Is => None,
            _ => expected.and_then(|x| {
                let x = self.resolve(x);
                let inner = self.tys.option_elem(x)?;
                match self.kind(inner) {
                    TyKind::Ref(_, _, t) => Some(t),
                    _ => None,
                }
            }),
        };
        let Some(t) = self.any_target(e, explicit, turbofish, want, name_span, !mutable) else { return Some(self.any_fail(args)) };
        self.check_args(&[], args, name_span);
        let autoref = if mutable { Autoref::RefMut } else { Autoref::Ref };
        self.set_res(e, Res::Any { op, derefs, autoref });
        Some(match op {
            AnyOp::Is => BOOL,
            _ => {
                let r = self.tys.mk_ref(mutable, t);
                self.tys.mk_option(r)
            }
        })
    }

    /// Checks the arguments of a failed call (an error is reported) for
    /// their own errors; the call's type is the error type.
    fn any_fail(&mut self, args: &[ExprId]) -> Ty {
        for &a in args {
            self.expr(a, None);
        }
        ERROR
    }

    /// `x.type_id()`, by rustc's probe order: at each autoderef step,
    /// a reference step's pointee is Self first (the `&self` receiver is
    /// the step itself), then the step under an autoref. A dyn Self whose
    /// principal reaches `Any` answers through its vtable without `Any`
    /// in scope (an object candidate); any other Self needs `Any` in
    /// scope (the blanket impl).
    fn type_id_method(&mut self, e: ExprId, rt: Ty, name_span: Span, args: &[ExprId]) -> Option<Ty> {
        let p = self.p;
        let in_scope = method::trait_in_scope_pub(self, p.gx.lang.any);
        let mut cur = self.resolve(rt);
        let mut hit: Option<(Ty, u8, bool)> = None;
        for derefs in 0..32u8 {
            let mut cands: Vec<(Ty, u8)> = Vec::new();
            if let TyKind::Ref(_, Mut::Shared, inner) = self.tys.kind(cur) {
                cands.push((self.resolve(inner), derefs + 1));
            }
            cands.push((cur, derefs));
            for (self_ty, d) in cands {
                if matches!(self.kind(self_ty), TyKind::Dyn(..)) && dyn_reaches_any(p, &mut self.tys, self_ty) {
                    hit = Some((self_ty, d, true));
                    break;
                }
                if in_scope {
                    hit = Some((self_ty, d, false));
                    break;
                }
            }
            if hit.is_some() {
                break;
            }
            cur = match self.tys.kind(cur) {
                TyKind::Ref(_, _, inner) => self.resolve(inner),
                _ => match self.tys.smart_elem(cur) {
                    Some(inner) => self.resolve(inner),
                    None => break,
                },
            };
        }
        let (self_ty, derefs, dynamic) = hit?;
        self.check_args(&[], args, name_span);
        let id_ty = generics::type_id_ty(&mut self.tys);
        if dynamic {
            self.set_res(e, Res::Any { op: AnyOp::DynTypeId, derefs, autoref: Autoref::Ref });
            return Some(id_ty);
        }
        let self_ty = self.deep(self_ty);
        if !self.any_type_ok(self_ty, None, false, true, name_span) {
            return Some(ERROR);
        }
        let i = self.ei(e);
        self.out.generic_args[i] = vec![GenericArg::Ty(self_ty)];
        self.set_res(e, Res::Any { op: AnyOp::TypeId, derefs, autoref: Autoref::Ref });
        Some(id_ty)
    }

    /// True when a call's callee path is `TypeId::of` (`std::any::TypeId::of`
    /// after the resolver expands an import).
    pub(super) fn is_type_id_of(&self, segs: &[ast::PathSeg]) -> bool {
        let names: Vec<&str> = segs.iter().map(|s| self.p.interner.get(s.name)).collect();
        matches!(names.as_slice(), ["std" | "core", "any", "TypeId", "of"])
    }

    /// `TypeId::of::<T>()` (`std::any::TypeId::of`): the callee path's
    /// resolution, with T recorded for lowering.
    pub(super) fn type_id_of_path(&mut self, e: ExprId, seg: &ast::PathSeg, span: Span) -> Option<Res> {
        let written = seg.type_args();
        if written.len() != 1 {
            self.err("L0110", span, "`TypeId::of` takes one type argument", "Write `TypeId::of::<Type>()`.");
            return None;
        }
        let t = self.resolve_written(written[0]);
        let t = self.deep(t);
        if !self.any_type_ok(t, Some(written[0]), true, true, span) {
            return None;
        }
        let i = self.ei(e);
        self.out.generic_args[i] = vec![GenericArg::Ty(t)];
        Some(Res::Any { op: AnyOp::TypeIdOf, derefs: 0, autoref: Autoref::None })
    }

    /// The type a downcast tests: the turbofish, else the type the
    /// expected result fixes (`want`). Records it for lowering. None
    /// (after an error) when it is missing or not a valid `T: Any`.
    fn any_target(
        &mut self,
        e: ExprId,
        explicit: &[Option<GenericArg>],
        turbofish: &[ast::GenericArg],
        want: Option<Ty>,
        span: Span,
        refs_ok: bool,
    ) -> Option<Ty> {
        if explicit.len() > 1 {
            self.err("L0110", span, "this method takes one type argument", "Write `downcast_ref::<Type>()`.");
            return None;
        }
        let written = match turbofish.first() {
            Some(ast::GenericArg::Type(w)) => Some(*w),
            _ => None,
        };
        let t = match explicit.first().copied().flatten() {
            Some(GenericArg::Ty(t)) => t,
            Some(_) => {
                self.err("L0110", span, "this method takes a type argument", "Write `downcast_ref::<Type>()`.");
                return None;
            }
            None => match want {
                Some(t) => t,
                None => {
                    self.err(
                        "L0610",
                        span,
                        "type annotations needed: the type to downcast to must be known here",
                        "Name it with a turbofish, as in `downcast_ref::<Type>()`.",
                    );
                    return None;
                }
            },
        };
        let t = self.deep(t);
        // A turbofish type's elided references may be `'static`; an
        // inferred one's regions come from elsewhere.
        let refs_ok = refs_ok && written.is_some();
        if !self.any_type_ok(t, written, refs_ok, false, span) {
            return None;
        }
        let i = self.ei(e);
        self.out.generic_args[i] = vec![GenericArg::Ty(t)];
        Some(t)
    }

    /// Checks one `T: Any` type at a `core::any` call, reporting why it
    /// fails: unknown parts (L0610), unsized where that is not allowed
    /// (L0110, rustc E0277), or not
    /// provably `'static` (L0612 for a type parameter, L0705 otherwise).
    /// An instance skips the `'static` part: its template proved it.
    pub(super) fn any_type_ok(&mut self, t: Ty, written: Option<ast::TyId>, refs_ok: bool, unsized_ok: bool, span: Span) -> bool {
        let p = self.p;
        if self.tys.flags(t).contains_infer() {
            self.err(
                "L0610",
                span,
                format!("type annotations needed: `{}` must be known here", self.tn(t)),
                "Write the full type, for example with a turbofish.",
            );
            return false;
        }
        if matches!(self.kind(t), TyKind::Error) {
            return false;
        }
        if contains_opaque(&self.tys, t) {
            self.errs.push(generics::dyn_not_yet(span, "the type id of an `impl Trait` type"));
            return false;
        }
        // `TypeId::of` and `type_id` take `T: ?Sized`; a downcast's T is sized.
        if !unsized_ok && !self.sized_ok(t) {
            let tn = self.tn(t);
            self.err("L0110", span, format!("the size for values of type `{tn}` cannot be known"), "Use a sized type here.");
            return false;
        }
        if matches!(p.gx.fn_class.get(self.fid.0 as usize), Some(generics::FnClass::Instance)) {
            return true;
        }
        let named = written.is_some_and(|w| generics::names_lifetime(p.ast, p.interner, w));
        if named || (!refs_ok && contains_ref(&self.tys, t)) {
            let tn = self.tn(t);
            self.err(
                "L0705",
                span,
                format!("lust cannot prove that `{tn}` lives for `'static`, which `Any` requires"),
                "Use a type without references here.",
            );
            return false;
        }
        if let Some((code, msg)) = self.static_bound_err(t, 0) {
            self.err(code, span, msg, "Use a type that lives for `'static` here, or add a `'static` bound to the type parameter.");
            return false;
        }
        true
    }
}

/// True when a reference type occurs anywhere in `t`.
fn contains_ref(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(..) => true,
        TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => contains_ref(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| contains_ref(tys, e)),
        TyKind::Adt(_, a) | TyKind::Closure(_, a) | TyKind::FnDef(_, a) => {
            tys.is_chars_ty(t) || tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| contains_ref(tys, e)))
        }
        TyKind::Dyn(..) => {
            object::principal_of(tys, t).is_some_and(|pr| tys.args(pr.args).iter().any(|g| g.as_ty().is_some_and(|e| contains_ref(tys, e))))
        }
        TyKind::FnPtr(sig) => {
            let s = tys.sig(sig).value;
            contains_ref(tys, s.output) || tys.tys_of(s.inputs).iter().any(|&e| contains_ref(tys, e))
        }
        _ => false,
    }
}

/// True when an `impl Trait` type occurs anywhere in `t`.
fn contains_opaque(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Opaque(..) => true,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => contains_opaque(tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| contains_opaque(tys, e)),
        TyKind::Adt(_, a) | TyKind::Closure(_, a) | TyKind::FnDef(_, a) | TyKind::Projection(_, a) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| contains_opaque(tys, e)))
        }
        _ => false,
    }
}
