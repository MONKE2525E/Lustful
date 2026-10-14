// Conversion trait methods on builtin values (W-STD-B): `as_ref`,
// `as_mut` (AsRef, AsMut), `borrow`, `borrow_mut` (Borrow,
// BorrowMut), and `to_owned` (ToOwned), with the impl sets core and
// alloc declare for the types lust has (generics.rs lang facts).
//
// Self is bound as rustc's probe binds it: the receiver with one
// reference peeled (the by-value step of a `&self` method), else the
// receiver by autoref. AsRef and AsMut forward through references;
// Borrow does not (`impl Borrow<T> for &T` is its own impl). The trait
// argument comes from the template's bound in an instance of a generic
// body, else from the expected type, else from a single impl; several
// impls and no expected type are rustc's E0283 (L0610 here).
use super::*;

/// One conversion trait method.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Conv {
    AsRef,
    AsMut,
    Borrow,
    BorrowMut,
}

impl<'p, 'a> Ctx<'p, 'a> {
    /// True when a lang trait is in scope by the std `use` rule, or as
    /// the trait of the impl this body is in.
    fn lang_trait_imported(&self, trait_def: DefId, module: &str, name: &str) -> bool {
        self.std_trait_imported(module, name) || self.enclosing_impl_trait_pub() == Some(trait_def)
    }

    /// `as_ref`, `as_mut`, `borrow`, `borrow_mut`, and `to_owned` on a
    /// builtin receiver (user Adts and parameters resolve their impls
    /// in the generic method search first). None when the call is not
    /// one of these, so the other dispatch runs (RefCell's inherent
    /// `borrow` when Borrow is not in scope).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn convert_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        rt: Ty,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        expected: Option<Ty>,
    ) -> Option<Ty> {
        let p = self.p;
        let lang = p.gx.lang;
        let n = p.interner.get(name);
        if !args.is_empty() {
            return None;
        }
        let rt = self.deep(rt);
        // Self: where the template's pick put it (an instance of a
        // generic body), else one reference peeled (the by-value step of
        // a `&self` method), else the receiver by autoref.
        let conv_traits = [lang.as_ref, lang.as_mut, lang.borrow, lang.borrow_mut, lang.to_owned];
        let (self_ty, self_derefs) = match self.replay_pick(e).filter(|pk| conv_traits.contains(&pk.trait_def)) {
            Some(pick) => {
                let mut t = rt;
                for _ in 0..pick.derefs {
                    t = match self.tys.kind(t) {
                        TyKind::Ref(_, _, inner) => self.deep(inner),
                        _ => return None,
                    };
                }
                (t, pick.derefs)
            }
            None => match self.tys.kind(rt) {
                TyKind::Ref(_, _, inner) => (self.deep(inner), 1u8),
                _ => (rt, 0u8),
            },
        };
        if self.tys.local_adt(self_ty).is_some() || matches!(self.tys.kind(self_ty), TyKind::Param(_) | TyKind::Projection(..)) {
            return None;
        }
        // A builtin with an inherent `borrow` of its own (RefCell and its
        // kin) wins at its step: rustc probes inherent methods first.
        // Only the types below have none.
        let plain = |cx: &Self, t: Ty| {
            matches!(
                cx.tys.builtin_of(t),
                None | Some(BuiltinTy::String | BuiltinTy::Vec | BuiltinTy::Option | BuiltinTy::Result | BuiltinTy::Boxed | BuiltinTy::Rc)
                    | Some(BuiltinTy::Sync(crate::ty::sync::SyncTy::Arc))
            )
        };
        let conv = match n {
            "as_ref" => Conv::AsRef,
            "as_mut" => Conv::AsMut,
            "borrow" if self.lang_trait_imported(lang.borrow, "borrow", "Borrow") && plain(self, self_ty) => Conv::Borrow,
            "borrow_mut" if self.lang_trait_imported(lang.borrow_mut, "borrow", "BorrowMut") && plain(self, self_ty) => Conv::BorrowMut,
            "to_owned" => return self.to_owned_call(e, recv, rt, self_ty, self_derefs, name_span),
            _ => return None,
        };
        // AsRef and AsMut forward `&T` and `&mut T` to T's impls.
        let (core, core_derefs) = if matches!(conv, Conv::AsRef | Conv::AsMut) {
            let mut c = self_ty;
            let mut d = self_derefs;
            while let TyKind::Ref(_, _, inner) = self.tys.kind(c) {
                c = self.deep(inner);
                d += 1;
            }
            (c, d)
        } else {
            (self_ty, self_derefs)
        };
        let cands = self.conv_targets(conv, core);
        if cands.is_empty() {
            return None;
        }
        let trait_def = match conv {
            Conv::AsRef => lang.as_ref,
            Conv::AsMut => lang.as_mut,
            Conv::Borrow => lang.borrow,
            Conv::BorrowMut => lang.borrow_mut,
        };
        let mutable = matches!(conv, Conv::AsMut | Conv::BorrowMut);
        // The trait argument: the template's bound, the one impl (rustc
        // selects it before the result coerces: `let s: &str =
        // boxed_string.as_ref()` is `&String`, deref-coerced), or the
        // expected type among several impls.
        let bound = self.instance_bound_arg(trait_def, self_ty);
        let want = bound.or_else(|| {
            if cands.len() == 1 {
                return Some(cands[0]);
            }
            let ex = self.deep(expected?);
            match self.tys.kind(ex) {
                TyKind::Ref(_, m, u) if m.is_mut() == mutable || !mutable => Some(self.deep(u)),
                _ => None,
            }
        });
        let target = match want {
            Some(u) => match cands.iter().copied().find(|&c| c == u).or_else(|| cands.iter().copied().find(|&c| self.unify(c, u))) {
                Some(c) => c,
                None => {
                    let (tn, un) = (self.tn(self_ty), self.tn(u));
                    let tr = self.trait_name(trait_def);
                    self.err("L0612", name_span, format!("no impl of `{tr}<{un}>` for `{tn}`"), "Change the target type.");
                    return Some(ERROR);
                }
            },
            None if cands.len() == 1 => cands[0],
            None => {
                self.err(
                    "L0610",
                    name_span,
                    format!("type annotations needed: `{n}` on `{}` has several impls", self.tn(self_ty)),
                    "Annotate the result type, for example `let s: &str = x.as_ref();`.",
                );
                return Some(ERROR);
            }
        };
        let b = self.conv_builtin(core, target);
        let autoref = if mutable { Autoref::RefMut } else { Autoref::Ref };
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::BuiltinMethod { b, derefs: core_derefs, autoref });
        Some(self.tys.mk_ref(mutable, target))
    }

    /// The trait arguments of a conversion trait's impls for `core`.
    fn conv_targets(&mut self, conv: Conv, core: Ty) -> Vec<Ty> {
        let bytes = self.tys.intern(TyKind::Slice(int(IntTy::U8)));
        let k = self.tys.kind(core);
        let mut out: Vec<Ty> = Vec::new();
        // Borrow and BorrowMut: every type borrows as itself.
        if matches!(conv, Conv::Borrow | Conv::BorrowMut) {
            out.push(core);
        }
        let elem_slice = |cx: &mut Self, e: Ty| cx.tys.intern(TyKind::Slice(e));
        match (conv, k) {
            (Conv::AsRef, TyKind::Str) => out.extend([STR, bytes]),
            (Conv::AsMut, TyKind::Str) => out.push(STR),
            (Conv::AsRef | Conv::AsMut, TyKind::Slice(_)) => out.push(core),
            (_, TyKind::Array(e, _)) => {
                let s = elem_slice(self, e);
                out.push(s);
            }
            (Conv::Borrow, TyKind::Ref(_, _, inner)) => out.push(inner),
            (Conv::BorrowMut, TyKind::Ref(_, m, inner)) if m.is_mut() => out.push(inner),
            _ if self.tys.is_string_ty(core) => match conv {
                Conv::AsRef => out.extend([STR, bytes]),
                _ => out.push(STR),
            },
            _ => {
                if let Some(e) = self.tys.vec_elem(core) {
                    let s = elem_slice(self, e);
                    out.push(s);
                    if matches!(conv, Conv::AsRef | Conv::AsMut) {
                        out.push(core);
                    }
                } else if let Some(e) = self.tys.boxed_elem(core) {
                    out.push(e);
                } else if let Some(e) = self.tys.rc_elem(core)
                    && matches!(conv, Conv::AsRef | Conv::Borrow)
                {
                    out.push(e);
                }
            }
        }
        out
    }

    /// The builtin that converts `&core` to `&target`.
    fn conv_builtin(&self, core: Ty, target: Ty) -> Builtin {
        if core == target {
            return Builtin::ConvIdent;
        }
        match self.tys.kind(core) {
            TyKind::Str => Builtin::ConvStrBytes,
            TyKind::Array(..) => Builtin::ConvArraySlice,
            TyKind::Ref(..) => Builtin::ConvDeref,
            _ if self.tys.is_string_ty(core) => {
                if target == STR {
                    Builtin::StringAsStr
                } else {
                    Builtin::StringAsBytes
                }
            }
            _ if self.tys.vec_elem(core).is_some() => Builtin::VecAsSlice,
            _ if self.tys.rc_elem(core).is_some() => Builtin::ConvRcInner,
            _ => Builtin::ConvDeref,
        }
    }

    /// `to_owned()`: `str` to String, `[T]` to `Vec<T>`, and `T: Clone`
    /// to a clone of Self (which can be a reference: `(&&s).to_owned()`
    /// is `&String`).
    fn to_owned_call(&mut self, e: ExprId, recv: ExprId, rt: Ty, self_ty: Ty, self_derefs: u8, name_span: Span) -> Option<Ty> {
        let _ = rt;
        let (b, ret) = match self.tys.kind(self_ty) {
            TyKind::Str => (Builtin::StrToString, STRING),
            TyKind::Slice(el) => {
                if !has_clone(self.p, &self.tys, el) {
                    return None;
                }
                (Builtin::SliceToVec, self.tys.mk_vec(el))
            }
            _ => {
                if !has_clone(self.p, &self.tys, self_ty) {
                    return None;
                }
                (Builtin::Clone, self_ty)
            }
        };
        self.check_packed_borrow(recv, name_span);
        self.set_res(e, Res::BuiltinMethod { b, derefs: self_derefs, autoref: Autoref::Ref });
        Some(ret)
    }

    /// In an instance of a generic body, the trait argument of the
    /// template's bound `self_ty: trait_def<U>` (substituted at the
    /// instance's args): what the template's call through that bound
    /// meant, which a builtin Self type cannot tell by its impls alone.
    fn instance_bound_arg(&mut self, trait_def: DefId, self_ty: Ty) -> Option<Ty> {
        let p = self.p;
        let info = p.gx.instances.get(&self.fid)?;
        let tl = info.template_local?;
        let env = p.gx.fn_scopes.get(tl.0 as usize)?.env.clone();
        let args: Vec<GenericArg> = p.tys.args(info.args).to_vec();
        for pred in env {
            let Predicate::Trait(b) = pred else { continue };
            if b.value.def != trait_def || b.count != 0 {
                continue;
            }
            let tr = crate::traits::index::subst_trait_ref_pub(&mut self.tys, b.value, &args);
            // A bound on a projection (`I::Item: AsRef<str>`) names its
            // Self normalized in the instance (check/project.rs).
            let a: Vec<Ty> = self.tys.args(tr.args).to_vec().into_iter().filter_map(|g| g.as_ty()).collect();
            let a: Vec<Ty> = a.into_iter().map(|t| self.normalize_here(t)).collect();
            if a.first().copied() == Some(self_ty) {
                return a.get(1).copied();
            }
        }
        None
    }
}
