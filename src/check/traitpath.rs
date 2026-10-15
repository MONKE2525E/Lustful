// A trait method named through its trait as a value or a call:
// `Into::into`, `From::from`, `Clone::clone`, `ToString::to_string`,
// `Default::default`, and user traits in the same shape
// (`.map(Into::into)`, `let f = Clone::clone;`, `Into::into(x)`).
//
// Neither Self nor the trait's other inputs are written, so the
// path is typed like a deferred assoc call (`assoc_call_deferred`):
// the trait obligation stays queued, the value's type is an
// `FnDef` over the trait method itself (its signature is the trait
// method's, so inference through `.map(..)` and friends works),
// and body end selects what the value really calls: a written
// impl's fn, a trait default, a std conversion builtin
// (`Builtin::ConvInto` for `From`/`Into`, `Clone`, `ToString`,
// the `Default` glue), a numeric widening cast, or - in a template
// the param env proves - the trait method's signature stub, as a
// deferred method call does. Anything else is a reject.
use super::*;

/// What a deferred trait fn path selects at body end.
pub(super) enum TraitFnRes {
    /// A real fn (an impl's, a trait default's, or a stub) with its
    /// full generic arguments.
    Fn(LocalDefId, Vec<GenericArg>),
    /// One std conversion builtin (`ConvInto`, `Clone`, `ToString`).
    Builtin(Builtin),
    /// A numeric widening `From`/`Into`: a cast.
    Cast,
    /// The `Default` glue.
    Default,
    /// Nothing lust can call; already reported, or to report.
    Failed,
}

impl<'p> Ctx<'p> {
    /// The trait a two-or-more segment path heads with, when it is a
    /// trait name (bare, or a canonical std trait path) and its last
    /// segment names one of its methods. Returns the trait def, the
    /// method def, and the trait segment. None when the head is a
    /// type, alias, or type parameter of the same name, as in
    /// `self_from_expected_call`.
    pub(super) fn trait_path_head(&mut self, segs: &[ast::PathSeg]) -> Option<(DefId, DefId, usize)> {
        let p = self.p;
        if segs.len() < 2 {
            return None;
        }
        let last = segs.len() - 1;
        let tdef = if segs.len() == 2 {
            if p.type_names.contains_key(&segs[0].name)
                || p.aliases.contains_key(&segs[0].name)
                || self.body_scope.param_tys.iter().any(|(n, _)| *n == segs[0].name)
            {
                return None;
            }
            p.gx.resolve_cx(&p.type_names, &p.aliases).trait_by_bare_name(&p.interner, segs[0].name)?
        } else {
            let path: Vec<&str> = segs[..last].iter().map(|s| self.name(s.name)).collect();
            if crate::ty::lang::std_path_kind(&path) != Some(crate::ty::lang::StdPathKind::Trait) {
                return None;
            }
            // A full canonical path names its trait whether or not the
            // trait is in the prelude (`std::borrow::Borrow`), as
            // `trait_def_of_path` reads it: by name, not by bare name.
            p.gx.resolve_cx(&p.type_names, &p.aliases).trait_by_name(&p.interner, segs[last - 1].name)?
        };
        let rec = p.gx.index.trait_record(tdef)?;
        // A std path through another trait of the same bare name must
        // not answer for this one: the record's own name is the seg's.
        if rec.name != segs[last - 1].name && segs.len() > 2 {
            return None;
        }
        let method = rec.method_by_name(segs[last].name)?;
        Some((tdef, method, last - 1))
    }

    /// True for a `ToString::to_string` path (bare or canonical).
    /// `ToString` is not a lang trait and its shipped-source record
    /// exists only when the program splices that source in, so the
    /// path has a marker form of its own (`to_string_ref`).
    fn is_to_string_path(&self, segs: &[ast::PathSeg]) -> bool {
        let names: Vec<&str> = segs.iter().map(|s| self.p.interner.get(s.name)).collect();
        matches!(names.as_slice(), ["ToString", "to_string"] | ["std" | "alloc", "string", "ToString", "to_string"])
    }

    /// The marker trait ref of a `ToString::to_string` path with no
    /// trait record in this program: Self a fresh variable, and no
    /// obligation (body end asks for `Display` instead, which is
    /// what the blanket impl needs).
    fn to_string_ref(&mut self, e: ExprId, segs: &[ast::PathSeg], span: Span) -> Option<(TraitRef, DefId)> {
        if segs.iter().any(|s| s.has_args()) {
            self.err("L0107", span, "`to_string` takes no generic arguments", "Remove the `::<...>`.");
            return None;
        }
        let _ = e;
        let (tdef, method) = generics::to_string_defs();
        let v = self.new_var(false);
        let args = self.tys.intern_args(&[GenericArg::Ty(v)]);
        Some((TraitRef { def: tdef, args, bindings: EMPTY_BINDINGS }, method))
    }

    /// `Trait::method` as a value: its `FnDef` type over the trait
    /// method, with Self and the trait's other inputs as fresh
    /// variables the queued obligation and the uses around it fix.
    pub(super) fn trait_path_fn_value(&mut self, e: ExprId, segs: &[ast::PathSeg], span: Span) -> Option<Ty> {
        if self.trait_path_head(segs).is_none() && self.is_to_string_path(segs) {
            let (tr, method) = self.to_string_ref(e, segs, span)?;
            self.deferred_trait_fn_values.push((e, tr, segs[segs.len() - 1].name, Vec::new(), span));
            return Some(self.tys.intern(TyKind::FnDef(method, tr.args)));
        }
        let (tdef, method_def, tseg) = self.trait_path_head(segs)?;
        let (tr, full) = self.trait_path_ref(e, segs, tdef, method_def, tseg, span)?;
        let n_trait = self.tys.args(tr.args).len();
        self.deferred_trait_fn_values.push((e, tr, segs[segs.len() - 1].name, full[n_trait..].to_vec(), span));
        let args = self.tys.intern_args(&full);
        Some(self.tys.intern(TyKind::FnDef(method_def, args)))
    }

    /// `Trait::method(args)` as a call, after the assoc-call paths
    /// had no answer: typed by the trait method's signature like the
    /// value form, with the call itself deferred to body end.
    pub(super) fn trait_path_call(&mut self, e: ExprId, callee: ExprId, segs: &[ast::PathSeg], args: &[ExprId], span: Span) -> Option<Ty> {
        if self.trait_path_head(segs).is_none() && self.is_to_string_path(segs) {
            let (tr, method) = self.to_string_ref(e, segs, span)?;
            let full: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
            let (mut params, ret) = self.trait_method_sig(method, &full)?;
            self.normalize_params(&mut params, span);
            self.deferred_trait_fn_calls.push((e, tr, segs[segs.len() - 1].name, Vec::new(), span));
            self.check_args(&params, args, span);
            return Some(self.normalize_use(ret, span));
        }
        let (tdef, method_def, tseg) = self.trait_path_head(segs)?;
        let (tr, full) = self.trait_path_ref(e, segs, tdef, method_def, tseg, span)?;
        let _ = callee;
        let (mut params, ret) = self.trait_method_sig(method_def, &full)?;
        self.normalize_params(&mut params, span);
        let n_trait = self.tys.args(tr.args).len();
        self.deferred_trait_fn_calls.push((e, tr, segs[segs.len() - 1].name, full[n_trait..].to_vec(), span));
        self.check_args(&params, args, span);
        Some(self.normalize_use(ret, span))
    }

    /// The trait ref and full generic arguments (trait, then the
    /// method's own) of a trait path: Self a fresh variable, written
    /// trait arguments honored, the trait obligation queued and the
    /// pick recorded, as `assoc_call_deferred` records them.
    fn trait_path_ref(
        &mut self,
        e: ExprId,
        segs: &[ast::PathSeg],
        tdef: DefId,
        method_def: DefId,
        tseg: usize,
        span: Span,
    ) -> Option<(TraitRef, Vec<GenericArg>)> {
        let p = self.p;
        let rec = p.gx.index.trait_record(tdef)?.clone();
        let base = self.new_var(false);
        let tr = if matches!(segs[tseg].args, ast::GenericArgs::Angle(_)) {
            let tref = ast::TraitRefExpr { path: segs[..=tseg].to_vec() };
            match self.written_trait_ref(base, &tref, span) {
                Ok(tr) if tr.def == tdef => tr,
                Ok(_) => return None,
                Err(d) => {
                    self.errs.push(d);
                    return None;
                }
            }
        } else {
            self.assoc_trait_ref(e, base, None, tdef, &rec)
        };
        let n_trait = rec.generics.params.len();
        let mut full: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
        // The method's own arguments: the turbofish on the method
        // segment, else fresh variables.
        let own_written = segs[segs.len() - 1].type_args();
        let (own_kinds, preds): (Vec<ParamKind>, Vec<Predicate>) = match p.gx.trait_methods.get(&method_def) {
            Some(t) => (t.generics.params.iter().skip(n_trait).map(|x| x.kind).collect(), t.generics.predicates.clone()),
            None => (Vec::new(), Vec::new()),
        };
        if own_written.len() > own_kinds.len() {
            self.err("L0107", span, "this trait method takes no generic arguments here", "Remove the `::<...>`.");
            return None;
        }
        for (i, kind) in own_kinds.iter().enumerate() {
            full.push(match own_written.get(i) {
                Some(w) => GenericArg::Ty(self.resolve_written(*w)),
                None => match kind {
                    ParamKind::Type => GenericArg::Ty(self.new_var(false)),
                    ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
                    ParamKind::Const(_) => GenericArg::Const(self.fresh_const_var()),
                },
            });
        }
        self.push_predicates(&preds, &full, span);
        self.obl.push_trait_at(tr, span, 0);
        self.record_pick(e, tdef, 0, ReceiverForm::Value);
        Some((tr, full))
    }

    /// True when `def` is a trait method lust has a signature for
    /// (a written trait's template, or a lang trait's sig table).
    pub(super) fn is_trait_method_def(&self, def: DefId) -> bool {
        self.p.gx.trait_methods.contains_key(&def)
            || self.p.gx.lang_method_sigs.contains_key(&def)
            || def == generics::to_string_defs().1
    }

    /// A trait method's signature under `full` (trait arguments,
    /// then its own), as `assoc_call_deferred` instantiates it.
    pub(super) fn trait_method_sig(&mut self, method_def: DefId, full: &[GenericArg]) -> Option<(Vec<Ty>, Ty)> {
        if method_def == generics::to_string_defs().1 {
            let self_ty = full.first().and_then(|g| g.as_ty())?;
            return Some((vec![self.tys.mk_ref(false, self_ty)], STRING));
        }
        let p = self.p;
        let (sig_params, sig_ret) = match p.gx.trait_methods.get(&method_def) {
            Some(t) => (t.params.clone(), t.ret),
            None => {
                let s = p.gx.lang_method_sigs.get(&method_def)?;
                (s.params.clone(), s.ret)
            }
        };
        let params: Vec<Ty> = sig_params.iter().map(|&t| subst(&mut self.tys, t, full)).collect();
        let ret = subst(&mut self.tys, sig_ret, full);
        Some((params, ret))
    }

    /// True when this body's param env bounds `t` by `Display`
    /// (the `ToString` blanket's one need, for a marker value in a
    /// template check).
    fn display_in_env(&mut self, t: Ty) -> bool {
        let display = self.p.gx.lang.display;
        self.solve_env().iter().any(|pred| match pred {
            Predicate::Trait(b) => {
                b.value.def == display && self.tys.args(b.value.args).first().and_then(|g| g.as_ty()).is_some_and(|s| self.deep(s) == t)
            }
            _ => false,
        })
    }

    /// What a deferred trait fn path calls, at body end (see the
    /// file head). `tr`'s arguments are read as bound by now.
    pub(super) fn trait_fn_finish(&mut self, tr: TraitRef, name: Sym, own: &[GenericArg], span: Span) -> TraitFnRes {
        let p = self.p;
        let lang = &p.gx.lang;
        // Reading the trait ref as bound by now.
        let targs: Vec<Ty> = self.tys.args(tr.args).to_vec().into_iter().filter_map(|g| g.as_ty()).map(|t| self.deep(t)).collect();
        let known = |cx: &Self, t: Ty| !cx.tys.flags(t).contains_infer() && !cx.has_error_kind(t);
        let is_from = tr.def == lang.from && self.name(name) == "from";
        let is_into = tr.def == lang.into && self.name(name) == "into";
        if (is_from || is_into) && targs.len() >= 2 {
            let (src, dst) = if is_from { (targs[1], targs[0]) } else { (targs[0], targs[1]) };
            if known(self, src) && known(self, dst) {
                if convert::std_from(p, &self.tys, dst, src).is_some() {
                    return TraitFnRes::Builtin(Builtin::ConvInto);
                }
                let (sk, dk) = (self.kind(src), self.kind(dst));
                if matches!(sk, TyKind::Int(_) | TyKind::Float(_) | TyKind::Char | TyKind::Bool)
                    && matches!(dk, TyKind::Int(_) | TyKind::Float(_) | TyKind::Char)
                    && Self::numeric_from_ok(sk, dk)
                {
                    return TraitFnRes::Cast;
                }
            }
        }
        // A written impl's fn, or the trait's default body.
        if let Some((f, mut prefix)) = self.trait_fn_of(tr, name, true, span) {
            prefix.extend(own.iter().copied());
            return TraitFnRes::Fn(f, prefix);
        }
        // `Into` through a written `From` impl (core's blanket): the
        // from fn is the value.
        if is_into && targs.len() >= 2 {
            let fargs = self.tys.intern_args(&[GenericArg::Ty(targs[1]), GenericArg::Ty(targs[0])]);
            let ftr = TraitRef { def: lang.from, args: fargs, bindings: EMPTY_BINDINGS };
            let from_name = p.interner.intern("from");
            if let Some((f, prefix)) = self.trait_fn_of(ftr, from_name, true, span) {
                return TraitFnRes::Fn(f, prefix);
            }
        }
        // The param env proves it (a template check): the stub.
        if let Selection::ParamEvidence(i) = self.select_obligation(tr)
            && i != usize::MAX
            && let Some(rec) = p.gx.index.trait_record(tr.def)
            && let Some(m) = rec.method_by_name(name)
            && let Some(&stub) = p.gx.trait_method_stubs.get(&m)
        {
            let mut full: Vec<GenericArg> =
                self.tys.args(tr.args).to_vec().into_iter().map(|g| if let GenericArg::Ty(t) = g { GenericArg::Ty(self.deep(t)) } else { g }).collect();
            full.extend(own.iter().copied());
            return TraitFnRes::Fn(stub, full);
        }
        let self_ty = targs.first().copied().unwrap_or(ERROR);
        // A synthetic conversion impl (`Borrow::borrow` on a builtin
        // Self) has no fn: the value is the conversion builtin.
        if targs.len() >= 2
            && known(self, self_ty)
            && known(self, targs[1])
            && let Some(b) = self.conv_call_builtin(tr.def, self_ty, targs[1])
        {
            return TraitFnRes::Builtin(b);
        }
        if tr.def == lang.clone && self.name(name) == "clone" && has_clone(p, &self.tys, self_ty) {
            return TraitFnRes::Builtin(Builtin::Clone);
        }
        if tr.def == lang.default && self.name(name) == "default" && has_default(p, &self.tys, self_ty) {
            self.record_glue_reads(lang.default, self_ty);
            return TraitFnRes::Default;
        }
        if self.name(name) == "to_string"
            && (tr.def == generics::to_string_defs().0
                || p.gx.resolve_cx(&p.type_names, &p.aliases).trait_by_bare_name(&p.interner, p.interner.intern("ToString")) == Some(tr.def))
            && (has_display(p, &self.tys, self_ty) || self.display_in_env(self_ty))
        {
            return TraitFnRes::Builtin(Builtin::ToString);
        }
        TraitFnRes::Failed
    }

    /// Body end for trait fn values: point each at what it calls
    /// (a real fn item, or a builtin-marker `FnDef` over the trait
    /// method that lowering expands), as `finish_deferred_methods`
    /// points deferred calls.
    pub(super) fn finish_trait_fn_values(&mut self) {
        for (e, tr, name, own, span) in std::mem::take(&mut self.deferred_trait_fn_values) {
            let ei = self.ei(e);
            match self.trait_fn_finish(tr, name, &own, span) {
                TraitFnRes::Fn(f, full) => {
                    if self.p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
                        self.generic_sites.push((ei, f, full.clone()));
                    }
                    self.set_res(e, Res::Fn(f));
                    // The value's type was the trait method's
                    // `FnDef`; other recordings embed it (a `Map`
                    // adapter's closure type is its `F` argument),
                    // so rewrite it to the selected fn's item type
                    // through the whole checked body.
                    if let TyKind::FnDef(method, _) = self.kind(self.out.expr_ty[ei]) {
                        let args = self.tys.intern_args(&full);
                        let to = self.tys.intern(TyKind::FnDef(self.p.def_id(f), args));
                        let mut from: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
                        from.extend(own.iter().copied());
                        if method != self.p.def_id(f) {
                            for (i, t) in self.out.expr_ty.clone().iter().enumerate() {
                            }
                            self.rewrite_fn_def(method, &from, to);
                        }
                        self.out.expr_ty[ei] = to;
                    }
                }
                TraitFnRes::Builtin(b) => {
                    self.finish_marker_value(e, Res::Builtin(b), tr, name, span);
                }
                TraitFnRes::Cast => {
                    self.finish_marker_value(e, Res::Builtin(Builtin::ConvInto), tr, name, span);
                }
                TraitFnRes::Default => {
                    self.finish_marker_value(e, Res::Builtin(Builtin::DefaultGlue), tr, name, span);
                }
                TraitFnRes::Failed => self.trait_fn_failed(tr, name, span, true),
            }
        }
    }

    /// A builtin-marker trait fn value: the resolution names the
    /// builtin and the type stays the trait method's `FnDef` (its
    /// arguments as bound by now), which calls through it expand.
    /// A reification to a fn pointer has no fn to point at: reject.
    fn finish_marker_value(&mut self, e: ExprId, res: Res, tr: TraitRef, name: Sym, span: Span) {
        let ei = self.ei(e);
        if matches!(self.out.coerce[ei], Coerce::ReifyFn(_)) {
            let tn = self.trait_name(tr.def);
            self.err(
                "L0641",
                span,
                format!("`{tn}::{}` converted to a function pointer is not supported yet", self.name(name)),
                "Wrap it in a closure instead.",
            );
            return;
        }
        self.set_res(e, res);
    }

    /// Body end for calls through a trait fn value (and direct
    /// `Trait::name(..)` calls deferred the same way).
    pub(super) fn finish_trait_fn_calls(&mut self) {
        for (e, tr, name, own, span) in std::mem::take(&mut self.deferred_trait_fn_calls) {
            let ei = self.ei(e);
            match self.trait_fn_finish(tr, name, &own, span) {
                TraitFnRes::Fn(f, full) => {
                    if self.p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
                        self.generic_sites.push((ei, f, full));
                    }
                    self.set_res(e, Res::Fn(f));
                }
                TraitFnRes::Builtin(b) => self.set_res(e, Res::Builtin(b)),
                TraitFnRes::Cast => self.set_res(e, Res::FromCast),
                TraitFnRes::Default => self.set_res(e, Res::DefaultVal),
                TraitFnRes::Failed => self.trait_fn_failed(tr, name, span, false),
            }
        }
    }

    /// Replaces every `FnDef(method, from)` in the checked body's
    /// recorded types with `to` (the selected fn's item type):
    /// adapter types and generic sites embed the value's type, not
    /// just the value expression itself.
    fn rewrite_fn_def(&mut self, method: DefId, from: &[GenericArg], to: Ty) {
        let from: Vec<GenericArg> = from
            .iter()
            .map(|g| match g {
                GenericArg::Ty(t) => GenericArg::Ty(self.deep(*t)),
                other => *other,
            })
            .collect();
        for i in 0..self.out.expr_ty.len() {
            self.out.expr_ty[i] = self.rewrite_ty(self.out.expr_ty[i], method, &from, to);
        }
        for i in 0..self.out.pat_ty.len() {
            self.out.pat_ty[i] = self.rewrite_ty(self.out.pat_ty[i], method, &from, to);
        }
        for i in 0..self.out.locals.len() {
            self.out.locals[i].ty = self.rewrite_ty(self.out.locals[i].ty, method, &from, to);
        }
        for i in 0..self.out.generic_args.len() {
            let args: Vec<GenericArg> = std::mem::take(&mut self.out.generic_args[i]);
            self.out.generic_args[i] = args
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.rewrite_ty(t, method, &from, to)),
                    other => other,
                })
                .collect();
        }
        for i in 0..self.generic_sites.len() {
            let args: Vec<GenericArg> = std::mem::take(&mut self.generic_sites[i].2);
            self.generic_sites[i].2 = args
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.rewrite_ty(t, method, &from, to)),
                    other => other,
                })
                .collect();
        }
    }

    /// `rewrite_fn_def` on one type.
    fn rewrite_ty(&mut self, t: Ty, method: DefId, from: &[GenericArg], to: Ty) -> Ty {
        // An adapter's closure argument is often a variable bound
        // to the FnDef type, not the type itself.
        let t = self.deep(t);
        let args_of = |cx: &mut Self, a: ArgsId| -> Vec<GenericArg> {
            cx.tys
                .args(a)
                .to_vec()
                .into_iter()
                .map(|g| match g {
                    GenericArg::Ty(e) => GenericArg::Ty(cx.rewrite_ty(e, method, from, to)),
                    other => other,
                })
                .collect()
        };
        match self.tys.kind(t) {
            TyKind::FnDef(def, a) => {
                let cur: Vec<GenericArg> = self
                    .tys
                    .args(a)
                    .to_vec()
                    .into_iter()
                    .map(|g| match g {
                        GenericArg::Ty(e) => GenericArg::Ty(self.deep(e)),
                        other => other,
                    })
                    .collect();
                if def == method {
                }
                if def == method && cur == from {
                    to
                } else {
                    let na = args_of(self, a);
                    let na = self.tys.intern_args(&na);
                    self.tys.intern(TyKind::FnDef(def, na))
                }
            }
            TyKind::Adt(def, a) => {
                let na = args_of(self, a);
                self.tys.mk_adt(def, &na)
            }
            TyKind::Closure(def, a) => {
                let na = args_of(self, a);
                let na = self.tys.intern_args(&na);
                self.tys.intern(TyKind::Closure(def, na))
            }
            TyKind::Ref(r, m, e) => {
                let e = self.rewrite_ty(e, method, from, to);
                self.tys.intern(TyKind::Ref(r, m, e))
            }
            TyKind::RawPtr(m, e) => {
                let e = self.rewrite_ty(e, method, from, to);
                self.tys.intern(TyKind::RawPtr(m, e))
            }
            TyKind::Slice(e) => {
                let e = self.rewrite_ty(e, method, from, to);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.rewrite_ty(e, method, from, to);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let elems: Vec<Ty> = self.tys.tys_of(ts).to_vec().into_iter().map(|e| self.rewrite_ty(e, method, from, to)).collect();
                let ts = self.tys.intern_tys(&elems);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::FnPtr(sig) => {
                let s = self.tys.sig(sig);
                let (count, value) = (s.count, s.value);
                let inputs: Vec<Ty> =
                    self.tys.tys_of(value.inputs).to_vec().into_iter().map(|e| self.rewrite_ty(e, method, from, to)).collect();
                let inputs = self.tys.intern_tys(&inputs);
                let output = self.rewrite_ty(value.output, method, from, to);
                let ns = self.tys.intern_sig(crate::ty::Binder { count, value: crate::ty::FnSig { inputs, output, ..value } });
                self.tys.intern(TyKind::FnPtr(ns))
            }
            _ => t,
        }
    }

    /// A trait fn path nothing selected for. The queued obligation
    /// already reported most of these; report the rest once.
    fn trait_fn_failed(&mut self, tr: TraitRef, name: Sym, span: Span, _value: bool) {
        if !self.errs.is_empty() {
            return;
        }
        let tn = self.trait_name(tr.def);
        self.err(
            "L0641",
            span,
            format!("`{tn}::{}` as a function is not supported yet", self.name(name)),
            "Call it through a value or a qualified path, such as `<Type as Trait>::name`, or wrap it in a closure.",
        );
    }
}
