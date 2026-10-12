// Type checking for one function body. Inference is local to the body: unification plus
// integer-literal variables. Output is a set of side tables that lowering reads.
use crate::ast::{self, BinOp, Expr, ExprId, FmtPiece, MacroKind, Pat, PatId, Stmt, UnOp};
use crate::collect::*;
use crate::diag::{Diag, Span, unsupported};
use crate::intern::Sym;
use crate::types::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Autoref {
    None,
    Ref,
    RefMut,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Builtin {
    StringNew,
    StringFrom,
    StringWithCapacity,
    VecNew,
    VecWithCapacity,
    EnvArgs,
    ArgsCount,
    StrLen,
    StrIsEmpty,
    StrToString,
    StringLen,
    StringIsEmpty,
    StringPushStr,
    StringPush,
    StringAsStr,
    VecLen,
    VecIsEmpty,
    VecPush,
    Clone,
    ToString,
    WrappingAdd,
    WrappingSub,
    WrappingMul,
    Abs,
    Pow,
    Min,
    Max,
    OptIsSome,
    OptIsNone,
    OptUnwrap,
    OptExpect,
    OptUnwrapOr,
    VecPop,
    VecGet,
    VecFirst,
    VecLast,
    VecContains,
    VecSwap,
    VecClear,
    VecInsert,
    VecRemove,
    VecTruncate,
    StrContains,
    StrStartsWith,
    StrEndsWith,
    StrTrim,
    StrToUppercase,
    StrToLowercase,
    StrChars,
    CharsNext,
    CharsCount,
    CharIsDigit,
    CharIsAlphabetic,
    CharIsAlphanumeric,
    CharIsWhitespace,
    CharIsUppercase,
    CharIsLowercase,
    CharToUppercase,
    CharToLowercase,
    CharToDigit,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Res {
    None,
    Local(u32),
    Fn(FnId),
    /// A unit variant value, a tuple-variant constructor, or a struct literal target.
    Variant(AdtId, u32),
    Builtin(Builtin),
    /// `None`, and `Some` used as a constructor.
    OptNone,
    OptSome,
    Method {
        f: FnId,
        derefs: u8,
        autoref: Autoref,
    },
    BuiltinMethod {
        b: Builtin,
        derefs: u8,
        autoref: Autoref,
    },
    Field {
        derefs: u8,
        index: u32,
    },
    /// Operand deref counts for binary operators, and for compound assignment.
    Bin {
        ld: u8,
        rd: u8,
    },
    Index {
        derefs: u8,
    },
}

/// A coercion applied where a value meets an expected type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Coerce {
    None,
    /// `&String` to `&str`, or `&&str` style deref coercions ending in `&str`.
    StrFromString,
    /// `&mut T` to `&T`.
    MutToShared,
    /// `&mut T` passed where `&mut T` is expected: reborrow, so the original is not moved.
    Reborrow,
    /// `&&T` (n extra references) to `&T`: copy the inner reference out.
    Deref(u8),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindMode {
    Move,
    Ref(bool),
}

#[derive(Clone, Copy, Debug)]
pub enum PatRes {
    None,
    Binding {
        local: u32,
        mode: BindMode,
    },
    Variant(AdtId, u32),
    /// `Some(..)` (true) or `None` (false).
    Opt(bool),
}

pub struct LocalInfo {
    pub name: Sym,
    pub ty: Ty,
    pub mutable: bool,
    pub span: Span,
}

/// The checker's output for one function.
pub struct Checked<'g> {
    pub tys: Tys<'g>,
    pub expr_base: u32,
    pub pat_base: u32,
    pub expr_ty: Vec<Ty>,
    pub expr_res: Vec<Res>,
    pub coerce: Vec<Coerce>,
    pub pat_ty: Vec<Ty>,
    pub pat_res: Vec<PatRes>,
    /// Number of implicit derefs before matching each pattern (default binding modes).
    pub pat_derefs: Vec<u8>,
    pub locals: Vec<LocalInfo>,
    /// Locals bound to the function parameters, in order (including `self`).
    pub param_locals: Vec<u32>,
}

impl Checked<'_> {
    pub fn ty(&self, e: ExprId) -> Ty {
        self.expr_ty[(e.0 - self.expr_base) as usize]
    }
    pub fn res(&self, e: ExprId) -> Res {
        self.expr_res[(e.0 - self.expr_base) as usize]
    }
    pub fn coerce(&self, e: ExprId) -> Coerce {
        self.coerce[(e.0 - self.expr_base) as usize]
    }
    pub fn pat_ty(&self, p: PatId) -> Ty {
        self.pat_ty[(p.0 - self.pat_base) as usize]
    }
    pub fn pat_res(&self, p: PatId) -> PatRes {
        self.pat_res[(p.0 - self.pat_base) as usize]
    }
    pub fn pat_derefs(&self, p: PatId) -> u8 {
        self.pat_derefs[(p.0 - self.pat_base) as usize]
    }
}

struct Var {
    bound: Option<Ty>,
}

struct LoopCtx {
    break_ty: Option<Ty>,
    is_loop: bool,
}

struct Ctx<'p, 'a> {
    p: &'p Program<'a>,
    f: &'p FnInfo<'a>,
    tys: Tys<'p>,
    vars: Vec<Var>,
    out: Checked<'p>,
    scopes: Vec<(Sym, u32)>,
    loops: Vec<LoopCtx>,
    errs: Vec<Diag>,
    negated_lits: Vec<ExprId>,
    self_ty: Option<Ty>,
}

/// Type-checks one function body.
pub fn check_fn<'p, 'a>(p: &'p Program<'a>, fid: FnId) -> (Checked<'p>, Vec<Diag>) {
    let f = p.fn_info(fid);
    let def = f.def;
    let n_exprs = (def.exprs.1 - def.exprs.0) as usize;
    let n_pats = (def.pats.1 - def.pats.0) as usize;
    let mut cx = Ctx {
        p,
        f,
        tys: Tys::new(&p.tys),
        vars: Vec::new(),
        out: Checked {
            tys: Tys::new(&p.tys),
            expr_base: def.exprs.0,
            pat_base: def.pats.0,
            expr_ty: vec![ERROR; n_exprs],
            expr_res: vec![Res::None; n_exprs],
            coerce: vec![Coerce::None; n_exprs],
            pat_ty: vec![ERROR; n_pats],
            pat_res: vec![PatRes::None; n_pats],
            pat_derefs: vec![0; n_pats],
            locals: Vec::new(),
            param_locals: Vec::new(),
        },
        scopes: Vec::new(),
        loops: Vec::new(),
        errs: Vec::new(),
        negated_lits: Vec::new(),
        self_ty: f.owner.map(|a| p.tys.get(TyKind::Adt(a)).expect("ADT types are interned during collection")),
    };
    let mut pi = 0;
    if let Some(sp) = &def.self_param {
        let l = cx.add_local(p.known.self_value, f.params[0], sp.mutable, sp.span);
        cx.out.param_locals.push(l);
        pi = 1;
    }
    for param in &def.params {
        let l = cx.add_local(param.name, f.params[pi], param.mutable, param.span);
        cx.out.param_locals.push(l);
        pi += 1;
    }
    let body_ty = cx.block(def.body, Some(f.ret));
    let body_span = p.ast.block(def.body).span;
    if let Some(tail) = p.ast.block(def.body).tail {
        cx.coerce_expr(tail, body_ty, f.ret);
    } else {
        cx.coerce_at(body_ty, f.ret, body_span, None);
    }
    cx.finish();
    let Ctx { out, tys, errs, .. } = cx;
    let mut out = out;
    out.tys = tys;
    (out, errs)
}

impl<'p, 'a> Ctx<'p, 'a> {
    fn err(&mut self, code: &'static str, span: Span, msg: impl Into<String>, fix: impl Into<String>) {
        self.errs.push(Diag::new(code, span, msg, fix));
    }
    fn span(&self, e: ExprId) -> Span {
        self.p.ast.expr_span(e)
    }
    fn name(&self, s: Sym) -> &str {
        self.p.name(s)
    }
    /// Type name for messages, with inference variables resolved.
    fn tn(&self, t: Ty) -> String {
        match self.kind(t) {
            TyKind::Vec(e) => format!("Vec<{}>", self.tn(e)),
            TyKind::Option(e) => format!("Option<{}>", self.tn(e)),
            TyKind::Ref(m, e) => format!("&{}{}", if m { "mut " } else { "" }, self.tn(e)),
            _ => ty_name(self.p, &self.tys, self.resolve(t)),
        }
    }
    fn ei(&self, e: ExprId) -> usize {
        (e.0 - self.out.expr_base) as usize
    }
    fn set(&mut self, e: ExprId, t: Ty) -> Ty {
        let i = self.ei(e);
        self.out.expr_ty[i] = t;
        t
    }
    fn set_res(&mut self, e: ExprId, r: Res) {
        let i = self.ei(e);
        self.out.expr_res[i] = r;
    }
    fn add_local(&mut self, name: Sym, ty: Ty, mutable: bool, span: Span) -> u32 {
        let l = self.out.locals.len() as u32;
        self.out.locals.push(LocalInfo { name, ty, mutable, span });
        self.scopes.push((name, l));
        l
    }
    fn lookup(&self, name: Sym) -> Option<u32> {
        self.scopes.iter().rev().find(|(n, _)| *n == name).map(|&(_, l)| l)
    }

    // ---------- Inference ----------

    fn new_var(&mut self, int: bool) -> Ty {
        self.vars.push(Var { bound: None });
        let id = self.vars.len() as u32 - 1;
        self.tys.intern(TyKind::Var(id, int))
    }
    /// Follows variable bindings at the top level only.
    fn resolve(&self, mut t: Ty) -> Ty {
        while let TyKind::Var(v, _) = self.tys.kind(t) {
            match self.vars[v as usize].bound {
                Some(b) => t = b,
                None => return t,
            }
        }
        t
    }
    fn kind(&self, t: Ty) -> TyKind {
        self.tys.kind(self.resolve(t))
    }
    /// Fully resolves a type, interning new structural types as needed. Unbound integer
    /// variables become i32.
    fn zonk(&mut self, t: Ty) -> Ty {
        let t = self.resolve(t);
        match self.tys.kind(t) {
            TyKind::Var(v, int) => {
                let d = if int { I32 } else { ERROR };
                self.vars[v as usize].bound = Some(d);
                d
            }
            TyKind::Vec(e) => {
                let e = self.zonk(e);
                self.tys.intern(TyKind::Vec(e))
            }
            TyKind::Option(e) => {
                let e = self.zonk(e);
                self.tys.intern(TyKind::Option(e))
            }
            TyKind::Ref(m, e) => {
                let e = self.zonk(e);
                self.tys.intern(TyKind::Ref(m, e))
            }
            _ => t,
        }
    }
    /// Resolves variables at every depth, keeping unbound ones. Trait queries need this.
    fn deep(&mut self, t: Ty) -> Ty {
        let t = self.resolve(t);
        match self.tys.kind(t) {
            TyKind::Vec(e) => {
                let e = self.deep(e);
                self.tys.intern(TyKind::Vec(e))
            }
            TyKind::Option(e) => {
                let e = self.deep(e);
                self.tys.intern(TyKind::Option(e))
            }
            TyKind::Ref(m, e) => {
                let e = self.deep(e);
                self.tys.intern(TyKind::Ref(m, e))
            }
            _ => t,
        }
    }

    fn unify(&mut self, a: Ty, b: Ty) -> bool {
        let (a, b) = (self.resolve(a), self.resolve(b));
        if a == b {
            return true;
        }
        match (self.tys.kind(a), self.tys.kind(b)) {
            (TyKind::Error, _) | (_, TyKind::Error) => true,
            (TyKind::Var(v, vi), TyKind::Var(w, wi)) => {
                // Bind the general variable to the integer one, so the integer constraint survives.
                if vi && !wi {
                    self.vars[w as usize].bound = Some(a);
                } else {
                    self.vars[v as usize].bound = Some(b);
                }
                true
            }
            (TyKind::Var(v, int), k) | (k, TyKind::Var(v, int)) => {
                if int && !matches!(k, TyKind::Int(_)) {
                    return false;
                }
                let other = if matches!(self.tys.kind(a), TyKind::Var(..)) { b } else { a };
                if self.occurs(v, other) {
                    return false;
                }
                self.vars[v as usize].bound = Some(other);
                true
            }
            (TyKind::Vec(x), TyKind::Vec(y)) | (TyKind::Option(x), TyKind::Option(y)) => self.unify(x, y),
            (TyKind::Ref(m, x), TyKind::Ref(n, y)) => m == n && self.unify(x, y),
            _ => false,
        }
    }
    fn occurs(&self, v: u32, t: Ty) -> bool {
        match self.kind(t) {
            TyKind::Var(w, _) => w == v,
            TyKind::Vec(e) | TyKind::Option(e) | TyKind::Ref(_, e) => self.occurs(v, e),
            _ => false,
        }
    }
    fn mismatch(&mut self, span: Span, expected: Ty, found: Ty) {
        let (e, f) = (self.tn(expected), self.tn(found));
        let fix = if e == "&str" && f == "String" {
            "Borrow it: write `&value` or `value.as_str()`.".to_string()
        } else if e == "String" && f == "&str" {
            "Convert it: write `value.to_string()`.".to_string()
        } else if f.starts_with('&') && e == f[1..] {
            "Dereference it with `*value`, or clone it if the type is not Copy.".to_string()
        } else if e.starts_with('&') && f == e[1..] {
            "Borrow it with `&value`.".to_string()
        } else {
            format!("Change the value to type `{e}`, or change the expected type.")
        };
        self.err("L0110", span, format!("mismatched types: expected `{e}`, found `{f}`"), fix);
    }
    /// Checks `found` against `expected` at a coercion site. Records the coercion on `e`.
    fn coerce_at(&mut self, found: Ty, expected: Ty, span: Span, e: Option<ExprId>) -> bool {
        let (fk, ek) = (self.kind(found), self.kind(expected));
        if fk == TyKind::Never {
            return true;
        }
        // Count reference layers, for deref coercions.
        let depth = |cx: &Self, mut t: Ty| {
            let mut n = 0u8;
            while let TyKind::Ref(_, inner) = cx.kind(t) {
                t = inner;
                n += 1;
            }
            (n, t)
        };
        let (fd, fbase) = depth(self, found);
        let (ed, _) = depth(self, expected);
        let c = match (fk, ek) {
            (TyKind::Ref(..), TyKind::Ref(false, s)) if self.kind(s) == TyKind::Str && self.kind(fbase) == TyKind::String => {
                Coerce::StrFromString
            }
            (TyKind::Ref(..), TyKind::Ref(false, _))
                if fd > ed && {
                    let mut t = found;
                    for _ in 0..fd - ed {
                        if let TyKind::Ref(_, inner) = self.kind(t) {
                            t = inner;
                        }
                    }
                    matches!(self.kind(t), TyKind::Ref(false, _)) && self.unify(t, expected)
                } =>
            {
                Coerce::Deref(fd - ed)
            }
            (TyKind::Ref(true, x), TyKind::Ref(false, y)) if self.unify(x, y) => Coerce::MutToShared,
            (TyKind::Ref(true, x), TyKind::Ref(true, y)) if self.unify(x, y) => Coerce::Reborrow,
            _ => {
                if !self.unify(found, expected) {
                    self.mismatch(span, expected, found);
                    return false;
                }
                Coerce::None
            }
        };
        if let Some(e) = e {
            let i = self.ei(e);
            self.out.coerce[i] = c;
        }
        true
    }
    fn coerce_expr(&mut self, e: ExprId, found: Ty, expected: Ty) -> bool {
        let span = self.span(e);
        self.coerce_at(found, expected, span, Some(e))
    }
    fn expect_expr(&mut self, e: ExprId, expected: Ty) -> Ty {
        let t = self.expr(e, Some(expected));
        self.coerce_expr(e, t, expected);
        t
    }

    // ---------- Blocks and statements ----------

    fn block(&mut self, b: ast::BlockId, expected: Option<Ty>) -> Ty {
        let block = self.p.ast.block(b);
        let scope = self.scopes.len();
        let mut diverges = false;
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, ty, init, span } => {
                    let declared = ty.map(|t| self.resolve_written(t));
                    let ty = match (declared, init) {
                        (Some(d), Some(init)) => {
                            let t = self.expr(*init, Some(d));
                            self.coerce_expr(*init, t, d);
                            if self.kind(t) == TyKind::Never {
                                diverges = true;
                            }
                            d
                        }
                        (Some(d), None) => d,
                        (None, Some(init)) => {
                            let t = self.expr(*init, None);
                            if self.kind(t) == TyKind::Never {
                                diverges = true;
                            }
                            t
                        }
                        (None, None) => self.new_var(false),
                    };
                    match self.p.ast.pat(*pat) {
                        Pat::Binding { name, mutable, by_ref } => {
                            let (name, mutable, by_ref) = (*name, *mutable, *by_ref);
                            let lty = if by_ref { self.tys.intern(TyKind::Ref(mutable, ty)) } else { ty };
                            let l = self.add_local(name, lty, mutable && !by_ref, *span);
                            let pi = (pat.0 - self.out.pat_base) as usize;
                            self.out.pat_ty[pi] = ty;
                            let mode = if by_ref { BindMode::Ref(mutable) } else { BindMode::Move };
                            self.out.pat_res[pi] = PatRes::Binding { local: l, mode };
                        }
                        Pat::Wild => {
                            let pi = (pat.0 - self.out.pat_base) as usize;
                            self.out.pat_ty[pi] = ty;
                        }
                        _ => {
                            let s = self.p.ast.pat_span(*pat);
                            self.errs.push(unsupported(s, "destructuring in `let`"));
                        }
                    }
                }
                Stmt::Expr { expr, semi } => {
                    let t = self.expr(*expr, if *semi { None } else { Some(UNIT) });
                    if self.kind(t) == TyKind::Never {
                        diverges = true;
                    } else if !semi && !self.unify(t, UNIT) {
                        let s = self.span(*expr);
                        self.err("L0110", s, format!("expected `()`, found `{}`", self.tn(t)), "Add a `;` after this expression.");
                    }
                }
            }
        }
        let t = match block.tail {
            Some(tail) => self.expr(tail, expected),
            None if diverges => NEVER,
            None => UNIT,
        };
        self.scopes.truncate(scope);
        t
    }

    fn resolve_written(&mut self, t: ast::TyId) -> Ty {
        let p = self.p;
        match resolve_ty(p.ast, p.interner, p.known, &p.type_names, &mut self.tys, t, self.self_ty) {
            Ok(t) => t,
            Err(d) => {
                self.errs.push(d);
                ERROR
            }
        }
    }

    // ---------- Expressions ----------

    fn expr(&mut self, e: ExprId, expected: Option<Ty>) -> Ty {
        let t = self.expr_inner(e, expected);
        self.set(e, t)
    }

    fn expr_inner(&mut self, e: ExprId, expected: Option<Ty>) -> Ty {
        let span = self.span(e);
        let p = self.p;
        match p.ast.expr(e) {
            Expr::Int(_, Some(s)) => int(IntTy::from_suffix(*s)),
            Expr::Int(_, None) => match expected.map(|t| (self.resolve(t), self.kind(t))) {
                Some((t, TyKind::Int(_))) => t,
                Some((t, TyKind::Var(_, true))) => t,
                _ => self.new_var(true),
            },
            Expr::Bool(_) => BOOL,
            Expr::Char(_) => CHAR,
            Expr::Str(_) => REF_STR,
            Expr::Unit => UNIT,
            Expr::SelfValue => match self.lookup(p.known.self_value) {
                Some(l) => {
                    self.set_res(e, Res::Local(l));
                    self.out.locals[l as usize].ty
                }
                None => {
                    self.err("L0101", span, "`self` is not available here", "Only methods with a `self` parameter can use `self`.");
                    ERROR
                }
            },
            Expr::Path(segs) => self.path_expr(e, segs, span),
            Expr::Block(b) => self.block(*b, expected),
            Expr::If { cond, then, els } => {
                self.expect_expr(*cond, BOOL);
                match els {
                    None => {
                        let t = self.block(*then, Some(UNIT));
                        let bspan = p.ast.block(*then).span;
                        if let Some(tail) = p.ast.block(*then).tail {
                            self.coerce_expr(tail, t, UNIT);
                        } else {
                            self.coerce_at(t, UNIT, bspan, None);
                        }
                        UNIT
                    }
                    Some(els) => {
                        let t1 = self.block(*then, expected);
                        let t2 = self.expr(*els, expected.or(Some(t1)));
                        self.join(t1, t2, Some(*els), span)
                    }
                }
            }
            Expr::While { cond, body } => {
                self.expect_expr(*cond, BOOL);
                self.loops.push(LoopCtx { break_ty: None, is_loop: false });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                self.loops.pop();
                UNIT
            }
            Expr::Loop { body } => {
                self.loops.push(LoopCtx { break_ty: None, is_loop: true });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                let l = self.loops.pop().unwrap();
                l.break_ty.unwrap_or(NEVER)
            }
            Expr::For { pat, iter, body } => {
                let item = self.for_iter(*iter);
                let scope = self.scopes.len();
                self.pattern(*pat, item, false);
                self.loops.push(LoopCtx { break_ty: None, is_loop: false });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                self.loops.pop();
                self.scopes.truncate(scope);
                UNIT
            }
            Expr::Match { scrut, arms } => {
                let st = self.expr(*scrut, None);
                let mut result: Option<Ty> = None;
                for arm in arms {
                    let scope = self.scopes.len();
                    self.pattern(arm.pat, st, true);
                    if let Some(g) = arm.guard {
                        self.expect_expr(g, BOOL);
                    }
                    let bt = self.expr(arm.body, expected.or(result));
                    result = Some(match result {
                        None => bt,
                        Some(r) => self.join(r, bt, Some(arm.body), self.span(arm.body)),
                    });
                    self.scopes.truncate(scope);
                }
                self.exhaustive(st, arms, span);
                result.unwrap_or(NEVER)
            }
            Expr::Call { callee, args } => self.call(e, *callee, args, span),
            Expr::MethodCall { recv, name, name_span, generics, args } => {
                if !generics.is_empty() {
                    self.errs.push(unsupported(*name_span, "turbofish on method calls"));
                }
                self.method_call(e, *recv, *name, *name_span, args)
            }
            Expr::Field { base, name } => {
                let bt = self.expr(*base, None);
                let (derefs, inner) = self.autoderef(bt);
                if let TyKind::Adt(a) = self.kind(inner) {
                    let adt = p.adt(a);
                    if !adt.is_enum
                        && let Some(i) = adt.variants[0].fields.iter().position(|f| f.name == *name)
                    {
                        self.set_res(e, Res::Field { derefs, index: i as u32 });
                        return adt.variants[0].fields[i].ty;
                    }
                }
                if !matches!(self.kind(inner), TyKind::Error) {
                    let tn = self.tn(bt);
                    self.err("L0103", span, format!("no field `{}` on type `{tn}`", self.name(*name)), "Check the field name.");
                }
                ERROR
            }
            Expr::Index { base, index } => {
                let bt = self.expr(*base, None);
                let (derefs, inner) = self.autoderef(bt);
                self.expect_expr(*index, USIZE);
                match self.kind(inner) {
                    TyKind::Vec(elem) => {
                        self.set_res(e, Res::Index { derefs });
                        elem
                    }
                    TyKind::Error => ERROR,
                    TyKind::String | TyKind::Str => {
                        self.err(
                            "L0113",
                            span,
                            "strings cannot be indexed by an integer",
                            "Use `.chars()` later, or `.as_bytes()`. Not supported in the prototype yet.",
                        );
                        ERROR
                    }
                    _ => {
                        let tn = self.tn(bt);
                        self.err(
                            "L0113",
                            span,
                            format!("cannot index into a value of type `{tn}`"),
                            "Only Vec supports indexing in the prototype.",
                        );
                        ERROR
                    }
                }
            }
            Expr::Binary { op, lhs, rhs } => self.binary(e, *op, *lhs, *rhs, span),
            Expr::Unary { op, expr } => {
                if *op == UnOp::Neg
                    && let Expr::Int(..) = p.ast.expr(*expr)
                {
                    self.negated_lits.push(*expr);
                }
                let t = self.expr(*expr, expected);
                let k = self.kind(t);
                match (op, k) {
                    (UnOp::Neg, TyKind::Int(i)) if i.signed() => t,
                    (UnOp::Neg, TyKind::Var(_, true)) => t,
                    (UnOp::Not, TyKind::Bool | TyKind::Int(_) | TyKind::Var(_, true)) => t,
                    (_, TyKind::Error) => ERROR,
                    _ => {
                        let tn = self.tn(t);
                        let sym = if *op == UnOp::Neg { "-" } else { "!" };
                        self.err(
                            "L0113",
                            span,
                            format!("cannot apply unary `{sym}` to type `{tn}`"),
                            "Use a signed integer type for `-`, or a bool or integer for `!`.",
                        );
                        ERROR
                    }
                }
            }
            Expr::Cast { expr, ty } => {
                let target = self.resolve_written(*ty);
                let t = self.expr(*expr, None);
                let ok = match (self.kind(t), self.kind(target)) {
                    // An integer of unknown type stays open: later uses decide it (default i32).
                    (TyKind::Var(_, true), TyKind::Int(_)) => true,
                    (TyKind::Int(_) | TyKind::Bool | TyKind::Char, TyKind::Int(_)) => true,
                    (TyKind::Int(IntTy::U8), TyKind::Char) => true,
                    (TyKind::Error, _) | (_, TyKind::Error) => true,
                    _ => false,
                };
                if !ok {
                    let (a, b) = (self.tn(t), self.tn(target));
                    self.err(
                        "L0116",
                        span,
                        format!("cannot cast `{a}` as `{b}`"),
                        "Lust allows `as` between integers, from bool and char to integers, and from u8 to char.",
                    );
                }
                target
            }
            Expr::Ref { mutable, expr } => {
                let inner_expected = expected.and_then(|t| match self.kind(t) {
                    TyKind::Ref(_, inner) => Some(inner),
                    _ => None,
                });
                let t = self.expr(*expr, inner_expected);
                self.tys.intern(TyKind::Ref(*mutable, t))
            }
            Expr::Deref(inner) => {
                let t = self.expr(*inner, None);
                match self.kind(t) {
                    TyKind::Ref(_, x) => x,
                    TyKind::Error => ERROR,
                    _ => {
                        let tn = self.tn(t);
                        self.err(
                            "L0113",
                            span,
                            format!("type `{tn}` cannot be dereferenced"),
                            "Only references can be dereferenced with `*`.",
                        );
                        ERROR
                    }
                }
            }
            Expr::Assign { lhs, rhs } => {
                let lt = self.expr(*lhs, None);
                self.place_check(*lhs);
                self.expect_expr(*rhs, lt);
                UNIT
            }
            Expr::AssignOp { op, lhs, rhs } => {
                let lt = self.expr(*lhs, None);
                self.place_check(*lhs);
                let rt = self.expr(*rhs, Some(lt));
                let lk = self.kind(lt);
                if lk == TyKind::String && *op == BinOp::Add {
                    self.coerce_expr(*rhs, rt, REF_STR);
                    self.set_res(e, Res::Bin { ld: 0, rd: 0 });
                    return UNIT;
                }
                let (rd, rinner) = self.peel_one_ref(rt);
                let ok = match (*op, lk) {
                    (_, TyKind::Error) => true,
                    (BinOp::Shl | BinOp::Shr, TyKind::Int(_) | TyKind::Var(_, true)) => {
                        matches!(self.kind(rinner), TyKind::Int(_) | TyKind::Var(_, true))
                    }
                    (_, TyKind::Int(_) | TyKind::Var(_, true)) => self.unify(lt, rinner),
                    (BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor, TyKind::Bool) => self.unify(lt, rinner),
                    _ => false,
                };
                if !ok {
                    let (a, b) = (self.tn(lt), self.tn(rt));
                    self.err(
                        "L0113",
                        span,
                        format!("cannot apply `{}=` to `{a}` and `{b}`", op.symbol()),
                        "Both sides must be the same integer type.",
                    );
                }
                self.set_res(e, Res::Bin { ld: 0, rd });
                UNIT
            }
            Expr::StructLit { path, fields } => self.struct_lit(e, path, fields, span),
            Expr::Range { .. } => {
                self.errs.push(unsupported(span, "ranges outside `for` loops"));
                ERROR
            }
            Expr::Break(val) => {
                let Some(lp) = self.loops.last() else {
                    self.err("L0120", span, "`break` outside of a loop", "Remove the break, or put it inside a loop.");
                    return NEVER;
                };
                let is_loop = lp.is_loop;
                let prev = lp.break_ty;
                match val {
                    Some(v) if !is_loop => {
                        self.expr(*v, None);
                        self.err("L0120", span, "`break` with a value is only allowed in `loop`", "Remove the value, or use `loop`.");
                    }
                    Some(v) => {
                        let t = self.expr(*v, prev);
                        match prev {
                            Some(pt) => {
                                self.coerce_expr(*v, t, pt);
                            }
                            None => self.loops.last_mut().unwrap().break_ty = Some(t),
                        }
                    }
                    None if is_loop => match prev {
                        Some(pt) => {
                            self.coerce_at(UNIT, pt, span, None);
                        }
                        None => self.loops.last_mut().unwrap().break_ty = Some(UNIT),
                    },
                    None => {}
                }
                NEVER
            }
            Expr::Continue => {
                if self.loops.is_empty() {
                    self.err("L0120", span, "`continue` outside of a loop", "Remove the continue, or put it inside a loop.");
                }
                NEVER
            }
            Expr::Return(val) => {
                let ret = self.f.ret;
                match val {
                    Some(v) => {
                        self.expect_expr(*v, ret);
                    }
                    None => {
                        self.coerce_at(UNIT, ret, span, None);
                    }
                }
                NEVER
            }
            Expr::Macro { kind, args, fmt, repeat } => self.macro_expr(e, *kind, args, fmt, *repeat, span, expected),
        }
    }

    fn unit_body(&mut self, t: Ty, b: ast::BlockId) {
        let block = self.p.ast.block(b);
        if let Some(tail) = block.tail {
            self.coerce_expr(tail, t, UNIT);
        }
    }

    /// Joins the types of two branches. A diverging branch takes the other branch's type.
    fn join(&mut self, a: Ty, b: Ty, be: Option<ExprId>, span: Span) -> Ty {
        if self.kind(a) == TyKind::Never {
            return b;
        }
        if self.kind(b) == TyKind::Never {
            return a;
        }
        if let Some(be) = be {
            if self.coerce_expr(be, b, a) {
                return a;
            }
            return ERROR;
        }
        if !self.unify(a, b) {
            self.mismatch(span, a, b);
            return ERROR;
        }
        a
    }

    /// Requires an assignable place expression on the left of `=`.
    fn place_check(&mut self, e: ExprId) {
        let ok = match self.p.ast.expr(e) {
            Expr::Path(segs) => segs.len() == 1 && matches!(self.out.expr_res[self.ei(e)], Res::Local(_)),
            Expr::Field { .. } | Expr::Index { .. } | Expr::Deref(_) | Expr::SelfValue => true,
            _ => false,
        };
        if !ok {
            let s = self.span(e);
            self.err("L0121", s, "invalid left-hand side of assignment", "Assign to a variable, a field, an index, or `*reference`.");
        }
    }

    /// Strips all references. Returns the count and the inner type.
    fn autoderef(&self, t: Ty) -> (u8, Ty) {
        let mut t = self.resolve(t);
        let mut n = 0;
        while let TyKind::Ref(_, inner) = self.tys.kind(t) {
            t = self.resolve(inner);
            n += 1;
        }
        (n, t)
    }
    fn peel_one_ref(&self, t: Ty) -> (u8, Ty) {
        match self.kind(t) {
            TyKind::Ref(_, inner) => (1, inner),
            _ => (0, t),
        }
    }

    fn path_expr(&mut self, e: ExprId, segs: &[ast::PathSeg], span: Span) -> Ty {
        let p = self.p;
        if segs.len() == 1 {
            let name = segs[0].name;
            if let Some(l) = self.lookup(name) {
                self.set_res(e, Res::Local(l));
                return self.out.locals[l as usize].ty;
            }
            if let Some(&f) = p.fn_names.get(&name) {
                self.set_res(e, Res::Fn(f));
                return ERROR;
            }
            if name == p.known.None {
                self.set_res(e, Res::OptNone);
                let v = self.new_var(false);
                return self.tys.intern(TyKind::Option(v));
            }
            if let Some(&a) = p.type_names.get(&name) {
                let adt = p.adt(a);
                if !adt.is_enum && adt.variants[0].shape == VariantShape::Unit {
                    self.set_res(e, Res::Variant(a, 0));
                    return self.tys.intern(TyKind::Adt(a));
                }
            }
            self.err(
                "L0101",
                span,
                format!("cannot find value `{}` in this scope", self.name(name)),
                "Check the spelling, or declare it with `let` first.",
            );
            return ERROR;
        }
        if let Some(r) = self.resolve_assoc(segs, span) {
            self.set_res(e, r);
            if let Res::Variant(a, v) = r {
                let variant = &p.adt(a).variants[v as usize];
                if variant.shape == VariantShape::Unit {
                    return self.tys.intern(TyKind::Adt(a));
                }
            }
            return ERROR;
        }
        ERROR
    }

    /// Resolves `Type::item` and `std::env::args`. Reports an error and returns None on failure.
    fn resolve_assoc(&mut self, segs: &[ast::PathSeg], span: Span) -> Option<Res> {
        let p = self.p;
        let k = p.known;
        let names: Vec<Sym> = segs.iter().map(|s| s.name).collect();
        if names == [k.std, k.env, k.args] {
            return Some(Res::Builtin(Builtin::EnvArgs));
        }
        if segs.len() != 2 {
            self.errs.push(unsupported(span, "module paths"));
            return None;
        }
        let (ty_name, item) = (names[0], names[1]);
        if ty_name == k.String {
            let b = if item == k.new {
                Builtin::StringNew
            } else if item == k.from {
                Builtin::StringFrom
            } else if item == k.with_capacity {
                Builtin::StringWithCapacity
            } else {
                self.err(
                    "L0104",
                    span,
                    format!("no function `String::{}`", self.name(item)),
                    "Lust supports String::new, String::from, and String::with_capacity.",
                );
                return None;
            };
            return Some(Res::Builtin(b));
        }
        if ty_name == k.Vec {
            let b = if item == k.new {
                Builtin::VecNew
            } else if item == k.with_capacity {
                Builtin::VecWithCapacity
            } else {
                self.err(
                    "L0104",
                    span,
                    format!("no function `Vec::{}`", self.name(item)),
                    "Lust supports Vec::new and Vec::with_capacity.",
                );
                return None;
            };
            return Some(Res::Builtin(b));
        }
        let adt = if ty_name == p.known.self_type { self.f.owner } else { p.type_names.get(&ty_name).copied() };
        let Some(a) = adt else {
            self.err("L0101", span, format!("cannot find type `{}`", self.name(ty_name)), "Check the spelling.");
            return None;
        };
        let def = p.adt(a);
        if def.is_enum
            && let Some(v) = def.variants.iter().position(|v| v.name == item)
        {
            return Some(Res::Variant(a, v as u32));
        }
        if let Some(&f) = p.methods.get(&(a, item)) {
            return Some(Res::Fn(f));
        }
        let tn = self.name(ty_name).to_string();
        self.err("L0104", span, format!("no variant or associated function `{}` on `{tn}`", self.name(item)), "Check the name.");
        None
    }

    fn call(&mut self, e: ExprId, callee: ExprId, args: &[ExprId], span: Span) -> Ty {
        let p = self.p;
        let res = match p.ast.expr(callee) {
            Expr::Path(segs) if segs.len() == 1 => {
                let name = segs[0].name;
                if self.lookup(name).is_some() {
                    self.err("L0114", span, "this value is not a function", "Closures are not supported yet. Call a named function.");
                    return ERROR;
                }
                match p.fn_names.get(&name) {
                    Some(&f) => Res::Fn(f),
                    None if name == p.known.Some => Res::OptSome,
                    None => {
                        let cs = self.span(callee);
                        self.err(
                            "L0101",
                            cs,
                            format!("cannot find function `{}`", self.name(name)),
                            "Check the spelling, or define the function.",
                        );
                        for &a in args {
                            self.expr(a, None);
                        }
                        return ERROR;
                    }
                }
            }
            Expr::Path(segs) => {
                let cs = self.span(callee);
                match self.resolve_assoc(segs, cs) {
                    Some(r) => r,
                    None => {
                        for &a in args {
                            self.expr(a, None);
                        }
                        return ERROR;
                    }
                }
            }
            _ => {
                self.err("L0114", span, "only named functions can be called", "Closures and function values are not supported yet.");
                return ERROR;
            }
        };
        self.set_res(callee, res);
        self.set_res(e, res);
        if res == Res::OptSome {
            if args.len() != 1 {
                self.err("L0105", span, "`Some` takes one argument", "Write `Some(value)`.");
                return ERROR;
            }
            let t = self.expr(args[0], None);
            return self.tys.intern(TyKind::Option(t));
        }
        match res {
            Res::Fn(f) => {
                // Path calls such as `Type::method(x)` pass `self` explicitly, so all params apply.
                let info = p.fn_info(f);
                self.check_args(&info.params.clone(), args, span);
                info.ret
            }
            Res::Variant(a, v) => {
                let variant = &p.adt(a).variants[v as usize];
                if variant.shape != VariantShape::Tuple {
                    self.err("L0114", span, "this variant is not a tuple variant", "Use `Type::Variant` or `Type::Variant { .. }`.");
                    return ERROR;
                }
                let params: Vec<Ty> = variant.fields.iter().map(|f| f.ty).collect();
                self.check_args(&params, args, span);
                self.tys.intern(TyKind::Adt(a))
            }
            Res::Builtin(b) => {
                let (params, ret): (Vec<Ty>, Ty) = match b {
                    Builtin::StringNew => (vec![], STRING),
                    Builtin::StringFrom => (vec![REF_STR], STRING),
                    Builtin::StringWithCapacity => (vec![USIZE], STRING),
                    Builtin::EnvArgs => (vec![], ARGS),
                    Builtin::VecNew | Builtin::VecWithCapacity => {
                        let generics = match p.ast.expr(callee) {
                            Expr::Path(segs) => segs[0].generics.clone(),
                            _ => Vec::new(),
                        };
                        let elem = match generics.first() {
                            Some(&g) => self.resolve_written(g),
                            None => self.new_var(false),
                        };
                        let params = if b == Builtin::VecNew { vec![] } else { vec![USIZE] };
                        (params, self.tys.intern(TyKind::Vec(elem)))
                    }
                    _ => unreachable!(),
                };
                self.check_args(&params, args, span);
                ret
            }
            _ => ERROR,
        }
    }

    fn check_args(&mut self, params: &[Ty], args: &[ExprId], span: Span) {
        if params.len() != args.len() {
            self.err(
                "L0105",
                span,
                format!("this function takes {} argument(s) but {} were given", params.len(), args.len()),
                "Pass exactly the declared arguments.",
            );
        }
        for (i, &a) in args.iter().enumerate() {
            match params.get(i) {
                Some(&pt) => {
                    self.expect_expr(a, pt);
                }
                None => {
                    self.expr(a, None);
                }
            }
        }
    }

    fn method_call(&mut self, e: ExprId, recv: ExprId, name: Sym, name_span: Span, args: &[ExprId]) -> Ty {
        let p = self.p;
        let k = p.known;
        let rt = self.expr(recv, None);
        let rt = self.deep(rt);
        let (derefs, base) = self.autoderef(rt);
        let bk = self.tys.kind(base);
        // User methods.
        if let TyKind::Adt(a) = bk
            && let Some(&f) = p.methods.get(&(a, name))
        {
            let info = p.fn_info(f);
            let Some(sk) = info.self_kind else {
                self.err(
                    "L0104",
                    name_span,
                    format!("`{}` is an associated function, not a method", self.name(name)),
                    "Call it as `Type::name(...)`.",
                );
                return ERROR;
            };
            let autoref = match sk {
                ast::SelfKind::Value => Autoref::None,
                ast::SelfKind::Ref => Autoref::Ref,
                ast::SelfKind::RefMut => Autoref::RefMut,
            };
            self.set_res(e, Res::Method { f, derefs, autoref });
            let params = info.params[1..].to_vec();
            self.check_args(&params, args, name_span);
            return info.ret;
        }
        // `clone` on a reference to a non-Clone type clones the reference.
        if name == k.clone {
            if !has_clone(p, &self.tys, base) && derefs > 0 {
                // Peel all but the last reference; the clone copies that reference.
                let mut cur = self.resolve(rt);
                for _ in 0..derefs - 1 {
                    if let TyKind::Ref(_, inner) = self.tys.kind(cur) {
                        cur = self.resolve(inner);
                    }
                }
                self.set_res(e, Res::BuiltinMethod { b: Builtin::Clone, derefs: derefs - 1, autoref: Autoref::Ref });
                self.check_args(&[], args, name_span);
                return cur;
            }
            if has_clone(p, &self.tys, base) {
                self.set_res(e, Res::BuiltinMethod { b: Builtin::Clone, derefs, autoref: Autoref::Ref });
                self.check_args(&[], args, name_span);
                return base;
            }
        }
        use Builtin as B;
        let found: Option<(B, Autoref, Vec<Ty>, Ty)> = match bk {
            TyKind::String => {
                if name == k.len {
                    Some((B::StringLen, Autoref::Ref, vec![], USIZE))
                } else if name == k.is_empty {
                    Some((B::StringIsEmpty, Autoref::Ref, vec![], BOOL))
                } else if name == k.push_str {
                    Some((B::StringPushStr, Autoref::RefMut, vec![REF_STR], UNIT))
                } else if name == k.push {
                    Some((B::StringPush, Autoref::RefMut, vec![CHAR], UNIT))
                } else if name == k.as_str {
                    Some((B::StringAsStr, Autoref::Ref, vec![], REF_STR))
                } else if name == k.to_string {
                    Some((B::ToString, Autoref::Ref, vec![], STRING))
                } else {
                    // String derefs to str, so it has every str method.
                    self.str_method(name)
                }
            }
            TyKind::Str => {
                if name == k.len {
                    Some((B::StrLen, Autoref::Ref, vec![], USIZE))
                } else if name == k.is_empty {
                    Some((B::StrIsEmpty, Autoref::Ref, vec![], BOOL))
                } else if name == k.to_string || name == k.to_owned {
                    Some((B::StrToString, Autoref::Ref, vec![], STRING))
                } else {
                    self.str_method(name)
                }
            }
            TyKind::Vec(elem) => {
                let opt_ref = {
                    let r = self.tys.intern(TyKind::Ref(false, elem));
                    self.tys.intern(TyKind::Option(r))
                };
                let opt = self.tys.intern(TyKind::Option(elem));
                if name == k.len {
                    Some((B::VecLen, Autoref::Ref, vec![], USIZE))
                } else if name == k.is_empty {
                    Some((B::VecIsEmpty, Autoref::Ref, vec![], BOOL))
                } else if name == k.push {
                    Some((B::VecPush, Autoref::RefMut, vec![elem], UNIT))
                } else if name == k.pop {
                    Some((B::VecPop, Autoref::RefMut, vec![], opt))
                } else if name == k.get {
                    Some((B::VecGet, Autoref::Ref, vec![USIZE], opt_ref))
                } else if name == k.first {
                    Some((B::VecFirst, Autoref::Ref, vec![], opt_ref))
                } else if name == k.last {
                    Some((B::VecLast, Autoref::Ref, vec![], opt_ref))
                } else if name == k.contains {
                    let r = self.tys.intern(TyKind::Ref(false, elem));
                    Some((B::VecContains, Autoref::Ref, vec![r], BOOL))
                } else if name == k.swap {
                    Some((B::VecSwap, Autoref::RefMut, vec![USIZE, USIZE], UNIT))
                } else if name == k.clear {
                    Some((B::VecClear, Autoref::RefMut, vec![], UNIT))
                } else if name == k.insert {
                    Some((B::VecInsert, Autoref::RefMut, vec![USIZE, elem], UNIT))
                } else if name == k.remove {
                    Some((B::VecRemove, Autoref::RefMut, vec![USIZE], elem))
                } else if name == k.truncate {
                    Some((B::VecTruncate, Autoref::RefMut, vec![USIZE], UNIT))
                } else {
                    None
                }
            }
            TyKind::Option(inner) => {
                if name == k.is_some {
                    Some((B::OptIsSome, Autoref::Ref, vec![], BOOL))
                } else if name == k.is_none {
                    Some((B::OptIsNone, Autoref::Ref, vec![], BOOL))
                } else if name == k.unwrap {
                    Some((B::OptUnwrap, Autoref::None, vec![], inner))
                } else if name == k.expect {
                    Some((B::OptExpect, Autoref::None, vec![REF_STR], inner))
                } else if name == k.unwrap_or {
                    Some((B::OptUnwrapOr, Autoref::None, vec![inner], inner))
                } else {
                    None
                }
            }
            TyKind::Chars => {
                let opt = self.tys.intern(TyKind::Option(CHAR));
                if name == k.next {
                    Some((B::CharsNext, Autoref::RefMut, vec![], opt))
                } else if name == k.count {
                    Some((B::CharsCount, Autoref::None, vec![], USIZE))
                } else {
                    None
                }
            }
            TyKind::Char if name != k.to_string => {
                let b = [
                    (k.is_ascii_digit, B::CharIsDigit),
                    (k.is_ascii_alphabetic, B::CharIsAlphabetic),
                    (k.is_ascii_alphanumeric, B::CharIsAlphanumeric),
                    (k.is_ascii_whitespace, B::CharIsWhitespace),
                    (k.is_ascii_uppercase, B::CharIsUppercase),
                    (k.is_ascii_lowercase, B::CharIsLowercase),
                ];
                if let Some(&(_, b)) = b.iter().find(|(n, _)| *n == name) {
                    Some((b, Autoref::Ref, vec![], BOOL))
                } else if name == k.to_ascii_uppercase {
                    Some((B::CharToUppercase, Autoref::Ref, vec![], CHAR))
                } else if name == k.to_ascii_lowercase {
                    Some((B::CharToLowercase, Autoref::Ref, vec![], CHAR))
                } else if name == k.to_digit {
                    let o = self.tys.intern(TyKind::Option(int(IntTy::U32)));
                    Some((B::CharToDigit, Autoref::None, vec![int(IntTy::U32)], o))
                } else {
                    None
                }
            }
            TyKind::Int(i) => {
                let t = base;
                if name == k.wrapping_add {
                    Some((B::WrappingAdd, Autoref::None, vec![t], t))
                } else if name == k.wrapping_sub {
                    Some((B::WrappingSub, Autoref::None, vec![t], t))
                } else if name == k.wrapping_mul {
                    Some((B::WrappingMul, Autoref::None, vec![t], t))
                } else if name == k.abs && i.signed() {
                    Some((B::Abs, Autoref::None, vec![], t))
                } else if name == k.pow {
                    Some((B::Pow, Autoref::None, vec![int(IntTy::U32)], t))
                } else if name == k.min {
                    Some((B::Min, Autoref::None, vec![t], t))
                } else if name == k.max {
                    Some((B::Max, Autoref::None, vec![t], t))
                } else if name == k.to_string {
                    Some((B::ToString, Autoref::Ref, vec![], STRING))
                } else {
                    None
                }
            }
            TyKind::Bool | TyKind::Char if name == k.to_string => Some((B::ToString, Autoref::Ref, vec![], STRING)),
            TyKind::Args if name == k.count => Some((B::ArgsCount, Autoref::None, vec![], USIZE)),
            // Trait methods work on an integer of unknown type; inherent ones (pow, abs) do not.
            TyKind::Var(_, true) if name == k.min => Some((B::Min, Autoref::None, vec![base], base)),
            TyKind::Var(_, true) if name == k.max => Some((B::Max, Autoref::None, vec![base], base)),
            TyKind::Var(_, true) if name == k.to_string => Some((B::ToString, Autoref::Ref, vec![], STRING)),
            TyKind::Var(_, true) => {
                self.err(
                    "L0111",
                    name_span,
                    format!("cannot call method `{}` on an integer whose type is not known yet", self.name(name)),
                    "Add a type suffix such as `5i64`, or a type annotation on the variable.",
                );
                return ERROR;
            }
            TyKind::Error => return ERROR,
            _ => None,
        };
        match found {
            Some((b, autoref, params, ret)) => {
                self.set_res(e, Res::BuiltinMethod { b, derefs, autoref });
                self.check_args(&params, args, name_span);
                ret
            }
            None => {
                for &a in args {
                    self.expr(a, None);
                }
                let tn = self.tn(base);
                self.err(
                    "L0104",
                    name_span,
                    format!("no method `{}` on type `{tn}`", self.name(name)),
                    "Check the method name. The prototype supports a small std subset (see README).",
                );
                ERROR
            }
        }
    }

    /// For `String == &str` style comparisons between different string types: the deref counts
    /// that reach each side's `String` or `str`. None if the types are not a valid mixed pair.
    fn mixed_string_eq(&self, a: Ty, b: Ty) -> Option<(u8, u8)> {
        let (ld, lb) = self.autoderef(a);
        let (rd, rb) = self.autoderef(b);
        let (lk, rk) = (self.tys.kind(lb), self.tys.kind(rb));
        if lk == rk || !matches!(lk, TyKind::String | TyKind::Str) || !matches!(rk, TyKind::String | TyKind::Str) {
            return None;
        }
        let lref = if lk == TyKind::Str { ld.checked_sub(1)? } else { ld };
        let rref = if rk == TyKind::Str { rd.checked_sub(1)? } else { rd };
        (lref == rref).then_some((ld, rd))
    }

    /// Methods shared by `str` and `String` (through Deref). The receiver is always `&self`.
    fn str_method(&mut self, name: Sym) -> Option<(Builtin, Autoref, Vec<Ty>, Ty)> {
        use Builtin as B;
        let k = self.p.known;
        let chars = self.tys.intern(TyKind::Chars);
        let table = [
            (k.contains, B::StrContains, vec![REF_STR], BOOL),
            (k.starts_with, B::StrStartsWith, vec![REF_STR], BOOL),
            (k.ends_with, B::StrEndsWith, vec![REF_STR], BOOL),
            (k.trim, B::StrTrim, vec![], REF_STR),
            (k.to_uppercase, B::StrToUppercase, vec![], STRING),
            (k.to_lowercase, B::StrToLowercase, vec![], STRING),
            (k.chars, B::StrChars, vec![], chars),
        ];
        table.into_iter().find(|(n, ..)| *n == name).map(|(_, b, params, ret)| (b, Autoref::Ref, params, ret))
    }

    fn binary(&mut self, e: ExprId, op: BinOp, lhs: ExprId, rhs: ExprId, span: Span) -> Ty {
        use BinOp::*;
        if matches!(op, And | Or) {
            self.expect_expr(lhs, BOOL);
            self.expect_expr(rhs, BOOL);
            return BOOL;
        }
        let lt = self.expr(lhs, None);
        let rt = self.expr(rhs, Some(lt));
        let (lk, rk) = (self.kind(lt), self.kind(rt));
        if lk == TyKind::Error || rk == TyKind::Error {
            return if op.is_cmp() { BOOL } else { ERROR };
        }
        let bad = |cx: &mut Self| {
            let (a, b) = (cx.tn(lt), cx.tn(rt));
            let fix = if op.is_cmp() && (a.starts_with('&') != b.starts_with('&')) {
                "Compare values of the same type: dereference the reference with `*`, or borrow the other side."
            } else {
                "Both operands must have the same type, and the type must support this operator."
            };
            cx.err("L0113", span, format!("cannot apply `{}` to `{a}` and `{b}`", op.symbol()), fix);
            if op.is_cmp() { BOOL } else { ERROR }
        };
        if op.is_cmp() {
            // String equality across String and &str.
            let (ld, lb) = self.autoderef(lt);
            let (rd, rb) = self.autoderef(rt);
            let (lbk, rbk) = (self.tys.kind(lb), self.tys.kind(rb));
            let stringy = |k: TyKind| matches!(k, TyKind::String | TyKind::Str);
            if stringy(lbk) && stringy(rbk) && matches!(op, Eq | Ne) {
                let lref = if lbk == TyKind::Str { ld - 1 } else { ld };
                let rref = if rbk == TyKind::Str { rd - 1 } else { rd };
                // Rust has String == &str, &str == String, String == str, and same-type comparisons.
                let ok = (lbk == rbk && ld == rd) || (lref == 0 && rref == 0) || (ld == rd && lbk != rbk && lref == rref);
                if !ok {
                    return bad(self);
                }
                self.set_res(e, Res::Bin { ld, rd });
                return BOOL;
            }
            if ld != rd || !self.unify(lb, rb) {
                return bad(self);
            }
            let lb = self.deep(lb);
            let ok = match self.tys.kind(lb) {
                TyKind::Int(_) | TyKind::Var(_, true) | TyKind::Bool | TyKind::Char => true,
                TyKind::String | TyKind::Str => true,
                _ if matches!(op, Eq | Ne) => has_eq(self.p, &self.tys, lb),
                _ => false,
            };
            if !ok {
                let tn = self.tn(lb);
                let fix = if matches!(op, Eq | Ne) {
                    "Add #[derive(PartialEq)] to the type."
                } else {
                    "Ordering is only supported for integers, bool, char, and strings."
                };
                self.err("L0112", span, format!("type `{tn}` cannot be compared with `{}`", op.symbol()), fix);
            }
            self.set_res(e, Res::Bin { ld, rd });
            return BOOL;
        }
        // String + &str.
        if op == Add && lk == TyKind::String {
            self.coerce_expr(rhs, rt, REF_STR);
            self.set_res(e, Res::Bin { ld: 0, rd: 0 });
            return STRING;
        }
        let (ld, li) = self.peel_one_ref(lt);
        let (rd, ri) = self.peel_one_ref(rt);
        let (lik, rik) = (self.kind(li), self.kind(ri));
        let int_like = |k: TyKind| matches!(k, TyKind::Int(_) | TyKind::Var(_, true));
        let result = match op {
            Shl | Shr if int_like(lik) && int_like(rik) => li,
            BitAnd | BitOr | BitXor if lik == TyKind::Bool && rik == TyKind::Bool => BOOL,
            Add | Sub | Mul | Div | Rem | BitAnd | BitOr | BitXor if int_like(lik) && int_like(rik) => {
                if !self.unify(li, ri) {
                    return bad(self);
                }
                li
            }
            _ => return bad(self),
        };
        self.set_res(e, Res::Bin { ld, rd });
        result
    }

    fn struct_lit(&mut self, e: ExprId, path: &[ast::PathSeg], fields: &[(Sym, Span, ExprId)], span: Span) -> Ty {
        let p = self.p;
        let target = if path.len() == 1 {
            let n = path[0].name;
            let a = if n == p.known.self_type { self.f.owner } else { p.type_names.get(&n).copied() };
            a.filter(|&a| !p.adt(a).is_enum).map(|a| (a, 0u32))
        } else {
            match self.resolve_assoc(path, span) {
                Some(Res::Variant(a, v)) => Some((a, v)),
                _ => return ERROR,
            }
        };
        let Some((a, v)) = target else {
            for &(_, _, fe) in fields {
                self.expr(fe, None);
            }
            self.err("L0102", span, "unknown struct", "Check the struct name.");
            return ERROR;
        };
        self.set_res(e, Res::Variant(a, v));
        let variant = &p.adt(a).variants[v as usize];
        if variant.shape != VariantShape::Named && !(variant.fields.is_empty() && fields.is_empty()) {
            self.err("L0110", span, "this is not a struct with named fields", "Use the tuple or unit form.");
            return ERROR;
        }
        let mut seen = vec![false; variant.fields.len()];
        for &(fname, fspan, fe) in fields {
            match variant.fields.iter().position(|f| f.name == fname) {
                Some(i) => {
                    if seen[i] {
                        self.err("L0106", fspan, format!("field `{}` is set twice", self.name(fname)), "Remove one of them.");
                    }
                    seen[i] = true;
                    self.expect_expr(fe, variant.fields[i].ty);
                }
                None => {
                    self.expr(fe, None);
                    self.err("L0103", fspan, format!("no field `{}` on this struct", self.name(fname)), "Check the field name.");
                }
            }
        }
        let missing: Vec<String> =
            variant.fields.iter().zip(&seen).filter(|(_, s)| !**s).map(|(f, _)| self.name(f.name).to_string()).collect();
        if !missing.is_empty() {
            self.err(
                "L0107",
                span,
                format!("missing fields: {}", missing.join(", ")),
                "Set every field. Struct update syntax is not supported yet.",
            );
        }
        self.tys.intern(TyKind::Adt(a))
    }

    fn for_iter(&mut self, iter: ExprId) -> Ty {
        let p = self.p;
        if let Expr::Range { lo, hi, .. } = p.ast.expr(iter) {
            let (Some(lo), Some(hi)) = (*lo, *hi) else {
                let s = self.span(iter);
                self.errs.push(unsupported(s, "open ranges"));
                return ERROR;
            };
            let lt = self.expr(lo, None);
            let ht = self.expr(hi, Some(lt));
            let ok = matches!(self.kind(lt), TyKind::Int(_) | TyKind::Var(_, true)) && self.unify(lt, ht);
            if !ok {
                let s = self.span(iter);
                let (a, b) = (self.tn(lt), self.tn(ht));
                self.err(
                    "L0110",
                    s,
                    format!("range bounds must be the same integer type, found `{a}` and `{b}`"),
                    "Use integers of one type.",
                );
            }
            self.set(iter, ERROR);
            return lt;
        }
        let t = self.expr(iter, None);
        match self.kind(t) {
            TyKind::Chars => CHAR,
            TyKind::Ref(m, inner) => match self.kind(inner) {
                TyKind::Vec(elem) => self.tys.intern(TyKind::Ref(m, elem)),
                _ => {
                    let s = self.span(iter);
                    let tn = self.tn(t);
                    self.err("L0113", s, format!("cannot iterate over `{tn}`"), "Iterate over a range, `&vec`, or `&mut vec`.");
                    ERROR
                }
            },
            TyKind::Vec(_) => {
                let s = self.span(iter);
                self.errs.push(unsupported(s, "iterating a Vec by value"));
                ERROR
            }
            TyKind::Error => ERROR,
            _ => {
                let s = self.span(iter);
                let tn = self.tn(t);
                self.err("L0113", s, format!("cannot iterate over `{tn}`"), "Iterate over a range, `&vec`, or `&mut vec`.");
                ERROR
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn macro_expr(
        &mut self,
        e: ExprId,
        kind: MacroKind,
        args: &[ExprId],
        fmt: &[FmtPiece],
        repeat: bool,
        span: Span,
        expected: Option<Ty>,
    ) -> Ty {
        let fixed = match kind {
            MacroKind::Assert => 1,
            MacroKind::AssertEq | MacroKind::AssertNe => 2,
            MacroKind::Vec => args.len(),
            _ => 0,
        };
        let result = match kind {
            MacroKind::Vec => {
                let elem_expected = expected.and_then(|t| match self.kind(t) {
                    TyKind::Vec(e) => Some(e),
                    _ => None,
                });
                let elem = elem_expected.unwrap_or_else(|| self.new_var(false));
                if repeat {
                    self.expect_expr(args[0], elem);
                    self.expect_expr(args[1], USIZE);
                    let elem = self.deep(elem);
                    if !has_clone(self.p, &self.tys, elem) && !matches!(self.kind(elem), TyKind::Var(..)) {
                        let tn = self.tn(elem);
                        self.err(
                            "L0112",
                            span,
                            format!("`vec![x; n]` needs Clone, but `{tn}` is not Clone"),
                            "Derive Clone on the element type.",
                        );
                    }
                } else {
                    for &a in args {
                        self.expect_expr(a, elem);
                    }
                }
                return self.tys.intern(TyKind::Vec(elem));
            }
            MacroKind::Assert => {
                if let Some(&c) = args.first() {
                    self.expect_expr(c, BOOL);
                }
                UNIT
            }
            MacroKind::AssertEq | MacroKind::AssertNe => {
                if args.len() >= 2 {
                    let a = self.expr(args[0], None);
                    let b = self.expr(args[1], Some(a));
                    let s = self.span(args[1]);
                    if let Some((ld, rd)) = self.mixed_string_eq(a, b) {
                        // String against &str: compared as strings, as Rust's PartialEq impls do.
                        self.set_res(e, Res::Bin { ld, rd });
                    } else if self.unify(a, b) {
                        let a = self.deep(a);
                        if !has_eq(self.p, &self.tys, a) || !has_debug(self.p, &self.tys, a) {
                            let tn = self.tn(a);
                            self.err(
                                "L0112",
                                span,
                                format!("assert_eq! needs PartialEq and Debug, but `{tn}` lacks one"),
                                "Derive PartialEq and Debug on the type.",
                            );
                        }
                    } else {
                        self.mismatch(s, a, b);
                    }
                }
                UNIT
            }
            MacroKind::Println | MacroKind::Print | MacroKind::Eprintln | MacroKind::Eprint => UNIT,
            MacroKind::Format => STRING,
            MacroKind::Panic | MacroKind::Todo | MacroKind::Unreachable => NEVER,
        };
        for piece in fmt {
            if let FmtPiece::Arg { index, debug } = piece {
                let a = args[*index];
                let t = self.expr(a, None);
                let t = self.deep(t);
                let ok = if *debug {
                    has_debug(self.p, &self.tys, t)
                } else {
                    has_display(&self.tys, t) || matches!(self.kind(t), TyKind::Var(_, true))
                };
                if !ok {
                    let tn = self.tn(t);
                    let (what, fix) = if *debug {
                        ("Debug", "Add #[derive(Debug)] to the type.")
                    } else {
                        ("Display", "Use `{:?}` with #[derive(Debug)], or format the fields yourself.")
                    };
                    let s = self.span(a);
                    self.err("L0112", s, format!("`{tn}` does not implement {what}"), fix);
                }
            }
        }
        // Arguments not referenced by the format string (only possible in assert macros).
        for (i, &a) in args.iter().enumerate() {
            if i >= fixed && !fmt.iter().any(|p| matches!(p, FmtPiece::Arg { index, .. } if *index == i)) {
                self.expr(a, None);
            }
        }
        result
    }

    // ---------- Patterns ----------

    /// Checks a pattern against a value of type `t`. Applies default binding modes.
    fn pattern(&mut self, pat: PatId, t: Ty, in_match: bool) {
        self.pattern_mode(pat, t, BindMode::Move, in_match);
    }

    fn pattern_mode(&mut self, pat: PatId, t: Ty, mode: BindMode, in_match: bool) {
        let p = self.p;
        let pi = (pat.0 - self.out.pat_base) as usize;
        let span = p.ast.pat_span(pat);
        // Default binding modes: a non-binding pattern auto-derefs a reference scrutinee.
        let mut t = self.resolve(t);
        let mut mode = mode;
        let opt = self.option_pattern(pat);
        let structural = opt.is_some()
            || matches!(p.ast.pat(pat), Pat::TupleStruct { .. } | Pat::Struct { .. } | Pat::Path(_) | Pat::Lit(_) | Pat::Range { .. });
        if structural {
            let mut derefs = 0;
            while let TyKind::Ref(m, inner) = self.tys.kind(t) {
                // A string literal pattern matches `&str` directly.
                if matches!(p.ast.pat(pat), Pat::Lit(l) if matches!(p.ast.expr(*l), Expr::Str(_))) && self.kind(inner) == TyKind::Str {
                    break;
                }
                derefs += 1;
                mode = match mode {
                    BindMode::Ref(false) => BindMode::Ref(false),
                    _ => BindMode::Ref(m),
                };
                t = self.resolve(inner);
            }
            self.out.pat_derefs[pi] = derefs;
        }
        self.out.pat_ty[pi] = t;
        if let Some(is_some) = opt {
            let inner = self.new_var(false);
            let ot = self.tys.intern(TyKind::Option(inner));
            if !self.unify(ot, t) {
                self.mismatch(span, t, ot);
                return;
            }
            self.out.pat_res[pi] = PatRes::Opt(is_some);
            if let (true, Pat::TupleStruct { elems, .. }) = (is_some, p.ast.pat(pat)) {
                self.pattern_mode(elems[0], inner, mode, in_match);
            }
            return;
        }
        match p.ast.pat(pat) {
            Pat::Wild => {}
            Pat::Binding { name, mutable, by_ref } => {
                let mode = if *by_ref { BindMode::Ref(*mutable) } else { mode };
                let lty = match mode {
                    BindMode::Move => t,
                    BindMode::Ref(m) => self.tys.intern(TyKind::Ref(m, t)),
                };
                let mutable_local = *mutable && !*by_ref;
                if mutable_local && mode != BindMode::Move {
                    self.err(
                        "L0122",
                        span,
                        "`mut` binding under a reference is not allowed here",
                        "Remove `mut`, or match on the value instead of a reference.",
                    );
                }
                let l = self.add_local(*name, lty, mutable_local, span);
                self.out.pat_res[pi] = PatRes::Binding { local: l, mode };
            }
            Pat::Lit(l) => {
                let lt = self.expr(*l, Some(t));
                if !self.unify(lt, t) {
                    self.mismatch(span, t, lt);
                }
                if !in_match {
                    self.errs.push(unsupported(span, "refutable patterns here"));
                }
            }
            Pat::Range { lo, hi } => {
                let a = self.expr(*lo, Some(t));
                let b = self.expr(*hi, Some(t));
                if !self.unify(a, t) || !self.unify(b, t) || !matches!(self.kind(t), TyKind::Int(_) | TyKind::Char | TyKind::Var(_, true)) {
                    self.err(
                        "L0110",
                        span,
                        "range patterns need integer or char bounds of the matched type",
                        "Use bounds of the scrutinee's type.",
                    );
                }
            }
            Pat::Path(segs) | Pat::TupleStruct { path: segs, .. } | Pat::Struct { path: segs, .. } => {
                let target = if segs.len() == 1 {
                    let n = segs[0].name;
                    let a = if n == p.known.self_type { self.f.owner } else { p.type_names.get(&n).copied() };
                    a.filter(|&a| !p.adt(a).is_enum).map(|a| (a, 0))
                } else {
                    match self.resolve_assoc(segs, span) {
                        Some(Res::Variant(a, v)) => Some((a, v)),
                        Some(_) => {
                            self.err("L0110", span, "expected a variant or struct in this pattern", "Use `Type::Variant`.");
                            None
                        }
                        None => return,
                    }
                };
                let Some((a, v)) = target else {
                    self.err("L0102", span, "unknown struct or variant in pattern", "Check the name.");
                    return;
                };
                let adt_ty = self.tys.intern(TyKind::Adt(a));
                if !self.unify(adt_ty, t) {
                    self.mismatch(span, t, adt_ty);
                    return;
                }
                self.out.pat_res[pi] = PatRes::Variant(a, v);
                let variant = &p.adt(a).variants[v as usize];
                match p.ast.pat(pat) {
                    Pat::Path(_) => {
                        if variant.shape != VariantShape::Unit {
                            self.err("L0110", span, "this variant has fields", "Match its fields with `(..)` or `{ .. }`.");
                        }
                    }
                    Pat::TupleStruct { elems, .. } => {
                        if variant.shape != VariantShape::Tuple || variant.fields.len() != elems.len() {
                            self.err(
                                "L0110",
                                span,
                                format!("this variant has {} field(s)", variant.fields.len()),
                                "Match every field, or use `_` for the ones you do not need.",
                            );
                            return;
                        }
                        for (i, &sub) in elems.iter().enumerate() {
                            let ft = variant.fields[i].ty;
                            self.pattern_mode(sub, ft, mode, in_match);
                        }
                    }
                    Pat::Struct { fields, rest, .. } => {
                        if variant.shape != VariantShape::Named {
                            self.err("L0110", span, "this variant does not have named fields", "Use the tuple form.");
                            return;
                        }
                        for &(fname, sub) in fields {
                            match variant.fields.iter().position(|f| f.name == fname) {
                                Some(i) => {
                                    let ft = variant.fields[i].ty;
                                    self.pattern_mode(sub, ft, mode, in_match);
                                }
                                None => {
                                    let s = p.ast.pat_span(sub);
                                    self.err(
                                        "L0103",
                                        s,
                                        format!("no field `{}` in this variant", self.name(fname)),
                                        "Check the field name.",
                                    );
                                }
                            }
                        }
                        if !rest && fields.len() < variant.fields.len() {
                            self.err(
                                "L0107",
                                span,
                                "pattern does not mention all fields",
                                "Add the missing fields, or end the pattern with `..`.",
                            );
                        }
                    }
                    _ => unreachable!(),
                }
            }
            Pat::Or(alts) => {
                // Each alternative must bind the same names; the prototype only allows no bindings.
                for &alt in alts {
                    let before = self.out.locals.len();
                    self.pattern_mode(alt, t, mode, in_match);
                    if self.out.locals.len() != before {
                        let s = p.ast.pat_span(alt);
                        self.errs.push(unsupported(s, "bindings inside `|` patterns"));
                    }
                }
            }
        }
    }

    /// `Some(p)` is Some(true), `None` is Some(false), anything else is None.
    fn option_pattern(&self, pat: PatId) -> Option<bool> {
        let k = self.p.known;
        match self.p.ast.pat(pat) {
            Pat::Binding { name, mutable: false, by_ref: false } if *name == k.None => Some(false),
            Pat::TupleStruct { path, elems } if path.len() == 1 && path[0].name == k.Some && elems.len() == 1 => Some(true),
            _ => None,
        }
    }

    /// Exhaustiveness for `match`. Recurses into nested enum and Option patterns. Conservative:
    /// in rare multi-field cases it can reject a match that Rust accepts (lust is a subset).
    fn exhaustive(&mut self, scrut_ty: Ty, arms: &[ast::Arm], span: Span) {
        let p = self.p;
        let pats: Vec<PatId> = arms.iter().filter(|a| a.guard.is_none()).map(|a| a.pat).collect();
        if self.covers(&pats) {
            return;
        }
        let (_, base) = self.autoderef(scrut_ty);
        let msg = match self.kind(base) {
            TyKind::Adt(a) if p.adt(a).is_enum => {
                let mut flat = Vec::new();
                pats.iter().for_each(|&x| self.flatten_or(x, &mut flat));
                let missing: Vec<String> = (0..p.adt(a).variants.len())
                    .filter(|&v| !flat.iter().any(|&x| matches!(self.pres(x), PatRes::Variant(_, w) if w as usize == v)))
                    .map(|v| format!("{}::{}", self.name(p.adt(a).name), self.name(p.adt(a).variants[v].name)))
                    .collect();
                if missing.is_empty() {
                    "non-exhaustive match: some nested cases are missing".to_string()
                } else {
                    format!("non-exhaustive match: missing {}", missing.join(", "))
                }
            }
            TyKind::Error => return,
            _ => "non-exhaustive match".to_string(),
        };
        self.err("L0115", span, msg, "Add arms for the missing cases, or add a `_ => ...` arm.");
    }

    fn pres(&self, pat: PatId) -> PatRes {
        self.out.pat_res[(pat.0 - self.out.pat_base) as usize]
    }

    fn flatten_or(&self, pat: PatId, out: &mut Vec<PatId>) {
        match self.p.ast.pat(pat) {
            Pat::Or(alts) => alts.iter().for_each(|&a| self.flatten_or(a, out)),
            _ => out.push(pat),
        }
    }

    /// True if `pats`, all matching values of one type, together match every value.
    fn covers(&self, pats: &[PatId]) -> bool {
        let p = self.p;
        let mut flat = Vec::new();
        pats.iter().for_each(|&x| self.flatten_or(x, &mut flat));
        if flat.iter().any(|&x| self.irrefutable(x)) {
            return true;
        }
        for &x in &flat {
            match (self.pres(x), p.ast.pat(x)) {
                (PatRes::Opt(_), _) => {
                    let none = flat.iter().any(|&y| matches!(self.pres(y), PatRes::Opt(false)));
                    let somes: Vec<PatId> = flat
                        .iter()
                        .filter_map(|&y| match (self.pres(y), p.ast.pat(y)) {
                            (PatRes::Opt(true), Pat::TupleStruct { elems, .. }) => Some(elems[0]),
                            _ => None,
                        })
                        .collect();
                    return none && !somes.is_empty() && self.covers(&somes);
                }
                (PatRes::Variant(a, _), _) if p.adt(a).is_enum => {
                    return (0..p.adt(a).variants.len()).all(|v| self.covers_variant(&flat, a, v as u32));
                }
                (_, Pat::Lit(_)) if matches!(self.kind(self.out.pat_ty[(x.0 - self.out.pat_base) as usize]), TyKind::Bool) => {
                    let (mut t, mut f) = (false, false);
                    for &y in &flat {
                        self.cover_bools(y, &mut t, &mut f);
                    }
                    return t && f;
                }
                _ => {}
            }
        }
        false
    }

    /// Does some combination of rows for variant `v` cover all of its values?
    fn covers_variant(&self, flat: &[PatId], a: AdtId, v: u32) -> bool {
        let p = self.p;
        let nf = p.adt(a).variants[v as usize].fields.len();
        // One row per pattern for this variant; `None` is a field the pattern skips with `..`.
        let rows: Vec<Vec<Option<PatId>>> = flat
            .iter()
            .filter(|&&y| matches!(self.pres(y), PatRes::Variant(b, w) if b == a && w == v))
            .map(|&y| {
                let mut row = vec![None; nf];
                match p.ast.pat(y) {
                    Pat::TupleStruct { elems, .. } => elems.iter().enumerate().for_each(|(i, &e)| row[i] = Some(e)),
                    Pat::Struct { fields, .. } => {
                        for &(fname, sub) in fields {
                            if let Some(i) = p.adt(a).variants[v as usize].fields.iter().position(|f| f.name == fname) {
                                row[i] = Some(sub);
                            }
                        }
                    }
                    _ => {}
                }
                row
            })
            .collect();
        if rows.is_empty() {
            return false;
        }
        let free = |c: &Option<PatId>| c.is_none_or(|x| self.irrefutable(x));
        if rows.iter().any(|r| r.iter().all(free)) {
            return true;
        }
        // One refutable column, with every other column free in all rows: recurse on that column.
        (0..nf).any(|j| {
            rows.iter().all(|r| r.iter().enumerate().all(|(i, c)| i == j || free(c)))
                && self.covers(&rows.iter().filter_map(|r| r[j]).collect::<Vec<_>>())
                && rows.iter().all(|r| r[j].is_some())
        })
    }

    fn irrefutable(&self, pat: PatId) -> bool {
        let p = self.p;
        if matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Opt(_)) {
            return false;
        }
        match p.ast.pat(pat) {
            Pat::Wild | Pat::Binding { .. } => true,
            Pat::Or(alts) => alts.iter().any(|&a| self.irrefutable(a)),
            Pat::Struct { fields, .. } => {
                matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Variant(a, _) if !p.adt(a).is_enum)
                    && fields.iter().all(|&(_, s)| self.irrefutable(s))
            }
            Pat::TupleStruct { elems, .. } => {
                matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Variant(a, _) if !p.adt(a).is_enum)
                    && elems.iter().all(|&s| self.irrefutable(s))
            }
            Pat::Path(_) => matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Variant(a, _) if !p.adt(a).is_enum),
            _ => false,
        }
    }

    fn cover_bools(&self, pat: PatId, t: &mut bool, f: &mut bool) {
        match self.p.ast.pat(pat) {
            Pat::Or(alts) => {
                for &a in alts {
                    self.cover_bools(a, t, f);
                }
            }
            Pat::Lit(l) => match self.p.ast.expr(*l) {
                Expr::Bool(true) => *t = true,
                Expr::Bool(false) => *f = true,
                _ => {}
            },
            _ => {}
        }
    }

    // ---------- Finish ----------

    /// Resolves every recorded type, defaults integer variables, and checks literal ranges.
    fn finish(&mut self) {
        for i in 0..self.out.expr_ty.len() {
            let t = self.out.expr_ty[i];
            self.out.expr_ty[i] = self.zonk(t);
        }
        for i in 0..self.out.pat_ty.len() {
            let t = self.out.pat_ty[i];
            self.out.pat_ty[i] = self.zonk(t);
        }
        for i in 0..self.out.locals.len() {
            let t = self.out.locals[i].ty;
            let z = self.zonk(t);
            if z == ERROR && !self.has_error_kind(t) {
                let span = self.out.locals[i].span;
                let name = self.name(self.out.locals[i].name).to_string();
                self.err(
                    "L0111",
                    span,
                    format!("cannot infer the type of `{name}`"),
                    "Add a type annotation, such as `let v: Vec<i64> = Vec::new();`.",
                );
            }
            self.out.locals[i].ty = z;
        }
        // Literal range checks.
        let base = self.out.expr_base;
        for i in 0..self.out.expr_ty.len() {
            let e = ExprId(base + i as u32);
            if let Expr::Int(v, _) = self.p.ast.expr(e)
                && let TyKind::Int(it) = self.tys.kind(self.out.expr_ty[i])
            {
                let neg = self.negated_lits.contains(&e);
                let max = if neg && it.signed() { it.max() + 1 } else { it.max() };
                if *v > max {
                    let s = self.span(e);
                    self.err(
                        "L0118",
                        s,
                        format!("literal out of range for `{}`", it.name()),
                        format!("Use a value that fits in `{}`, or a wider type.", it.name()),
                    );
                }
            }
        }
    }

    fn has_error_kind(&self, t: Ty) -> bool {
        match self.kind(t) {
            TyKind::Error => true,
            TyKind::Vec(e) | TyKind::Option(e) | TyKind::Ref(_, e) => self.has_error_kind(e),
            _ => false,
        }
    }
}
