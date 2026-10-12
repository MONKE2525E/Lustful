// Type checking for one function body. Inference is local to the body: unification plus
// integer-literal variables. Output is a set of side tables that lowering reads.
// Signature collection runs before body checking, in `collect`.
pub mod collect;
pub mod obligations;

use crate::ast::{self, BinOp, Expr, ExprId, FmtPiece, MacroKind, Pat, PatId, Stmt, UnOp};
use crate::check::collect::*;
use crate::diag::{CtxtId, Diag, Span, not_yet, unsupported};
use crate::driver::graph::{BindingRes, Head, Namespace, Reads, ReceiverForm, SigOf};
use crate::intern::Sym;
use crate::ty::defs::DefKind as DefsKind;
use crate::ty::lang;
use crate::ty::*;

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
    SliceLen,
    SliceIsEmpty,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Res {
    None,
    Local(u32),
    Fn(LocalDefId),
    /// A unit variant value, a tuple-variant constructor, or a struct literal target.
    Variant(AdtId, u32),
    Builtin(Builtin),
    /// `None`, and `Some` used as a constructor.
    OptNone,
    OptSome,
    Method {
        f: LocalDefId,
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
    /// Operand deref counts for binary operators, compound assignment, and unary operators (`ld` only).
    Bin {
        ld: u8,
        rd: u8,
    },
    Index {
        derefs: u8,
    },
    /// A `core::intrinsics::<name>` call that passed the privilege check.
    /// The payload is the intrinsic's registry id (`ty::lang::INTRINSICS`).
    /// Only spliced shipped-library source can produce this resolution.
    Intrinsic(u32),
    /// A range index `base[lo..hi]` producing a slice place (W-CORELANG).
    SliceIndex {
        derefs: u8,
    },
    /// A static item read, by index into `Program::statics` (W-CORELANG).
    Static(u32),
    /// A compile-time usize constant: `size_of`, `align_of`, `offset_of!`.
    ConstUsize(u64),
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
    /// `&[T; N]` to a slice reference; the bool is the target mutability.
    SliceFromArray(bool),
    /// `&Vec<T>` to a slice reference; the bool is the target mutability.
    SliceFromVec(bool),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindMode {
    Move,
    Ref(bool),
}

#[derive(Clone, Copy, Debug)]
pub enum PatRes {
    None,
    /// A const item used as a pattern, by index into `Program::consts`.
    ConstItem(u32),
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
    /// The const value of an expression the checker evaluated (a const item
    /// reference or an inline const block), parallel to `expr_ty`.
    pub const_exprs: Vec<Option<crate::ty::consteval::ConstValue>>,
    pub expr_res: Vec<Res>,
    pub coerce: Vec<Coerce>,
    pub pat_ty: Vec<Ty>,
    pub pat_res: Vec<PatRes>,
    /// Number of implicit derefs before matching each pattern (default binding modes).
    pub pat_derefs: Vec<u8>,
    pub locals: Vec<LocalInfo>,
    /// Locals bound to the function parameters, in order (including `self`).
    pub param_locals: Vec<u32>,
    /// Every cross-item node this body read through a query function
    /// (docs/ARCH.md section 8.2). Stored with the result; nothing consumes
    /// it for invalidation yet (S7 is record-only).
    pub reads: Reads,
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
    pub fn const_value(&self, e: ExprId) -> Option<&crate::ty::consteval::ConstValue> {
        self.const_exprs[(e.0 - self.expr_base) as usize].as_ref()
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
    /// True when `break` may carry a value (a `loop` or a labeled block).
    is_loop: bool,
    /// True for a labeled block, which `continue` cannot target.
    is_block: bool,
    /// The label and its binding span; hygiene reads the span's context.
    label: Option<(Sym, Span)>,
}

struct Ctx<'p, 'a> {
    p: &'p Program<'a>,
    f: &'p FnInfo<'a>,
    /// The module this fn is defined in (root without the resolver),
    /// for field visibility checks (ARCH 1.5).
    module: crate::ty::defs::ModuleId,
    tys: Tys<'p>,
    vars: Vec<Var>,
    out: Checked<'p>,
    /// Locals by (name, hygiene context): a local a macro introduces does
    /// not bind a caller ident of the same name, and an ident the caller
    /// passes in keeps the caller's context (ARCH 6.3).
    scopes: Vec<((Sym, CtxtId), u32)>,
    loops: Vec<LoopCtx>,
    errs: Vec<Diag>,
    negated_lits: Vec<ExprId>,
    self_ty: Option<Ty>,
    /// The trait obligation queue (ARCH 2.4). Empty until W-TRAITS-CORE fills it;
    /// the hook calls at its fixed run points are already in place below.
    obl: obligations::Obligations,
}

/// Type-checks one function body.
pub fn check_fn<'p, 'a>(p: &'p Program<'a>, fid: LocalDefId) -> (Checked<'p>, Vec<Diag>) {
    let f = p.fn_info(fid);
    let def = f.def;
    let n_exprs = (def.exprs.1 - def.exprs.0) as usize;
    let n_pats = (def.pats.1 - def.pats.0) as usize;
    let mut cx = Ctx {
        p,
        f,
        module: p.resolved.as_ref().and_then(|t| t.fn_module.get(fid.0 as usize).copied()).unwrap_or(crate::ty::defs::ROOT_MODULE),
        tys: Tys::new(&p.tys),
        vars: Vec::new(),
        out: Checked {
            tys: Tys::new(&p.tys),
            expr_base: def.exprs.0,
            pat_base: def.pats.0,
            expr_ty: vec![ERROR; n_exprs],
            const_exprs: vec![None; n_exprs],
            expr_res: vec![Res::None; n_exprs],
            coerce: vec![Coerce::None; n_exprs],
            pat_ty: vec![ERROR; n_pats],
            pat_res: vec![PatRes::None; n_pats],
            pat_derefs: vec![0; n_pats],
            locals: Vec::new(),
            param_locals: Vec::new(),
            reads: Reads::new(),
        },
        scopes: Vec::new(),
        loops: Vec::new(),
        errs: Vec::new(),
        negated_lits: Vec::new(),
        self_ty: f.owner.map(|a| p.tys.get_adt_ty(a).expect("ADT types are interned during collection")),
        obl: obligations::Obligations::new(),
    };
    let mut pi = 0;
    if let Some(sp) = &def.self_param {
        let l = cx.add_local(p.known.self_value, f.params[0], sp.mutable, sp.span);
        cx.out.param_locals.push(l);
        pi = 1;
    }
    let mut seen_params: Vec<Sym> = Vec::new();
    for param in &def.params {
        if seen_params.contains(&param.name) {
            let name = p.name(param.name).to_string();
            cx.err("L0106", param.span, format!("`{name}` is defined more than once"), "Rename one of the parameters.");
        }
        seen_params.push(param.name);
        let l = cx.add_local(param.name, f.params[pi], param.mutable, param.span);
        cx.out.param_locals.push(l);
        pi += 1;
    }
    // A declaration without a body (trait or foreign fn shape) has nothing
    // to check; the parser does not build those today.
    if let Some(body) = def.body {
        let body_ty = cx.block(body, Some(f.ret));
        let body_span = p.ast.block(body).span;
        if let Some(tail) = p.ast.block(body).tail {
            cx.coerce_expr(tail, body_ty, f.ret);
        } else {
            cx.coerce_at(body_ty, f.ret, body_span, None);
        }
    }
    cx.finish();
    let Ctx { out, tys, errs, .. } = cx;
    let mut out = out;
    out.tys = tys;
    (out, errs)
}

/// True if Rust can compare two string-like operands for equality. `ld` and `rd` are the
/// reference depths of the two sides and `lk` and `rk` their base kinds (`String` or `Str`).
/// The model: peel the common reference layers (the blanket `&A == &B` impl), then require
/// one of the base impls: String==String, String==str, String==&str, str==String,
/// str==str, or &str==String.
/// The name and binding span of an optional AST label.
fn label_of(label: &Option<ast::Label>) -> Option<(Sym, Span)> {
    label.map(|l| (l.name, l.span))
}

/// Maps written tuple pattern elements to field indexes. At most one `..`
/// may appear; elements after it count from the end. None on an arity
/// mismatch or a second `..`. Lowering uses the same mapping.
pub fn map_tuple_elems(ast: &crate::ast::Ast, elems: &[PatId], nfields: usize) -> Option<Vec<(usize, PatId)>> {
    let rest = elems.iter().position(|&s| matches!(ast.pat(s), Pat::Rest));
    match rest {
        None => {
            if elems.len() != nfields {
                return None;
            }
            Some(elems.iter().enumerate().map(|(i, &s)| (i, s)).collect())
        }
        Some(r) => {
            if elems[r + 1..].iter().any(|&s| matches!(ast.pat(s), Pat::Rest)) {
                return None;
            }
            let suffix = elems.len() - r - 1;
            if r + suffix > nfields {
                return None;
            }
            let mut out: Vec<(usize, PatId)> = elems[..r].iter().enumerate().map(|(i, &s)| (i, s)).collect();
            for (j, &s) in elems[r + 1..].iter().enumerate() {
                out.push((nfields - suffix + j, s));
            }
            Some(out)
        }
    }
}

fn string_eq_ok(ld: u8, lk_is_string: bool, rd: u8, rk_is_string: bool) -> bool {
    let peel = ld.min(rd);
    let (la, ra) = ((ld - peel, lk_is_string), (rd - peel, rk_is_string));
    let string = (0, true);
    let str_ = (0, false);
    let ref_str = (1, false);
    matches!(
        (la, ra),
        (a, b) if (a == string && (b == string || b == str_ || b == ref_str))
            || (a == str_ && (b == string || b == str_))
            || (a == ref_str && b == string)
    )
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
        let t = self.resolve(t);
        match self.tys.kind(t) {
            TyKind::Ref(_, m, e) => format!("&{}{}", if m.is_mut() { "mut " } else { "" }, self.tn(e)),
            _ => match self.tys.builtin_of(t) {
                Some(BuiltinTy::Vec) => format!("Vec<{}>", self.tn(self.tys.adt_first_ty_arg(t).unwrap_or(ERROR))),
                Some(BuiltinTy::Option) => format!("Option<{}>", self.tn(self.tys.adt_first_ty_arg(t).unwrap_or(ERROR))),
                _ => ty_name(self.p, &self.tys, t),
            },
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
        // `span` must be the binding name's own span: its context is the
        // hygiene key. Callers pass the pattern or parameter name span.
        self.scopes.push(((name, span.ctxt), l));
        l
    }
    fn lookup(&self, name: Sym, ctxt: CtxtId) -> Option<u32> {
        // The newest visible binding of this name: same context, or one a
        // body-local macro could already see at its definition (ARCH 6.3).
        self.scopes
            .iter()
            .rev()
            .find(|((n, _), l)| *n == name && crate::diag::ctxt_can_see_local(ctxt, self.out.locals[*l as usize].span))
            .map(|&(_, l)| l)
    }

    // Cross-item reads go through the section 8.2 query functions on
    // `Program`, which record into this body's read set. Bodies ask in
    // their own module (the root in single-file programs).
    fn binding(&mut self, ns: Namespace, name: Sym) -> BindingRes {
        let p = self.p;
        let module = self.module;
        p.binding(&mut self.out.reads, module, ns, name)
    }

    /// Field visibility (ARCH 1.5): a private field of a struct from
    /// another module is L0510. Only resolver-built programs carry the
    /// field table; single-file programs are all one module.
    fn check_field_vis(&mut self, a: AdtId, field: Sym, span: Span) {
        let p = self.p;
        let Some(tables) = &p.resolved else { return };
        let def = p.def_of_adt(a);
        if let Some((def_mod, fields)) = tables.field_vis.get(&def)
            && let Some(vis) = fields.get(&field)
            && !tables.visible(vis, *def_mod, self.module, p.interner)
        {
            let name = self.name(field).to_string();
            self.err(
                "L0510",
                span,
                format!("field `{name}` is private"),
                "Make the field `pub(crate)` (the smallest widening that works).",
            );
        }
    }

    /// The tuple struct a value binding names as a constructor, if it names one.
    fn tuple_struct_ctor(&mut self, name: Sym) -> Option<AdtId> {
        match self.binding(Namespace::Value, name) {
            BindingRes::Def(def) => match self.p.adt_by_def(def) {
                Some(a) if !self.p.adt(a).is_enum && self.p.adt(a).variants[0].shape == VariantShape::Tuple => Some(a),
                _ => None,
            },
            _ => None,
        }
    }

    /// The free fn a value binding names, if it names one.
    fn binding_fn(&mut self, name: Sym) -> Option<LocalDefId> {
        match self.binding(Namespace::Value, name) {
            BindingRes::Def(def) if self.p.binding_kind(def) == Some(DefsKind::Fn) => self.p.local_def(def.hash),
            _ => None,
        }
    }

    // ---------- Inference ----------

    fn new_var(&mut self, int: bool) -> Ty {
        self.vars.push(Var { bound: None });
        let id = self.vars.len() as u32 - 1;
        self.tys.intern(TyKind::Infer(InferId(id, int)))
    }
    /// Follows variable bindings at the top level only.
    fn resolve(&self, mut t: Ty) -> Ty {
        while let TyKind::Infer(v) = self.tys.kind(t) {
            match self.vars[v.index() as usize].bound {
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
        self.rebuild(t, true)
    }
    /// Resolves variables at every depth, keeping unbound ones. Trait queries need this.
    fn deep(&mut self, t: Ty) -> Ty {
        self.rebuild(t, false)
    }
    /// The shared walk of `zonk` and `deep` over the structural kinds a body can form.
    /// A type with no inference variable anywhere (the cached flag) is returned as is,
    /// so the common signature types cost one flag read. With `zonk`, an unbound
    /// variable is defaulted (integer variables to i32, others to the error type).
    fn rebuild(&mut self, t: Ty, zonk: bool) -> Ty {
        let t = self.resolve(t);
        match self.tys.kind(t) {
            TyKind::Infer(v) => {
                if !zonk {
                    return t;
                }
                let d = if v.is_int() { I32 } else { ERROR };
                self.vars[v.index() as usize].bound = Some(d);
                d
            }
            _ if !self.tys.flags(t).contains_infer() => t,
            TyKind::Ref(r, m, e) => {
                let e = self.rebuild(e, zonk);
                self.tys.intern(TyKind::Ref(r, m, e))
            }
            TyKind::Slice(e) => {
                let e = self.rebuild(e, zonk);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.rebuild(e, zonk);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let old: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.rebuild(e, zonk)).collect();
                let ts = self.tys.intern_tys(&new);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::Adt(d, a) => {
                // Rebuild each type arg in place: the new list is allocated only
                // when some arg actually changes (the common deep() case does not).
                let n = self.tys.args(a).len();
                let mut new: Option<Vec<GenericArg>> = None;
                for i in 0..n {
                    let g = self.tys.args(a)[i];
                    let g2 = match g {
                        GenericArg::Ty(e) => GenericArg::Ty(self.rebuild(e, zonk)),
                        other => other,
                    };
                    if g2 != g {
                        let v = new.get_or_insert_with(|| self.tys.args(a).to_vec());
                        v[i] = g2;
                    } else if let Some(v) = &mut new {
                        v[i] = g2;
                    }
                }
                match new {
                    None => t,
                    Some(v) => {
                        let a = self.tys.intern_args(&v);
                        self.tys.intern(TyKind::Adt(d, a))
                    }
                }
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
            (TyKind::Infer(v), TyKind::Infer(w)) => {
                // Bind the general variable to the integer one, so the integer constraint survives.
                if v.is_int() && !w.is_int() {
                    self.vars[w.index() as usize].bound = Some(a);
                } else {
                    self.vars[v.index() as usize].bound = Some(b);
                }
                true
            }
            (TyKind::Infer(v), k) | (k, TyKind::Infer(v)) => {
                if v.is_int() && !matches!(k, TyKind::Int(_)) {
                    return false;
                }
                let other = if matches!(self.tys.kind(a), TyKind::Infer(_)) { b } else { a };
                if self.occurs(v.index(), other) {
                    return false;
                }
                self.vars[v.index() as usize].bound = Some(other);
                true
            }
            // Regions do not take part in this equality: every region is `Erased`
            // until milestone 6 gives them their own solver (ARCH 5).
            (TyKind::Ref(_, m, x), TyKind::Ref(_, n, y)) => m == n && self.unify(x, y),
            (TyKind::Adt(d, x), TyKind::Adt(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::Tuple(x), TyKind::Tuple(y)) => {
                self.tys.tys_of(x).len() == self.tys.tys_of(y).len()
                    && (0..self.tys.tys_of(x).len()).all(|i| {
                        let (u, v) = (self.tys.tys_of(x)[i], self.tys.tys_of(y)[i]);
                        self.unify(u, v)
                    })
            }
            (TyKind::Slice(x), TyKind::Slice(y)) => self.unify(x, y),
            (TyKind::Array(x, n), TyKind::Array(y, m)) => n == m && self.unify(x, y),
            _ => false,
        }
    }
    /// Two generic argument lists unify element by element, in declared order.
    /// Type args unify; lifetime and const args must already be equal. Indexed
    /// reads only, so the common one-element `Vec<T>` case allocates nothing.
    fn unify_args(&mut self, a: ArgsId, b: ArgsId) -> bool {
        let n = self.tys.args(a).len();
        if n != self.tys.args(b).len() {
            return false;
        }
        for i in 0..n {
            let ok = match (self.tys.args(a)[i], self.tys.args(b)[i]) {
                (GenericArg::Ty(x), GenericArg::Ty(y)) => self.unify(x, y),
                (x, y) => x == y,
            };
            if !ok {
                return false;
            }
        }
        true
    }
    fn occurs(&self, v: u32, t: Ty) -> bool {
        match self.kind(t) {
            TyKind::Infer(w) => w.index() == v,
            TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => self.occurs(v, e),
            TyKind::Adt(_, a) => (0..self.tys.args(a).len()).any(|i| match self.tys.args(a)[i].as_ty() {
                Some(e) => self.occurs(v, e),
                None => false,
            }),
            TyKind::Tuple(ts) => {
                let n = self.tys.tys_of(ts).len();
                (0..n).any(|i| {
                    let e = self.tys.tys_of(ts)[i];
                    self.occurs(v, e)
                })
            }
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
        // ARCH 2.4 run point: the obligation queue runs at coercion sites.
        self.obl.run_at_coercion();
        let (fk, ek) = (self.kind(found), self.kind(expected));
        if fk == TyKind::Never {
            return true;
        }
        // Count reference layers, for deref coercions.
        let depth = |cx: &Self, mut t: Ty| {
            let mut n = 0u8;
            while let TyKind::Ref(_, _, inner) = cx.kind(t) {
                t = inner;
                n += 1;
            }
            (n, t)
        };
        let (fd, fbase) = depth(self, found);
        let (ed, _) = depth(self, expected);
        let c = match (fk, ek) {
            (TyKind::Ref(..), TyKind::Ref(_, Mut::Shared, s))
                if self.kind(s) == TyKind::Str && self.tys.is_string_ty(self.resolve(fbase)) =>
            {
                Coerce::StrFromString
            }
            (TyKind::Ref(..), TyKind::Ref(_, Mut::Shared, _))
                if fd > ed && {
                    let mut t = found;
                    for _ in 0..fd - ed {
                        if let TyKind::Ref(_, _, inner) = self.kind(t) {
                            t = inner;
                        }
                    }
                    matches!(self.kind(t), TyKind::Ref(_, Mut::Shared, _)) && self.unify(t, expected)
                } =>
            {
                Coerce::Deref(fd - ed)
            }
            (TyKind::Ref(_, Mut::Mut, x), TyKind::Ref(_, Mut::Shared, y)) if self.unify(x, y) => Coerce::MutToShared,
            (TyKind::Ref(_, Mut::Mut, x), TyKind::Ref(_, Mut::Mut, y)) if self.unify(x, y) => Coerce::Reborrow,
            (TyKind::Ref(_, fm, x), TyKind::Ref(_, em, y))
                if matches!(self.kind(y), TyKind::Slice(_))
                    && (!em.is_mut() || fm.is_mut())
                    && match self.kind(x) {
                        TyKind::Array(xe, _) => match self.kind(y) {
                            TyKind::Slice(ye) => self.unify(xe, ye),
                            _ => false,
                        },
                        _ => false,
                    } =>
            {
                Coerce::SliceFromArray(em.is_mut())
            }
            (TyKind::Ref(_, fm, x), TyKind::Ref(_, em, y))
                if matches!(self.kind(y), TyKind::Slice(_))
                    && (!em.is_mut() || fm.is_mut())
                    && match self.tys.vec_elem(self.resolve(x)) {
                        Some(xe) => match self.kind(y) {
                            TyKind::Slice(ye) => self.unify(xe, ye),
                            _ => false,
                        },
                        None => false,
                    } =>
            {
                Coerce::SliceFromVec(em.is_mut())
            }
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
                Stmt::Let { pat, ty, init, .. } => {
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
                            let lty = if by_ref { self.tys.mk_ref(mutable, ty) } else { ty };
                            // The binding's hygiene key is the pattern name's
                            // own context, not the `let` keyword's (ARCH 6.3).
                            let l = self.add_local(name, lty, mutable && !by_ref, self.p.ast.pat_span(*pat));
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
                            if init.is_none() {
                                let s = self.p.ast.pat_span(*pat);
                                self.errs.push(unsupported(s, "destructuring in `let` without an initializer"));
                            } else {
                                self.pattern(*pat, ty, false);
                                if !self.irrefutable(*pat) {
                                    let s = self.p.ast.pat_span(*pat);
                                    self.err(
                                        "L0110",
                                        s,
                                        "refutable pattern in local binding",
                                        "Use `match` or `if let` for a pattern that can fail.",
                                    );
                                }
                            }
                        }
                    }
                }
                // Body items and statement macros are rejected by the parser today.
                Stmt::Item(_) | Stmt::Macro { .. } => {}
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
        // A written type name in a body is a type-namespace binding read.
        // Primitive names and `Self` are scope layers, not bindings.
        if let ast::TyExpr::Path(segs) = p.ast.ty(t) {
            let seg = if segs.len() > 1 && segs[0].name == p.known.std {
                segs.last()
            } else if segs.len() == 1 {
                segs.first()
            } else {
                None
            };
            if let Some(seg) = seg {
                let name = seg.name;
                if p.known.int_ty(name).is_none()
                    && name != p.known.bool
                    && name != p.known.char
                    && name != p.known.str
                    && name != p.known.self_type
                {
                    self.binding(Namespace::Type, name);
                }
            }
        }
        match resolve_ty(p.ast, p.interner, p.known, &p.type_names, &p.aliases, &mut self.tys, t, self.self_ty) {
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
                Some((t, k)) if k.is_int_infer() => t,
                _ => self.new_var(true),
            },
            Expr::Float(i) => {
                let text = p.ast.strings[*i as usize].as_str();
                match crate::check::collect::parse_float_literal(text) {
                    Some((_, suffix)) => match suffix {
                        Some(f) => self.tys.float_ty(f),
                        None => match expected.map(|t| self.kind(t)) {
                            Some(TyKind::Float(_)) => expected.unwrap(),
                            _ => self.tys.float_ty(FloatTy::F64),
                        },
                    },
                    None => {
                        self.err("L0118", span, "invalid float literal", "Write the literal in a simpler form.");
                        ERROR
                    }
                }
            }
            Expr::Bool(_) => BOOL,
            Expr::Char(_) => CHAR,
            Expr::Str(_) => REF_STR,
            Expr::Unit => UNIT,
            Expr::SelfValue => match self.lookup(p.known.self_value, span.ctxt) {
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
            Expr::While { label, cond, body } => {
                self.expect_expr(*cond, BOOL);
                self.loops.push(LoopCtx { break_ty: None, is_loop: false, is_block: false, label: label_of(label) });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                self.loops.pop();
                UNIT
            }
            Expr::Loop { label, body } => {
                self.loops.push(LoopCtx { break_ty: None, is_loop: true, is_block: false, label: label_of(label) });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                let l = self.loops.pop().unwrap();
                l.break_ty.unwrap_or(NEVER)
            }
            Expr::For { label, pat, iter, body } => {
                let item = self.for_iter(*iter);
                let scope = self.scopes.len();
                self.pattern(*pat, item, false);
                self.loops.push(LoopCtx { break_ty: None, is_loop: false, is_block: false, label: label_of(label) });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                self.loops.pop();
                self.scopes.truncate(scope);
                UNIT
            }
            Expr::Match { scrut, arms } => {
                let st = self.expr(*scrut, None);
                // ARCH 2.12 run point: a match must know the scrutinee enum.
                self.obl.run_before_structural();
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
            Expr::MethodCall { recv, name, name_span, generic_args, args } => {
                if !generic_args.is_empty() {
                    self.errs.push(not_yet("L0721", *name_span, "turbofish on method calls"));
                }
                self.method_call(e, *recv, *name, *name_span, args)
            }
            Expr::Field { base, name } => {
                let bt = self.expr(*base, None);
                // ARCH 2.12 run point: a field access must know the base type.
                self.obl.run_before_structural();
                let (derefs, inner) = self.autoderef(bt);
                if let Some(a) = self.tys.local_adt(inner) {
                    let adt = p.adt(a);
                    if !adt.is_enum
                        && let Some(i) = adt.variants[0].fields.iter().position(|f| f.name == *name)
                    {
                        self.check_field_vis(a, *name, span);
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
                // ARCH 2.12 run point: an index must know the indexed type; the
                // index type then follows from the selected `Index` impl.
                self.obl.run_before_structural();
                let (derefs, inner) = self.autoderef(bt);
                if let Expr::Range { lo, hi, .. } = p.ast.expr(*index) {
                    // A range index makes a slice place. Bounds are usize.
                    // The range expression itself is not checked as a value;
                    // give it the error-free unit record so lowering (which
                    // reads the bounds directly) never sees a stale type.
                    for b in [lo, hi].into_iter().flatten() {
                        self.expect_expr(*b, USIZE);
                    }
                    self.set(*index, UNIT);
                    let elem = match self.kind(inner) {
                        TyKind::Array(elem, _) | TyKind::Slice(elem) => Some(elem),
                        _ => self.tys.vec_elem(inner),
                    };
                    match elem {
                        Some(elem) => {
                            self.set_res(e, Res::SliceIndex { derefs });
                            return self.tys.intern(TyKind::Slice(elem));
                        }
                        None => {
                            if !matches!(self.kind(inner), TyKind::Error) {
                                let tn = self.tn(bt);
                                self.err(
                                    "L0113",
                                    span,
                                    format!("cannot slice a value of type `{tn}`"),
                                    "Slice an array, a Vec, or a slice.",
                                );
                            }
                            return ERROR;
                        }
                    }
                }
                self.expect_expr(*index, USIZE);
                match self.kind(inner) {
                    TyKind::Array(elem, _) | TyKind::Slice(elem) => {
                        self.set_res(e, Res::Index { derefs });
                        elem
                    }
                    _ if self.tys.vec_elem(inner).is_some() => {
                        self.set_res(e, Res::Index { derefs });
                        self.tys.vec_elem(inner).unwrap()
                    }
                    TyKind::Error => ERROR,
                    _ if self.kind(inner) == TyKind::Str || self.tys.is_string_ty(inner) => {
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
                // Rust has `-` and `!` for `&T` (shared references only, not `&mut T`).
                let (d, inner) = match self.kind(t) {
                    TyKind::Ref(_, Mut::Shared, inner) => (1, inner),
                    _ => (0, t),
                };
                self.set_res(e, Res::Bin { ld: d, rd: 0 });
                let k = self.kind(inner);
                match (op, k) {
                    (UnOp::Neg, TyKind::Float(_)) => inner,
                    (UnOp::Neg, TyKind::Int(i)) if i.signed() => inner,
                    (UnOp::Neg, k) if k.is_int_infer() => inner,
                    (UnOp::Not, TyKind::Bool | TyKind::Int(_)) => inner,
                    (UnOp::Not, k) if k.is_int_infer() => inner,
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
                let enum_cast = match self.tys.local_adt(self.resolve(t)) {
                    Some(a) => p.adt(a).is_enum && p.adt(a).variants.iter().all(|v| v.shape == VariantShape::Unit),
                    None => false,
                };
                let ok = match (self.kind(t), self.kind(target)) {
                    // An integer of unknown type stays open: later uses decide it (default i32).
                    (k, TyKind::Int(_)) if k.is_int_infer() => true,
                    (_, TyKind::Int(_)) if enum_cast => true,
                    (TyKind::Int(_) | TyKind::Bool | TyKind::Char, TyKind::Int(_)) => true,
                    (TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Float(_), TyKind::Float(_)) => true,
                    (TyKind::Float(_), TyKind::Int(_) | TyKind::Char) => true,
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
            Expr::Ref { mutable, expr, .. } => {
                let inner_expected = expected.and_then(|t| match self.kind(t) {
                    TyKind::Ref(_, _, inner) => Some(inner),
                    _ => None,
                });
                let t = self.expr(*expr, inner_expected);
                self.check_packed_borrow(*expr, span);
                self.tys.mk_ref(*mutable, t)
            }
            Expr::Deref(inner) => {
                let t = self.expr(*inner, None);
                // ARCH 2.12 run point: a deref must know the pointee source type.
                self.obl.run_before_structural();
                match self.kind(t) {
                    TyKind::Ref(_, _, x) => x,
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
                if self.tys.is_string_ty(self.resolve(lt)) && *op == BinOp::Add {
                    self.coerce_expr(*rhs, rt, REF_STR);
                    self.set_res(e, Res::Bin { ld: 0, rd: 0 });
                    return UNIT;
                }
                let (rd, rinner) = self.peel_one_ref(rt);
                // `x += &y` is fine, but Rust has no compound assignment with a `&mut` operand.
                let rmut = matches!(self.kind(rt), TyKind::Ref(_, Mut::Mut, _));
                let int_like = |k: TyKind| matches!(k, TyKind::Int(_)) || k.is_int_infer();
                let ok = !rmut
                    && match (*op, lk) {
                        (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem, TyKind::Float(_)) => self.unify(lt, rinner),
                        (_, TyKind::Error) => true,
                        (BinOp::Shl | BinOp::Shr, k) if int_like(k) => int_like(self.kind(rinner)),
                        (_, k) if int_like(k) => self.unify(lt, rinner),
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
            Expr::StructLit { path, fields, update } => self.struct_lit(e, path, fields, *update, span),
            Expr::Range { .. } => {
                self.errs.push(unsupported(span, "ranges outside `for` loops"));
                ERROR
            }
            Expr::Break { label, value: val } => {
                let target = match label {
                    None => self.loops.len().checked_sub(1),
                    Some(l) => self
                        .loops
                        .iter()
                        .rposition(|lp| lp.label.is_some_and(|(n, bs)| n == l.name && crate::diag::ctxt_can_see_local(l.span.ctxt, bs))),
                };
                let Some(ti) = target else {
                    match label {
                        Some(l) => {
                            let n = self.name(l.name).to_string();
                            self.err("L0120", span, format!("cannot find label `'{n}` in this scope"), "Check the label name.");
                        }
                        None => self.err("L0120", span, "`break` outside of a loop", "Remove the break, or put it inside a loop."),
                    }
                    if let Some(v) = val {
                        self.expr(*v, None);
                    }
                    return NEVER;
                };
                let is_loop = self.loops[ti].is_loop;
                let prev = self.loops[ti].break_ty;
                match val {
                    Some(v) if !is_loop => {
                        self.expr(*v, None);
                        self.err(
                            "L0120",
                            span,
                            "`break` with a value is only allowed in `loop` and labeled blocks",
                            "Remove the value, or use `loop`.",
                        );
                    }
                    Some(v) => {
                        let t = self.expr(*v, prev);
                        match prev {
                            Some(pt) => {
                                self.coerce_expr(*v, t, pt);
                            }
                            None => self.loops[ti].break_ty = Some(t),
                        }
                    }
                    None if is_loop => match prev {
                        Some(pt) => {
                            self.coerce_at(UNIT, pt, span, None);
                        }
                        None => self.loops[ti].break_ty = Some(UNIT),
                    },
                    None => {}
                }
                NEVER
            }
            Expr::Continue(label) => {
                let found = match label {
                    None => self.loops.iter().rposition(|lp| !lp.is_block),
                    Some(l) => self
                        .loops
                        .iter()
                        .rposition(|lp| lp.label.is_some_and(|(n, bs)| n == l.name && crate::diag::ctxt_can_see_local(l.span.ctxt, bs))),
                };
                match found {
                    None => match label {
                        Some(l) => {
                            let n = self.name(l.name).to_string();
                            self.err("L0120", span, format!("cannot find label `'{n}` in this scope"), "Check the label name.");
                        }
                        None => self.err("L0120", span, "`continue` outside of a loop", "Remove the continue, or put it inside a loop."),
                    },
                    Some(ti) if self.loops[ti].is_block => {
                        self.err("L0120", span, "`continue` cannot target a labeled block", "`continue` needs a loop label.");
                    }
                    Some(_) => {}
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
            Expr::LabeledBlock { label, body } => {
                self.loops.push(LoopCtx { break_ty: None, is_loop: true, is_block: true, label: Some((label.name, label.span)) });
                let t = self.block(*body, expected);
                let l = self.loops.pop().unwrap();
                match l.break_ty {
                    Some(bt) => self.join(bt, t, None, span),
                    None => t,
                }
            }
            Expr::Macro { kind, args, fmt, repeat } => self.macro_expr(e, *kind, args, fmt, *repeat, span, expected),
            Expr::Tuple(elems) => {
                let exp: Option<Vec<Ty>> = expected.and_then(|t| match self.kind(t) {
                    TyKind::Tuple(ts) if self.tys.tys_of(ts).len() == elems.len() => Some(self.tys.tys_of(ts).to_vec()),
                    _ => None,
                });
                let mut out = Vec::with_capacity(elems.len());
                for (i, &el) in elems.iter().enumerate() {
                    out.push(self.expr(el, exp.as_ref().map(|v| v[i])));
                }
                let ts = self.tys.intern_tys(&out);
                self.tys.intern(TyKind::Tuple(ts))
            }
            Expr::Array(elems) => {
                let exp_elem = expected.and_then(|t| match self.kind(t) {
                    TyKind::Array(el, _) => Some(el),
                    _ => None,
                });
                let elem = match (exp_elem, elems.first()) {
                    (Some(el), _) => {
                        for &el_e in elems {
                            self.expect_expr(el_e, el);
                        }
                        el
                    }
                    (None, Some(&first)) => {
                        let el = self.expr(first, None);
                        for &el_e in &elems[1..] {
                            self.expect_expr(el_e, el);
                        }
                        el
                    }
                    (None, None) => self.new_var(false),
                };
                let c = self.tys.intern_const(ConstKind::Int(elems.len() as u128));
                self.tys.intern(TyKind::Array(elem, c))
            }
            Expr::ArrayRepeat { value, len } => {
                let exp_elem = expected.and_then(|t| match self.kind(t) {
                    TyKind::Array(el, _) => Some(el),
                    _ => None,
                });
                let elem = self.expr(*value, exp_elem);
                self.expect_expr(*len, USIZE);
                let n = crate::check::collect::eval_array_len(p.ast, *len);
                match n {
                    Some(n) => {
                        let const_val = self.out.const_exprs[self.ei(*value)].is_some();
                        if n > 1 && !const_val && !is_copy(p, &self.tys, self.resolve(elem)) {
                            self.err(
                                "L0110",
                                span,
                                "the trait `Copy` is not implemented for this type",
                                "Array repeat with a length above 1 needs a Copy element, or write the elements out.",
                            );
                        }
                        let c = self.tys.intern_const(ConstKind::Int(n));
                        self.tys.intern(TyKind::Array(elem, c))
                    }
                    None => {
                        self.err(
                            "L0110",
                            span,
                            "array repeat length must be a constant integer",
                            "Write a literal length such as `[0; 4]`.",
                        );
                        ERROR
                    }
                }
            }
            Expr::TupleField { base, index } => {
                let bt = self.expr(*base, None);
                self.obl.run_before_structural();
                let (derefs, inner) = self.autoderef(bt);
                let field_ty = match self.kind(inner) {
                    TyKind::Tuple(ts) => self.tys.tys_of(ts).get(*index as usize).copied(),
                    _ => match self.tys.local_adt(inner) {
                        Some(a) if !p.adt(a).is_enum && p.adt(a).variants[0].shape == VariantShape::Tuple => {
                            p.adt(a).variants[0].fields.get(*index as usize).map(|f| f.ty)
                        }
                        _ => None,
                    },
                };
                match field_ty {
                    Some(t) => {
                        self.set_res(e, Res::Field { derefs, index: *index });
                        t
                    }
                    None => {
                        if !matches!(self.kind(inner), TyKind::Error) {
                            let tn = self.tn(bt);
                            self.err("L0103", span, format!("no field `{index}` on type `{tn}`"), "Check the field index.");
                        }
                        ERROR
                    }
                }
            }
            Expr::ConstBlock(_) => {
                let mut ccx = CheckCx { cx: self };
                match crate::ty::consteval::eval(&mut ccx, e, expected) {
                    Ok((v, t)) => {
                        let i = ccx.cx.ei(e);
                        ccx.cx.out.const_exprs[i] = Some(v);
                        t
                    }
                    Err(d) => {
                        ccx.cx.errs.push(d);
                        ERROR
                    }
                }
            }
            Expr::OffsetOf { ty, fields } => {
                let t = self.resolve_written(*ty);
                let mut cur = self.deep(t);
                let mut off: u64 = 0;
                let mut bad = false;
                for &fname in fields {
                    let Some(a) = self.tys.local_adt(cur) else {
                        self.err("L0110", span, "`offset_of!` needs a struct type", "Use a struct with named fields.");
                        bad = true;
                        break;
                    };
                    if !matches!(
                        p.adt(a).repr.kind,
                        crate::ty::layout::ReprKind::C | crate::ty::layout::ReprKind::Packed | crate::ty::layout::ReprKind::Transparent
                    ) {
                        self.err(
                            "L0650",
                            span,
                            "`offset_of!` on a default-repr type is not supported",
                            "Add `#[repr(C)]` to the type, or measure with `size_of`.",
                        );
                        bad = true;
                        break;
                    }
                    let Some(i) = p.adt(a).variants[0].fields.iter().position(|f| f.name == fname) else {
                        self.err("L0103", span, format!("no field `{}` for `offset_of!`", self.name(fname)), "Check the field name.");
                        bad = true;
                        break;
                    };
                    match crate::ty::layout::layout_of_ty(&self.tys, p, cur) {
                        Ok(l) => off += l.field_offsets.get(i).copied().unwrap_or(0),
                        Err(()) => {
                            self.err(
                                "L0652",
                                span,
                                "unsupported layout form in `offset_of!`",
                                "Use a type inside the supported layout grammar.",
                            );
                            bad = true;
                            break;
                        }
                    }
                    cur = p.adt(a).variants[0].fields[i].ty;
                }
                if bad {
                    ERROR
                } else {
                    self.set_res(e, Res::ConstUsize(off));
                    USIZE
                }
            }
            // AST v2 expression forms the parser still rejects.
            Expr::Closure { .. }
            | Expr::Try(_)
            | Expr::Await(_)
            | Expr::AsyncBlock { .. }
            | Expr::UnsafeBlock(_)
            | Expr::Let { .. }
            | Expr::QPath { .. }
            | Expr::Underscore
            | Expr::MacroCall(_) => ERROR,
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
    /// A reference to a packed field could be unaligned (ARCH 4.4): any borrow
    /// of a field place whose base is a packed Adt, explicit or implicit
    /// (method autoref, format arguments), is an error at the borrow.
    fn check_packed_borrow(&mut self, place_e: ExprId, span: Span) {
        let base = match self.p.ast.expr(place_e) {
            Expr::Field { base, .. } | Expr::TupleField { base, .. } => *base,
            _ => return,
        };
        let bt = self.out.expr_ty[self.ei(base)];
        let (_, inner) = self.autoderef(bt);
        if let Some(a) = self.tys.local_adt(inner)
            && self.p.adt(a).repr.kind == crate::ty::layout::ReprKind::Packed
        {
            self.err("L0651", span, "reference to a packed field is not allowed", "Copy the field value into a local first.");
        }
    }

    /// Assignment into a static is never a plain place write here: an
    /// immutable static cannot be assigned, and a mutable one needs `unsafe`.
    fn static_root(&self, e: ExprId) -> Option<u32> {
        match self.p.ast.expr(e) {
            Expr::Path(_) => match self.out.expr_res[self.ei(e)] {
                Res::Static(idx) => Some(idx),
                _ => None,
            },
            Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Index { base, .. } => self.static_root(*base),
            _ => None,
        }
    }

    fn place_check(&mut self, e: ExprId) {
        if let Some(idx) = self.static_root(e) {
            let s = self.span(e);
            if self.p.statics[idx as usize].mutable {
                self.err(
                    "L0404",
                    s,
                    "writing a mutable static requires `unsafe`, which is not supported",
                    "Make the static immutable, or use a local variable.",
                );
            } else {
                self.err("L0121", s, "cannot assign to an immutable static", "Statics are read-only; use a variable instead.");
            }
            return;
        }
        let ok = match self.p.ast.expr(e) {
            Expr::Path(segs) => segs.len() == 1 && matches!(self.out.expr_res[self.ei(e)], Res::Local(_)),
            Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. } | Expr::Deref(_) | Expr::SelfValue => true,
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
        while let TyKind::Ref(_, _, inner) = self.tys.kind(t) {
            t = self.resolve(inner);
            n += 1;
        }
        (n, t)
    }
    fn peel_one_ref(&self, t: Ty) -> (u8, Ty) {
        match self.kind(t) {
            TyKind::Ref(_, _, inner) => (1, inner),
            _ => (0, t),
        }
    }
    /// The value of a literal expression (an integer, possibly negated, or a char), if it is one.
    fn const_scalar(&self, e: ExprId) -> Option<i128> {
        match self.p.ast.expr(e) {
            Expr::Int(v, _) => Some(*v as i128),
            Expr::Char(c) => Some(*c as i128),
            Expr::Unary { op: UnOp::Neg, expr } => match self.p.ast.expr(*expr) {
                Expr::Int(v, _) => Some(-(*v as i128)),
                _ => None,
            },
            _ => None,
        }
    }
    /// The mutability of each reference layer of `t`, outermost first.
    fn ref_layers(&self, t: Ty) -> Vec<bool> {
        let mut out = Vec::new();
        let mut t = t;
        while let TyKind::Ref(_, m, inner) = self.kind(t) {
            out.push(m.is_mut());
            t = inner;
        }
        out
    }

    fn path_expr(&mut self, e: ExprId, segs: &[ast::PathSeg], span: Span) -> Ty {
        let p = self.p;
        if segs.len() == 1 {
            let name = segs[0].name;
            if let Some(l) = self.lookup(name, span.ctxt) {
                self.set_res(e, Res::Local(l));
                return self.out.locals[l as usize].ty;
            }
            // One value-namespace binding read covers the fn and constructor
            // cases below. The prelude `None` keeps its place between them,
            // as before: it is a prelude name, not a module binding.
            let bound = self.binding(Namespace::Value, name);
            if let BindingRes::Def(def) = bound
                && p.binding_kind(def) == Some(DefsKind::Fn)
                && let Some(f) = p.local_def(def.hash)
            {
                self.set_res(e, Res::Fn(f));
                return ERROR;
            }
            if let BindingRes::Def(def) = bound {
                match p.binding_kind(def) {
                    Some(DefsKind::Const) => {
                        if let Some(idx) = p.const_by_def(def) {
                            let c = &p.consts[idx as usize];
                            let (v, t) = (c.value.clone(), c.ty);
                            let i = self.ei(e);
                            self.out.const_exprs[i] = Some(v);
                            // The value lives in the global store; rebuild the
                            // type in this body's overlay so unification sees it.
                            return self.deep(t);
                        }
                    }
                    Some(DefsKind::Static) => {
                        if let Some(idx) = p.static_by_def(def) {
                            let st = &p.statics[idx as usize];
                            if st.mutable {
                                self.err(
                                    "L0404",
                                    span,
                                    "reading a mutable static requires `unsafe`, which is not supported",
                                    "Make the static immutable, or read it through a const.",
                                );
                                return ERROR;
                            }
                            let t = st.ty;
                            self.set_res(e, Res::Static(idx));
                            return self.deep(t);
                        }
                    }
                    _ => {}
                }
            }
            if name == p.known.None {
                self.set_res(e, Res::OptNone);
                let v = self.new_var(false);
                return self.tys.mk_option(v);
            }
            if let BindingRes::Def(def) = bound
                && let Some(a) = p.adt_by_def(def)
            {
                let unit = match p.sig_of(&mut self.out.reads, def) {
                    SigOf::Adt(adt) => !adt.is_enum && adt.variants[0].shape == VariantShape::Unit,
                    _ => false,
                };
                if unit {
                    self.set_res(e, Res::Variant(a, 0));
                    return self.tys.adt_ty(a);
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
        // Primitive associated consts: `i64::MAX`, `u32::BITS`, and kin.
        if segs.len() == 2
            && let Some(it) = p.known.int_ty(segs[0].name)
        {
            let item = self.name(segs[1].name);
            let bits = it.bits();
            let v = match item {
                "MAX" => Some(crate::ty::consteval::truncate_to_int(it.max128() as i128, it)),
                "MIN" => Some(if it.signed() { if bits >= 128 { i128::MIN } else { -(1i128 << (bits - 1)) } } else { 0 }),
                "BITS" => Some(bits as i128),
                _ => None,
            };
            if let Some(v) = v {
                let (ty, val) = if item == "BITS" {
                    (int(IntTy::U32), crate::ty::consteval::ConstValue::Int(v))
                } else {
                    // u128::MAX does not fit an i128; store its bits as -1 and
                    // let materialization reinterpret them at the u128 type.
                    let val = if it == IntTy::U128 && item == "MAX" { -1 } else { v };
                    (int(it), crate::ty::consteval::ConstValue::Int(val))
                };
                let i = self.ei(e);
                self.out.const_exprs[i] = Some(val);
                return ty;
            }
        }
        if let Some(r) = self.resolve_assoc(segs, span) {
            self.set_res(e, r);
            if let Res::Variant(a, v) = r {
                let variant = &p.adt(a).variants[v as usize];
                if variant.shape == VariantShape::Unit {
                    return self.tys.adt_ty(a);
                }
            }
            return ERROR;
        }
        ERROR
    }

    /// Resolves a `core::intrinsics::<name>` path. Order is fixed: the
    /// name must exist in the registry, the call site's crate must be on
    /// the row's privilege list, and codegen must implement the row.
    /// A user call site never has a shipped crate, so it stops at the
    /// privilege test with L0642 (docs/ARCH.md sections 3.1 and 3.2).
    fn resolve_intrinsic(&mut self, name: Sym, span: Span) -> Option<Res> {
        let text = self.name(name).to_string();
        let Some(id) = lang::intrinsic_by_name(&text) else {
            self.err(
                "L0104",
                span,
                format!("no intrinsic `core::intrinsics::{text}`"),
                "Intrinsics are a closed registry (src/ty/lang.rs). Call a public std item instead.",
            );
            return None;
        };
        let def = lang::intrinsic(id);
        if !def.allows(self.p.shipped_crate_at(span)) {
            self.err(
                "L0642",
                span,
                format!("intrinsic `core::intrinsics::{text}` can only be called from lust's shipped library crates"),
                "Call the public std item that wraps it instead.",
            );
            return None;
        }
        if !def.implemented {
            self.err(
                "L0640",
                span,
                format!("intrinsic `core::intrinsics::{text}` is declared but not yet implemented"),
                "Implement the registry row and its runtime hook first (docs/ARCH.md section 3.2).",
            );
            return None;
        }
        Some(Res::Intrinsic(id))
    }

    /// Resolves `Type::item` and `std::env::args`. Reports an error and returns None on failure.
    fn resolve_assoc(&mut self, segs: &[ast::PathSeg], span: Span) -> Option<Res> {
        let p = self.p;
        let k = p.known;
        let names: Vec<Sym> = segs.iter().map(|s| s.name).collect();
        if names.len() == 3 && names[0] == k.core && names[1] == k.intrinsics {
            return self.resolve_intrinsic(names[2], span);
        }
        // Shipped source std fns (the `STD_FNS` registry). A declared row
        // with no body yet rejects with L0640; an implemented row routes
        // to the spliced body the loader put in this program. If std was
        // not loaded (the driver trigger missed this spelling), the path
        // falls through to the module-path reject below, never an accept.
        if names[0] == k.std {
            for def in lang::STD_FNS {
                if def.path.len() == names.len() && def.path.iter().zip(&names).all(|(s, n)| *s == self.name(*n)) {
                    if !def.implemented {
                        self.err(
                            "L0640",
                            span,
                            format!("`{}` is declared but not yet implemented in lust std", def.path.join("::")),
                            "Use a std item lust implements today, or write the behavior in your own code.",
                        );
                        return None;
                    }
                    if let Some(f) = p.std_fn_for_path(&names) {
                        return Some(Res::Fn(f));
                    }
                    break;
                }
            }
        }
        if names == [k.std, k.env, k.args] {
            return Some(Res::Builtin(Builtin::EnvArgs));
        }
        if names.len() == 3
            && (names[0] == k.std || names[0] == k.core)
            && self.name(names[1]) == "mem"
            && matches!(self.name(names[2]), "size_of" | "align_of")
        {
            let align = self.name(names[2]) == "align_of";
            return Some(self.layout_query(&segs[2], align, span));
        }
        if segs.len() != 2 {
            self.errs.push(not_yet("L0505", span, "module paths"));
            return None;
        }
        let (ty_name, item) = (names[0], names[1]);
        // The first segment is a type-namespace binding read (`Self` is a
        // scope name, not a binding, and records nothing).
        let ty_bound = if ty_name == k.self_type { BindingRes::Absent } else { self.binding(Namespace::Type, ty_name) };
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
        let adt = if ty_name == p.known.self_type {
            self.f.owner
        } else {
            match ty_bound {
                BindingRes::Def(def) => p.adt_by_def(def),
                _ => None,
            }
        };
        let Some(a) = adt else {
            self.err("L0101", span, format!("cannot find type `{}`", self.name(ty_name)), "Check the spelling.");
            return None;
        };
        // The variant and associated-item tables of the Adt are part of its
        // signature read. Associated fns get their own index query when the
        // trait index lands (W-TRAITS-CORE); the method map stays behind
        // this `Sig` read until then.
        let adef = p.def_of_adt(a);
        let is_variant = match p.sig_of(&mut self.out.reads, adef) {
            SigOf::Adt(def) if def.is_enum => def.variants.iter().position(|v| v.name == item),
            _ => None,
        };
        if let Some(v) = is_variant {
            return Some(Res::Variant(a, v as u32));
        }
        if let Some(&f) = p.methods.get(&(a, item)) {
            return Some(Res::Fn(f));
        }
        let tn = self.name(ty_name).to_string();
        self.err("L0104", span, format!("no variant or associated function `{}` on `{tn}`", self.name(item)), "Check the name.");
        None
    }

    /// A `size_of` or `align_of` query on the given turbofish type argument:
    /// the layout engine answers, or the layout reject fires (ARCH 4.4).
    fn layout_query(&mut self, seg: &ast::PathSeg, align: bool, span: Span) -> Res {
        let args = seg.type_args();
        if args.len() != 1 {
            self.err("L0105", span, "this function takes one type argument", "Write `size_of::<Type>()`.");
            return Res::ConstUsize(0);
        }
        let t = self.resolve_written(args[0]);
        let p: &Program<'_> = self.p;
        let t = self.deep(t);
        match crate::ty::layout::layout_of_ty(&self.tys, p, t) {
            Ok(l) => Res::ConstUsize(if align { l.align } else { l.size }),
            Err(()) => {
                self.err(
                    "L0652",
                    span,
                    format!("unsupported layout form: `{}`", self.tn(t)),
                    "Use a type inside the supported layout grammar.",
                );
                Res::ConstUsize(0)
            }
        }
    }

    fn call(&mut self, e: ExprId, callee: ExprId, args: &[ExprId], span: Span) -> Ty {
        let p = self.p;
        let res = match p.ast.expr(callee) {
            Expr::Path(segs) if segs.len() == 1 => {
                let name = segs[0].name;
                if self.lookup(name, self.span(callee).ctxt).is_some() {
                    self.err("L0114", span, "this value is not a function", "Closures are not supported yet. Call a named function.");
                    return ERROR;
                }
                match self.binding_fn(name) {
                    Some(f) => Res::Fn(f),
                    None if name == p.known.Some => Res::OptSome,
                    None if matches!(self.name(name), "size_of" | "align_of") && !segs[0].type_args().is_empty() => {
                        let align = self.name(name) == "align_of";
                        self.layout_query(&segs[0], align, span)
                    }
                    None => match self.tuple_struct_ctor(name) {
                        Some(a) => Res::Variant(a, 0),
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
                    },
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
            return self.tys.mk_option(t);
        }
        match res {
            Res::ConstUsize(_) => {
                if !args.is_empty() {
                    self.err("L0105", span, "this function takes no arguments", "Write `size_of::<Type>()`.");
                }
                USIZE
            }
            Res::Fn(f) => {
                // Path calls such as `Type::method(x)` pass `self` explicitly, so all params apply.
                let (params, ret) = match p.sig_of(&mut self.out.reads, p.def_id(f)) {
                    SigOf::Fn(info) => (info.params.clone(), info.ret),
                    _ => return ERROR,
                };
                self.check_args(&params, args, span);
                ret
            }
            Res::Variant(a, v) => {
                let adef = p.def_of_adt(a);
                let _ = p.sig_of(&mut self.out.reads, adef);
                let variant = &p.adt(a).variants[v as usize];
                if variant.shape != VariantShape::Tuple {
                    self.err("L0114", span, "this variant is not a tuple variant", "Use `Type::Variant` or `Type::Variant { .. }`.");
                    return ERROR;
                }
                let params: Vec<Ty> = variant.fields.iter().map(|f| f.ty).collect();
                self.check_args(&params, args, span);
                self.tys.adt_ty(a)
            }
            Res::Builtin(b) => {
                let (params, ret): (Vec<Ty>, Ty) = match b {
                    Builtin::StringNew => (vec![], STRING),
                    Builtin::StringFrom => (vec![REF_STR], STRING),
                    Builtin::StringWithCapacity => (vec![USIZE], STRING),
                    Builtin::EnvArgs => (vec![], ARGS),
                    Builtin::VecNew | Builtin::VecWithCapacity => {
                        let generics = match p.ast.expr(callee) {
                            Expr::Path(segs) => segs[0].type_args(),
                            _ => Vec::new(),
                        };
                        let elem = match generics.first() {
                            Some(&g) => self.resolve_written(g),
                            None => self.new_var(false),
                        };
                        let params = if b == Builtin::VecNew { vec![] } else { vec![USIZE] };
                        (params, self.tys.mk_vec(elem))
                    }
                    _ => unreachable!(),
                };
                self.check_args(&params, args, span);
                ret
            }
            Res::Intrinsic(id) => {
                let def = lang::intrinsic(id);
                let params: Vec<Ty> = def.params.iter().map(|s| s.resolve(&mut self.tys)).collect();
                self.check_args(&params, args, span);
                def.ret.resolve(&mut self.tys)
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
        // ARCH 2.12 run point: a method call must know the receiver type. The
        // obligation queue runs just before that head is required (ARCH 2.4).
        self.obl.run_before_structural();
        let (derefs, base) = self.autoderef(rt);
        let bk = self.tys.kind(base);
        // User methods, through the method-set probes of section 2.10: every
        // form is probed in order and recorded, hit or miss, before the
        // builtin compat dispatch below runs.
        let head = Head::of(&self.tys, base);
        let mut user = None;
        for form in ReceiverForm::PROBE_ORDER {
            let set = p.method_set(&mut self.out.reads, head, name, form);
            if let Some(c) = set.first() {
                user = Some(c);
                break;
            }
        }
        if let Some(c) = user {
            let f = p.local_def(c.def.hash).expect("a method candidate names a local fn");
            let Some(form) = c.receiver else {
                self.err(
                    "L0104",
                    name_span,
                    format!("`{}` is an associated function, not a method", self.name(name)),
                    "Call it as `Type::name(...)`.",
                );
                return ERROR;
            };
            let autoref = match form {
                ReceiverForm::Value => Autoref::None,
                ReceiverForm::Ref => Autoref::Ref,
                ReceiverForm::RefMut => Autoref::RefMut,
            };
            let (params, ret) = match p.sig_of(&mut self.out.reads, c.def) {
                SigOf::Fn(info) => (info.params[1..].to_vec(), info.ret),
                _ => return ERROR,
            };
            if autoref != Autoref::None {
                self.check_packed_borrow(recv, name_span);
            }
            self.set_res(e, Res::Method { f, derefs, autoref });
            self.check_args(&params, args, name_span);
            return ret;
        }
        // `clone` on a reference to a non-Clone type clones the reference.
        if name == k.clone {
            if !has_clone(p, &self.tys, base) && derefs > 0 {
                // Peel all but the last reference; the clone copies that reference.
                let mut cur = self.resolve(rt);
                for _ in 0..derefs - 1 {
                    if let TyKind::Ref(_, _, inner) = self.tys.kind(cur) {
                        cur = self.resolve(inner);
                    }
                }
                self.check_packed_borrow(recv, name_span);
                self.set_res(e, Res::BuiltinMethod { b: Builtin::Clone, derefs: derefs - 1, autoref: Autoref::Ref });
                self.check_args(&[], args, name_span);
                return cur;
            }
            if has_clone(p, &self.tys, base) {
                self.check_packed_borrow(recv, name_span);
                self.set_res(e, Res::BuiltinMethod { b: Builtin::Clone, derefs, autoref: Autoref::Ref });
                self.check_args(&[], args, name_span);
                return base;
            }
        }
        use Builtin as B;
        // Builtin methods dispatch on the v2 builtin def in the first slot and on
        // the general kind in the second; user Adts were handled above.
        let found: Option<(B, Autoref, Vec<Ty>, Ty)> = match (self.tys.builtin_of(base), bk) {
            (Some(BuiltinTy::String), _) => {
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
            (None, TyKind::Str) => {
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
            (Some(BuiltinTy::Vec), _) => {
                let elem = self.tys.adt_first_ty_arg(base).unwrap_or(ERROR);
                // Return types are built only in the arms that return them:
                // interning has no visible effect, so the common arms skip it.
                if name == k.len {
                    Some((B::VecLen, Autoref::Ref, vec![], USIZE))
                } else if name == k.is_empty {
                    Some((B::VecIsEmpty, Autoref::Ref, vec![], BOOL))
                } else if name == k.push {
                    Some((B::VecPush, Autoref::RefMut, vec![elem], UNIT))
                } else if name == k.pop {
                    let opt = self.tys.mk_option(elem);
                    Some((B::VecPop, Autoref::RefMut, vec![], opt))
                } else if name == k.get {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecGet, Autoref::Ref, vec![USIZE], opt_ref))
                } else if name == k.first {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecFirst, Autoref::Ref, vec![], opt_ref))
                } else if name == k.last {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecLast, Autoref::Ref, vec![], opt_ref))
                } else if name == k.contains {
                    let r = self.tys.mk_ref(false, elem);
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
            (None, TyKind::Slice(_)) | (None, TyKind::Array(..)) => {
                if name == k.len {
                    Some((B::SliceLen, Autoref::Ref, vec![], USIZE))
                } else if name == k.is_empty {
                    Some((B::SliceIsEmpty, Autoref::Ref, vec![], BOOL))
                } else {
                    None
                }
            }
            (Some(BuiltinTy::Option), _) => {
                let inner = self.tys.adt_first_ty_arg(base).unwrap_or(ERROR);
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
            (Some(BuiltinTy::Chars), _) => {
                let opt = self.tys.mk_option(CHAR);
                if name == k.next {
                    Some((B::CharsNext, Autoref::RefMut, vec![], opt))
                } else if name == k.count {
                    Some((B::CharsCount, Autoref::None, vec![], USIZE))
                } else {
                    None
                }
            }
            (None, TyKind::Char) if name != k.to_string => {
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
                    let o = self.tys.mk_option(int(IntTy::U32));
                    Some((B::CharToDigit, Autoref::None, vec![int(IntTy::U32)], o))
                } else {
                    None
                }
            }
            (None, TyKind::Int(i)) => {
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
            (None, TyKind::Bool | TyKind::Char) if name == k.to_string => Some((B::ToString, Autoref::Ref, vec![], STRING)),
            (Some(BuiltinTy::Args), _) if name == k.count => Some((B::ArgsCount, Autoref::None, vec![], USIZE)),
            // Trait methods work on an integer of unknown type; inherent ones (pow, abs) do not.
            (None, k2) if k2.is_int_infer() && name == k.min => Some((B::Min, Autoref::None, vec![base], base)),
            (None, k2) if k2.is_int_infer() && name == k.max => Some((B::Max, Autoref::None, vec![base], base)),
            (None, k2) if k2.is_int_infer() && name == k.to_string => Some((B::ToString, Autoref::Ref, vec![], STRING)),
            (None, k2) if k2.is_int_infer() => {
                self.err(
                    "L0111",
                    name_span,
                    format!("cannot call method `{}` on an integer whose type is not known yet", self.name(name)),
                    "Add a type suffix such as `5i64`, or a type annotation on the variable.",
                );
                return ERROR;
            }
            (_, TyKind::Error) => return ERROR,
            _ => None,
        };
        match found {
            Some((b, autoref, params, ret)) => {
                if autoref != Autoref::None {
                    self.check_packed_borrow(recv, name_span);
                }
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
        let stringy = |t: Ty| self.tys.kind(t) == TyKind::Str || self.tys.is_string_ty(t);
        if lb == rb || !stringy(lb) || !stringy(rb) {
            return None;
        }
        string_eq_ok(ld, self.tys.is_string_ty(lb), rd, self.tys.is_string_ty(rb)).then_some((ld, rd))
    }

    /// Methods shared by `str` and `String` (through Deref). The receiver is always `&self`.
    fn str_method(&mut self, name: Sym) -> Option<(Builtin, Autoref, Vec<Ty>, Ty)> {
        use Builtin as B;
        let k = self.p.known;
        let chars = CHARS;
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
        // ARCH 2.12 run point: an operator on a non-scalar must know the left
        // operand type. The scalar path above and below needs no trait search.
        self.obl.run_before_structural();
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
            let stringy = |t: Ty| self.tys.kind(t) == TyKind::Str || self.tys.is_string_ty(t);
            if stringy(lb) && stringy(rb) && matches!(op, Eq | Ne) {
                if !string_eq_ok(ld, self.tys.is_string_ty(lb), rd, self.tys.is_string_ty(rb)) {
                    return bad(self);
                }
                self.set_res(e, Res::Bin { ld, rd });
                return BOOL;
            }
            // Equality allows `&T` against `&mut T`; ordering needs the same mutability.
            if !matches!(op, Eq | Ne) && self.ref_layers(lt) != self.ref_layers(rt) {
                return bad(self);
            }
            if ld != rd || !self.unify(lb, rb) {
                return bad(self);
            }
            let lb = self.deep(lb);
            let ok = match self.tys.kind(lb) {
                TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Str => true,
                k if k.is_int_infer() || self.tys.is_string_ty(lb) => true,
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
        if op == Add && self.tys.is_string_ty(self.resolve(lt)) {
            self.coerce_expr(rhs, rt, REF_STR);
            self.set_res(e, Res::Bin { ld: 0, rd: 0 });
            return STRING;
        }
        // Arithmetic and bit operations exist for `&T` operands, but not for `&mut T`.
        if matches!(lk, TyKind::Ref(_, Mut::Mut, _)) || matches!(rk, TyKind::Ref(_, Mut::Mut, _)) {
            return bad(self);
        }
        let (ld, li) = self.peel_one_ref(lt);
        let (rd, ri) = self.peel_one_ref(rt);
        let (lik, rik) = (self.kind(li), self.kind(ri));
        let int_like = |k: TyKind| matches!(k, TyKind::Int(_)) || k.is_int_infer();
        let result = match op {
            Add | Sub | Mul | Div | Rem if matches!(lik, TyKind::Float(_)) && matches!(rik, TyKind::Float(_)) => {
                if !self.unify(li, ri) {
                    return bad(self);
                }
                li
            }
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

    fn struct_lit(&mut self, e: ExprId, path: &[ast::PathSeg], fields: &[(Sym, Span, ExprId)], update: Option<ExprId>, span: Span) -> Ty {
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
            if let Some(u) = update {
                self.expr(u, None);
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
                    self.check_field_vis(a, fname, fspan);
                    self.expect_expr(fe, variant.fields[i].ty);
                }
                None => {
                    self.expr(fe, None);
                    self.err("L0103", fspan, format!("no field `{}` on this struct", self.name(fname)), "Check the field name.");
                }
            }
        }
        // Struct update: the fields not written come from the base value.
        if let Some(u) = update {
            if p.adt(a).is_enum {
                self.expr(u, None);
                self.err("L0110", span, "functional record update syntax requires a struct", "Set every field of the variant.");
                return ERROR;
            }
            let at = self.tys.adt_ty(a);
            self.expect_expr(u, at);
            return at;
        }
        let missing: Vec<String> =
            variant.fields.iter().zip(&seen).filter(|(_, s)| !**s).map(|(f, _)| self.name(f.name).to_string()).collect();
        if !missing.is_empty() {
            self.err(
                "L0107",
                span,
                format!("missing fields: {}", missing.join(", ")),
                "Set every field, or fill the rest from another value with `..base`.",
            );
        }
        self.tys.adt_ty(a)
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
            let ok = (matches!(self.kind(lt), TyKind::Int(_)) || self.kind(lt).is_int_infer()) && self.unify(lt, ht);
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
            _ if self.tys.is_chars_ty(self.resolve(t)) => CHAR,
            TyKind::Ref(r, m, inner) => {
                let elem = match self.kind(self.resolve(inner)) {
                    TyKind::Slice(elem) | TyKind::Array(elem, _) => Some(elem),
                    _ => self.tys.vec_elem(self.resolve(inner)),
                };
                match elem {
                    Some(elem) => self.tys.intern(TyKind::Ref(r, m, elem)),
                    None => {
                        let s = self.span(iter);
                        let tn = self.tn(t);
                        self.err("L0113", s, format!("cannot iterate over `{tn}`"), "Iterate over a range, `&vec`, or `&mut vec`.");
                        ERROR
                    }
                }
            }
            TyKind::Array(elem, _) => elem,
            _ if self.tys.vec_elem(self.resolve(t)).is_some() => {
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
                let elem_expected = expected.and_then(|t| self.tys.vec_elem(self.resolve(t)));
                let elem = elem_expected.unwrap_or_else(|| self.new_var(false));
                if repeat {
                    self.expect_expr(args[0], elem);
                    self.expect_expr(args[1], USIZE);
                    let elem = self.deep(elem);
                    if !has_clone(self.p, &self.tys, elem) && !matches!(self.kind(elem), TyKind::Infer(_)) {
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
                return self.tys.mk_vec(elem);
            }
            MacroKind::Assert => {
                if let Some(&c) = args.first() {
                    self.expect_expr(c, BOOL);
                }
                UNIT
            }
            MacroKind::AssertEq | MacroKind::AssertNe => {
                if args.len() < 2 {
                    self.err("L0105", span, "this macro takes 2 arguments", "Pass both values to compare.");
                } else {
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
                let ok = if *debug { has_debug(self.p, &self.tys, t) } else { has_display(&self.tys, t) || self.kind(t).is_int_infer() };
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
        // Format arguments are borrowed: a packed field may not be one.
        let borrowed_args: &[ExprId] = match kind {
            MacroKind::AssertEq | MacroKind::AssertNe => &args[..args.len().min(2)],
            MacroKind::Vec | MacroKind::Assert => &[],
            _ => args,
        };
        for &a in borrowed_args {
            self.check_packed_borrow(a, span);
        }
        result
    }

    // ---------- Patterns ----------

    /// Checks a pattern against a value of type `t`. Applies default binding modes.
    /// Records one pattern binding with the local type its mode gives it.
    fn bind_pattern_local(&mut self, pi: usize, name: Sym, mutable: bool, by_ref: bool, t: Ty, mode: BindMode, span: Span) {
        let mode = if by_ref { BindMode::Ref(mutable) } else { mode };
        let lty = match mode {
            BindMode::Move => t,
            BindMode::Ref(m) => self.tys.mk_ref(m, t),
        };
        let mutable_local = mutable && !by_ref;
        if mutable_local && mode != BindMode::Move {
            self.err(
                "L0122",
                span,
                "`mut` binding under a reference is not allowed here",
                "Remove `mut`, or match on the value instead of a reference.",
            );
        }
        let l = self.add_local(name, lty, mutable_local, span);
        self.out.pat_res[pi] = PatRes::Binding { local: l, mode };
    }

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
            || matches!(
                p.ast.pat(pat),
                Pat::TupleStruct { .. }
                    | Pat::Struct { .. }
                    | Pat::Path(_)
                    | Pat::Lit(_)
                    | Pat::Range { .. }
                    | Pat::Tuple(_)
                    | Pat::Slice { .. }
            );
        if structural {
            let mut derefs = 0;
            while let TyKind::Ref(_, m, inner) = self.tys.kind(t) {
                // A string literal pattern matches `&str` directly.
                if matches!(p.ast.pat(pat), Pat::Lit(l) if matches!(p.ast.expr(*l), Expr::Str(_))) && self.kind(inner) == TyKind::Str {
                    break;
                }
                derefs += 1;
                mode = match mode {
                    BindMode::Ref(false) => BindMode::Ref(false),
                    _ => BindMode::Ref(m.is_mut()),
                };
                t = self.resolve(inner);
            }
            self.out.pat_derefs[pi] = derefs;
        }
        self.out.pat_ty[pi] = t;
        if let Some(is_some) = opt {
            let inner = self.new_var(false);
            let ot = self.tys.mk_option(inner);
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
        // A plain name that resolves to a const item is a const pattern, not
        // a binding (unless a local binding shadows the name).
        if let Pat::Binding { name, mutable: false, by_ref: false } = p.ast.pat(pat)
            && self.lookup(*name, span.ctxt).is_none()
            && let Some(&idx) = p.const_names.get(name)
        {
            let c = &p.consts[idx as usize];
            if !matches!(
                c.value,
                crate::ty::consteval::ConstValue::Int(_)
                    | crate::ty::consteval::ConstValue::Bool(_)
                    | crate::ty::consteval::ConstValue::Char(_)
            ) {
                self.errs.push(unsupported(span, "non-scalar const patterns"));
                return;
            }
            let ct = c.ty;
            if !self.unify(ct, t) {
                self.mismatch(span, t, ct);
                return;
            }
            self.out.pat_res[pi] = PatRes::ConstItem(idx);
            return;
        }
        match p.ast.pat(pat) {
            Pat::Wild => {}
            Pat::Binding { name, mutable, by_ref } => {
                self.bind_pattern_local(pi, *name, *mutable, *by_ref, t, mode, span);
            }
            Pat::At { name, mutable, by_ref, inner } => {
                self.bind_pattern_local(pi, *name, *mutable, *by_ref, t, mode, span);
                self.pattern_mode(*inner, t, mode, in_match);
            }
            Pat::Ref { mutable, inner } => match self.kind(t) {
                TyKind::Ref(_, m, inner_ty) => {
                    if *mutable && !m.is_mut() {
                        self.err(
                            "L0110",
                            span,
                            "pattern requires `&mut`, but the matched type is a shared reference",
                            "Use `&` in the pattern, or match on a `&mut` value.",
                        );
                    }
                    // An explicit `&` resets the default binding mode inside it.
                    self.pattern_mode(*inner, inner_ty, BindMode::Move, in_match);
                }
                TyKind::Error => self.pattern_mode(*inner, ERROR, mode, in_match),
                _ => {
                    let tn = self.tn(t);
                    self.err(
                        "L0110",
                        span,
                        format!("reference pattern cannot match a value of type `{tn}`"),
                        "Match on a reference, or remove the `&`.",
                    );
                    self.pattern_mode(*inner, ERROR, mode, in_match);
                }
            },
            Pat::Lit(l) => {
                let lt = self.expr(*l, Some(t));
                if !self.unify(lt, t) {
                    self.mismatch(span, t, lt);
                }
                if !in_match {
                    self.errs.push(unsupported(span, "refutable patterns here"));
                }
            }
            Pat::Range { lo, hi, .. } => {
                // The parser only builds two-bound ranges today; a half-open
                // range checks its one bound the same way.
                let mut bound_tys = Vec::new();
                if let Some(lo) = lo {
                    bound_tys.push((*lo, self.expr(*lo, Some(t))));
                }
                if let Some(hi) = hi {
                    bound_tys.push((*hi, self.expr(*hi, Some(t))));
                }
                if let [(lo_e, _), (hi_e, _)] = bound_tys[..]
                    && let (Some(lo_v), Some(hi_v)) = (self.const_scalar(lo_e), self.const_scalar(hi_e))
                    && lo_v > hi_v
                {
                    self.err(
                        "L0119",
                        span,
                        "lower range bound is greater than the upper bound",
                        "Swap the bounds, or fix the values. An empty range pattern never matches.",
                    );
                }
                if bound_tys.iter().any(|&(_, bt)| !self.unify(bt, t))
                    || !(matches!(self.kind(t), TyKind::Int(_) | TyKind::Char) || self.kind(t).is_int_infer())
                {
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
                let adt_ty = self.tys.adt_ty(a);
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
                        if variant.shape != VariantShape::Tuple {
                            self.err(
                                "L0110",
                                span,
                                format!("this variant has {} field(s)", variant.fields.len()),
                                "Match every field, or use `_` for the ones you do not need.",
                            );
                            return;
                        }
                        let Some(mapped) = map_tuple_elems(p.ast, elems, variant.fields.len()) else {
                            self.err(
                                "L0110",
                                span,
                                format!("this variant has {} field(s)", variant.fields.len()),
                                "Match every field, use `_`, or skip the middle with `..`.",
                            );
                            return;
                        };
                        for (i, sub) in mapped {
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
                                    self.check_field_vis(a, fname, p.ast.pat_span(sub));
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
            Pat::Tuple(elems) => {
                if elems.is_empty() {
                    if !self.unify(t, UNIT) {
                        self.mismatch(span, t, UNIT);
                    }
                    return;
                }
                let elem_tys: Vec<Ty> = (0..elems.len()).map(|_| self.new_var(false)).collect();
                // A rest element means the arity is not the written count; take
                // element types from the scrutinee tuple when it is known.
                let known: Option<Vec<Ty>> = match self.kind(t) {
                    TyKind::Tuple(ts) => Some(self.tys.tys_of(ts).to_vec()),
                    _ => None,
                };
                match known {
                    Some(kt) => {
                        let Some(mapped) = map_tuple_elems(p.ast, elems, kt.len()) else {
                            self.err(
                                "L0110",
                                span,
                                format!("this tuple has {} element(s)", kt.len()),
                                "Match every element, use `_`, or skip the middle with `..`.",
                            );
                            return;
                        };
                        for (i, sub) in mapped {
                            self.pattern_mode(sub, kt[i], mode, in_match);
                        }
                    }
                    None => {
                        if elems.iter().any(|&s| matches!(p.ast.pat(s), Pat::Rest)) {
                            self.err(
                                "L0110",
                                span,
                                "cannot use `..` when the tuple type is not known",
                                "Add a type annotation, or match every element.",
                            );
                            return;
                        }
                        for (i, &sub) in elems.iter().enumerate() {
                            self.pattern_mode(sub, elem_tys[i], mode, in_match);
                        }
                        let ts = self.tys.intern_tys(&elem_tys);
                        let tt = self.tys.intern(TyKind::Tuple(ts));
                        if !self.unify(tt, t) {
                            self.mismatch(span, t, tt);
                        }
                    }
                }
            }
            // A bare `..` only appears inside tuple and slice forms, which map
            // it away before recursing; anywhere else it is a syntax error.
            Pat::Rest => {
                self.err("L0110", span, "`..` can only be used in tuple and slice patterns", "Remove the `..`.");
            }
            Pat::Slice { prefix, middle, suffix } => {
                let (elem, arr_len) = match self.kind(t) {
                    TyKind::Array(elem, c) => {
                        let n = match self.tys.const_kind(c) {
                            ConstKind::Int(n) => Some(n as u64),
                            _ => None,
                        };
                        (elem, n)
                    }
                    TyKind::Slice(elem) => (elem, None),
                    TyKind::Error => {
                        for &sub in prefix.iter().chain(suffix.iter()) {
                            self.pattern_mode(sub, ERROR, mode, in_match);
                        }
                        if let Some(mid) = middle {
                            if !matches!(p.ast.pat(*mid), Pat::Rest) {
                                self.pattern_mode(*mid, ERROR, mode, in_match);
                            }
                        }
                        return;
                    }
                    _ => {
                        let tn = self.tn(t);
                        self.err(
                            "L0110",
                            span,
                            format!("slice pattern cannot match a value of type `{tn}`"),
                            "Match on an array or a slice, for example `&value[..]`.",
                        );
                        for &sub in prefix.iter().chain(suffix.iter()) {
                            self.pattern_mode(sub, ERROR, mode, in_match);
                        }
                        return;
                    }
                };
                let fixed = (prefix.len() + suffix.len()) as u64;
                if let Some(n) = arr_len {
                    let bad = if middle.is_some() { fixed > n } else { fixed != n };
                    if bad {
                        self.err(
                            "L0110",
                            span,
                            format!("pattern requires {fixed} element(s) but the array has {n}"),
                            "Change the pattern length, or skip the middle with `..`.",
                        );
                        return;
                    }
                }
                for &sub in prefix.iter().chain(suffix.iter()) {
                    self.pattern_mode(sub, elem, mode, in_match);
                }
                if let Some(mid) = middle {
                    match p.ast.pat(*mid) {
                        Pat::Rest | Pat::Wild => {}
                        Pat::Binding { by_ref: true, .. } => {
                            let st = self.tys.intern(TyKind::Slice(elem));
                            self.pattern_mode(*mid, st, mode, in_match);
                        }
                        Pat::Binding { .. } => match (mode, arr_len) {
                            (BindMode::Move, Some(n)) => {
                                let c = self.tys.intern_const(ConstKind::Int((n - fixed) as u128));
                                let at = self.tys.intern(TyKind::Array(elem, c));
                                self.pattern_mode(*mid, at, BindMode::Move, in_match);
                            }
                            (BindMode::Move, None) => {
                                self.err(
                                    "L0110",
                                    span,
                                    "cannot bind the middle of a slice pattern by value",
                                    "Match on a reference, or use `ref` for the binding.",
                                );
                            }
                            (BindMode::Ref(_), _) => {
                                let st = self.tys.intern(TyKind::Slice(elem));
                                self.pattern_mode(*mid, st, mode, in_match);
                            }
                        },
                        _ => {
                            let st = self.tys.intern(TyKind::Slice(elem));
                            self.pattern_mode(*mid, st, mode, in_match);
                        }
                    }
                }
            }
            Pat::Paren(inner) => self.pattern_mode(*inner, t, mode, in_match),
            // AST v2 pattern forms the parser still rejects.
            Pat::QPath { .. } | Pat::MacroCall(_) => {}
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
        let msg = match self.tys.local_adt(base) {
            Some(a) if p.adt(a).is_enum => {
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
            _ if self.kind(base) == TyKind::Error => return,
            _ => "non-exhaustive match".to_string(),
        };
        self.err("L0115", span, msg, "Add arms for the missing cases, or add a `_ => ...` arm.");
    }

    /// Follows `@`, parenthesized, and reference wrappers to the pattern they
    /// wrap. For exhaustiveness only: a reference wrapper adds no condition.
    fn pat_unwrap(&self, mut pat: PatId) -> PatId {
        loop {
            match self.p.ast.pat(pat) {
                Pat::At { inner, .. } | Pat::Paren(inner) | Pat::Ref { inner, .. } => pat = *inner,
                _ => return pat,
            }
        }
    }

    fn pres(&self, pat: PatId) -> PatRes {
        // An `@` or parenthesized wrapper takes the resolution of what it wraps
        // for exhaustiveness, when the wrapped pattern has a variant or
        // Option resolution of its own.
        let own = self.out.pat_res[(pat.0 - self.out.pat_base) as usize];
        match self.p.ast.pat(pat) {
            Pat::At { inner, .. } | Pat::Paren(inner) | Pat::Ref { inner, .. } => match self.pres(*inner) {
                r @ (PatRes::Variant(..) | PatRes::Opt(_)) => r,
                _ => own,
            },
            _ => own,
        }
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
                        .filter_map(|&y| match (self.pres(y), p.ast.pat(self.pat_unwrap(y))) {
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
                match p.ast.pat(self.pat_unwrap(y)) {
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
            Pat::Tuple(elems) => elems.iter().all(|&s| matches!(p.ast.pat(s), Pat::Rest) || self.irrefutable(s)),
            Pat::Ref { inner, .. } => self.irrefutable(*inner),
            Pat::At { inner, .. } => self.irrefutable(*inner),
            Pat::Slice { prefix, suffix, .. } => {
                let t = self.out.pat_ty[(pat.0 - self.out.pat_base) as usize];
                let arr_ok = match self.kind(t) {
                    TyKind::Array(_, c) => match self.tys.const_kind(c) {
                        ConstKind::Int(n) => (prefix.len() + suffix.len()) as u128 <= n,
                        _ => false,
                    },
                    _ => prefix.is_empty() && suffix.is_empty(),
                };
                arr_ok && prefix.iter().chain(suffix.iter()).all(|&s| self.irrefutable(s))
            }
            Pat::Paren(inner) => self.irrefutable(*inner),
            Pat::Rest => true,
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
        // ARCH 2.4 run point: the obligation queue runs at body end to a fixpoint.
        // Anything left there is an annotation error, never a silent default.
        self.obl.run_at_body_end();
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
                let max = if neg && it.signed() { it.max128() + 1 } else { it.max128() };
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
            TyKind::Ref(_, _, e) | TyKind::Slice(e) | TyKind::Array(e, _) => self.has_error_kind(e),
            TyKind::Adt(_, a) => (0..self.tys.args(a).len()).any(|i| match self.tys.args(a)[i].as_ty() {
                Some(e) => self.has_error_kind(e),
                None => false,
            }),
            TyKind::Tuple(ts) => {
                let n = self.tys.tys_of(ts).len();
                (0..n).any(|i| {
                    let e = self.tys.tys_of(ts)[i];
                    self.has_error_kind(e)
                })
            }
            _ => false,
        }
    }
}

/// The const evaluator's context over a body being checked: names resolve
/// through the program tables and the Binding query, as in body checking.
struct CheckCx<'x, 'p, 'a> {
    cx: &'x mut Ctx<'p, 'a>,
}

impl<'a, 'p> crate::ty::consteval::ConstCx<'a> for CheckCx<'_, 'p, 'a> {
    type Tys = Tys<'p>;

    fn tys(&mut self) -> &mut Tys<'p> {
        &mut self.cx.tys
    }
    fn tys_ref(&self) -> &Tys<'p> {
        &self.cx.tys
    }
    fn ast(&self) -> &'a ast::Ast {
        self.cx.p.ast
    }
    fn sym_text(&self, s: Sym) -> &str {
        self.cx.name(s)
    }
    fn const_item(&mut self, name: Sym) -> Option<crate::ty::consteval::TypedValue> {
        let &i = self.cx.p.const_names.get(&name)?;
        let c = &self.cx.p.consts[i as usize];
        Some((c.value.clone(), c.ty))
    }
    fn static_item(&mut self, name: Sym) -> Option<(u32, Ty)> {
        self.cx.p.static_names.get(&name).map(|&i| (i, self.cx.p.statics[i as usize].ty))
    }
    fn call_target(&mut self, callee: ExprId) -> crate::ty::consteval::CallTarget {
        use crate::ty::consteval::{CallTarget, ConstFnBody};
        let p = self.cx.p;
        let ast::Expr::Path(segs) = p.ast.expr(callee) else { return CallTarget::Unknown };
        let last = segs[segs.len() - 1].name;
        let ltext = self.cx.name(last).to_string();
        if matches!(ltext.as_str(), "size_of" | "align_of") {
            let args = segs[segs.len() - 1].type_args();
            if args.len() == 1 {
                let t = self.cx.resolve_written(args[0]);
                return if ltext == "size_of" { CallTarget::SizeOf(t) } else { CallTarget::AlignOf(t) };
            }
            return CallTarget::Unknown;
        }
        if segs.len() == 1 && last == p.known.Some {
            return CallTarget::VariantCtor { adt: AdtId(u32::MAX), variant: 1, ty: ERROR };
        }
        let span = self.cx.span(callee);
        let fid = if segs.len() == 1 {
            if self.cx.lookup(last, span.ctxt).is_some() {
                return CallTarget::Unknown;
            }
            self.cx.binding_fn(last)
        } else {
            match self.cx.resolve_assoc(segs, span) {
                Some(Res::Fn(f)) => Some(f),
                Some(Res::Variant(a, v)) => {
                    return CallTarget::VariantCtor { adt: a, variant: v, ty: self.cx.tys.adt_ty(a) };
                }
                Some(Res::Builtin(_)) => return CallTarget::NonConst,
                _ => None,
            }
        };
        if let Some(f) = fid {
            let info = p.fn_info(f);
            if !info.is_const {
                return CallTarget::NonConst;
            }
            let Some(body) = info.def.body else { return CallTarget::NonConst };
            if info.self_kind.is_some() {
                return CallTarget::Unknown;
            }
            let params: Vec<(Sym, bool, Option<ast::PatId>)> = info.def.params.iter().map(|pp| (pp.name, pp.mutable, pp.pat)).collect();
            return CallTarget::ConstFn(ConstFnBody { params, param_tys: info.params.clone(), ret: info.ret, body });
        }
        if let Some(a) = self.cx.tuple_struct_ctor(last)
            && segs.len() == 1
        {
            return CallTarget::VariantCtor { adt: a, variant: 0, ty: self.cx.tys.adt_ty(a) };
        }
        if segs.len() == 2 && matches!(self.cx.name(segs[0].name), "String" | "Vec") {
            return CallTarget::NonConst;
        }
        CallTarget::Unknown
    }
    fn unit_variant(&mut self, segs: &[ast::PathSeg], expected: Option<Ty>) -> Option<(AdtId, u32, Ty)> {
        let p = self.cx.p;
        if segs.len() == 1 && segs[0].name == p.known.None {
            let elem = expected.and_then(|t| self.cx.tys.option_elem(t)).unwrap_or(ERROR);
            let ty = self.cx.tys.mk_option(elem);
            return Some((AdtId(u32::MAX), 0, ty));
        }
        let (adt, variant) = variant_of(p, segs)?;
        if p.adt(adt).variants[variant as usize].shape != VariantShape::Unit {
            return None;
        }
        Some((adt, variant, self.cx.tys.adt_ty(adt)))
    }
    fn struct_target(&mut self, path: &[ast::PathSeg]) -> Option<(AdtId, u32, Ty)> {
        let (adt, variant) = variant_of(self.cx.p, path)?;
        Some((adt, variant, self.cx.tys.adt_ty(adt)))
    }
    fn pattern_variant(&mut self, segs: &[ast::PathSeg]) -> Option<(AdtId, u32)> {
        variant_of(self.cx.p, segs)
    }
    fn variant_fields(&self, adt: AdtId, variant: u32) -> Vec<(Sym, Ty)> {
        if adt.0 == u32::MAX {
            return Vec::new();
        }
        self.cx.p.adt(adt).variants[variant as usize].fields.iter().map(|f| (f.name, f.ty)).collect()
    }
    fn resolve_ty(&mut self, t: ast::TyId) -> Ty {
        self.cx.resolve_written(t)
    }
    fn layout(&mut self, t: Ty) -> Option<crate::ty::layout::Layout> {
        let p: &Program<'_> = self.cx.p;
        let t = self.cx.deep(t);
        crate::ty::layout::layout_of_ty(&self.cx.tys, p, t).ok()
    }
    fn discriminant(&self, adt: AdtId, variant: u32) -> i128 {
        self.cx.p.adt(adt).variants[variant as usize].disc
    }
}

/// The (Adt, variant) a path denotes in the compat tables.
fn variant_of(p: &Program<'_>, segs: &[ast::PathSeg]) -> Option<(AdtId, u32)> {
    if segs.len() == 1 {
        let &a = p.type_names.get(&segs[0].name)?;
        if p.adt(a).is_enum {
            return None;
        }
        return Some((a, 0));
    }
    if segs.len() == 2 {
        let &a = p.type_names.get(&segs[0].name)?;
        let v = p.adt(a).variants.iter().position(|v| v.name == segs[1].name)?;
        return Some((a, v as u32));
    }
    None
}
