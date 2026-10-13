// Type checking for one function body. Inference is local to the body: unification plus
// integer-literal variables. Output is a set of side tables that lowering reads.
// Signature collection runs before body checking, in `collect`.
pub mod closure;
pub mod collect;
pub mod generics;
pub mod method;
pub mod obligations;
pub mod picks;

use crate::ast::{self, BinOp, Expr, ExprId, FmtKind, FmtPiece, FmtSpec, ItemKind, MacroKind, Pat, PatId, Stmt, UnOp};
use crate::check::collect::*;
use crate::check::generics::Scope;
use crate::diag::{CtxtId, Diag, Span, not_yet, unsupported};
use crate::driver::graph::{BindingRes, Fingerprint, Head, Namespace, Reads, ReceiverForm, SigOf};
use crate::intern::{Interner, Sym};
use crate::traits::solve::{Selection, SolveCx, Solver};
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
    WrappingDiv,
    WrappingRem,
    WrappingNeg,
    WrappingPow,
    WrappingShl,
    WrappingShr,
    WrappingAbs,
    CheckedAdd,
    CheckedSub,
    CheckedMul,
    CheckedDiv,
    CheckedRem,
    CheckedNeg,
    CheckedAbs,
    CheckedPow,
    CheckedShl,
    CheckedShr,
    SaturatingAdd,
    SaturatingSub,
    SaturatingMul,
    SaturatingDiv,
    SaturatingNeg,
    SaturatingAbs,
    SaturatingPow,
    OverflowingAdd,
    OverflowingSub,
    OverflowingMul,
    OverflowingDiv,
    OverflowingRem,
    OverflowingNeg,
    OverflowingAbs,
    OverflowingPow,
    OverflowingShl,
    OverflowingShr,
    CountOnes,
    CountZeros,
    LeadingZeros,
    TrailingZeros,
    LeadingOnes,
    TrailingOnes,
    RotateLeft,
    RotateRight,
    SwapBytes,
    ReverseBits,
    DivEuclid,
    RemEuclid,
    Signum,
    IsPositive,
    IsNegative,
    IsPowerOfTwo,
    FloatSqrt,
    FloatPowi,
    FloatPowf,
    FloatExp,
    FloatLn,
    FloatLog,
    FloatLog2,
    FloatLog10,
    FloatMulAdd,
    FloatFloor,
    FloatCeil,
    FloatRound,
    FloatTrunc,
    FloatFract,
    FloatAbs,
    FloatSignum,
    FloatRecip,
    FloatMin,
    FloatMax,
    FloatIsNan,
    FloatIsInfinite,
    FloatIsFinite,
    FloatIsSignPositive,
    FloatIsSignNegative,
    FloatToBits,
    FloatCopysign,
    F32FromBits,
    F64FromBits,
    CharLenUtf8,
    CharLenUtf16,
    CharIsAscii,
    CharIsAsciiPunctuation,
    CharIsAsciiGraphic,
    CharIsAsciiHexdigit,
    CharIsAsciiControl,
    CharIsDigitRadix,
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
    VecCapacity,
    VecReserve,
    VecReserveExact,
    VecShrinkToFit,
    VecShrinkTo,
    VecSwapRemove,
    VecAppend,
    VecExtendFromSlice,
    VecSplitOff,
    VecResize,
    VecDedup,
    VecReverse,
    VecFirstMut,
    VecLastMut,
    VecGetMut,
    VecAsSlice,
    VecAsMutSlice,
    SliceToVec,
    VecFrom,
    MemDrop,
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
    /// `Ok` and `Err` used as constructors.
    ResOk,
    ResErr,
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
    /// `size_of_val` of an unsized value (`[T]` or `str`): the length
    /// builtin for the argument times the element size (1 for `str`).
    SizeOfVal {
        len: Builtin,
        elem: u64,
    },
    /// A comparison trait method (`partial_cmp`, `cmp`, `eq`, `lt`,
    /// and kin) on a scalar receiver: lowering emits the scalar
    /// comparison directly, as the binary operators do. `derefs`
    /// counts autoderefs from the receiver to the scalar.
    PrimCmp {
        kind: PrimCmpKind,
        derefs: u8,
    },
    /// A binary operator through an operator trait: the trait
    /// method to call (a template until mono rewrites it through
    /// `Checked::generic_args`), with operand deref counts.
    TraitBin {
        f: LocalDefId,
        ld: u8,
        rd: u8,
    },
    /// A numeric `From::from` call, lowered as a cast to the
    /// call's type. Widening conversions only (checked).
    FromCast,
    /// A scalar `Default::default()` call, lowered as the zero
    /// value of the call's type.
    DefaultVal,
    /// A `for` loop through `IntoIterator`: the `into_iter` and
    /// `next` methods to call (templates until mono rewrites
    /// them through `Checked::generic_args`).
    ForTrait {
        into_iter: LocalDefId,
        next: LocalDefId,
    },
    /// A call through a function pointer value in the callee expression.
    Indirect,
    /// A `?` with no error conversion: on `Option`, or on `Result`
    /// whose error type already matches the enclosing return type.
    TryPlain,
    /// A `?` on `Result` whose error converts through this
    /// `From::from` method (a template until mono rewrites it
    /// through `Checked::generic_args`; `LocalDefId(u32::MAX)` when
    /// only param evidence proves it in a template body).
    TryFrom(LocalDefId),
    /// A `?` on `Result` whose error converts by a numeric
    /// widening cast (the `From` impls with no user fn).
    TryCast,
    /// A `?` on `Result` whose error converts through the builtin
    /// `From<&str> for String` or `From<&String> for String`: a
    /// copy into a fresh String with no user fn behind it.
    TryStringFrom,
    /// A call of a closure value (ARCH 2.9). `kind` is the Fn trait
    /// the call goes through (an `FnOnce` call consumes the callee),
    /// `derefs` the reference layers peeled off the callee. Lowering
    /// finds the body fn from the callee's closure type.
    ClosureCall {
        kind: closure::ClosureKind,
        derefs: u8,
    },
}

/// Which scalar comparison a `Res::PrimCmp` call computes. The
/// Adt is `core::cmp::Ordering`'s session-local index (variants
/// Less, Equal, Greater in that order).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PrimCmpKind {
    /// `PartialOrd::partial_cmp` -> `Option<Ordering>`.
    Partial(AdtId),
    /// `Ord::cmp` -> `Ordering`.
    Total(AdtId),
    /// `eq`/`ne`/`lt`/`le`/`gt`/`ge` -> `bool`, the binary comparison.
    Op(ast::BinOp),
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

/// What a lone pattern identifier resolves to (see `Ctx::pat_ident`).
enum PatIdent {
    Const(u32),
    Static,
    Variant(AdtId, u32),
    Other,
}

#[derive(Clone, Copy, Debug)]
pub enum PatRes {
    None,
    /// A const item used as a pattern, by index into `Program::consts`.
    ConstItem(u32),
    /// A primitive associated const used as a pattern (`i64::MAX`):
    /// its value (the pattern type carries the width).
    PrimConst(i128),
    /// A body-local const used as a pattern, by index into `Program::body_consts`.
    BodyConst(u32),
    Binding {
        local: u32,
        mode: BindMode,
    },
    Variant(AdtId, u32),
    /// `Some(..)` (true) or `None` (false).
    Opt(bool),
    /// `Ok(..)` (true) or `Err(..)` (false).
    Res(bool),
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
    /// The const value of a pattern that is a primitive associated
    /// const (`u8::MAX => ..`), parallel to `pat_res`.
    pub pat_const: Vec<Option<crate::ty::consteval::ConstValue>>,
    /// Number of implicit derefs before matching each pattern (default binding modes).
    pub pat_derefs: Vec<u8>,
    /// Generic arguments of each generic call or method call, by
    /// expression index (empty for plain calls), after zonking.
    /// Lowering resolves the template in the call's `Res` plus
    /// these args to a mono instance.
    pub generic_args: Vec<Vec<GenericArg>>,
    /// Instance requests found while checking: (template,
    /// zonked args in this body's store). Mono lifts and
    /// materializes them; the driver never reads this.
    pub inst_requests: Vec<(LocalDefId, Vec<GenericArg>)>,
    /// Trait picks of a template check (see `picks.rs`), in check
    /// order. Mono stores them for the body's other checks.
    pub trait_picks: Vec<(ExprId, picks::TraitPick)>,
    pub locals: Vec<LocalInfo>,
    /// Locals bound to the function parameters, in order (including `self`).
    pub param_locals: Vec<u32>,
    /// Every cross-item node this body read through a query function
    /// (docs/ARCH.md section 8.2). Stored with the result; nothing consumes
    /// it for invalidation yet (S7 is record-only).
    pub reads: Reads,
    /// The closure expressions of this body, in check order, zonked.
    pub closures: Vec<closure::ClosureInfo>,
    /// Every closure call and the Fn trait it goes through. Mono keeps
    /// the template's answers for its instances (`template_calls`).
    pub closure_calls: Vec<(ExprId, closure::ClosureKind)>,
    /// True when this is a closure body fn whose parent failed to
    /// check: the parent reports the errors, lowering emits nothing.
    pub poisoned: bool,
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
    pub fn pat_const(&self, p: PatId) -> Option<&crate::ty::consteval::ConstValue> {
        self.pat_const[(p.0 - self.pat_base) as usize].as_ref()
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
    /// Items declared in enclosing blocks, keyed like locals by name and
    /// hygiene context, holding stmt item indexes.
    item_scopes: Vec<Vec<((Sym, CtxtId), u32)>>,
    loops: Vec<LoopCtx>,
    errs: Vec<Diag>,
    negated_lits: Vec<ExprId>,
    /// The trait obligation queue (ARCH 2.4), run at the fixed
    /// points in `run_obligations`.
    obl: obligations::Obligations,
    /// This fn's own local id, for its scope and env.
    fid: LocalDefId,
    /// Selection state (memos, cycle stack) for this body.
    solver: Solver,
    /// Rollback trail of variable bindings, for solver probes.
    trail: Vec<u32>,
    /// The scope body annotations resolve under (with `_` markers on).
    body_scope: Scope,
    /// Generic call sites to turn into instance requests at
    /// finish: (expression index, template, args before zonking).
    generic_sites: Vec<(usize, LocalDefId, Vec<GenericArg>)>,
    /// Trait method calls whose impl is selected at finish (see
    /// `method::confirm_deferred`).
    deferred_methods: Vec<method::DeferredMethod>,
    /// Operators whose result waits on an `Output` obligation because
    /// an operand was a general variable at their first check (see
    /// `binary`).
    deferred_binops: Vec<ExprId>,
    /// Format arguments whose type was still a variable when
    /// the format check ran: (type, spec, span). The format test
    /// re-runs at finish (W-TRAITS-CORE).
    deferred_fmt: Vec<(Ty, FmtSpec, Span)>,
    /// Element types a builtin Vec or slice method needs to be
    /// Clone (`extend_from_slice`, `resize`, `to_vec`), re-tested
    /// at finish like the format traits: the element type can
    /// still be a variable at the call.
    deferred_clone: Vec<(Ty, Span)>,
    /// Element types a builtin Vec method needs to be PartialEq
    /// (`contains`, `dedup`), re-tested at finish as above.
    deferred_eq: Vec<(Ty, Span)>,
    /// True while normalization runs inside `unify`, to keep
    /// projection normalization from recursing into itself.
    in_norm: bool,
    /// Const inference variables (from `generics::INFER_MARKER_BASE`)
    /// to the consts they bound to.
    const_bindings: std::collections::HashMap<u32, ConstId>,
    next_const_id: u32,
    /// Closures checked so far in this body (see `check::closure`).
    closures: Vec<closure::ClosureInfo>,
    /// Return types of the closure bodies being checked, innermost last:
    /// `return` inside a closure returns from the closure.
    closure_rets: Vec<Ty>,
    /// This body's closure expressions in token order, for their defs.
    closure_order: Option<Vec<ExprId>>,
    /// Scalar operators checked while both operand types were still
    /// open (a closure's `|a, b| a + b`): (expr, op, operand type).
    /// Lowering emits the builtin operator, so the types must turn out
    /// scalar by body end (see `finish`).
    open_binops: Vec<(ExprId, BinOp, Ty)>,
}

/// The module a body checks in: the module of the def that owns
/// the body, exactly as a non-generic body in that module sees it
/// (ARCH 1.5). AST fns read `fn_module` by `LocalDefId`. Fns mono
/// appends are past that vec: an instance takes its template's
/// module, and a trait-default template (or a template with no
/// local form) takes the module its def was defined in. Closure
/// body fns never reach here (`check_fn` checks them as their
/// parent). Without resolver tables every body is in the root.
fn defining_module(p: &Program, fid: LocalDefId) -> crate::ty::defs::ModuleId {
    let root = crate::ty::defs::ROOT_MODULE;
    let Some(tables) = &p.resolved else { return root };
    // A def's defining module from the resolver table. Associated
    // defs (trait methods) are not module items, so the walk
    // climbs to their parent def (the trait), which is one.
    let module_of_def = |p: &Program, mut def: crate::def::DefId| -> crate::ty::defs::ModuleId {
        for _ in 0..4 {
            if let Some(info) = tables.def_info.get(&def) {
                return info.module;
            }
            // The parent def, or (trait methods carry none) the
            // trait the index files the def under.
            let parent = p.defs.parent_of(def).or_else(|| p.gx.index.trait_of_method(def)).or_else(|| p.gx.index.trait_of_assoc(def));
            let Some(parent) = parent else { break };
            def = parent;
        }
        root
    };
    let mut cur = fid;
    // Instances name their template directly, so this walks at
    // most one hop in practice; the bound guards only against a
    // malformed table.
    for _ in 0..8 {
        if let Some(m) = tables.fn_module.get(cur.0 as usize) {
            return *m;
        }
        if let Some(info) = p.gx.instances.get(&cur) {
            if let Some(template) = info.template_local {
                cur = template;
                continue;
            }
            return module_of_def(p, info.template_def);
        }
        return p.fn_defs.get(cur.0 as usize).map_or(root, |&def| module_of_def(p, def));
    }
    root
}

/// Type-checks one function body. A closure body fn checks as its
/// parent fn (closures share their parent's inference); the parent's
/// own entry reports any errors, so the closure fn reports none and
/// marks the result poisoned instead.
pub fn check_fn<'p, 'a>(p: &'p Program<'a>, fid: LocalDefId) -> (Checked<'p>, Vec<Diag>) {
    if let Some(def) = p.gx.closure_fns.get(&fid)
        && let Some(entry) = p.gx.closures.get(def)
    {
        let (mut ck, errs) = check_fn(p, entry.parent);
        ck.poisoned = !errs.is_empty();
        return (ck, Vec::new());
    }
    let f = p.fn_info(fid);
    let def = f.def;
    let n_exprs = (def.exprs.1 - def.exprs.0) as usize;
    let n_pats = (def.pats.1 - def.pats.0) as usize;
    let mut cx = Ctx {
        p,
        f,
        module: defining_module(p, fid),
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
            pat_const: vec![None; n_pats],
            pat_derefs: vec![0; n_pats],
            generic_args: vec![Vec::new(); n_exprs],
            inst_requests: Vec::new(),
            trait_picks: Vec::new(),
            locals: Vec::new(),
            param_locals: Vec::new(),
            reads: if p.record_reads { Reads::new() } else { Reads::off() },
            closures: Vec::new(),
            closure_calls: Vec::new(),
            poisoned: false,
        },
        scopes: Vec::new(),
        item_scopes: Vec::new(),
        loops: Vec::new(),
        errs: Vec::new(),
        negated_lits: Vec::new(),
        obl: obligations::Obligations::new(),
        fid,
        solver: Solver::new(),
        trail: Vec::new(),
        body_scope: {
            let mut sc = p.gx.fn_scopes.get(fid.0 as usize).map_or_else(Scope::default, |fs| fs.scope.clone());
            sc.infer_cell = Some(std::sync::Arc::new(std::sync::atomic::AtomicU32::new(generics::INFER_MARKER_BASE)));
            if sc.self_ty.is_none() {
                sc.self_ty = f.owner.map(|a| p.tys.get_adt_ty(a).expect("ADT types are interned during collection"));
            }
            sc
        },
        generic_sites: Vec::new(),
        deferred_methods: Vec::new(),
        deferred_binops: Vec::new(),
        deferred_fmt: Vec::new(),
        deferred_clone: Vec::new(),
        deferred_eq: Vec::new(),
        in_norm: false,
        const_bindings: std::collections::HashMap::new(),
        next_const_id: generics::INFER_MARKER_BASE,
        closures: Vec::new(),
        closure_rets: Vec::new(),
        closure_order: None,
        open_binops: Vec::new(),
    };
    if let Some(sibs) = p.fn_siblings.get(&fid) {
        let layer: Vec<((Sym, CtxtId), u32)> = sibs
            .iter()
            .filter_map(|&si| {
                let name = match &p.ast.stmt_items[si as usize].kind {
                    ItemKind::Fn(d) => Some((d.name, d.name_span.ctxt)),
                    ItemKind::Const(c) => c.name.map(|n| (n, c.name_span.ctxt)),
                    ItemKind::Static(st) => Some((st.name, st.name_span.ctxt)),
                    _ => None,
                };
                name.map(|n| (n, si))
            })
            .collect();
        cx.item_scopes.push(layer);
    }
    // A template body keeps its `Param` types: the store answers
    // the structural trait queries on them from the env (`Tys::env`).
    cx.tys.env = p.gx.fn_scopes.get(fid.0 as usize).map_or(&[], |fs| fs.env.as_slice());
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
        // A plain parameter name that resolves to a const item or a
        // unit variant is a refutable pattern, not a binding (rustc
        // E0005); a static name cannot be a pattern at all.
        if param.pat.is_none() && !param.mutable {
            match cx.pat_ident(param.name) {
                PatIdent::Const(_) => {
                    cx.err(
                        "L0110",
                        param.span,
                        "refutable pattern in function argument",
                        "Rename the parameter: this name is a const item, so it would be a pattern, not a binding.",
                    );
                }
                PatIdent::Static => {
                    cx.err("L0110", param.span, "statics cannot be used as patterns", "Rename the parameter: this name is a static item.");
                }
                PatIdent::Variant(a, _) if p.adt(a).is_enum => {
                    cx.err(
                        "L0110",
                        param.span,
                        "refutable pattern in function argument",
                        "Rename the parameter: this name is an enum variant, so it would be a pattern, not a binding.",
                    );
                }
                PatIdent::Variant(a, _) => {
                    // A unit struct name as a parameter is a unit
                    // pattern: legal only against its own type.
                    let at = cx.tys.adt_ty(a);
                    if !cx.unify(at, f.params[pi]) {
                        cx.mismatch(param.span, f.params[pi], at);
                    }
                }
                _ => {}
            }
        }
        let l = cx.add_local(param.name, f.params[pi], param.mutable, param.span);
        cx.out.param_locals.push(l);
        pi += 1;
    }
    // A template's parameters and return value are values of their
    // types, which must be `Sized` under its env (rustc E0277): a
    // `T: ?Sized` param, or `self` in a trait default body without
    // `Self: Sized`. Collect checks the concrete forms (`[T]`, `str`).
    if cx.is_template_check() {
        let mut slots: Vec<(Ty, Span)> = Vec::new();
        let mut i = 0;
        if let Some(sp) = &def.self_param {
            slots.push((f.params[0], sp.span));
            i = 1;
        }
        for param in &def.params {
            slots.push((f.params[i], param.span));
            i += 1;
        }
        slots.push((f.ret, def.ret.map_or(def.name_span, |t| p.ast.ty_span(t))));
        for (t, span) in slots {
            if !cx.sized_ok(t) {
                let tn = cx.tn(t);
                cx.err(
                    "L0110",
                    span,
                    format!("the size for values of type `{tn}` cannot be known"),
                    "Pass the value behind a reference such as `&T`, or drop the `?Sized` bound.",
                );
            }
        }
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
/// A value the overflow lint knows at compile time. Integers hold the
/// value's bits in an i128: for every integer type except `u128` that
/// is also the mathematical value, and `u128` operations read the bits
/// back as a u128, so values at or above 2^127 stay exact.
#[derive(Clone, PartialEq)]
enum KVal {
    Int(i128),
    Bool(bool),
    /// A known enum discriminant: the adt and the variant index. The
    /// payload stays unknown.
    Enum(AdtId, u32),
    Agg(Vec<Option<KVal>>),
}

type KEnv = Vec<Option<KVal>>;

/// Whether a match pattern matches a known scrutinee value, when the
/// overflow lint can tell.
enum KCov {
    Yes,
    No,
    Unknown,
}

/// State of the overflow-lint walk: addressed locals, the stack of loop
/// and labeled-block frames collecting break values, and one operation to
/// leave alone (the `a = a + 1` form).
struct KLint {
    addressed: Vec<bool>,
    frames: Vec<(Option<Sym>, Vec<Option<KVal>>)>,
    suppress: Option<(ExprId, u32)>,
    /// The current path is known to be unreachable (a known branch that
    /// is taken diverges): the rest of the block is not linted.
    dead: bool,
    /// `#[allow(arithmetic_overflow)]` on the function.
    allow_arith: bool,
    /// `#[allow(unconditional_panic)]` on the function.
    allow_panic: bool,
    /// Statement-level allows in force (`#[allow(..)] let ..;`).
    stmt_allow_arith: u32,
    stmt_allow_panic: u32,
}

/// True when an attribute is `#[allow(<name>)]` (possibly one of several).
pub fn allow_attr(attr: &ast::Attr, interner: &Interner, name: &str) -> bool {
    if attr.path.len() != 1 || interner.get(attr.path[0].name) != "allow" {
        return false;
    }
    let ast::AttrInput::List(_, trees) = &attr.input else { return false };
    fn has(trees: &[crate::lexer::TokenTree], interner: &Interner, name: &str) -> bool {
        trees.iter().any(|t| match t {
            crate::lexer::TokenTree::Token(tok) => matches!(tok.tok, crate::lexer::Tok::Ident(s) if interner.get(s) == name),
            crate::lexer::TokenTree::Delim(_, inner, _) => has(inner, interner, name),
        })
    }
    has(trees, interner, name)
}


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
                Some(BuiltinTy::Result) => {
                    let (a, b) = self.tys.result_args(t).unwrap_or((ERROR, ERROR));
                    format!("Result<{}, {}>", self.tn(a), self.tn(b))
                }
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
    /// The body item a name denotes in the enclosing blocks, innermost first.
    fn body_item_of(&self, name: Sym, ctxt: CtxtId) -> Option<crate::check::collect::BodyItem> {
        for layer in self.item_scopes.iter().rev() {
            for &(n, idx) in layer.iter().rev() {
                if n == (name, ctxt) {
                    return self.p.body_items.get(&idx).copied();
                }
            }
        }
        None
    }

    fn binding(&mut self, ns: Namespace, name: Sym) -> BindingRes {
        let p = self.p;
        let module = self.module;
        p.binding(&mut self.out.reads, module, ns, name)
    }

    /// A primitive associated const used as a pattern (`u8::MAX`,
    /// `char::MAX`): its value and type, if the path names one.
    fn primitive_const_pattern(&mut self, segs: &[ast::PathSeg]) -> Option<(crate::ty::consteval::ConstValue, Ty)> {
        use crate::ty::consteval::ConstValue;
        if segs.len() != 2 {
            return None;
        }
        let item = self.name(segs[1].name);
        if let Some(it) = self.p.known.int_ty(segs[0].name) {
            let t = int(it);
            let v = match item {
                "MAX" => crate::ty::consteval::truncate_to_int(it.max128() as i128, it),
                "MIN" => {
                    if it.signed() {
                        if it.bits() >= 128 { i128::MIN } else { -(1i128 << (it.bits() - 1)) }
                    } else {
                        0
                    }
                }
                "BITS" => return Some((ConstValue::Int(it.bits() as i128), int(IntTy::U32))),
                _ => return None,
            };
            // u128::MAX is stored as its raw bits, as in the evaluator.
            let v = if it == IntTy::U128 && item == "MAX" { -1 } else { v };
            return Some((ConstValue::Int(v), t));
        }
        if segs[0].name == self.p.known.char {
            let c = match item {
                "MAX" => char::MAX,
                "MIN" => char::MIN,
                _ => return None,
            };
            return Some((ConstValue::Char(c), CHAR));
        }
        None
    }

    /// What a lone identifier in a pattern resolves to through the
    /// module bindings (imports included): a const item, a static, or
    /// a unit variant or struct constructor. Anything else stays a
    /// fresh binding. The binding query records the read, so a body
    /// rechecks when the name's target changes.
    fn pat_ident(&mut self, name: Sym) -> PatIdent {
        use crate::resolve::imports::{BindState, Target};
        let p = self.p;
        if let BindingRes::Def(def) = self.binding(Namespace::Value, name) {
            let flat = p.resolved.as_ref().and_then(|t| t.def_info.get(&def)).map(|i| i.flat);
            match p.binding_kind(def) {
                Some(DefsKind::Const) => {
                    if let Some(i) = p.const_by_def(def).or_else(|| flat.and_then(|f| p.const_names.get(&f).copied())) {
                        return PatIdent::Const(i);
                    }
                }
                Some(DefsKind::Static) => {
                    if p.static_by_def(def).or_else(|| flat.and_then(|f| p.static_names.get(&f).copied())).is_some() {
                        return PatIdent::Static;
                    }
                }
                _ => {}
            }
            if let Some(a) = p.adt_by_def(def).or_else(|| flat.and_then(|f| p.type_names.get(&f).copied())) {
                if p.adt(a).is_enum {
                    // A variant import answers with the enum's def in
                    // the binding query; the raw table keeps the variant.
                    if let Some(tables) = &p.resolved
                        && let Some(BindState::One(b)) = tables.lookup(self.module, Namespace::Value, name)
                        && let Target::Variant(vdef, vname) = b.target
                        && vdef == def
                        && let Some(v) = p.adt(a).variants.iter().position(|x| x.name == vname)
                    {
                        return PatIdent::Variant(a, v as u32);
                    }
                    return PatIdent::Other;
                }
                return PatIdent::Variant(a, 0);
            }
        }
        // Without resolver tables the flat name maps answer directly.
        if let Some(&i) = p.const_names.get(&name) {
            return PatIdent::Const(i);
        }
        if p.static_names.contains_key(&name) {
            return PatIdent::Static;
        }
        if let Some(&a) = p.type_names.get(&name)
            && !p.adt(a).is_enum
        {
            return PatIdent::Variant(a, 0);
        }
        PatIdent::Other
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

    /// Tuple-field visibility, like `check_field_vis` for `t.1` forms.
    fn check_tuple_field_vis(&mut self, a: AdtId, index: u32, span: Span) {
        let p = self.p;
        let Some(tables) = &p.resolved else { return };
        let def = p.def_of_adt(a);
        if let Some((def_mod, fields)) = tables.tuple_field_vis.get(&def)
            && let Some(vis) = fields.get(index as usize)
            && !tables.visible(vis, *def_mod, self.module, p.interner)
        {
            self.err(
                "L0510",
                span,
                format!("field `{index}` is private"),
                "Make the field `pub(crate)` (the smallest widening that works).",
            );
        }
    }

    /// A tuple struct constructor is private when any of its fields is
    /// (rustc E0603), for calls and patterns alike.
    fn check_ctor_vis(&mut self, a: AdtId, span: Span) {
        let p = self.p;
        let Some(tables) = &p.resolved else { return };
        let def = p.def_of_adt(a);
        if let Some((def_mod, fields)) = tables.tuple_field_vis.get(&def)
            && fields.iter().any(|vis| !tables.visible(vis, *def_mod, self.module, p.interner))
        {
            let name = p.display_path(p.adt(a).name);
            self.err(
                "L0510",
                span,
                format!("tuple struct constructor `{name}` is private"),
                "Make every field `pub(crate)`, or add a public constructor function.",
            );
        }
    }

    /// Inherent method visibility for a method call on a user type.
    fn check_method_vis(&mut self, base: Ty, name: Sym, span: Span) {
        let p = self.p;
        let Some(tables) = &p.resolved else { return };
        let Some(a) = self.tys.local_adt(base) else { return };
        let def = p.def_of_adt(a);
        if let Some(methods) = tables.assoc_vis.get(&def)
            && let Some((vis, def_mod)) = methods.get(&name)
            && !tables.visible(vis, *def_mod, self.module, p.interner)
        {
            self.err(
                "L0510",
                span,
                format!("method `{}` is private", self.name(name)),
                "Make the method `pub(crate)` (the smallest widening that works).",
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

    /// The `fn(params) -> ret` pointer type for a signature.
    fn fn_ptr_ty(&mut self, params: &[Ty], ret: Ty) -> Ty {
        let inputs = self.tys.intern_tys(params);
        let sig =
            self.tys.intern_sig(crate::ty::Binder::plain(crate::ty::FnSig { inputs, output: ret, is_unsafe: false, extern_c: false }));
        self.tys.intern(TyKind::FnPtr(sig))
    }

    /// The zero-sized fn-item type of a plain (non-generic) fn used as a
    /// value. Generic fns as values are not supported yet.
    fn fn_value_ty(&mut self, f: LocalDefId, span: Span) -> Ty {
        if matches!(self.p.gx.fn_templates.get(f.0 as usize), Some(Some(_))) {
            self.errs.push(not_yet("L0614", span, "generic functions as values"));
            return ERROR;
        }
        self.tys.intern(TyKind::FnDef(self.p.def_id(f), EMPTY_ARGS))
    }

    /// The callable-item type of a tuple struct or tuple variant
    /// constructor used as a value. It is an `FnDef` over the Adt def
    /// with the variant index as a const argument, so a later call
    /// through the value can decode which constructor it is. Generic
    /// Adts as values are not supported yet.
    fn ctor_value_ty(&mut self, a: AdtId, v: u32, span: Span) -> Ty {
        if !self.p.gx.adt_generics[a.0 as usize].params.is_empty() {
            self.errs.push(not_yet("L0614", span, "generic constructors as values"));
            return ERROR;
        }
        let c = self.tys.intern_const(ConstKind::Int(v as u128));
        let args = self.tys.intern_args(&[GenericArg::Const(c)]);
        self.tys.intern(TyKind::FnDef(self.p.def_of_adt(a), args))
    }

    /// The variant a constructor `FnDef` type names, from its const arg.
    fn ctor_variant(&self, args: ArgsId) -> u32 {
        match self.tys.args(args).first() {
            Some(GenericArg::Const(c)) => match self.tys.const_kind(*c) {
                ConstKind::Int(v) => v as u32,
                _ => 0,
            },
            _ => 0,
        }
    }

    /// The (params, return) signature of a callable type: a fn pointer,
    /// a fn item, or a constructor item.
    fn callable_sig(&mut self, t: Ty) -> Option<(Vec<Ty>, Ty)> {
        let p = self.p;
        match self.kind(t) {
            TyKind::FnPtr(sig) => {
                let s = self.tys.sig(sig).value;
                Some((self.tys.tys_of(s.inputs).to_vec(), s.output))
            }
            TyKind::FnDef(def, args) => {
                if let Some(a) = p.adt_by_def(def) {
                    let v = self.ctor_variant(args);
                    let variant = &p.adt(a).variants[v as usize];
                    let params = variant.fields.iter().map(|f| f.ty).collect();
                    Some((params, self.tys.adt_ty(a)))
                } else {
                    let f = p.local_def(def.hash)?;
                    match p.sig_of(&mut self.out.reads, def) {
                        SigOf::Fn(info) => Some((info.params.clone(), info.ret)),
                        _ => {
                            let _ = f;
                            None
                        }
                    }
                }
            }
            _ => None,
        }
    }

    /// True when `t` is a plain fn's item type (not a constructor), so it
    /// coerces to a function pointer backed by a slot trampoline.
    fn is_fn_item(&self, t: Ty) -> bool {
        match self.kind(t) {
            TyKind::FnDef(def, _) => self.p.adt_by_def(def).is_none(),
            _ => false,
        }
    }

    /// The free fn a value binding names, if it names one.
    fn binding_fn(&mut self, name: Sym) -> Option<LocalDefId> {
        match self.binding(Namespace::Value, name) {
            BindingRes::Def(def) if self.p.binding_kind(def) == Some(DefsKind::Fn) => self.p.local_def(def.hash),
            _ => None,
        }
    }

    // ---------- Obligations (ARCH 2.4) ----------

    /// Binds one inference variable, recording it on the probe
    /// trail so solver probes can roll back (see `SolveCx`).
    fn bind_var(&mut self, var: u32, t: Ty) {
        self.trail.push(var);
        self.vars[var as usize].bound = Some(t);
    }

    /// A probe snapshot of the variable bindings (see `SolveCx`).
    fn snapshot_vars(&mut self) -> usize {
        <Self as SolveCx>::snapshot(self)
    }

    /// Rolls variable bindings back to a probe snapshot.
    fn rollback_vars(&mut self, snap: usize) {
        <Self as SolveCx>::rollback(self, snap);
    }

    /// How many obligations wait, for probe rollback.
    fn obl_len(&self) -> usize {
        self.obl.len()
    }

    /// Drops obligations queued since an `obl_len` snapshot.
    fn obl_truncate(&mut self, len: usize) {
        self.obl.truncate(len);
    }

    /// A fresh const inference variable.
    fn fresh_const_var(&mut self) -> ConstId {
        let id = self.next_const_id;
        self.next_const_id += 1;
        self.tys.intern_const(ConstKind::Infer(id))
    }

    /// The const a const inference variable bound to, if any.
    fn resolve_const(&self, c: ConstId) -> ConstId {
        match self.tys.const_kind(c) {
            ConstKind::Infer(id) if id >= generics::INFER_MARKER_BASE => self.const_bindings.get(&id).copied().unwrap_or(c),
            _ => c,
        }
    }

    /// Unifies two consts, binding a const inference variable.
    fn unify_const(&mut self, a: ConstId, b: ConstId) -> bool {
        let (a, b) = (self.resolve_const(a), self.resolve_const(b));
        if a == b {
            return true;
        }
        match (self.tys.const_kind(a), self.tys.const_kind(b)) {
            (ConstKind::Infer(x), _) if x >= generics::INFER_MARKER_BASE => {
                self.const_bindings.insert(x, b);
                true
            }
            (_, ConstKind::Infer(x)) if x >= generics::INFER_MARKER_BASE => {
                self.const_bindings.insert(x, a);
                true
            }
            _ => false,
        }
    }

    /// Fresh instantiation arguments for one generics list, by
    /// parameter kind (used for Adt applications at literals).
    fn fresh_args(&mut self, generics: &Generics) -> Vec<GenericArg> {
        generics
            .params
            .iter()
            .map(|param| match param.kind {
                ParamKind::Type => GenericArg::Ty(self.new_var(false)),
                ParamKind::Lifetime => GenericArg::Lifetime(Region::Erased),
                ParamKind::Const(_) => GenericArg::Const(self.fresh_const_var()),
            })
            .collect()
    }

    /// This body's elaborated param env.
    fn env(&self) -> &'p [Predicate] {
        self.p.gx.fn_scopes.get(self.fid.0 as usize).map_or(&[], |fs| &fs.env)
    }

    /// Normalizes one type here (section 2.5) through this body's
    /// solver. The solver state is taken out for the call because
    /// the context itself is the `SolveCx`.
    fn normalize_here(&mut self, t: Ty) -> Ty {
        if !self.tys.flags(t).contains_projection() {
            return t;
        }
        let p = self.p;
        let env: &[Predicate] = p.gx.fn_scopes.get(self.fid.0 as usize).map_or(&[], |fs| &fs.env);
        let mut solver = std::mem::take(&mut self.solver);
        let out = crate::traits::solve::normalize(&mut solver, self, &p.gx.index, env, t);
        self.solver = solver;
        out
    }

    /// Selects evidence for one trait obligation, with the
    /// structural answers of sections 2.7 (`Sized`, auto traits)
    /// and the derive-family queries ahead of the general solver
    /// where they are exact. Commits bindings on success, like
    /// `Solver::select`.
    fn select_obligation(&mut self, tr: TraitRef) -> Selection {
        self.select_obligation_at(tr, Span::default(), 0)
    }

    /// `select_obligation` at one nesting depth: a confirmed
    /// impl's nested predicates are queued at depth + 1, so a
    /// self-referential impl (`impl<X> T for Vec<X> where
    /// Vec<X>: T`) overflows through the queue (section 2.4
    /// step 7) instead of looping. Synchronous callers pass the
    /// span to blame and depth 0.
    fn select_obligation_at(&mut self, tr: TraitRef, span: Span, depth: u16) -> Selection {
        let p = self.p;
        let lang = &p.gx.lang;
        // Projections in the trait ref normalize first: an
        // associated bound like `<Local2 as IntoIter>::It: Iter`
        // selects against the concrete iterator type.
        let tr = {
            let raw: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
            let normed: Vec<GenericArg> = raw
                .iter()
                .map(|&g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.normalize_here(t)),
                    other => other,
                })
                .collect();
            let args = self.tys.intern_args(&normed);
            TraitRef { args, ..tr }
        };
        let self_ty = self.deep(self.tys.args(tr.args)[0].as_ty().unwrap_or(ERROR));
        if tr.def == lang.sized {
            // A general variable may still become `[T]` or `str`
            // (`f(s)` runs this queue before the argument unifies):
            // keep the obligation until the variable is known.
            if matches!(self.tys.kind(self_ty), TyKind::Infer(v) if !v.is_int() && !v.is_float()) {
                return Selection::Ambiguous;
            }
            return if self.sized_ok(self_ty) { Selection::ParamEvidence(usize::MAX) } else { Selection::NoImpl };
        }
        // Numeric `From` obligations are widening casts, with no
        // impl behind them in this subset's lang records.
        if tr.def == lang.from
            && let Some(input) = self.tys.args(tr.args).get(1).and_then(|g| g.as_ty())
        {
            let input = self.deep(input);
            if Self::numeric_from_ok(self.kind(input), self.kind(self_ty)) {
                return Selection::ParamEvidence(usize::MAX);
            }
            if matches!(self.kind(input), TyKind::Int(_) | TyKind::Char | TyKind::Bool)
                && matches!(self.kind(self_ty), TyKind::Int(_) | TyKind::Char | TyKind::Bool)
            {
                return Selection::NoImpl;
            }
        }
        if lang.is_auto(tr.def) {
            match self.auto_holds(tr.def, self_ty) {
                Some(true) => return Selection::ParamEvidence(usize::MAX),
                Some(false) => return Selection::NoImpl,
                None => {}
            }
        }
        let env: &[Predicate] = p.gx.fn_scopes.get(self.fid.0 as usize).map_or(&[], |fs| &fs.env);
        let mut solver = std::mem::take(&mut self.solver);
        let sel = solver.select(self, &p.gx.index, env, tr);
        self.solver = solver;
        if sel == Selection::NoImpl && self.derive_query_holds(tr.def, self_ty) {
            return Selection::ParamEvidence(usize::MAX);
        }
        if let Selection::Impl { nested, .. } = &sel {
            if depth >= 64 {
                return Selection::Overflow;
            }
            for pred in nested.clone() {
                match pred {
                    Predicate::Trait(b) if b.count == 0 => self.obl.push_trait_at(b.value, span, depth + 1),
                    Predicate::AssocEq(b) if b.count == 0 => self.obl.push(obligations::Obligation::AssocEq { eq: b.value, span }),
                    _ => {}
                }
            }
        }
        sel
    }

    /// The derive-family structural queries, for types the impl
    /// index has no record for (tuples, arrays, slices, refs).
    /// User and builtin Adts answer through the solver instead.
    fn derive_query_holds(&mut self, trait_def: DefId, self_ty: Ty) -> bool {
        let p = self.p;
        let lang = &p.gx.lang;
        match self.tys.kind(self_ty) {
            TyKind::Tuple(_) | TyKind::Array(..) | TyKind::Slice(_) | TyKind::Ref(..) | TyKind::RawPtr(..) => {}
            TyKind::Closure(..) if trait_def == lang.copy || trait_def == lang.clone => {}
            _ => return false,
        }
        if trait_def == lang.copy {
            is_copy(p, &self.tys, self_ty)
        } else if trait_def == lang.clone {
            has_clone(p, &self.tys, self_ty)
        } else if trait_def == lang.debug {
            has_debug(p, &self.tys, self_ty)
        } else if trait_def == lang.partial_eq || trait_def == lang.eq {
            has_eq(p, &self.tys, self_ty)
        } else {
            false
        }
    }

    /// `Sized` by structure (section 2.7 basics): a parameter is
    /// sized when the env says so; an Adt when its fields are,
    /// with an unsized last field making the Adt unsized.
    fn sized_ok(&mut self, t: Ty) -> bool {
        let t = self.normalize_here(t);
        match self.tys.kind(t) {
            TyKind::Str | TyKind::Slice(_) | TyKind::Dyn(..) => false,
            TyKind::Param(p) => self.env().iter().any(|pred| {
                matches!(pred, Predicate::Trait(b) if b.value.def == self.p.gx.lang.sized
                    && self.tys.args(b.value.args)[0].as_ty().is_some_and(|s| matches!(self.tys.kind(s), TyKind::Param(q) if q == p)))
            }),
            TyKind::Projection(..) => true,
            TyKind::Infer(_) => true,
            _ => {
                if let Some(a) = self.tys.local_adt(t) {
                    // Only a last field can be unsized. Without a
                    // materialized instance, `local_adt` answers with the
                    // template, whose fields are over its own params:
                    // substitute this application's args first.
                    let p = self.p;
                    let args: Vec<GenericArg> = self.tys.adt_parts(t).map(|(_, a)| self.tys.args(a).to_vec()).unwrap_or_default();
                    let lasts: Vec<Ty> = p.adt(a).variants.iter().filter_map(|v| v.fields.last().map(|f| f.ty)).collect();
                    lasts.into_iter().all(|f| {
                        let f = if args.is_empty() { f } else { subst(&mut self.tys, f, &args) };
                        self.sized_ok(f)
                    })
                } else {
                    crate::check::collect::is_sized_ty(&self.tys, t)
                }
            }
        }
    }

    /// An auto trait by structure (section 2.7). None when the
    /// answer needs the param env or inference to move first.
    fn auto_holds(&mut self, trait_def: DefId, t: Ty) -> Option<bool> {
        let mut seen: Vec<Ty> = Vec::new();
        self.auto_inner(trait_def, t, &mut seen)
    }

    fn auto_inner(&mut self, trait_def: DefId, t: Ty, seen: &mut Vec<Ty>) -> Option<bool> {
        let lang = &self.p.gx.lang;
        let t = self.resolve(t);
        if seen.contains(&t) {
            return Some(true);
        }
        match self.tys.kind(t) {
            TyKind::Error => Some(true),
            TyKind::Infer(_) | TyKind::Projection(..) => None,
            TyKind::Param(_) => {
                let env = self.env();
                Some(env.iter().any(|pred| {
                    matches!(pred, Predicate::Trait(b) if b.value.def == trait_def
                        && self.tys.args(b.value.args)[0].as_ty() == Some(t))
                }))
            }
            TyKind::RawPtr(..) => Some(trait_def == lang.unpin),
            TyKind::Ref(_, m, e) => {
                seen.push(t);
                let need = if trait_def == lang.send && !m.is_mut() { lang.sync } else { trait_def };
                if trait_def == lang.unpin {
                    return Some(true);
                }
                self.auto_inner(need, e, seen)
            }
            TyKind::Slice(e) | TyKind::Array(e, _) => {
                seen.push(t);
                self.auto_inner(trait_def, e, seen)
            }
            TyKind::Tuple(ts) => {
                seen.push(t);
                let elems: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                let mut unknown = false;
                for e in elems {
                    match self.auto_inner(trait_def, e, seen) {
                        Some(false) => return Some(false),
                        None => unknown = true,
                        _ => {}
                    }
                }
                if unknown { None } else { Some(true) }
            }
            _ => {
                if let Some(e) = self.tys.vec_elem(t).or_else(|| self.tys.option_elem(t)) {
                    seen.push(t);
                    return self.auto_inner(trait_def, e, seen);
                }
                if let Some((a, b)) = self.tys.result_args(t) {
                    seen.push(t);
                    let mut unknown = false;
                    for e in [a, b] {
                        match self.auto_inner(trait_def, e, seen) {
                            Some(false) => return Some(false),
                            None => unknown = true,
                            _ => {}
                        }
                    }
                    return if unknown { None } else { Some(true) };
                }
                if let Some(a) = self.tys.local_adt(t) {
                    seen.push(t);
                    let fields: Vec<Ty> = self.p.adt(a).variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
                    let mut unknown = false;
                    for f in fields {
                        match self.auto_inner(trait_def, f, seen) {
                            Some(false) => return Some(false),
                            None => unknown = true,
                            _ => {}
                        }
                    }
                    return if unknown { None } else { Some(true) };
                }
                Some(true)
            }
        }
    }

    /// Pushes the predicates of one instantiated item bound set:
    /// trait predicates as obligations, equalities as `AssocEq`
    /// obligations.
    fn push_predicates(&mut self, preds: &[Predicate], subst_args: &[GenericArg], span: Span) {
        let mut out: Vec<obligations::Obligation> = Vec::new();
        for &pred in preds {
            let pred = crate::traits::index::subst_predicate(&mut self.tys, pred, subst_args);
            match pred {
                Predicate::Trait(b) if b.count == 0 => out.push(obligations::Obligation::Trait { trait_ref: b.value, span, depth: 0 }),
                Predicate::AssocEq(b) if b.count == 0 => out.push(obligations::Obligation::AssocEq { eq: b.value, span }),
                _ => {}
            }
        }
        // Elaborate so supertraits and binding equalities are
        // proved too, then queue the lot.
        let p = self.p;
        let traits_only: Vec<Predicate> =
            preds.iter().map(|&pred| crate::traits::index::subst_predicate(&mut self.tys, pred, subst_args)).collect();
        let elaborated = generics::elaborate_env(&mut self.tys, &p.gx.index, &traits_only);
        let mut queued = out;
        for pred in elaborated {
            match pred {
                Predicate::Trait(b) if b.count == 0 => {
                    if !queued.iter().any(|o| matches!(o, obligations::Obligation::Trait { trait_ref, .. } if *trait_ref == b.value)) {
                        queued.push(obligations::Obligation::Trait { trait_ref: b.value, span, depth: 0 });
                    }
                }
                Predicate::AssocEq(b) if b.count == 0 => {
                    if !queued.iter().any(|o| matches!(o, obligations::Obligation::AssocEq { eq, .. } if *eq == b.value)) {
                        queued.push(obligations::Obligation::AssocEq { eq: b.value, span });
                    }
                }
                _ => {}
            }
        }
        for o in queued {
            self.obl.push(o);
        }
    }

    /// Runs the obligation queue (the 2.4 run points). With
    /// `hard`, anything left is an error; without, unresolved
    /// obligations stay queued for the next point.
    fn run_obligations(&mut self, hard: bool) {
        if self.obl.is_empty() {
            return;
        }
        // A fixpoint over rounds: nested obligations and bindings
        // from one round can settle the next.
        for _round in 0..128 {
            let work = self.obl.take();
            if work.is_empty() {
                break;
            }
            let mut pending: Vec<obligations::Obligation> = Vec::new();
            let mut progress = false;
            for ob in work {
                match ob {
                    obligations::Obligation::AssocEq { eq, span } => {
                        if self.prove_assoc_eq(eq, span) {
                            progress = true;
                        } else {
                            pending.push(ob);
                        }
                    }
                    obligations::Obligation::Trait { trait_ref, span, depth } => match self.select_obligation_at(trait_ref, span, depth) {
                        Selection::Impl { unbound, .. } => {
                            progress = true;
                            if !unbound.is_empty() && self.still_unbound(&unbound, trait_ref) {
                                pending.push(ob);
                            }
                        }
                        Selection::ParamEvidence(_) | Selection::Builtin => {
                            progress = true;
                            self.prove_bindings(trait_ref, span);
                        }
                        Selection::Ambiguous => pending.push(ob),
                        Selection::NoImpl => {
                            progress = true;
                            let tn = self.tn(self.tys.args(trait_ref.args)[0].as_ty().unwrap_or(ERROR));
                            let tr_name = self.trait_name(trait_ref.def);
                            self.err("L0612", span, format!("no impl of `{tr_name}` for `{tn}`"), "Add the impl, or change the bound.");
                        }
                        Selection::Overflow => {
                            progress = true;
                            self.err(
                                "L0611",
                                span,
                                "trait selection overflowed: the obligations recurse too deeply",
                                "Simplify the impls or bounds involved.",
                            );
                        }
                    },
                }
            }
            for ob in pending {
                self.obl.push(ob);
            }
            if !progress {
                break;
            }
        }
        if hard && !self.obl.is_empty() {
            for ob in self.obl.take() {
                match ob {
                    obligations::Obligation::Trait { trait_ref, span, .. } => {
                        // One last try now that literal fallbacks and
                        // late bindings have run: an impl with a
                        // still-unbound parameter is the step-4
                        // error, everything else is annotation.
                        match self.select_obligation(trait_ref) {
                            Selection::Impl { unbound, .. } if !unbound.is_empty() => {
                                self.err(
                                    "L0613",
                                    span,
                                    "an impl parameter is not known from the trait inputs",
                                    "Rewrite the impl so every parameter follows from the trait reference or an associated equality.",
                                );
                            }
                            Selection::Impl { .. } | Selection::ParamEvidence(_) | Selection::Builtin => {}
                            Selection::NoImpl => {
                                let tn = self.tn(self.tys.args(trait_ref.args)[0].as_ty().unwrap_or(ERROR));
                                let tr_name = self.trait_name(trait_ref.def);
                                self.err("L0612", span, format!("no impl of `{tr_name}` for `{tn}`"), "Add the impl, or change the bound.");
                            }
                            _ => {
                                self.err(
                                    "L0610",
                                    span,
                                    "type annotations needed: this trait obligation could not be resolved",
                                    "Annotate the types involved so one impl is picked.",
                                );
                            }
                        }
                    }
                    obligations::Obligation::AssocEq { span, .. } => {
                        self.err(
                            "L0610",
                            span,
                            "type annotations needed: an associated type could not be resolved",
                            "Annotate the types involved, or name the associated type in the bound.",
                        );
                    }
                }
            }
        }
    }

    /// Binds the integer and float variables still free in a pending
    /// obligation to i32 and f64 (see `finish`).
    fn literal_fallback_in_obligations(&mut self) {
        let pending = self.obl.take();
        for ob in &pending {
            let mut tys: Vec<Ty> = Vec::new();
            let args = match ob {
                obligations::Obligation::Trait { trait_ref, .. } => trait_ref.args,
                obligations::Obligation::AssocEq { eq, .. } => {
                    tys.push(eq.ty);
                    eq.trait_args
                }
            };
            tys.extend(self.tys.args(args).iter().filter_map(|g| g.as_ty()));
            for t in tys {
                self.default_literal_vars(t);
            }
        }
        for ob in pending {
            self.obl.push(ob);
        }
    }

    /// `literal_fallback_in_obligations` for one type.
    fn default_literal_vars(&mut self, t: Ty) {
        let t = self.resolve(t);
        if !self.tys.flags(t).contains_infer() {
            return;
        }
        match self.tys.kind(t) {
            TyKind::Infer(v) if v.is_int() => self.bind_var(v.index(), I32),
            TyKind::Infer(v) if v.is_float() => {
                let f = self.tys.float_ty(FloatTy::F64);
                self.bind_var(v.index(), f);
            }
            TyKind::Ref(_, _, e) | TyKind::Slice(e) | TyKind::Array(e, _) | TyKind::RawPtr(_, e) => self.default_literal_vars(e),
            TyKind::Tuple(ts) => {
                for e in self.tys.tys_of(ts).to_vec() {
                    self.default_literal_vars(e);
                }
            }
            TyKind::Adt(_, a) | TyKind::Projection(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) => {
                for g in self.tys.args(a).to_vec() {
                    if let Some(e) = g.as_ty() {
                        self.default_literal_vars(e);
                    }
                }
            }
            _ => {}
        }
    }

    /// True while any of `unbound` still names a free variable in
    /// the confirmed selection (checked through the obligation,
    /// whose args the probe bound).
    fn still_unbound(&mut self, unbound: &[ParamId], _tr: TraitRef) -> bool {
        !unbound.is_empty()
    }

    /// Proves one associated equality by normalization. False
    /// when the projection does not normalize yet.
    fn prove_assoc_eq(&mut self, eq: AssocEqData, span: Span) -> bool {
        let proj = self.tys.intern(TyKind::Projection(AssocId(eq.assoc), eq.trait_args));
        let normed = self.normalize_here(proj);
        let want = self.normalize_here(eq.ty);
        if matches!(self.tys.kind(normed), TyKind::Projection(..)) && normed != want {
            return false;
        }
        if !self.unify(normed, want) {
            let (a, b) = (self.tn(want), self.tn(normed));
            self.err(
                "L0110",
                span,
                format!("associated type mismatch: expected `{a}`, found `{b}`"),
                "Change the binding or the impl's associated type.",
            );
        }
        true
    }

    /// Proves the bindings written on an obligation that the
    /// param env answered (the impl path proves them in its
    /// probe already).
    fn prove_bindings(&mut self, tr: TraitRef, span: Span) {
        let bindings: Vec<(DefId, GenericArg)> = self.tys.bindings(tr.bindings).to_vec();
        for (assoc, ga) in bindings {
            if let GenericArg::Ty(want) = ga {
                let eq = AssocEqData { assoc, trait_args: tr.args, ty: want };
                if !self.prove_assoc_eq(eq, span) {
                    self.obl.push(obligations::Obligation::AssocEq { eq, span });
                }
            }
        }
    }

    /// The display name of a trait def, for obligation errors.
    fn trait_name(&self, def: DefId) -> String {
        self.p.gx.index.trait_record(def).map_or_else(|| "?".to_string(), |r| self.p.display_path(r.name))
    }

    /// Replaces `_` markers in one resolved written type with
    /// fresh body variables (distinct per marker).
    fn instantiate_infers(&mut self, t: Ty) -> Ty {
        self.instantiate_inner(t, &mut std::collections::HashMap::new())
    }

    fn instantiate_inner(&mut self, t: Ty, map: &mut std::collections::HashMap<u32, Ty>) -> Ty {
        match self.tys.kind(t) {
            TyKind::Infer(v) if v.index() >= generics::INFER_MARKER_BASE => {
                if let Some(&u) = map.get(&v.index()) {
                    return u;
                }
                let u = self.new_var(false);
                map.insert(v.index(), u);
                u
            }
            _ if !self.tys.flags(t).contains_infer() => t,
            TyKind::Ref(r, m, e) => {
                let e = self.instantiate_inner(e, map);
                self.tys.intern(TyKind::Ref(r, m, e))
            }
            TyKind::Slice(e) => {
                let e = self.instantiate_inner(e, map);
                self.tys.intern(TyKind::Slice(e))
            }
            TyKind::Array(e, n) => {
                let e = self.instantiate_inner(e, map);
                self.tys.intern(TyKind::Array(e, n))
            }
            TyKind::Tuple(ts) => {
                let old: Vec<Ty> = self.tys.tys_of(ts).to_vec();
                let new: Vec<Ty> = old.iter().map(|&e| self.instantiate_inner(e, map)).collect();
                let ts = self.tys.intern_tys(&new);
                self.tys.intern(TyKind::Tuple(ts))
            }
            TyKind::Adt(d, a) => {
                let a = self.instantiate_args(a, map);
                self.tys.intern(TyKind::Adt(d, a))
            }
            TyKind::Projection(d, a) => {
                let a = self.instantiate_args(a, map);
                self.tys.intern(TyKind::Projection(d, a))
            }
            TyKind::FnDef(d, a) => {
                let a = self.instantiate_args(a, map);
                self.tys.intern(TyKind::FnDef(d, a))
            }
            _ => t,
        }
    }

    fn instantiate_args(&mut self, a: ArgsId, map: &mut std::collections::HashMap<u32, Ty>) -> ArgsId {
        let old: Vec<GenericArg> = self.tys.args(a).to_vec();
        let new: Vec<GenericArg> = old
            .iter()
            .map(|&g| match g {
                GenericArg::Ty(e) => GenericArg::Ty(self.instantiate_inner(e, map)),
                other => other,
            })
            .collect();
        self.tys.intern_args(&new)
    }

    // ---------- Inference ----------

    fn new_var(&mut self, int: bool) -> Ty {
        self.vars.push(Var { bound: None });
        let id = self.vars.len() as u32 - 1;
        self.tys.intern(TyKind::Infer(InferId(id, if int { InferKind::Int } else { InferKind::General })))
    }
    /// A fresh float-literal variable: binds only to a float type,
    /// defaults to f64 at body end.
    fn new_float_var(&mut self) -> Ty {
        self.vars.push(Var { bound: None });
        let id = self.vars.len() as u32 - 1;
        self.tys.intern(TyKind::Infer(InferId(id, InferKind::Float)))
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
                let d = if v.is_int() {
                    I32
                } else if v.is_float() {
                    self.tys.float_ty(FloatTy::F64)
                } else {
                    ERROR
                };
                self.bind_var(v.index(), d);
                d
            }
            TyKind::Array(e, n) if matches!(self.tys.const_kind(n), ConstKind::Infer(id) if id >= generics::INFER_MARKER_BASE) => {
                let e = self.rebuild(e, zonk);
                let n = self.resolve_const(n);
                self.tys.intern(TyKind::Array(e, n))
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
                let n = self.resolve_const(n);
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
                        GenericArg::Const(c) => GenericArg::Const(self.resolve_const(c)),
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
            TyKind::RawPtr(m, e) => {
                let e = self.rebuild(e, zonk);
                self.tys.intern(TyKind::RawPtr(m, e))
            }
            TyKind::Projection(d, a) => {
                let a = self.rebuild_args(a, zonk);
                self.tys.intern(TyKind::Projection(d, a))
            }
            TyKind::FnDef(d, a) => {
                let a = self.rebuild_args(a, zonk);
                self.tys.intern(TyKind::FnDef(d, a))
            }
            TyKind::Closure(d, a) => {
                let a = self.rebuild_args(a, zonk);
                self.tys.intern(TyKind::Closure(d, a))
            }
            TyKind::Opaque(d, a) => {
                let a = self.rebuild_args(a, zonk);
                self.tys.intern(TyKind::Opaque(d, a))
            }
            _ => t,
        }
    }

    fn rebuild_args(&mut self, a: ArgsId, zonk: bool) -> ArgsId {
        let old: Vec<GenericArg> = self.tys.args(a).to_vec();
        let new: Vec<GenericArg> = old
            .iter()
            .map(|&g| match g {
                GenericArg::Ty(e) => GenericArg::Ty(self.rebuild(e, zonk)),
                GenericArg::Const(c) => GenericArg::Const(self.resolve_const(c)),
                other => other,
            })
            .collect();
        self.tys.intern_args(&new)
    }

    fn unify(&mut self, a: Ty, b: Ty) -> bool {
        let (a, b) = (self.resolve(a), self.resolve(b));
        if a == b {
            return true;
        }
        // A projection that normalizes now unifies through its
        // normal form (section 2.5). Only when its args hold no
        // inference variable: selection inside probes already
        // handles the open case, and normalizing there would loop.
        if !self.in_norm {
            let na = if matches!(self.tys.kind(a), TyKind::Projection(..)) && !self.tys.flags(a).contains_infer() {
                self.in_norm = true;
                let n = self.normalize_here(a);
                self.in_norm = false;
                n
            } else {
                a
            };
            let nb = if matches!(self.tys.kind(b), TyKind::Projection(..)) && !self.tys.flags(b).contains_infer() {
                self.in_norm = true;
                let n = self.normalize_here(b);
                self.in_norm = false;
                n
            } else {
                b
            };
            if na != a || nb != b {
                return self.unify(na, nb);
            }
        }
        match (self.tys.kind(a), self.tys.kind(b)) {
            (TyKind::Error, _) | (_, TyKind::Error) => true,
            (TyKind::Infer(v), TyKind::Infer(w)) => {
                // Bind the general variable to the constrained one, so
                // the int or float constraint survives. An int variable
                // never unifies with a float variable.
                if (v.is_int() && w.is_float()) || (v.is_float() && w.is_int()) {
                    return false;
                }
                if (v.is_int() || v.is_float()) && !w.is_int() && !w.is_float() {
                    self.bind_var(w.index(), a);
                } else {
                    self.bind_var(v.index(), b);
                }
                true
            }
            (TyKind::Infer(v), k) | (k, TyKind::Infer(v)) => {
                if v.is_int() && !matches!(k, TyKind::Int(_)) {
                    return false;
                }
                if v.is_float() && !matches!(k, TyKind::Float(_)) {
                    return false;
                }
                let other = if matches!(self.tys.kind(a), TyKind::Infer(_)) { b } else { a };
                if self.occurs(v.index(), other) {
                    return false;
                }
                self.bind_var(v.index(), other);
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
            (TyKind::Array(x, n), TyKind::Array(y, m)) => self.unify_const(n, m) && self.unify(x, y),
            (TyKind::RawPtr(m, x), TyKind::RawPtr(n, y)) => m == n && self.unify(x, y),
            (TyKind::Projection(d, x), TyKind::Projection(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::FnDef(d, x), TyKind::FnDef(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::Closure(d, x), TyKind::Closure(e, y)) => d == e && self.unify_args(x, y),
            (TyKind::Opaque(d, x), TyKind::Opaque(e, y)) => d == e && self.unify_args(x, y),
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
                (GenericArg::Const(x), GenericArg::Const(y)) => self.unify_const(x, y),
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
        self.run_obligations(false);
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
                    // An exact structural match wins over a deref
                    // coercion: `&&S` against `&T` binds `T = &S`,
                    // never `T = S` through `*`. rustc coerces only
                    // when the types do not already unify, so try
                    // the plain unify first (rolled back; the
                    // fallback arm redoes it for real).
                    let snap_vars = self.snapshot_vars();
                    let obl_len = self.obl_len();
                    let exact = self.unify(found, expected);
                    self.rollback_vars(snap_vars);
                    self.obl_truncate(obl_len);
                    !exact && {
                        let mut t = found;
                        for _ in 0..fd - ed {
                            if let TyKind::Ref(_, _, inner) = self.kind(t) {
                                t = inner;
                            }
                        }
                        matches!(self.kind(t), TyKind::Ref(_, Mut::Shared, _)) && self.unify(t, expected)
                    }
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
            // A plain fn item coerces to a function pointer with the
            // same signature (the value materializes as its trampoline).
            (TyKind::FnDef(..), TyKind::FnPtr(_))
                if self.is_fn_item(found)
                    && self.callable_sig(found).is_some_and(|(params, ret)| self.fn_ptr_ty(&params, ret) == self.resolve(expected)) =>
            {
                // The expression now has the pointer type, so lowering
                // materializes the trampoline value for it.
                if let Some(e) = e {
                    self.set(e, expected);
                }
                Coerce::None
            }
            _ => {
                if !self.unify(found, expected) {
                    if self.coerce_deep(found, expected, e) {
                        // The whole value now has the expected type; the
                        // inner coercions recorded on its parts build it.
                        if let Some(e) = e {
                            self.set(e, expected);
                        }
                        return true;
                    }
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
    /// Structural equality with inference variables as wildcards.
    fn ty_matchish(&self, a: Ty, b: Ty) -> bool {
        let (a, b) = (self.resolve(a), self.resolve(b));
        if a == b {
            return true;
        }
        match (self.tys.kind(a), self.tys.kind(b)) {
            (TyKind::Infer(_), _) | (_, TyKind::Infer(_)) => true,
            (TyKind::Ref(_, _, x), TyKind::Ref(_, _, y)) => self.ty_matchish(x, y),
            (TyKind::Slice(x), TyKind::Slice(y)) | (TyKind::Array(x, _), TyKind::Array(y, _)) => self.ty_matchish(x, y),
            (TyKind::Tuple(xs), TyKind::Tuple(ys)) => {
                let (xs, ys) = (self.tys.tys_of(xs), self.tys.tys_of(ys));
                xs.len() == ys.len() && xs.iter().zip(ys).all(|(&x, &y)| self.ty_matchish(x, y))
            }
            (TyKind::Adt(d, x), TyKind::Adt(e, y)) => {
                d == e
                    && self.tys.args(x).len() == self.tys.args(y).len()
                    && self.tys.args(x).iter().zip(self.tys.args(y)).all(|(x, y)| match (x, y) {
                        (GenericArg::Ty(x), GenericArg::Ty(y)) => self.ty_matchish(*x, *y),
                        _ => x == y,
                    })
            }
            _ => false,
        }
    }

    /// True when a reference coercion (unsize to a slice, `&String` to
    /// `&str`, `&mut` to `&`) takes `f` to `e`. Pure: no unification.
    fn ref_coercible(&self, f: Ty, e: Ty) -> bool {
        let (TyKind::Ref(_, fm, x), TyKind::Ref(_, em, y)) = (self.kind(f), self.kind(e)) else { return false };
        if em.is_mut() && !fm.is_mut() {
            return false;
        }
        match self.kind(y) {
            TyKind::Slice(ye) => match self.kind(x) {
                TyKind::Array(xe, _) | TyKind::Slice(xe) => self.ty_matchish(xe, ye),
                _ => self.tys.vec_elem(self.resolve(x)).is_some_and(|xe| self.ty_matchish(xe, ye)),
            },
            TyKind::Str => self.tys.is_string_ty(self.resolve(x)),
            _ => self.ty_matchish(x, y),
        }
    }

    /// True when the fn item to fn pointer coercion takes `f` to `e`.
    /// Pure: no unification (the same test `coerce_at` applies).
    fn fn_coercible(&mut self, f: Ty, e: Ty) -> bool {
        matches!(self.kind(e), TyKind::FnPtr(_))
            && self.is_fn_item(f)
            && self.callable_sig(f).is_some_and(|(params, ret)| self.fn_ptr_ty(&params, ret) == self.resolve(e))
    }

    /// Coercion inside an aggregate value whose producer is in hand: a
    /// tuple literal, or a one-argument variant call such as `Some(&v)`
    /// where `&[u8]` is wanted. The inner coercions record on the inner
    /// expressions, so lowering applies them while building the value.
    /// Other shapes keep the plain type-mismatch error.
    fn coerce_deep(&mut self, found: Ty, expected: Ty, e: Option<ExprId>) -> bool {
        let Some(e) = e else { return false };
        let span = self.span(e);
        match (self.kind(found), self.kind(expected)) {
            (TyKind::Tuple(xs), TyKind::Tuple(ys)) => {
                let Expr::Tuple(elems) = self.p.ast.expr(e) else { return false };
                let (xs, ys) = (self.tys.tys_of(xs).to_vec(), self.tys.tys_of(ys).to_vec());
                if xs.len() != ys.len() || elems.len() != xs.len() {
                    return false;
                }
                if !xs.iter().zip(&ys).all(|(&x, &y)| self.ty_matchish(x, y) || self.ref_coercible(x, y) || self.fn_coercible(x, y)) {
                    return false;
                }
                elems.iter().zip(xs.iter().zip(&ys)).all(|(&el, (&x, &y))| self.coerce_at(x, y, span, Some(el)))
            }
            (TyKind::Adt(df, af), TyKind::Adt(de, ae)) if df == de => {
                let (fa, ea) = (self.tys.args(af).to_vec(), self.tys.args(ae).to_vec());
                if fa.len() != ea.len() || fa.len() != 1 {
                    return false;
                }
                let (Some(x), Some(y)) = (fa[0].as_ty(), ea[0].as_ty()) else { return false };
                if !self.ref_coercible(x, y) && !self.fn_coercible(x, y) {
                    return false;
                }
                // The producer must be a one-argument variant call
                // (`Some(..)`), whose argument carries the coercion.
                let Expr::Call { args, .. } = self.p.ast.expr(e) else { return false };
                if args.len() != 1 || !matches!(self.out.expr_res[self.ei(e)], Res::Variant(..) | Res::OptSome) {
                    return false;
                }
                let inner_found = self.out.expr_ty[self.ei(args[0])];
                self.coerce_at(inner_found, y, span, Some(args[0]))
            }
            _ => false,
        }
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
        {
            let mut layer: Vec<((Sym, CtxtId), u32)> = Vec::new();
            for stmt in &block.stmts {
                if let Stmt::Item(idx) = stmt {
                    if let Some(name) = match &self.p.ast.stmt_items[*idx as usize].kind {
                        ItemKind::Fn(d) => Some((d.name, d.name_span.ctxt)),
                        ItemKind::Const(c) => c.name.map(|n| (n, c.name_span.ctxt)),
                        ItemKind::Static(st) => Some((st.name, st.name_span.ctxt)),
                        _ => None,
                    } {
                        layer.push((name, *idx));
                    }
                }
            }
            self.item_scopes.push(layer);
        }
        let mut diverges = false;
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let { pat, ty, init, els, .. } => {
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
                    // The `else` block runs when the pattern does not
                    // match, so it is checked before the pattern binds
                    // anything (its names are not in scope there), and
                    // it must diverge, as in Rust.
                    if let Some(els_b) = els {
                        let et = self.block(*els_b, None);
                        if self.kind(et) != TyKind::Never {
                            self.err(
                                "L0110",
                                self.p.ast.block(*els_b).span,
                                "the `else` block of a `let...else` must diverge",
                                "End it with `return`, `break`, `continue`, or a panic.",
                            );
                        }
                    }
                    match self.p.ast.pat(*pat) {
                        // A plain name that resolves to a const, static,
                        // or unit path is a pattern, not a fresh binding:
                        // check it like any destructuring let, which
                        // rejects it as refutable where rustc does.
                        Pat::Binding { name, mutable: false, by_ref: false }
                            if self.lookup(*name, self.p.ast.pat_span(*pat).ctxt).is_none()
                                && !matches!(self.pat_ident(*name), PatIdent::Other) =>
                        {
                            if init.is_none() {
                                let s = self.p.ast.pat_span(*pat);
                                self.errs.push(unsupported(s, "destructuring in `let` without an initializer"));
                            } else {
                                self.pattern(*pat, ty, false);
                                if !self.irrefutable(*pat) {
                                    let s = self.p.ast.pat_span(*pat);
                                    if els.is_none() {
                                        self.err(
                                            "L0110",
                                            s,
                                            "refutable pattern in local binding",
                                            "Use `match`, `if let`, or `let...else` for a pattern that can fail.",
                                        );
                                    }
                                }
                            }
                        }
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
                                    if els.is_none() {
                                        self.err(
                                            "L0110",
                                            s,
                                            "refutable pattern in local binding",
                                            "Use `match`, `if let`, or `let...else` for a pattern that can fail.",
                                        );
                                    }
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
        self.item_scopes.pop();
        t
    }

    fn resolve_written(&mut self, t: ast::TyId) -> Ty {
        let p = self.p;
        let written_span = p.ast.ty_span(t);
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
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        match generics::resolve_scoped(p.ast, p.interner, p.known, &cx, &mut self.tys, t, &self.body_scope.clone()) {
            Ok(t) => {
                let t = self.instantiate_infers(t);
                let t = self.normalize_here(t);
                // A written type must be well-formed: the
                // bounds of every local Adt it applies become
                // obligations here (rustc E0277 at the type).
                self.wf_check_written(t, written_span);
                t
            }
            Err(d) => {
                self.errs.push(d);
                ERROR
            }
        }
    }

    /// Queues the well-formedness obligations of one body
    /// type: for every application of a local Adt inside it,
    /// the Adt's parameter bounds under the written arguments.
    fn wf_check_written(&mut self, t: Ty, span: Span) {
        if !self.p.gx.has_generics {
            return;
        }
        let mut stack: Vec<Ty> = vec![t];
        let mut seen: Vec<Ty> = Vec::new();
        while let Some(t) = stack.pop() {
            let t = self.deep(t);
            if seen.contains(&t) {
                continue;
            }
            seen.push(t);
            match self.tys.kind(t) {
                TyKind::Adt(d, a) => {
                    let argv: Vec<GenericArg> = self.tys.args(a).to_vec();
                    if let Some(idx) = self.p.gx.adt_info.iter().position(|&(def, _)| def == d) {
                        let preds = self.p.gx.adt_generics[idx].predicates.clone();
                        if !preds.is_empty() {
                            self.push_predicates(&preds, &argv, span);
                        }
                    }
                    for g in argv {
                        if let Some(e) = g.as_ty() {
                            stack.push(e);
                        }
                    }
                }
                TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => stack.push(e),
                TyKind::Tuple(ts) => stack.extend(self.tys.tys_of(ts).iter().copied()),
                TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => {
                    let argv: Vec<GenericArg> = self.tys.args(a).to_vec();
                    for g in argv {
                        if let Some(e) = g.as_ty() {
                            stack.push(e);
                        }
                    }
                }
                TyKind::FnPtr(sig) => {
                    let b = self.tys.sig(sig);
                    stack.extend(self.tys.tys_of(b.value.inputs).iter().copied());
                    stack.push(b.value.output);
                }
                _ => {}
            }
        }
    }

    /// Instantiates one fn template at a call site: fresh
    /// variables for its parameters (explicit turbofish types
    /// where written), the substituted signature, bound
    /// obligations queued, and the site recorded for mono.
    /// Returns (params, ret, args).
    fn instantiate_template(
        &mut self,
        e: ExprId,
        template: LocalDefId,
        generics: &Generics,
        explicit: &[Option<GenericArg>],
        span: Span,
    ) -> (Vec<Ty>, Ty, Vec<GenericArg>) {
        let p = self.p;
        let info = p.fn_info(template);
        // More written generic arguments than the item has
        // parameters is an arity error (rustc E0107); `explicit`
        // is aligned to `generics.params` at every call site.
        if explicit.len() > generics.params.len() {
            self.err(
                "L0107",
                span,
                format!("too many generic arguments: this item takes {}", generics.params.len()),
                "Remove the extra arguments.",
            );
        }
        let mut args: Vec<GenericArg> = Vec::with_capacity(generics.params.len());
        for (i, param) in generics.params.iter().enumerate() {
            let given = explicit.get(i).copied().flatten();
            args.push(match (given, &param.kind) {
                (Some(g), _) => g,
                (None, ParamKind::Type) => GenericArg::Ty(self.new_var(false)),
                (None, ParamKind::Lifetime) => GenericArg::Lifetime(Region::Erased),
                (None, ParamKind::Const(_)) => GenericArg::Const(self.fresh_const_var()),
            });
        }
        let params: Vec<Ty> = info.params.iter().map(|&t| subst(&mut self.tys, t, &args)).collect();
        let ret = subst(&mut self.tys, info.ret, &args);
        let preds = generics.predicates.clone();
        self.push_predicates(&preds, &args, span);
        self.generic_sites.push((self.ei(e), template, args.clone()));
        (params, ret, args)
    }


    /// The explicit generic arguments written on a call path
    /// (`f::<u8, _>(..)`), resolved in this body's scope and
    /// aligned to parameter positions. Unwritten positions are
    /// None.
    fn explicit_call_args(&mut self, callee: ExprId) -> Vec<Option<GenericArg>> {
        let p = self.p;
        let ast::Expr::Path(segs) = p.ast.expr(callee) else { return Vec::new() };
        let Some(seg) = segs.last() else { return Vec::new() };
        let ast::GenericArgs::Angle(written) = &seg.args else { return Vec::new() };
        let mut out = Vec::new();
        for a in written {
            out.push(match a {
                ast::GenericArg::Type(t) => Some(GenericArg::Ty(self.resolve_written(*t))),
                ast::GenericArg::Lifetime(_) => None,
                ast::GenericArg::Const(e) => {
                    let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                    let _ = cx;
                    crate::check::collect::eval_array_len(p.ast, p.interner, p.known, *e).map(|v| {
                        let c = self.tys.intern_const(ConstKind::Int(v));
                        GenericArg::Const(c)
                    })
                }
                ast::GenericArg::Binding { span, .. } => {
                    self.errs.push(not_yet("L0621", *span, "associated bindings in call arguments"));
                    None
                }
            });
        }
        out
    }

    // ---------- Expressions ----------

    /// The `&&` elements of a condition, left to right.
    fn split_and(&self, e: ExprId, out: &mut Vec<ExprId>) {
        match self.p.ast.expr(e) {
            Expr::Binary { op: BinOp::And, lhs, rhs } => {
                self.split_and(*lhs, out);
                self.split_and(*rhs, out);
            }
            _ => out.push(e),
        }
    }

    /// True when a condition is a let chain (some `&&` element is a `let`).
    fn is_let_chain(&self, cond: ExprId) -> bool {
        let mut elems = Vec::new();
        self.split_and(cond, &mut elems);
        elems.iter().any(|&e| matches!(self.p.ast.expr(e), Expr::Let { .. }))
    }

    /// Checks a let-chain condition: each `let` element binds into the
    /// current scope (visible to later elements and the then block, which
    /// the caller checks before truncating), each other element is bool.
    fn check_chain(&mut self, cond: ExprId) {
        let mut elems = Vec::new();
        self.split_and(cond, &mut elems);
        for el in elems {
            match self.p.ast.expr(el) {
                Expr::Let { pat, scrut } => {
                    let (pat, scrut) = (*pat, *scrut);
                    let st = self.expr(scrut, None);
                    self.set(el, BOOL);
                    self.pattern(pat, st, true);
                }
                _ => {
                    self.expect_expr(el, BOOL);
                }
            }
        }
    }

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
                        // An unsuffixed float literal stays a float
                        // variable until a use decides f32 or f64; it
                        // defaults to f64 at body end, like rustc.
                        None => match expected.map(|t| (self.resolve(t), self.kind(t))) {
                            Some((t, TyKind::Float(_))) => t,
                            Some((t, k)) if k.is_float_infer() => t,
                            _ => self.new_float_var(),
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
            Expr::If { cond, then, els } if self.is_let_chain(*cond) => {
                let scope = self.scopes.len();
                self.check_chain(*cond);
                match els {
                    None => {
                        let t = self.block(*then, Some(UNIT));
                        let bspan = p.ast.block(*then).span;
                        if let Some(tail) = p.ast.block(*then).tail {
                            self.coerce_expr(tail, t, UNIT);
                        } else {
                            self.coerce_at(t, UNIT, bspan, None);
                        }
                        self.scopes.truncate(scope);
                        UNIT
                    }
                    Some(els) => {
                        let t1 = self.block(*then, expected);
                        self.scopes.truncate(scope);
                        let t2 = self.expr(*els, expected.or(Some(t1)));
                        self.join(t1, t2, Some(*els), span)
                    }
                }
            }
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
            Expr::While { label, cond, body } if self.is_let_chain(*cond) => {
                let scope = self.scopes.len();
                self.check_chain(*cond);
                self.loops.push(LoopCtx { break_ty: None, is_loop: false, is_block: false, label: label_of(label) });
                let t = self.block(*body, Some(UNIT));
                self.unit_body(t, *body);
                self.loops.pop();
                self.scopes.truncate(scope);
                UNIT
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
                let item = self.for_iter(e, *iter);
                let scope = self.scopes.len();
                self.pattern(*pat, item, false);
                if !self.irrefutable(*pat) {
                    let s = self.p.ast.pat_span(*pat);
                    self.err(
                        "L0110",
                        s,
                        "refutable pattern in `for` loop binding",
                        "Use `while let` or `match` for a pattern that can fail.",
                    );
                }
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
                self.run_obligations(false);
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
                self.method_call(e, *recv, *name, *name_span, args, generic_args, expected)
            }
            Expr::Field { base, name } => {
                let bt = self.expr(*base, None);
                // ARCH 2.12 run point: a field access must know the base type.
                self.run_obligations(false);
                let bt = self.deep(bt);
                let (derefs, inner) = self.autoderef(bt);
                if let Some(a) = self.tys.local_adt(inner) {
                    let adt = p.adt(a);
                    if !adt.is_enum
                        && let Some(i) = adt.variants[0].fields.iter().position(|f| f.name == *name)
                    {
                        self.check_field_vis(a, *name, span);
                        self.set_res(e, Res::Field { derefs, index: i as u32 });
                        // A generic Adt's fields are the template's,
                        // substituted with this value's args (the
                        // instance AdtDef already has them concrete).
                        let fty = adt.variants[0].fields[i].ty;
                        return match self.tys.adt_parts(inner) {
                            Some((_, args)) if args != EMPTY_ARGS && self.tys.flags(fty).contains_param() => {
                                let gargs: Vec<GenericArg> = self.tys.args(args).to_vec();
                                subst(&mut self.tys, fty, &gargs)
                            }
                            _ => fty,
                        };
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
                self.run_obligations(false);
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
                    // A range index into a string makes a str place; the
                    // runtime range check also validates char boundaries.
                    if self.kind(inner) == TyKind::Str || self.tys.is_string_ty(inner) {
                        self.set_res(e, Res::SliceIndex { derefs });
                        return STR;
                    }
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
                                    "Slice an array, a Vec, a slice, or a string.",
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
                    (UnOp::Neg, k) if k.is_float_infer() => inner,
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
                // An unsuffixed literal takes its type from the cast
                // target: `300 as u8` is a u8 literal out of range,
                // and `3000000000 as u64` needs no i32 fit first.
                let exp = if crate::ty::consteval::is_unsuffixed_lit(p.ast, *expr) { Some(target) } else { None };
                let t = self.expr(*expr, exp);
                let enum_cast = match self.tys.local_adt(self.resolve(t)) {
                    Some(a) => p.adt(a).is_enum && p.adt(a).variants.iter().all(|v| v.shape == VariantShape::Unit),
                    None => false,
                };
                // A fn item casts to a fn pointer of the same signature,
                // and a fn pointer casts to itself. The item form goes
                // through the coercion path, which gives the inner
                // expression the pointer type for lowering.
                let fn_cast = match (self.kind(t), self.kind(target)) {
                    (TyKind::FnDef(..), TyKind::FnPtr(_)) if self.is_fn_item(t) => {
                        self.callable_sig(t).is_some_and(|(params, ret)| self.fn_ptr_ty(&params, ret) == self.resolve(target))
                            && self.coerce_at(t, target, span, Some(*expr))
                    }
                    (TyKind::FnPtr(_), TyKind::FnPtr(_)) => match (self.callable_sig(t), self.callable_sig(target)) {
                        (Some((pa, ra)), Some((pb, rb))) => {
                            pa.len() == pb.len() && pa.iter().zip(&pb).all(|(&a, &b)| self.unify(a, b)) && self.unify(ra, rb)
                        }
                        _ => false,
                    },
                    _ => false,
                };
                // A reference-to-reference cast is a coercion cast in
                // rustc (`&[T; N] as &[T]`, `&mut T as &T`, `&Vec<T> as
                // &[T]`): it holds exactly when the coercion does. The
                // probe rolls back on failure so the cast error below
                // is the only diagnostic.
                let ref_cast = matches!((self.kind(t), self.kind(target)), (TyKind::Ref(..), TyKind::Ref(..))) && {
                    let snap = self.snapshot_vars();
                    let obl_len = self.obl_len();
                    let err_len = self.errs.len();
                    if self.coerce_at(t, target, span, Some(*expr)) {
                        true
                    } else {
                        self.rollback_vars(snap);
                        self.obl_truncate(obl_len);
                        self.errs.truncate(err_len);
                        false
                    }
                };
                // The `as` table rustc enforces (E0054, E0604, E0606): bool
                // and char never cast to a float, only `u8` casts to char,
                // nothing casts to bool, a fieldless enum casts only to an
                // integer. A same-kind cast (`bool as bool`) is fine.
                let ok = fn_cast || ref_cast || match (self.kind(t), self.kind(target)) {
                    // An integer of unknown type stays open: later uses decide it (default i32).
                    (k, TyKind::Int(_)) if k.is_int_infer() => true,
                    (k, TyKind::Float(_) | TyKind::Int(_)) if k.is_float_infer() => true,
                    (_, TyKind::Int(_)) if enum_cast => true,
                    (TyKind::Int(_) | TyKind::Bool | TyKind::Char, TyKind::Int(_)) => true,
                    (TyKind::Int(_) | TyKind::Float(_), TyKind::Float(_)) => true,
                    (TyKind::Float(_), TyKind::Int(_)) => true,
                    (TyKind::Int(IntTy::U8) | TyKind::Char, TyKind::Char) => true,
                    (TyKind::Bool, TyKind::Bool) => true,
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
                self.run_obligations(false);
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
                let lt = self.assign_lhs_ty(*lhs);
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
                        (BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Rem, k) if k.is_float_infer() => self.unify(lt, rinner),
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
                // Edition 2024 (rustc E0695): an unlabeled break may not
                // target or pass through a labeled block. If the innermost
                // breakable is a labeled block, the break needs the label.
                if label.is_none()
                    && let Some(lp) = self.loops.last()
                    && lp.is_block
                {
                    self.err(
                        "L0120",
                        span,
                        "unlabeled `break` inside of a labeled block",
                        "Give the break the block's label, such as `break 'a;`.",
                    );
                    if let Some(v) = val {
                        self.expr(*v, None);
                    }
                    return NEVER;
                }
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
                let ret = self.closure_rets.last().copied().unwrap_or(self.f.ret);
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
                        // An array of plain fn items holds function
                        // pointers: retag the first element too when any
                        // element is a different fn item.
                        let elt = self.resolve(el);
                        let el = if elems.len() > 1 && self.is_fn_item(elt) {
                            match self.callable_sig(elt) {
                                Some((params, ret)) => {
                                    let fp = self.fn_ptr_ty(&params, ret);
                                    self.set(first, fp);
                                    fp
                                }
                                None => el,
                            }
                        } else {
                            el
                        };
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
                let errs_before = self.errs.len();
                self.expect_expr(*len, USIZE);
                // The scalar subset first; then the full bounded
                // evaluator, so size_of calls, const items, and const
                // fn calls all give lengths in expression position.
                let n = crate::check::collect::eval_array_len(p.ast, p.interner, p.known, *len).or_else(|| {
                    if self.errs.len() != errs_before {
                        return None;
                    }
                    let mut ccx = CheckCx { cx: self };
                    match crate::ty::consteval::eval(&mut ccx, *len, Some(USIZE)) {
                        Ok((crate::ty::consteval::ConstValue::Int(n), _)) if n >= 0 => Some(n as u128),
                        _ => None,
                    }
                });
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
                self.run_obligations(false);
                let (derefs, inner) = self.autoderef(bt);
                let field_ty = match self.kind(inner) {
                    TyKind::Tuple(ts) => self.tys.tys_of(ts).get(*index as usize).copied(),
                    _ => match self.tys.local_adt(inner) {
                        Some(a) if !p.adt(a).is_enum && p.adt(a).variants[0].shape == VariantShape::Tuple => {
                            // As for named fields: a generic Adt's field is
                            // the template's, substituted with these args.
                            p.adt(a).variants[0].fields.get(*index as usize).map(|f| match self.tys.adt_parts(inner) {
                                Some((_, args)) if args != EMPTY_ARGS && self.tys.flags(f.ty).contains_param() => {
                                    let gargs: Vec<GenericArg> = self.tys.args(args).to_vec();
                                    subst(&mut self.tys, f.ty, &gargs)
                                }
                                _ => f.ty,
                            })
                        }
                        _ => None,
                    },
                };
                match field_ty {
                    Some(t) => {
                        if let Some(a) = self.tys.local_adt(inner) {
                            self.check_tuple_field_vis(a, *index, span);
                        }
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
            Expr::Let { .. } => {
                self.errs.push(not_yet("L0820", span, "`let` outside an `if` or `while` condition chain"));
                ERROR
            }
            Expr::OffsetOf { ty, fields } => {
                let t = self.resolve_written(*ty);
                let mut cur = self.deep(t);
                // The offset is baked into this body as a constant; the
                // layout fingerprint hashes field types deeply, so one
                // read set over the root type covers the field walk.
                p.record_layout_reads(&mut self.out.reads, &self.tys, cur);
                let mut off: u64 = 0;
                let mut bad = false;
                for &ffield in fields {
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
                    let found = match ffield {
                        crate::ast::OffsetField::Name(fname) => p.adt(a).variants[0].fields.iter().position(|f| f.name == fname),
                        crate::ast::OffsetField::Index(idx) => {
                            if p.adt(a).variants[0].shape == VariantShape::Tuple && (idx as usize) < p.adt(a).variants[0].fields.len() {
                                Some(idx as usize)
                            } else {
                                None
                            }
                        }
                    };
                    let Some(i) = found else {
                        let shown = match ffield {
                            crate::ast::OffsetField::Name(fname) => self.name(fname).to_string(),
                            crate::ast::OffsetField::Index(idx) => idx.to_string(),
                        };
                        self.err("L0103", span, format!("no field `{shown}` for `offset_of!`"), "Check the field name.");
                        bad = true;
                        break;
                    };
                    match ffield {
                        crate::ast::OffsetField::Name(fname) => self.check_field_vis(a, fname, span),
                        crate::ast::OffsetField::Index(idx) => self.check_tuple_field_vis(a, idx, span),
                    }
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
            Expr::Closure { is_move, is_async: false, params, ret, body } => self.closure_expr(e, *is_move, params, *ret, *body, expected),
            Expr::Closure { .. } => {
                self.err("L0820", span, "async closures are not supported yet", "Use a plain closure.");
                ERROR
            }
            Expr::Try(inner) => self.try_expr(e, *inner, span),
            Expr::Underscore => {
                self.err(
                    "L0110",
                    span,
                    "in expressions, `_` can only be used on the left-hand side of an assignment",
                    "Remove the `_`, or use it as a discard target in an assignment.",
                );
                ERROR
            }
            // AST v2 expression forms the parser still rejects.
            Expr::Await(_)
            | Expr::AsyncBlock { .. }
            | Expr::UnsafeBlock(_)
            | Expr::QPath { .. }
            | Expr::MacroCall(_) => ERROR,
        }
    }

    /// The `?` operator. On `Option` the enclosing return type must
    /// be an `Option`; on `Result` it must be a `Result` whose error
    /// type matches, widens numerically, or converts through a
    /// `From` impl, selected here like `From::from` itself is in
    /// `assoc_call`. The conversion plan rides in `Res` for lowering.
    fn try_expr(&mut self, e: ExprId, inner: ExprId, span: Span) -> Ty {
        let p = self.p;
        let it0 = self.expr(inner, None);
        self.run_obligations(false);
        let it = self.resolve(it0);
        let ret = self.closure_rets.last().copied().unwrap_or(self.f.ret);
        let ret = self.resolve(ret);
        let general_var = |cx: &Self, t: Ty| matches!(cx.tys.kind(t), TyKind::Infer(v) if !v.is_int() && !v.is_float());
        if let Some(elem) = self.tys.option_elem(it) {
            let ok = self.tys.option_elem(ret).is_some()
                || (general_var(self, ret) && {
                    let v = self.new_var(false);
                    let o = self.tys.mk_option(v);
                    self.unify(ret, o)
                });
            if !ok && self.kind(it) != TyKind::Error && self.kind(ret) != TyKind::Error {
                self.err(
                    "L0112",
                    span,
                    "the `?` operator on an `Option` can only be used in a function that returns `Option`",
                    "Change the return type to `Option<_>`, or handle the `None` case with `match`.",
                );
            }
            self.set_res(e, Res::TryPlain);
            return elem;
        }
        if let Some((ok_t, err_t)) = self.tys.result_args(it) {
            let ret_err = match self.tys.result_args(ret) {
                Some((_, e2)) => Some(e2),
                None if general_var(self, ret) => {
                    let o = self.new_var(false);
                    let r = self.tys.mk_result(o, err_t);
                    if self.unify(ret, r) { Some(err_t) } else { None }
                }
                None => None,
            };
            let Some(ret_err) = ret_err else {
                if self.kind(it) != TyKind::Error && self.kind(ret) != TyKind::Error {
                    self.err(
                        "L0112",
                        span,
                        "the `?` operator on a `Result` can only be used in a function that returns `Result`",
                        "Change the return type to `Result<_, _>`, or handle the `Err` case with `match`.",
                    );
                }
                self.set_res(e, Res::TryPlain);
                return ok_t;
            };
            // The common case: the error types already agree.
            let snap = self.snapshot_vars();
            if self.unify(err_t, ret_err) {
                self.set_res(e, Res::TryPlain);
                return ok_t;
            }
            self.rollback_vars(snap);
            let (e1, e2) = (self.resolve(err_t), self.resolve(ret_err));
            if Self::numeric_from_ok(self.kind(e1), self.kind(e2)) {
                self.set_res(e, Res::TryCast);
                return ok_t;
            }
            // The builtin `From<&str>` and `From<&String>` for
            // String: a copy, with no impl record behind it.
            if e2 == STRING && matches!(self.kind(e1), TyKind::Ref(_, _, i) if i == STR || i == STRING) {
                self.set_res(e, Res::TryStringFrom);
                return ok_t;
            }
            let args_id = self.tys.intern_args(&[GenericArg::Ty(e2), GenericArg::Ty(e1)]);
            let tr = TraitRef { def: p.gx.lang.from, args: args_id, bindings: EMPTY_BINDINGS };
            // The obligation is what makes a generic body without the
            // `From` bound fail at finish; selection here only picks
            // the call target for lowering.
            self.obl.push_trait_at(tr, span, 0);
            let sel = self.select_obligation_at(tr, span, 0);
            let from_fn = match &sel {
                Selection::Impl { id, args: impl_args, .. } => {
                    self.method_instance_for_impl(e, *id, tr, impl_args.clone(), "from", span).map(|(local, _, _)| local)
                }
                _ => None,
            };
            match (sel, from_fn) {
                (_, Some(local)) => self.set_res(e, Res::TryFrom(local)),
                // The MAX marker is a template-only plan: an instance
                // check re-selects and fills in the real target. In a
                // concrete body it would lower as a plain move of the
                // wrong type, so it must not escape a template check.
                (Selection::Impl { .. } | Selection::ParamEvidence(_), None) if self.is_template_check() => {
                    self.set_res(e, Res::TryFrom(LocalDefId(u32::MAX)))
                }
                _ => {
                    let (a, b) = (self.tn(e1), self.tn(e2));
                    self.err(
                        "L0112",
                        span,
                        format!("the `?` operator cannot convert the error type `{a}` to `{b}`"),
                        format!("Implement `From<{a}>` for `{b}`, or map the error before the `?`."),
                    );
                    self.set_res(e, Res::TryPlain);
                }
            }
            return ok_t;
        }
        if self.kind(it) != TyKind::Error {
            let tn = self.tn(it);
            self.err(
                "L0112",
                span,
                format!("the `?` operator can only be used on `Option` or `Result` values, not `{tn}`"),
                "Remove the `?`, or produce an `Option` or `Result` first.",
            );
        }
        self.set_res(e, Res::TryPlain);
        ERROR
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
        // Two plain fn items (or an item and a pointer) with one
        // signature join as a function pointer.
        if self.is_fn_item(a) || self.is_fn_item(b) || matches!(self.kind(a), TyKind::FnPtr(_)) {
            if let (Some(sa), Some(sb)) = (self.callable_sig(a), self.callable_sig(b))
                && sa == sb
            {
                let fp = self.fn_ptr_ty(&sa.0, sa.1);
                if let Some(be) = be {
                    self.coerce_expr(be, b, fp);
                }
                return fp;
            }
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
    /// (method autoref, format arguments), is an error at the borrow, unless
    /// the field type has alignment 1, when every address is aligned for it
    /// and Rust allows the reference.
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
            let ft = self.deep(self.out.expr_ty[self.ei(place_e)]);
            if crate::ty::layout::layout_of_ty(&self.tys, self.p, ft).is_ok_and(|l| l.align <= 1) {
                return;
            }
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

    /// The type of an assignment target. Tuple and array targets are
    /// destructuring assignment: their elements are targets in turn,
    /// and `_` discards its element with a fresh type variable. Every
    /// other target checks as the place expression it is.
    fn assign_lhs_ty(&mut self, e: ExprId) -> Ty {
        match self.p.ast.expr(e) {
            Expr::Underscore => {
                let t = self.new_var(false);
                self.set(e, t)
            }
            Expr::Tuple(elems) => {
                let ts: Vec<Ty> = elems.iter().map(|&el| self.assign_lhs_ty(el)).collect();
                let id = self.tys.intern_tys(&ts);
                let t = self.tys.intern(TyKind::Tuple(id));
                self.set(e, t)
            }
            Expr::Array(elems) => {
                let mut elem_ty = None;
                for &el in elems {
                    let et = self.assign_lhs_ty(el);
                    match elem_ty {
                        None => elem_ty = Some(et),
                        Some(prev) => {
                            if !self.unify(prev, et) {
                                let s = self.span(el);
                                self.mismatch(s, prev, et);
                            }
                        }
                    }
                }
                let elem = elem_ty.unwrap_or_else(|| self.new_var(false));
                let c = self.tys.intern_const(ConstKind::Int(elems.len() as u128));
                let t = self.tys.intern(TyKind::Array(elem, c));
                self.set(e, t)
            }
            _ => self.expr(e, None),
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
            Expr::Underscore => true,
            Expr::Tuple(elems) | Expr::Array(elems) => {
                for &el in elems {
                    self.place_check(el);
                }
                return;
            }
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
        // A const item or associated const the checker evaluated.
        if let Some(cv) = &self.out.const_exprs[self.ei(e)] {
            return match cv {
                crate::ty::consteval::ConstValue::Int(v) => Some(*v),
                crate::ty::consteval::ConstValue::Char(c) => Some(*c as i128),
                crate::ty::consteval::ConstValue::Bool(b) => Some(*b as i128),
                _ => None,
            };
        }
        match self.p.ast.expr(e) {
            Expr::Int(v, _) => Some(*v as u128 as i128),
            Expr::Char(c) => Some(*c as i128),
            Expr::Unary { op: UnOp::Neg, expr } => match self.p.ast.expr(*expr) {
                Expr::Int(v, _) => {
                    if *v == (1u128 << 127) {
                        Some(i128::MIN)
                    } else {
                        Some(-(*v as i128))
                    }
                }
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
            match self.body_item_of(name, span.ctxt) {
                Some(crate::check::collect::BodyItem::Fn(f)) => {
                    self.set_res(e, Res::Fn(f));
                    return ERROR;
                }
                Some(crate::check::collect::BodyItem::Const(ci)) => {
                    let c = &p.body_consts[ci as usize];
                    let (v, t) = (c.value.clone(), c.ty);
                    let i = self.ei(e);
                    self.out.const_exprs[i] = Some(v);
                    return self.deep(t);
                }
                Some(crate::check::collect::BodyItem::Static(idx)) => {
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
                None => {}
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
                return self.fn_value_ty(f, span);
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
                let shape = match p.sig_of(&mut self.out.reads, def) {
                    SigOf::Adt(adt) if !adt.is_enum => Some(adt.variants[0].shape),
                    _ => None,
                };
                match shape {
                    Some(VariantShape::Unit) => {
                        self.set_res(e, Res::Variant(a, 0));
                        return self.tys.adt_ty(a);
                    }
                    Some(VariantShape::Tuple) => {
                        self.set_res(e, Res::Variant(a, 0));
                        return self.ctor_value_ty(a, 0, span);
                    }
                    _ => {}
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
        // Float associated consts: `f64::NAN`, `f32::EPSILON`,
        // `std::f64::consts::PI`, and kin.
        {
            let names: Vec<&str> = segs.iter().map(|s| self.name(s.name)).collect();
            let assoc = match names.as_slice() {
                [t, item] => Some((*t, *item, false)),
                [pre, t, c, item] if matches!(*pre, "std" | "core") && *c == "consts" => Some((*t, *item, true)),
                _ => None,
            };
            if let Some((ty_name, item, module)) = assoc {
                let f = match ty_name {
                    "f32" => Some(FloatTy::F32),
                    "f64" => Some(FloatTy::F64),
                    _ => None,
                };
                if let Some(f) = f {
                    use crate::ty::consteval::ConstValue;
                    if module {
                        if let Some(bits) = crate::ty::consteval::float_consts_value(f, item) {
                            let i = self.ei(e);
                            self.out.const_exprs[i] = Some(ConstValue::Float(bits, f));
                            return self.tys.float_ty(f);
                        }
                    } else if let Some((v, int_ty)) = crate::ty::consteval::primitive_float_assoc(f, item) {
                        let i = self.ei(e);
                        return match int_ty {
                            Some(it) => {
                                self.out.const_exprs[i] = Some(ConstValue::Int(v as i64 as i128));
                                int(it)
                            }
                            None => {
                                self.out.const_exprs[i] = Some(ConstValue::Float(v, f));
                                self.tys.float_ty(f)
                            }
                        };
                    }
                }
            }
        }
        // Char associated consts.
        if segs.len() == 2 && segs[0].name == p.known.char {
            let c = match self.name(segs[1].name) {
                "MAX" => Some(char::MAX),
                "MIN" => Some(char::MIN),
                _ => None,
            };
            if let Some(c) = c {
                let i = self.ei(e);
                self.out.const_exprs[i] = Some(crate::ty::consteval::ConstValue::Char(c));
                return CHAR;
            }
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
        // Associated consts of inherent impls (Self::A, Type::A) read
        // as their evaluated value, like free consts.
        if let Some((adt, item)) = self.assoc_const_key(segs)
            && let Some(&idx) = p.assoc_const_names.get(&(adt, item))
        {
            let c = &p.consts[idx as usize];
            let (v, t) = (c.value.clone(), c.ty);
            let i = self.ei(e);
            self.out.const_exprs[i] = Some(v);
            return self.deep(t);
        }
        if let Some(r) = self.resolve_assoc(segs, span) {
            self.set_res(e, r);
            if r == Res::OptNone {
                let v = self.new_var(false);
                return self.tys.mk_option(v);
            }
            if let Res::Variant(a, v) = r {
                let variant = &p.adt(a).variants[v as usize];
                if variant.shape == VariantShape::Unit {
                    return self.tys.adt_ty(a);
                }
                if variant.shape == VariantShape::Tuple {
                    return self.ctor_value_ty(a, v, span);
                }
            }
            if let Res::Fn(f) = r {
                return self.fn_value_ty(f, span);
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
        if names.len() == 2 && names[1] == k.from_bits {
            if names[0] == k.f64 {
                return Some(Res::Builtin(Builtin::F64FromBits));
            }
            if names[0] == k.f32 {
                return Some(Res::Builtin(Builtin::F32FromBits));
            }
        }
        // `std::cmp::Ordering::Less` and kin: the one four-segment
        // value path in the subset today (the enum is the synthetic
        // Adt collect registers under its builtin def).
        if names.len() == 4
            && (names[0] == k.std || names[0] == k.core)
            && self.name(names[1]) == "cmp"
            && self.name(names[2]) == "Ordering"
            && let Some(a) = p.tys.local_adt_of(generics::ordering_def())
        {
            return match p.adt(a).variants.iter().position(|v| v.name == names[3]) {
                Some(v) => Some(Res::Variant(a, v as u32)),
                None => {
                    self.err(
                        "L0104",
                        span,
                        format!("no variant `{}` on `Ordering`", self.name(names[3])),
                        "Check the name: `Less`, `Equal`, or `Greater`.",
                    );
                    None
                }
            };
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
            } else if item == k.from {
                Builtin::VecFrom
            } else {
                self.err(
                    "L0104",
                    span,
                    format!("no function `Vec::{}`", self.name(item)),
                    "Lust supports Vec::new, Vec::with_capacity, and Vec::from.",
                );
                return None;
            };
            return Some(Res::Builtin(b));
        }
        // Qualified builtin variant constructors: `Option::Some(..)`,
        // `Result::Ok(..)`, `Result::Err(..)`.
        if ty_name == k.Option && item == k.Some {
            return Some(Res::OptSome);
        }
        if ty_name == k.Option && item == k.None {
            return Some(Res::OptNone);
        }
        if ty_name == k.Result && item == k.Ok {
            return Some(Res::ResOk);
        }
        if ty_name == k.Result && item == k.Err {
            return Some(Res::ResErr);
        }
        let adt = if ty_name == p.known.self_type {
            self.self_adt()
        } else {
            match ty_bound {
                BindingRes::Def(def) => p.adt_by_def(def),
                _ => None,
            }
        };
        let Some(a) = adt else {
            self.err("L0101", span, format!("cannot find type `{}`", crate::intern::source_name(self.name(ty_name))), "Check the spelling.");
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
        if let Some(&f) = p.methods.get(&(a, item)).and_then(|fs| fs.first()) {
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
        // The answer is baked into this body as a constant. Record a
        // layout read for every Adt in the type: the written-type
        // binding read only names an outermost path, so a compound
        // type (`[S; 2]`, `(S, u8)`) would record nothing for `S`.
        p.record_layout_reads(&mut self.out.reads, &self.tys, t);
        // A template check has no layout for a type over its params;
        // each instance answers with its own (the template body is
        // never generated). A const context still needs the number,
        // and its evaluator rejects the param (`ConstCx::layout`).
        // The placeholder still needs rustc's `T: Sized` requirement:
        // `size_of::<T>()` with only `T: ?Sized` in the env rejects.
        if self.is_template_check() && self.tys.flags(t).contains_param() {
            if !self.sized_ok(t) {
                let tn = self.tn(t);
                self.err(
                    "L0110",
                    span,
                    format!("the size for values of type `{tn}` cannot be known"),
                    "Add a `Sized` bound, or use `size_of_val` on a reference.",
                );
            }
            return Res::ConstUsize(0);
        }
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

    /// True for the scalar widening conversions `From` provides in
    /// std (identity is the blanket's job and also answers true).
    fn numeric_from_ok(src: TyKind, dst: TyKind) -> bool {
        let bits = |k: TyKind| match k {
            TyKind::Int(i) => Some((i.bits(), i.signed())),
            TyKind::Bool => Some((1, false)),
            TyKind::Char => Some((32, false)),
            _ => None,
        };
        match (bits(src), bits(dst)) {
            (Some((sb, ss)), Some((db, ds))) => {
                if src == dst {
                    return true;
                }
                if matches!(src, TyKind::Char) {
                    return matches!(dst, TyKind::Int(IntTy::U32 | IntTy::U64 | IntTy::Usize));
                }
                if matches!(src, TyKind::Bool) {
                    return matches!(dst, TyKind::Int(_));
                }
                db > sb && (!ss || ds) || db >= sb && ss == ds && db > sb
            }
            _ => src == dst,
        }
    }

    /// The Adt `Self` names in this body: the method's owner, or the
    /// scope's Self type (a trait default assoc fn has no receiver to
    /// name an owner).
    fn self_adt(&self) -> Option<AdtId> {
        self.f.owner.or_else(|| self.body_scope.self_ty.and_then(|t| self.tys.local_adt(t)))
    }

    /// The Self type of `Type::name(..)` when the call goes through a
    /// trait: `Type` is an Adt with no variant and no inherent fn called
    /// `name`, or `picked` (the template check already resolved the call
    /// through a trait). Type arguments are fresh variables.
    fn trait_assoc_base(&mut self, segs: &[ast::PathSeg], picked: bool) -> Option<Ty> {
        let p = self.p;
        let (ty_name, item) = (segs[0].name, segs[1].name);
        let a = if ty_name == p.known.self_type {
            self.self_adt()?
        } else {
            match self.binding(Namespace::Type, ty_name) {
                BindingRes::Def(def) => p.adt_by_def(def)?,
                _ => return None,
            }
        };
        if !picked && (p.methods.contains_key(&(a, item)) || (p.adt(a).is_enum && p.adt(a).variants.iter().any(|v| v.name == item))) {
            return None;
        }
        let generics = p.gx.adt_generics.get(a.0 as usize).cloned().unwrap_or_default();
        if generics.params.is_empty() {
            return Some(self.tys.adt_ty(a));
        }
        let args = self.fresh_args(&generics);
        Some(self.tys.mk_adt(p.def_of_adt(a), &args))
    }

    /// `W::<u8>::new()`: type arguments written on the type segment
    /// of a path call fix the Self type of the inherent impl, and so
    /// the impl's parameters in the method's template args.
    fn unify_written_self(&mut self, callee: ExprId, f: LocalDefId, inst_args: &[GenericArg], span: Span) {
        let p = self.p;
        let Expr::Path(segs) = p.ast.expr(callee) else { return };
        if segs.len() != 2 || segs[0].type_args().is_empty() {
            return;
        }
        let Some(owner) = p.fn_info(f).owner else { return };
        let Some(self_tmpl) = p.gx.fn_scopes.get(f.0 as usize).and_then(|s| s.scope.self_ty) else { return };
        let generics = p.gx.adt_generics.get(owner.0 as usize).cloned().unwrap_or_default();
        let written: Vec<ast::TyId> = segs[0].type_args();
        if written.len() != generics.params.len() || generics.params.iter().any(|g| g.kind != ParamKind::Type) {
            self.err(
                "L0105",
                span,
                format!("`{}` takes {} type argument(s) but {} were given", self.name(segs[0].name), generics.params.len(), written.len()),
                "Write one type argument per type parameter.",
            );
            return;
        }
        let gargs: Vec<GenericArg> = written.iter().map(|&t| GenericArg::Ty(self.resolve_written(t))).collect();
        let written_ty = self.tys.mk_adt(p.def_of_adt(owner), &gargs);
        let self_ty = subst(&mut self.tys, self_tmpl, inst_args);
        if !self.unify(self_ty, written_ty) {
            self.mismatch(span, written_ty, self_ty);
        }
    }

    /// An associated function call through a trait:
    /// `<T as Tr>::name(..)` or `T::name(..)`. Selects the impl
    /// for the Self type and calls the method as a free fn (an
    /// explicit receiver is simply its first parameter).
    fn assoc_call(
        &mut self,
        e: ExprId,
        callee: ExprId,
        base: Ty,
        hint: Option<TraitRef>,
        name: Sym,
        args: &[ExprId],
        span: Span,
    ) -> Option<Ty> {
        let p = self.p;
        // Numeric `From::from` is a widening cast, with no user
        // fn behind it (the lang blanket covers only identity).
        if self.name(name) == "from" && args.len() == 1 && hint.is_none_or(|h| h.def == p.gx.lang.from) {
            let src = self.expr(args[0], None);
            if Self::numeric_from_ok(self.kind(src), self.kind(base)) {
                self.set_res(callee, Res::FromCast);
                self.set_res(e, Res::FromCast);
                return Some(base);
            }
            let src_kind = self.kind(src);
            if matches!(src_kind, TyKind::Int(_) | TyKind::Char | TyKind::Bool) || src_kind.is_int_infer() || src_kind.is_float_infer() {
                // With the input type known from the argument,
                // selection can pick between input-specific impls
                // (or, in a template check, the bounds for each From).
                let args_id = self.tys.intern_args(&[GenericArg::Ty(base), GenericArg::Ty(src)]);
                let tr = TraitRef { def: p.gx.lang.from, args: args_id, bindings: EMPTY_BINDINGS };
                let found = match self.select_obligation_at(tr, span, 0) {
                    Selection::Impl { id, args: impl_args, .. } => self.method_instance_for_impl(e, id, tr, impl_args, "from", span),
                    Selection::ParamEvidence(_) => self.stub_instance(e, tr, name, span),
                    _ => None,
                };
                if let Some((local, params, ret)) = found {
                    self.set_res(e, Res::Fn(local));
                    self.check_args(&params, args, span);
                    return Some(self.normalize_here(ret));
                }
                return None;
            }
        }
        if self.name(name) == "default"
            && args.is_empty()
            && matches!(self.kind(base), TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit)
        {
            self.set_res(callee, Res::DefaultVal);
            self.set_res(e, Res::DefaultVal);
            return Some(base);
        }
        // The trait: written, or the template check's pick, or the
        // where clauses of a type parameter (rustc probes those as
        // inherent candidates first), or every trait in scope.
        let bound = if hint.is_none() { self.bound_traits_with(base, name) } else { Vec::new() };
        let traits: Vec<DefId> = match (hint, self.replay_pick(e)) {
            (Some(tr), _) => vec![tr.def],
            (None, Some(pick)) => vec![pick.trait_def],
            (None, None) if !bound.is_empty() => bound,
            (None, None) => {
                p.gx.traits_by_method
                    .get(&name)
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .filter(|&d| method::trait_in_scope_pub(self, d))
                    .collect()
            }
        };
        let mut hits: Vec<(LocalDefId, Vec<Ty>, Ty)> = Vec::new();
        let mut hit_traits: Vec<DefId> = Vec::new();
        for trait_def in traits {
            let Some(rec) = p.gx.index.trait_record(trait_def).cloned() else { continue };
            if rec.method_by_name(name).is_none() {
                continue;
            }
            let n_inputs = rec.generics.params.len().saturating_sub(1);
            let snap = self.snapshot_vars();
            let obl_len = self.obl_len();
            let sites_len = self.generic_sites.len();
            let tr = match hint {
                Some(written) if written.def == trait_def => written,
                _ => {
                    let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(base)];
                    for _ in 0..n_inputs {
                        tr_args.push(GenericArg::Ty(self.new_var(false)));
                    }
                    let args_id = self.tys.intern_args(&tr_args);
                    TraitRef { def: trait_def, args: args_id, bindings: EMPTY_BINDINGS }
                }
            };
            match self.select_obligation_at(tr, span, 0) {
                Selection::Impl { id, args: impl_args, .. } => {
                    let mname = self.name(name).to_string();
                    if let Some(found) = self.method_instance_for_impl(e, id, tr, impl_args, &mname, span) {
                        hits.push(found);
                        hit_traits.push(trait_def);
                        continue;
                    }
                }
                Selection::ParamEvidence(_) => {
                    if let Some(found) = self.stub_instance(e, tr, name, span) {
                        hits.push(found);
                        hit_traits.push(trait_def);
                        continue;
                    }
                }
                _ => {}
            }
            self.rollback_vars(snap);
            self.obl_truncate(obl_len);
            self.generic_sites.truncate(sites_len);
        }
        match hits.len() {
            1 => {
                let (local, params, ret) = hits.into_iter().next().unwrap();
                self.record_pick(e, hit_traits[0], 0, ReceiverForm::Value);
                self.set_res(e, Res::Fn(local));
                self.check_args(&params, args, span);
                Some(self.normalize_here(ret))
            }
            0 => None,
            _ => {
                self.err(
                    "L0720",
                    span,
                    format!("multiple trait methods named `{}` apply here", self.name(name)),
                    "Call the method with a fully qualified path, such as `<Type as Trait>::method(...)`.",
                );
                for &a in args {
                    self.expr(a, None);
                }
                Some(ERROR)
            }
        }
    }

    /// The trait method's signature stub for a call the param env
    /// proves (a template check), instantiated at the trait ref's
    /// args and the method's own fresh ones: (stub, params, ret).
    fn stub_instance(&mut self, e: ExprId, tr: TraitRef, name: Sym, span: Span) -> Option<(LocalDefId, Vec<Ty>, Ty)> {
        let p = self.p;
        let method_def = p.gx.index.trait_record(tr.def)?.method_by_name(name)?;
        let stub = *p.gx.trait_method_stubs.get(&method_def)?;
        let generics = p.gx.fn_templates.get(stub.0 as usize)?.as_ref()?.generics.clone();
        let raw: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
        let prefix: Vec<Option<GenericArg>> = raw
            .iter()
            .map(|&g| {
                Some(match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.deep(t)),
                    other => other,
                })
            })
            .collect();
        let (params, ret, _) = self.instantiate_template(e, stub, &generics, &prefix, span);
        Some((stub, params, ret))
    }

    /// A call through an Fn-family bound of a type parameter or
    /// projection in this body's env (a template check). Rust calls
    /// through `Fn` when the bounds give it, else `FnMut`, else
    /// `FnOnce`: (the trait method's stub, the receiver form, the
    /// input types, the output type).
    fn fn_bound_call(&mut self, callee: Ty) -> Option<(LocalDefId, Autoref, Vec<Ty>, Ty)> {
        let p = self.p;
        let lang = p.gx.lang;
        for (tr, method, autoref) in
            [(lang.fn_, "call", Autoref::Ref), (lang.fn_mut, "call_mut", Autoref::RefMut), (lang.fn_once, "call_once", Autoref::None)]
        {
            let Some(bound) = self.env().iter().find_map(|pred| match pred {
                Predicate::Trait(b)
                    if b.count == 0 && b.value.def == tr && self.tys.args(b.value.args).first().and_then(|g| g.as_ty()) == Some(callee) =>
                {
                    Some(b.value)
                }
                _ => None,
            }) else {
                continue;
            };
            let inputs = match self.tys.args(bound.args).get(1).and_then(|g| g.as_ty()).map(|t| self.tys.kind(t)) {
                Some(TyKind::Tuple(ts)) => self.tys.tys_of(ts).to_vec(),
                _ => Vec::new(),
            };
            // The output: the bound's own binding when written there,
            // else its projection, which the env's equalities settle.
            let out_assoc = lang.output_of(tr)?;
            let out = match self.tys.bindings(bound.bindings).iter().find(|(d, _)| *d == out_assoc).and_then(|(_, g)| g.as_ty()) {
                Some(t) => t,
                None => self.tys.intern(TyKind::Projection(AssocId(out_assoc), bound.args)),
            };
            let method_def = p.gx.index.trait_record(tr)?.method_by_name(p.interner.intern(method))?;
            let stub = *p.gx.trait_method_stubs.get(&method_def)?;
            return Some((stub, autoref, inputs, out));
        }
        None
    }

    /// The call resolution for a callable value's type: a fn pointer
    /// calls indirectly, a fn item calls its fn directly, and a
    /// constructor item builds its variant.
    fn callable_res(&mut self, ct: Ty) -> Option<Res> {
        match self.kind(ct) {
            TyKind::FnPtr(_) => Some(Res::Indirect),
            TyKind::FnDef(def, cargs) => match self.p.adt_by_def(def) {
                Some(a) => Some(Res::Variant(a, self.ctor_variant(cargs))),
                None => self.p.local_def(def.hash).map(Res::Fn),
            },
            _ => None,
        }
    }

    fn call(&mut self, e: ExprId, callee: ExprId, args: &[ExprId], span: Span) -> Ty {
        let p = self.p;
        // A callee that names a local (or is not a path at all)
        // is a value call: closures and Fn-bound parameters.
        let is_value = match p.ast.expr(callee) {
            Expr::Path(segs) if segs.len() == 1 => self.lookup(segs[0].name, self.span(callee).ctxt).is_some(),
            Expr::Path(_) | Expr::QPath { .. } => false,
            _ => true,
        };
        if is_value {
            return self.value_call(e, callee, args, span);
        }
        // `std::mem::drop(value)`: move the value and drop it now.
        // A user fn or body item named `drop` shadows the prelude
        // name, so the one-segment form checks those first.
        if let Expr::Path(segs) = p.ast.expr(callee) {
            let names: Vec<&str> = segs.iter().map(|s| self.name(s.name)).collect();
            let qualified = matches!(names.as_slice(), ["std" | "core", "mem", "drop"] | ["mem", "drop"]);
            let bare = names.as_slice() == ["drop"]
                && self.binding_fn(segs[0].name).is_none()
                && self.body_item_of(segs[0].name, self.span(callee).ctxt).is_none();
            if qualified || bare {
                if args.len() != 1 {
                    self.err(
                        "L0105",
                        span,
                        "this function takes 1 argument but a different number was given",
                        "Pass exactly one value.",
                    );
                    for &a in args {
                        self.expr(a, None);
                    }
                    return ERROR;
                }
                self.expr(args[0], None);
                self.set_res(e, Res::Builtin(Builtin::MemDrop));
                return UNIT;
            }
        }
        // `std::mem::size_of_val(&value)`: the size of the value's type.
        if let Expr::Path(segs) = p.ast.expr(callee) {
            let names: Vec<&str> = segs.iter().map(|s| self.name(s.name)).collect();
            let is_sov = matches!(names.as_slice(), ["size_of_val"] | ["mem", "size_of_val"])
                || matches!(names.as_slice(), ["std" | "core", "mem", "size_of_val"]);
            if is_sov {
                if args.len() != 1 {
                    self.err(
                        "L0105",
                        span,
                        "this function takes 1 argument but a different number was given",
                        "Pass exactly one reference.",
                    );
                    for &a in args {
                        self.expr(a, None);
                    }
                    return ERROR;
                }
                let at = self.expr(args[0], None);
                let at = self.deep(at);
                let inner = match self.kind(at) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => {
                        let tn = self.tn(at);
                        self.err("L0110", span, format!("`size_of_val` takes a reference, found `{tn}`"), "Pass `&value`.");
                        return ERROR;
                    }
                };
                let inner = self.deep(inner);
                p.record_layout_reads(&mut self.out.reads, &self.tys, inner);
                // A template check has no layout for a type over its
                // params (`size_of_val(t)` with `T: ?Sized` included);
                // each instance answers with its own, as in
                // `layout_query`. No Sized proof is needed here.
                if self.is_template_check() && self.tys.flags(inner).contains_param() {
                    self.set_res(e, Res::ConstUsize(0));
                    return USIZE;
                }
                return match crate::ty::layout::layout_of_ty(&self.tys, p, inner) {
                    Ok(l) => {
                        self.set_res(e, Res::ConstUsize(l.size));
                        USIZE
                    }
                    Err(()) => {
                        // Unsized tails with a runtime length: a slice
                        // is `len * size_of::<elem>()`, a `str` is its
                        // byte length. Other unsized forms (a generic
                        // Adt with an unsized last field, `dyn`) stay
                        // the layout reject.
                        let tail = match self.kind(inner) {
                            TyKind::Slice(elem) => {
                                crate::ty::layout::layout_of_ty(&self.tys, p, elem).ok().map(|l| (Builtin::SliceLen, l.size))
                            }
                            TyKind::Str => Some((Builtin::StrLen, 1)),
                            _ => None,
                        };
                        match tail {
                            Some((len, elem)) => {
                                self.set_res(e, Res::SizeOfVal { len, elem });
                                USIZE
                            }
                            None => {
                                self.err(
                                    "L0652",
                                    span,
                                    format!("unsupported layout form: `{}`", self.tn(inner)),
                                    "Use a type inside the supported layout grammar.",
                                );
                                ERROR
                            }
                        }
                    }
                };
            }
        }
        let res = match p.ast.expr(callee) {
            Expr::Path(segs) if segs.len() == 1 => {
                let name = segs[0].name;
                match self.body_item_of(name, self.span(callee).ctxt) {
                    Some(crate::check::collect::BodyItem::Fn(f)) => Res::Fn(f),
                    _ => match self.binding_fn(name) {
                        Some(f) => Res::Fn(f),
                        None if name == p.known.Some => Res::OptSome,
                    None if name == p.known.Ok => Res::ResOk,
                    None if name == p.known.Err => Res::ResErr,
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
                    },
                }
            }
            Expr::QPath { self_ty, trait_path, segs } => {
                if segs.len() == 1 {
                    let base = self.resolve_written(*self_ty);
                    let hint = if trait_path.is_empty() {
                        None
                    } else {
                        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                        let tref = ast::TraitRefExpr { path: trait_path.clone() };
                        generics::resolve_trait_ref(
                            p.ast,
                            p.interner,
                            p.known,
                            &cx,
                            &mut self.tys,
                            &self.body_scope.clone(),
                            base,
                            &tref,
                            span,
                        )
                        .ok()
                    };
                    if let Some(t) = self.assoc_call(e, callee, base, hint, segs[0].name, args, span) {
                        return t;
                    }
                }
                for &a in args {
                    self.expr(a, None);
                }
                self.err("L0101", span, "cannot find the associated function", "Check the trait and the name.");
                return ERROR;
            }
            Expr::Path(segs) => {
                // `T::assoc_fn(..)` on a type parameter, or `Self::f(..)`
                // in a trait default body (Self is the trait's param):
                // the trait comes from the bounds in scope here.
                let param_self = self.body_scope.self_ty.filter(|&t| matches!(self.tys.kind(t), TyKind::Param(_)));
                if segs.len() == 2
                    && let Some(base) = self
                        .body_scope
                        .param_tys
                        .iter()
                        .find(|(n, _)| *n == segs[0].name)
                        .map(|&(_, t)| t)
                        .or(if segs[0].name == p.known.self_type { param_self } else { None })
                    && let Some(t) = self.assoc_call(e, callee, base, None, segs[1].name, args, span)
                {
                    return t;
                }
                // `Trait::method(self_arg, ..)`: the trait name
                // heads the path and the first argument is the
                // receiver. The Self type comes from that
                // argument (trial-checked, then rechecked by the
                // assoc call itself).
                if segs.len() == 2 && !args.is_empty() {
                    let cxr = p.gx.resolve_cx(&p.type_names, &p.aliases);
                    if let Some(tdef) = cxr.trait_by_name(p.interner, segs[0].name)
                        && let Some(rec) = p.gx.index.trait_record(tdef).cloned()
                        && rec.method_by_name(segs[1].name).is_some()
                    {
                        let snap = self.snapshot_vars();
                        let obl_len = self.obl_len();
                        let sites_len = self.generic_sites.len();
                        let err_len = self.errs.len();
                        let at = self.expr(args[0], None);
                        let at = self.deep(at);
                        self.rollback_vars(snap);
                        self.obl_truncate(obl_len);
                        self.generic_sites.truncate(sites_len);
                        self.errs.truncate(err_len);
                        let mut bases = vec![at];
                        if let TyKind::Ref(_, _, inner) = self.tys.kind(at) {
                            bases.insert(0, self.deep(inner));
                        }
                        for base in bases {
                            let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(base)];
                            for _ in 1..rec.generics.params.len() {
                                tr_args.push(GenericArg::Ty(self.new_var(false)));
                            }
                            let args_id = self.tys.intern_args(&tr_args);
                            let hint = TraitRef { def: tdef, args: args_id, bindings: EMPTY_BINDINGS };
                            if let Some(t) = self.assoc_call(e, callee, base, Some(hint), segs[1].name, args, span) {
                                return t;
                            }
                        }
                    }
                }
                // `M::from(x)`: an Adt with no variant or inherent fn of
                // that name finds it in the traits in scope (rustc
                // probes inherent items first, then traits). A call the
                // template check resolved through a trait keeps that
                // trait (`Self::mk()` in a trait default body).
                if segs.len() == 2
                    && let Some(base) = self.trait_assoc_base(segs, self.replay_pick(e).is_some())
                    && let Some(t) = self.assoc_call(e, callee, base, None, segs[1].name, args, span)
                {
                    return t;
                }
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
            _ => return self.value_call(e, callee, args, span),
        };
        // An indirect call's callee is a value expression with a
        // resolution of its own (a local, an index): keep it.
        if res != Res::Indirect {
            self.set_res(callee, res);
        }
        self.set_res(e, res);
        if res == Res::OptSome {
            if args.len() != 1 {
                self.err("L0105", span, "`Some` takes one argument", "Write `Some(value)`.");
                return ERROR;
            }
            let t = self.expr(args[0], None);
            return self.tys.mk_option(t);
        }
        if res == Res::ResOk || res == Res::ResErr {
            let who = if res == Res::ResOk { "Ok" } else { "Err" };
            if args.len() != 1 {
                self.err("L0105", span, format!("`{who}` takes one argument"), format!("Write `{who}(value)`."));
                return ERROR;
            }
            // Turbofish on the constructor or on `Result` itself pins
            // both sides; otherwise the other side is a fresh var.
            let turbo: Vec<Ty> = match p.ast.expr(callee) {
                Expr::Path(segs) => segs
                    .iter()
                    .flat_map(|s| s.type_args())
                    .filter(|&g| !matches!(p.ast.ty(g), ast::TyExpr::Infer))
                    .map(|g| self.resolve_written(g))
                    .collect(),
                _ => Vec::new(),
            };
            let (want, other) = if turbo.len() == 2 {
                if res == Res::ResOk { (Some(turbo[0]), turbo[1]) } else { (Some(turbo[1]), turbo[0]) }
            } else {
                (None, self.new_var(false))
            };
            let t = self.expr(args[0], want);
            return if res == Res::ResOk { self.tys.mk_result(t, other) } else { self.tys.mk_result(other, t) };
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
                if let Some(Some(tmpl)) = p.gx.fn_templates.get(f.0 as usize).cloned() {
                    let explicit = self.explicit_call_args(callee);
                    let (params, ret, inst_args) = self.instantiate_template(e, f, &tmpl.generics.clone(), &explicit, span);
                    self.unify_written_self(callee, f, &inst_args, span);
                    self.check_args(&params, args, span);
                    return self.normalize_here(ret);
                }
                let (params, ret) = match p.sig_of(&mut self.out.reads, p.def_id(f)) {
                    SigOf::Fn(info) => (info.params.clone(), info.ret),
                    _ => return ERROR,
                };
                self.check_args(&params, args, span);
                ret
            }
            Res::Variant(a, v) => {
                if !p.adt(a).is_enum {
                    self.check_ctor_vis(a, span);
                }
                let adef = p.def_of_adt(a);
                let _ = p.sig_of(&mut self.out.reads, adef);
                let variant = &p.adt(a).variants[v as usize];
                if variant.shape != VariantShape::Tuple {
                    self.err("L0114", span, "this variant is not a tuple variant", "Use `Type::Variant` or `Type::Variant { .. }`.");
                    return ERROR;
                }
                let n = p.gx.adt_generics[a.0 as usize].params.len();
                if n == 0 {
                    let params: Vec<Ty> = variant.fields.iter().map(|f| f.ty).collect();
                    self.check_args(&params, args, span);
                    self.tys.adt_ty(a)
                } else {
                    let gen_args: Vec<GenericArg> = self.fresh_args(&p.gx.adt_generics[a.0 as usize].clone());
                    let params: Vec<Ty> = variant.fields.iter().map(|f| subst(&mut self.tys, f.ty, &gen_args)).collect();
                    self.check_args(&params, args, span);
                    // Forming the type owes its parameter bounds.
                    let preds = p.gx.adt_generics[a.0 as usize].predicates.clone();
                    if !preds.is_empty() {
                        self.push_predicates(&preds, &gen_args, span);
                    }
                    self.tys.mk_adt(adef, &gen_args)
                }
            }
            Res::Indirect => {
                let ct = self.out.expr_ty[self.ei(callee)];
                match self.callable_sig(ct) {
                    Some((params, ret)) => {
                        self.check_args(&params, args, span);
                        ret
                    }
                    None => ERROR,
                }
            }
            Res::Builtin(b) => {
                let (params, ret): (Vec<Ty>, Ty) = match b {
                    Builtin::StringNew => (vec![], STRING),
                    Builtin::StringFrom => (vec![REF_STR], STRING),
                    Builtin::StringWithCapacity => (vec![USIZE], STRING),
                    Builtin::EnvArgs => (vec![], ARGS),
                    Builtin::F64FromBits => (vec![int(IntTy::U64)], self.tys.float_ty(FloatTy::F64)),
                    Builtin::F32FromBits => (vec![int(IntTy::U32)], self.tys.float_ty(FloatTy::F32)),
                    Builtin::VecFrom => {
                        // The three forms lust takes: `&[T]` and
                        // `&[T; N]` (clone each element, exact
                        // capacity) and `[T; N]` (move each element).
                        // The argument is checked once here to pick
                        // the form; `check_args` below then checks it
                        // against its own type.
                        let at = if args.len() == 1 { self.expr(args[0], None) } else { ERROR };
                        let at = self.resolve(at);
                        let elem = match self.kind(at) {
                            TyKind::Ref(_, _, inner) => match self.kind(self.resolve(inner)) {
                                TyKind::Slice(e) | TyKind::Array(e, _) => {
                                    self.deferred_clone.push((e, span));
                                    Some(e)
                                }
                                _ => None,
                            },
                            TyKind::Array(e, _) => Some(e),
                            TyKind::Error => Some(ERROR),
                            TyKind::Infer(_) => Some(ERROR),
                            _ => None,
                        };
                        match elem {
                            Some(e) => (vec![at], self.tys.mk_vec(e)),
                            None => {
                                let tn = self.tn(at);
                                self.err(
                                    "L0110",
                                    span,
                                    format!("`Vec::from` needs a slice or an array, found `{tn}`"),
                                    "Pass `&[T]`, `&[T; N]`, or `[T; N]`.",
                                );
                                (vec![at], ERROR)
                            }
                        }
                    }
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
        // Closure arguments check last, as rustc does: their parameter
        // types often come from the other arguments (`apply(|x| .., 5u8)`).
        for closures in [false, true] {
            for (i, &a) in args.iter().enumerate() {
                if matches!(self.p.ast.expr(a), Expr::Closure { .. }) != closures {
                    continue;
                }
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
    }

    /// A comparison trait method on a scalar receiver in method
    /// form (`a.partial_cmp(b)`, `a.cmp(b)`, `a.eq(b)`, `a.lt(b)`,
    /// and kin): core's impls for the scalar types are the scalar
    /// comparisons themselves, so the call resolves here and
    /// lowering emits them (`Res::PrimCmp`). This is also where a
    /// template pick for one of these traits lands in an instance
    /// (`builtin_only`: the trait was fixed by the template check,
    /// so no ambiguity question is asked again). Without a pick,
    /// another in-scope trait with an impl of the same method name
    /// for this receiver makes the call ambiguous in rustc: the
    /// probe then reports the ambiguity itself.
    #[allow(clippy::too_many_arguments)]
    fn prim_cmp_method(
        &mut self,
        e: ExprId,
        recv: ExprId,
        base: Ty,
        derefs: u8,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        builtin_only: bool,
    ) -> Option<Ty> {
        if !turbofish.is_empty() {
            return None;
        }
        let p = self.p;
        let lang = &p.gx.lang;
        let bk = self.kind(base);
        let intlike = matches!(bk, TyKind::Int(_)) || bk.is_int_infer();
        let floatlike = matches!(bk, TyKind::Float(_)) || bk.is_float_infer();
        if !intlike && !floatlike && !matches!(bk, TyKind::Bool | TyKind::Char) {
            return None;
        }
        let (kind, trait_def) = match self.name(name) {
            "partial_cmp" => (PrimCmpKind::Partial(p.tys.local_adt_of(generics::ordering_def())?), lang.partial_ord),
            "cmp" if !floatlike => (PrimCmpKind::Total(p.tys.local_adt_of(generics::ordering_def())?), lang.ord),
            "eq" => (PrimCmpKind::Op(BinOp::Eq), lang.partial_eq),
            "ne" => (PrimCmpKind::Op(BinOp::Ne), lang.partial_eq),
            "lt" => (PrimCmpKind::Op(BinOp::Lt), lang.partial_ord),
            "le" => (PrimCmpKind::Op(BinOp::Le), lang.partial_ord),
            "gt" => (PrimCmpKind::Op(BinOp::Gt), lang.partial_ord),
            "ge" => (PrimCmpKind::Op(BinOp::Ge), lang.partial_ord),
            _ => return None,
        };
        if !builtin_only {
            // Prelude traits are always in scope; a second in-scope
            // trait with an impl for this receiver would make the
            // call ambiguous (rustc E0034), never silently this one.
            let others: Vec<DefId> = p
                .gx
                .traits_by_method
                .get(&name)
                .cloned()
                .unwrap_or_default()
                .into_iter()
                .filter(|&d| d != trait_def && method::trait_in_scope_pub(self, d))
                .collect();
            for other in others {
                let Some(rec) = p.gx.index.trait_record(other) else { continue };
                let snap = self.snapshot_vars();
                let obl_len = self.obl_len();
                let mut tr_args: Vec<GenericArg> = vec![GenericArg::Ty(base)];
                for _ in 1..rec.generics.params.len() {
                    tr_args.push(GenericArg::Ty(self.new_var(false)));
                }
                let args_id = self.tys.intern_args(&tr_args);
                let tr = TraitRef { def: other, args: args_id, bindings: EMPTY_BINDINGS };
                let hits = matches!(self.select_obligation(tr), Selection::Impl { .. } | Selection::ParamEvidence(_));
                self.rollback_vars(snap);
                self.obl_truncate(obl_len);
                if hits {
                    // Declining would let the generic search below
                    // take the other trait alone (the lang candidate
                    // has no impl method fn there), which accepts a
                    // call rustc rejects as ambiguous: report it here.
                    self.err(
                        "L0720",
                        name_span,
                        format!("multiple trait methods named `{}` apply here", self.name(name)),
                        "Call the method with a fully qualified path, such as `<Type as Trait>::method(...)`.",
                    );
                    for &a in args {
                        self.expr(a, None);
                    }
                    return Some(ERROR);
                }
            }
        }
        self.check_packed_borrow(recv, name_span);
        let other_ty = self.tys.mk_ref(false, base);
        self.check_args(&[other_ty], args, name_span);
        self.set_res(e, Res::PrimCmp { kind, derefs });
        Some(match kind {
            PrimCmpKind::Partial(_) => {
                let ord = generics::ordering_ty(&mut self.tys);
                self.tys.mk_option(ord)
            }
            PrimCmpKind::Total(_) => generics::ordering_ty(&mut self.tys),
            PrimCmpKind::Op(_) => BOOL,
        })
    }

    fn method_call(
        &mut self,
        e: ExprId,
        recv: ExprId,
        name: Sym,
        name_span: Span,
        args: &[ExprId],
        turbofish: &[ast::GenericArg],
        expected: Option<Ty>,
    ) -> Ty {
        let p = self.p;
        let k = p.known;
        let rt = self.expr(recv, None);
        let rt = self.deep(rt);
        // ARCH 2.12 run point: a method call must know the receiver type. The
        // obligation queue runs just before that head is required (ARCH 2.4).
        self.run_obligations(false);
        let (derefs, base) = self.autoderef(rt);
        self.check_method_vis(base, name, name_span);
        let bk = self.tys.kind(base);
        // ARCH 2.12: a method call needs a known receiver head (rustc
        // E0282, also for a closure parameter a later call would fix).
        if let TyKind::Infer(v) = bk
            && !v.is_int()
            && !v.is_float()
        {
            self.err(
                "L0610",
                name_span,
                "type annotations needed: the receiver type must be known here",
                "Annotate the receiver's type, for example the closure parameter as `|x: Vec<u8>|`.",
            );
            for &a in args {
                self.expr(a, None);
            }
            return ERROR;
        }
        // User methods, through the method-set probes of section 2.10: every
        // form is probed in order and recorded, hit or miss, before the
        // builtin compat dispatch below runs.
        let head = Head::of(&self.tys, base);
        // Turbofish args of the method (`x.m::<U>(..)`), resolved
        // in this body's scope for the generic probes below.
        let explicit: Vec<Option<GenericArg>> = turbofish
            .iter()
            .map(|a| match a {
                ast::GenericArg::Type(t) => Some(GenericArg::Ty(self.resolve_written(*t))),
                ast::GenericArg::Const(e2) => crate::check::collect::eval_array_len(p.ast, p.interner, p.known, *e2).map(|v| {
                    let c = self.tys.intern_const(ConstKind::Int(v));
                    GenericArg::Const(c)
                }),
                _ => None,
            })
            .collect();
        // A call the template check resolved through a trait keeps
        // that trait in every other check of the body (ARCH 4.1):
        // selection on this body's Self type picks the impl, and no
        // method lookup runs again.
        let mut builtin_only = false;
        if let Some(pick) = self.replay_pick(e) {
            match picks::replay_method(self, e, rt, pick, name, name_span, args, &explicit, expected) {
                Some(ret) => return ret,
                None => builtin_only = true,
            }
        }
        // Generic and trait receivers go through the full 2.10
        // search (check/method.rs), which probes plain inherent
        // methods with the same recorded reads, in step+form
        // order. Builtin and scalar receivers stay on the path
        // below.
        if p.gx.has_generics
            && !builtin_only
            && (self.tys.local_adt(base).is_some()
                || matches!(self.tys.kind(base), TyKind::Param(_) | TyKind::Projection(..) | TyKind::Dyn(..)))
        {
            match method::generic_method_search(self, e, rt, name, name_span, args, &explicit, expected) {
                method::Probe::Hit(ret) => return ret,
                method::Probe::Failed => return ERROR,
                method::Probe::Miss => {}
            }
        }
        // Every candidate of every form, in probe order. The set
        // is keyed by the template Adt head, so a candidate only
        // counts when its receiver type unifies with this
        // receiver (a method of `impl W<u8>` does not apply to
        // `W<u32>`); templates confirm inside their probe.
        let mut assoc_fn_seen = false;
        for form in ReceiverForm::PROBE_ORDER {
            if builtin_only {
                break;
            }
            let set = p.method_set(&mut self.out.reads, head, name, form);
            for c in set.candidates {
                let Some(cform) = c.receiver else {
                    assoc_fn_seen = true;
                    continue;
                };
                let f = p.local_def(c.def.hash).expect("a method candidate names a local fn");
                if !turbofish.is_empty() && p.gx.fn_templates.get(f.0 as usize).is_none_or(|t| t.is_none()) {
                    self.errs.push(not_yet("L0721", name_span, "turbofish on method calls"));
                    for &a in args {
                        self.expr(a, None);
                    }
                    return ERROR;
                }
                // A generic inherent method: instantiate it like a
                // generic call, with the receiver unifying the impl
                // and method parameters.
                if p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) {
                    let probe = method::RcvProbe::at(self, base, cform);
                    match method::inherent_template_probe(self, e, probe, derefs, name, name_span, args, &explicit) {
                        method::Probe::Hit(ret) => return ret,
                        method::Probe::Failed => return ERROR,
                        method::Probe::Miss => continue,
                    }
                }
                let probe = method::RcvProbe::at(self, base, cform);
                let (params, ret) = match p.sig_of(&mut self.out.reads, c.def) {
                    SigOf::Fn(info) => (info.params.clone(), info.ret),
                    _ => return ERROR,
                };
                let snap_vars = self.snapshot_vars();
                let obl_len = self.obl_len();
                if params.first().is_none_or(|&want| !self.unify(want, probe.recv_ty)) {
                    self.rollback_vars(snap_vars);
                    self.obl_truncate(obl_len);
                    continue;
                }
                if probe.autoref != Autoref::None {
                    self.check_packed_borrow(recv, name_span);
                }
                self.set_res(e, Res::Method { f, derefs, autoref: probe.autoref });
                self.check_args(&params[1.min(params.len())..], args, name_span);
                return ret;
            }
        }
        if assoc_fn_seen {
            self.err(
                "L0104",
                name_span,
                format!("`{}` is an associated function, not a method", self.name(name)),
                "Call it as `Type::name(...)`.",
            );
            return ERROR;
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
        // Comparison trait methods on a scalar receiver
        // (`partial_cmp`, `cmp`, `eq`, `lt`, and kin in method
        // form): the template side is the lang stub, the instance
        // side is the scalar comparison itself.
        if let Some(ret) = self.prim_cmp_method(e, recv, base, derefs, name, name_span, args, turbofish, builtin_only) {
            return ret;
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
                    self.deferred_eq.push((elem, name_span));
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
                } else if name == k.capacity {
                    Some((B::VecCapacity, Autoref::Ref, vec![], USIZE))
                } else if name == k.reserve {
                    Some((B::VecReserve, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.reserve_exact {
                    Some((B::VecReserveExact, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.shrink_to_fit {
                    Some((B::VecShrinkToFit, Autoref::RefMut, vec![], UNIT))
                } else if name == k.shrink_to {
                    Some((B::VecShrinkTo, Autoref::RefMut, vec![USIZE], UNIT))
                } else if name == k.swap_remove {
                    Some((B::VecSwapRemove, Autoref::RefMut, vec![USIZE], elem))
                } else if name == k.append {
                    let r = self.tys.mk_ref(true, base);
                    Some((B::VecAppend, Autoref::RefMut, vec![r], UNIT))
                } else if name == k.extend_from_slice {
                    self.deferred_clone.push((elem, name_span));
                    let sl = self.tys.intern(TyKind::Slice(elem));
                    let r = self.tys.mk_ref(false, sl);
                    Some((B::VecExtendFromSlice, Autoref::RefMut, vec![r], UNIT))
                } else if name == k.split_off {
                    Some((B::VecSplitOff, Autoref::RefMut, vec![USIZE], base))
                } else if name == k.resize {
                    self.deferred_clone.push((elem, name_span));
                    Some((B::VecResize, Autoref::RefMut, vec![USIZE, elem], UNIT))
                } else if name == k.dedup {
                    self.deferred_eq.push((elem, name_span));
                    Some((B::VecDedup, Autoref::RefMut, vec![], UNIT))
                } else if name == k.reverse {
                    Some((B::VecReverse, Autoref::RefMut, vec![], UNIT))
                } else if name == k.first_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecFirstMut, Autoref::RefMut, vec![], opt_ref))
                } else if name == k.last_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecLastMut, Autoref::RefMut, vec![], opt_ref))
                } else if name == k.get_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecGetMut, Autoref::RefMut, vec![USIZE], opt_ref))
                } else if name == k.as_slice {
                    let sl = self.tys.intern(TyKind::Slice(elem));
                    let r = self.tys.mk_ref(false, sl);
                    Some((B::VecAsSlice, Autoref::Ref, vec![], r))
                } else if name == k.as_mut_slice {
                    let sl = self.tys.intern(TyKind::Slice(elem));
                    let r = self.tys.mk_ref(true, sl);
                    Some((B::VecAsMutSlice, Autoref::RefMut, vec![], r))
                } else {
                    None
                }
            }
            (None, TyKind::Slice(_)) | (None, TyKind::Array(..)) => {
                let elem = match bk {
                    TyKind::Slice(e) | TyKind::Array(e, _) => e,
                    _ => ERROR,
                };
                if name == k.len {
                    Some((B::SliceLen, Autoref::Ref, vec![], USIZE))
                } else if name == k.is_empty {
                    Some((B::SliceIsEmpty, Autoref::Ref, vec![], BOOL))
                } else if name == k.to_vec {
                    self.deferred_clone.push((elem, name_span));
                    let v = self.tys.mk_vec(elem);
                    Some((B::SliceToVec, Autoref::Ref, vec![], v))
                } else if name == k.reverse {
                    Some((B::VecReverse, Autoref::RefMut, vec![], UNIT))
                } else if name == k.first {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecFirst, Autoref::Ref, vec![], opt_ref))
                } else if name == k.last {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecLast, Autoref::Ref, vec![], opt_ref))
                } else if name == k.get {
                    let r = self.tys.mk_ref(false, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecGet, Autoref::Ref, vec![USIZE], opt_ref))
                } else if name == k.first_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecFirstMut, Autoref::RefMut, vec![], opt_ref))
                } else if name == k.last_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecLastMut, Autoref::RefMut, vec![], opt_ref))
                } else if name == k.get_mut {
                    let r = self.tys.mk_ref(true, elem);
                    let opt_ref = self.tys.mk_option(r);
                    Some((B::VecGetMut, Autoref::RefMut, vec![USIZE], opt_ref))
                } else if name == k.contains {
                    self.deferred_eq.push((elem, name_span));
                    let r = self.tys.mk_ref(false, elem);
                    Some((B::VecContains, Autoref::Ref, vec![r], BOOL))
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
                } else if name == k.is_digit {
                    Some((B::CharIsDigitRadix, Autoref::None, vec![int(IntTy::U32)], BOOL))
                } else if name == k.len_utf8 {
                    Some((B::CharLenUtf8, Autoref::None, vec![], USIZE))
                } else if name == k.len_utf16 {
                    Some((B::CharLenUtf16, Autoref::None, vec![], USIZE))
                } else if name == k.is_ascii {
                    Some((B::CharIsAscii, Autoref::Ref, vec![], BOOL))
                } else if name == k.is_ascii_punctuation {
                    Some((B::CharIsAsciiPunctuation, Autoref::Ref, vec![], BOOL))
                } else if name == k.is_ascii_graphic {
                    Some((B::CharIsAsciiGraphic, Autoref::Ref, vec![], BOOL))
                } else if name == k.is_ascii_hexdigit {
                    Some((B::CharIsAsciiHexdigit, Autoref::Ref, vec![], BOOL))
                } else if name == k.is_ascii_control {
                    Some((B::CharIsAsciiControl, Autoref::Ref, vec![], BOOL))
                } else {
                    None
                }
            }
            (None, TyKind::Int(i)) => self.int_method(name, base, i),
            (None, TyKind::Float(f)) => self.float_method(name, base, f),
            // A float of unknown width: float-returning methods return
            // the variable itself, so a later use can still settle it.
            (None, k2) if k2.is_float_infer() => self.float_method(name, base, FloatTy::F64),
            (None, TyKind::Bool | TyKind::Char) if name == k.to_string => Some((B::ToString, Autoref::Ref, vec![], STRING)),
            (Some(BuiltinTy::Args), _) if name == k.count => Some((B::ArgsCount, Autoref::None, vec![], USIZE)),
            // Trait methods work on an integer of unknown type; inherent ones (pow, abs) do not.
            (None, k2) if k2.is_int_infer() && name == k.min => Some((B::Min, Autoref::None, vec![base], base)),
            (None, k2) if k2.is_int_infer() && name == k.max => Some((B::Max, Autoref::None, vec![base], base)),
            (None, k2) if k2.is_int_infer() && name == k.to_string => Some((B::ToString, Autoref::Ref, vec![], STRING)),
            (None, k2) if k2.is_int_infer() => {
                // A trait method still applies: selection fixes the
                // integer type when exactly one impl matches, as in
                // rustc. Inherent integer methods need the type.
                if p.gx.has_generics && !builtin_only {
                    match method::generic_method_search(self, e, rt, name, name_span, args, &explicit, expected) {
                        method::Probe::Hit(ret) => return ret,
                        method::Probe::Failed => return ERROR,
                        method::Probe::Miss => {}
                    }
                }
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
                // Generic and trait methods over the full autoderef
                // chain (check/method.rs).
                if p.gx.has_generics && !builtin_only {
                    match method::generic_method_search(self, e, rt, name, name_span, args, &explicit, expected) {
                        method::Probe::Hit(ret) => return ret,
                        method::Probe::Failed => return ERROR,
                        method::Probe::Miss => {}
                    }
                }
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

    /// Inherent integer methods (`checked_add`, `count_ones`, and kin).
    /// All take the receiver by value. The 128-bit checked, saturating,
    /// and overflowing families (plus euclid division) are not
    /// implemented yet and answer None, like a missing method.
    fn int_method(&mut self, name: Sym, t: Ty, i: IntTy) -> Option<(Builtin, Autoref, Vec<Ty>, Ty)> {
        use Builtin as B;
        let k = self.p.known;
        let s = i.signed();
        let w128 = i.bits() >= 128;
        let u32t = int(IntTy::U32);
        let bin = |b: Builtin| Some((b, Autoref::None, vec![t], t));
        let chk = |b: Builtin, cx: &mut Self| {
            let o = cx.tys.mk_option(t);
            Some((b, Autoref::None, vec![t], o))
        };
        let ovf = |b: Builtin, cx: &mut Self| {
            let ts = cx.tys.intern_tys(&[t, BOOL]);
            let tt = cx.tys.intern(TyKind::Tuple(ts));
            Some((b, Autoref::None, vec![t], tt))
        };
        let sh = |b: Builtin| Some((b, Autoref::None, vec![u32t], t));
        let un = |b: Builtin| Some((b, Autoref::None, vec![], t));
        let n = name;
        // The families that stay within the value (wrapping and plain).
        if n == k.wrapping_add {
            return bin(B::WrappingAdd);
        }
        if n == k.wrapping_sub {
            return bin(B::WrappingSub);
        }
        if n == k.wrapping_mul {
            return bin(B::WrappingMul);
        }
        if n == k.wrapping_div && !w128 {
            return bin(B::WrappingDiv);
        }
        if n == k.wrapping_rem && !w128 {
            return bin(B::WrappingRem);
        }
        if n == k.wrapping_neg {
            return un(B::WrappingNeg);
        }
        if n == k.wrapping_pow && !w128 {
            return sh(B::WrappingPow);
        }
        if n == k.wrapping_shl {
            return sh(B::WrappingShl);
        }
        if n == k.wrapping_shr {
            return sh(B::WrappingShr);
        }
        if n == k.wrapping_abs && s {
            return un(B::WrappingAbs);
        }
        if n == k.abs && s {
            return un(B::Abs);
        }
        if n == k.pow {
            return sh(B::Pow);
        }
        if n == k.min {
            return bin(B::Min);
        }
        if n == k.max {
            return bin(B::Max);
        }
        if n == k.div_euclid && !w128 {
            return bin(B::DivEuclid);
        }
        if n == k.rem_euclid && !w128 {
            return bin(B::RemEuclid);
        }
        if n == k.signum && s {
            return un(B::Signum);
        }
        if n == k.is_positive && s {
            return Some((B::IsPositive, Autoref::None, vec![], BOOL));
        }
        if n == k.is_negative && s {
            return Some((B::IsNegative, Autoref::None, vec![], BOOL));
        }
        if n == k.is_power_of_two && !s {
            return Some((B::IsPowerOfTwo, Autoref::None, vec![], BOOL));
        }
        if n == k.count_ones {
            return Some((B::CountOnes, Autoref::None, vec![], u32t));
        }
        if n == k.count_zeros {
            return Some((B::CountZeros, Autoref::None, vec![], u32t));
        }
        if n == k.leading_zeros {
            return Some((B::LeadingZeros, Autoref::None, vec![], u32t));
        }
        if n == k.trailing_zeros {
            return Some((B::TrailingZeros, Autoref::None, vec![], u32t));
        }
        if n == k.leading_ones {
            return Some((B::LeadingOnes, Autoref::None, vec![], u32t));
        }
        if n == k.trailing_ones {
            return Some((B::TrailingOnes, Autoref::None, vec![], u32t));
        }
        if n == k.rotate_left {
            return sh(B::RotateLeft);
        }
        if n == k.rotate_right {
            return sh(B::RotateRight);
        }
        if n == k.swap_bytes {
            return un(B::SwapBytes);
        }
        if n == k.reverse_bits {
            return un(B::ReverseBits);
        }
        if n == k.to_string {
            return Some((B::ToString, Autoref::Ref, vec![], STRING));
        }
        if w128 {
            return None;
        }
        // Checked, saturating, and overflowing families (64-bit and below).
        if n == k.checked_add {
            return chk(B::CheckedAdd, self);
        }
        if n == k.checked_sub {
            return chk(B::CheckedSub, self);
        }
        if n == k.checked_mul {
            return chk(B::CheckedMul, self);
        }
        if n == k.checked_div {
            return chk(B::CheckedDiv, self);
        }
        if n == k.checked_rem {
            return chk(B::CheckedRem, self);
        }
        if n == k.checked_neg {
            let o = self.tys.mk_option(t);
            return Some((B::CheckedNeg, Autoref::None, vec![], o));
        }
        if n == k.checked_abs && s {
            let o = self.tys.mk_option(t);
            return Some((B::CheckedAbs, Autoref::None, vec![], o));
        }
        if n == k.checked_pow {
            let o = self.tys.mk_option(t);
            return Some((B::CheckedPow, Autoref::None, vec![u32t], o));
        }
        if n == k.checked_shl {
            let o = self.tys.mk_option(t);
            return Some((B::CheckedShl, Autoref::None, vec![u32t], o));
        }
        if n == k.checked_shr {
            let o = self.tys.mk_option(t);
            return Some((B::CheckedShr, Autoref::None, vec![u32t], o));
        }
        if n == k.saturating_add {
            return bin(B::SaturatingAdd);
        }
        if n == k.saturating_sub {
            return bin(B::SaturatingSub);
        }
        if n == k.saturating_mul {
            return bin(B::SaturatingMul);
        }
        if n == k.saturating_div {
            return bin(B::SaturatingDiv);
        }
        if n == k.saturating_neg && s {
            return un(B::SaturatingNeg);
        }
        if n == k.saturating_abs && s {
            return un(B::SaturatingAbs);
        }
        if n == k.saturating_pow {
            return sh(B::SaturatingPow);
        }
        if n == k.overflowing_add {
            return ovf(B::OverflowingAdd, self);
        }
        if n == k.overflowing_sub {
            return ovf(B::OverflowingSub, self);
        }
        if n == k.overflowing_mul {
            return ovf(B::OverflowingMul, self);
        }
        if n == k.overflowing_div {
            return ovf(B::OverflowingDiv, self);
        }
        if n == k.overflowing_rem {
            return ovf(B::OverflowingRem, self);
        }
        if n == k.overflowing_neg {
            let ts = self.tys.intern_tys(&[t, BOOL]);
            let tt = self.tys.intern(TyKind::Tuple(ts));
            return Some((B::OverflowingNeg, Autoref::None, vec![], tt));
        }
        if n == k.overflowing_abs && s {
            let ts = self.tys.intern_tys(&[t, BOOL]);
            let tt = self.tys.intern(TyKind::Tuple(ts));
            return Some((B::OverflowingAbs, Autoref::None, vec![], tt));
        }
        if n == k.overflowing_pow {
            let ts = self.tys.intern_tys(&[t, BOOL]);
            let tt = self.tys.intern(TyKind::Tuple(ts));
            return Some((B::OverflowingPow, Autoref::None, vec![u32t], tt));
        }
        if n == k.overflowing_shl {
            let ts = self.tys.intern_tys(&[t, BOOL]);
            let tt = self.tys.intern(TyKind::Tuple(ts));
            return Some((B::OverflowingShl, Autoref::None, vec![u32t], tt));
        }
        if n == k.overflowing_shr {
            let ts = self.tys.intern_tys(&[t, BOOL]);
            let tt = self.tys.intern(TyKind::Tuple(ts));
            return Some((B::OverflowingShr, Autoref::None, vec![u32t], tt));
        }
        None
    }

    /// Inherent float methods (`sqrt`, `powi`, `to_bits`, and kin).
    /// `t` is the receiver type (a float variable for an unsuffixed
    /// literal), `f` its width when known (f64 for a variable).
    fn float_method(&mut self, name: Sym, t: Ty, f: FloatTy) -> Option<(Builtin, Autoref, Vec<Ty>, Ty)> {
        use Builtin as B;
        let k = self.p.known;
        let un = |b: Builtin| Some((b, Autoref::None, vec![], t));
        let n = name;
        if n == k.sqrt {
            return un(B::FloatSqrt);
        }
        if n == k.abs {
            return un(B::FloatAbs);
        }
        if n == k.floor {
            return un(B::FloatFloor);
        }
        if n == k.ceil {
            return un(B::FloatCeil);
        }
        if n == k.round {
            return un(B::FloatRound);
        }
        if n == k.trunc {
            return un(B::FloatTrunc);
        }
        if n == k.fract {
            return un(B::FloatFract);
        }
        if n == k.signum {
            return un(B::FloatSignum);
        }
        if n == k.recip {
            return un(B::FloatRecip);
        }
        if n == k.exp {
            return un(B::FloatExp);
        }
        if n == k.ln {
            return un(B::FloatLn);
        }
        if n == k.log2 {
            return un(B::FloatLog2);
        }
        if n == k.log10 {
            return un(B::FloatLog10);
        }
        if n == k.powi {
            return Some((B::FloatPowi, Autoref::None, vec![int(IntTy::I32)], t));
        }
        if n == k.powf {
            return Some((B::FloatPowf, Autoref::None, vec![t], t));
        }
        if n == k.log {
            return Some((B::FloatLog, Autoref::None, vec![t], t));
        }
        if n == k.mul_add {
            return Some((B::FloatMulAdd, Autoref::None, vec![t, t], t));
        }
        if n == k.min {
            return Some((B::FloatMin, Autoref::None, vec![t], t));
        }
        if n == k.max {
            return Some((B::FloatMax, Autoref::None, vec![t], t));
        }
        if n == k.copysign {
            return Some((B::FloatCopysign, Autoref::None, vec![t], t));
        }
        if n == k.is_nan {
            return Some((B::FloatIsNan, Autoref::None, vec![], BOOL));
        }
        if n == k.is_infinite {
            return Some((B::FloatIsInfinite, Autoref::None, vec![], BOOL));
        }
        if n == k.is_finite {
            return Some((B::FloatIsFinite, Autoref::None, vec![], BOOL));
        }
        if n == k.is_sign_positive {
            return Some((B::FloatIsSignPositive, Autoref::None, vec![], BOOL));
        }
        if n == k.is_sign_negative {
            return Some((B::FloatIsSignNegative, Autoref::None, vec![], BOOL));
        }
        if n == k.to_bits {
            let bt = int(if f == FloatTy::F32 { IntTy::U32 } else { IntTy::U64 });
            return Some((B::FloatToBits, Autoref::None, vec![], bt));
        }
        if n == k.to_string {
            return Some((B::ToString, Autoref::Ref, vec![], STRING));
        }
        None
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

    /// One binary operator through its operator trait, with the
    /// result type normalized through `Output`. None when no
    /// impl applies (the caller reports the plain operator error).
    fn trait_binop(&mut self, e: ExprId, op: BinOp, li: Ty, ri: Ty, ld: u8, rd: u8, span: Span) -> Option<Ty> {
        use BinOp::*;
        let p = self.p;
        if !p.gx.has_generics {
            return None;
        }
        let lang = &p.gx.lang;
        let (trait_def, method_name) = match op {
            Add => (lang.add, "add"),
            Sub => (lang.sub, "sub"),
            Mul => (lang.mul, "mul"),
            Div => (lang.div, "div"),
            Rem => (lang.rem, "rem"),
            BitAnd => (lang.bit_and, "bitand"),
            BitOr => (lang.bit_or, "bitor"),
            BitXor => (lang.bit_xor, "bitxor"),
            Shl => (lang.shl, "shl"),
            Shr => (lang.shr, "shr"),
            _ => return None,
        };
        let out_var = self.new_var(false);
        let args_id = self.tys.intern_args(&[GenericArg::Ty(li), GenericArg::Ty(ri)]);
        let bindings = match lang.output_of(trait_def) {
            Some(assoc) => self.tys.intern_bindings(&[(assoc, GenericArg::Ty(out_var))]),
            None => EMPTY_BINDINGS,
        };
        let tr = TraitRef { def: trait_def, args: args_id, bindings };
        let (id, impl_args) = match self.select_obligation(tr) {
            Selection::Impl { id, args, .. } => (id, args),
            Selection::ParamEvidence(_) => {
                // A template check: the bound proves the operator. The
                // call is the trait method's stub; the result is the
                // bound's `Output`, or its rigid projection.
                let method_def = p.gx.index.trait_record(trait_def)?.method_by_name(p.interner.intern(method_name))?;
                let stub = *p.gx.trait_method_stubs.get(&method_def)?;
                if let Some(assoc) = lang.output_of(trait_def) {
                    let proj = self.tys.intern(TyKind::Projection(AssocId(assoc), args_id));
                    let normed = self.normalize_here(proj);
                    self.unify(out_var, normed);
                }
                self.set_res(e, Res::TraitBin { f: stub, ld, rd });
                return Some(self.normalize_here(out_var));
            }
            _ => return None,
        };
        let local = self.method_instance_for_impl(e, id, tr, impl_args, method_name, span)?;
        // The selected method's receiver and rhs are unified by
        // selection's probe through the trait ref above; record
        // the call for lowering.
        self.set_res(e, Res::TraitBin { f: local.0, ld, rd });
        Some(self.normalize_here(out_var))
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
        self.run_obligations(false);
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
        // Both operand types still open (closure parameters a later
        // call fixes, `|a, b| a + b`): assume the builtin scalar
        // operator (Rhs = Self), check at body end that the types are
        // scalar, and take the result from the operator's `Output`
        // as rustc's `Op<Rhs>` selection does (see the int arm below).
        if self.unbound_general(lt) && self.unbound_general(rt) {
            if !self.unify(lt, rt) {
                return bad(self);
            }
            self.open_binops.push((e, op, lt));
            self.set_res(e, Res::Bin { ld: 0, rd: 0 });
            if op.is_cmp() {
                return BOOL;
            }
            let lang = &self.p.gx.lang;
            let tr = match op {
                Add => lang.add,
                Sub => lang.sub,
                Mul => lang.mul,
                Div => lang.div,
                Rem => lang.rem,
                BitAnd => lang.bit_and,
                BitOr => lang.bit_or,
                BitXor => lang.bit_xor,
                Shl => lang.shl,
                _ => lang.shr,
            };
            let out = self.new_var(false);
            if let Some(assoc) = lang.output_of(tr) {
                let trait_args = self.tys.intern_args(&[GenericArg::Ty(lt), GenericArg::Ty(rt)]);
                self.obl.push(obligations::Obligation::AssocEq { eq: AssocEqData { assoc, trait_args, ty: out }, span });
            }
            return out;
        }
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
                k if k.is_int_infer() || k.is_float_infer() || self.tys.is_string_ty(lb) => true,
                _ if matches!(op, Eq | Ne) => has_eq(self.p, &self.tys, lb),
                _ => has_ord(self.p, &self.tys, lb),
            };
            if !ok {
                let tn = self.tn(lb);
                let fix = if matches!(op, Eq | Ne) {
                    "Add #[derive(PartialEq)] to the type."
                } else {
                    "Ordering is only supported for integers, floats, bool, char, strings, and tuples of those."
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
        // Operator traits on non-scalars (section 2.5): the
        // builtin scalar path above stays first, as ARCH requires.
        if !int_like(lik)
            && !matches!(lik, TyKind::Bool)
            && let Some(t) = self.trait_binop(e, op, li, ri, ld, rd, span)
        {
            return t;
        }
        let result = match op {
            Add | Sub | Mul | Div | Rem
                if (matches!(lik, TyKind::Float(_)) || lik.is_float_infer())
                    && (matches!(rik, TyKind::Float(_)) || rik.is_float_infer()) =>
            {
                if !self.unify(li, ri) {
                    return bad(self);
                }
                li
            }
            Shl | Shr if int_like(lik) && int_like(rik) => li,
            BitAnd | BitOr | BitXor if lik == TyKind::Bool && rik == TyKind::Bool => BOOL,
            // One concrete int side fixes an unbound variable on
            // the other: scalar `Add` (and friends) have
            // Rhs = Self, Output = Self, so this is the same
            // binding the trait impl would make. Closure
            // signature inference depends on it.
            Add | Sub | Mul | Div | Rem | BitAnd | BitOr | BitXor
                if (int_like(lik) && (int_like(rik) || matches!(rik, TyKind::Infer(_))))
                    || (int_like(rik) && matches!(lik, TyKind::Infer(_))) =>
            {
                let general = |k: TyKind| matches!(k, TyKind::Infer(v) if !v.is_int() && !v.is_float());
                // A second check of a closure body (`deferred_closures`)
                // sees the operand fixed by then; rustc checks the body
                // once, so an operator deferred there stays deferred.
                let deferred = general(lik) || general(rik) || self.deferred_binops.contains(&e);
                if deferred && !self.deferred_binops.contains(&e) {
                    self.deferred_binops.push(e);
                }
                if !self.unify(li, ri) {
                    return bad(self);
                }
                if deferred {
                    // An operand that is a general variable (a closure
                    // parameter not known yet): rustc resolves the
                    // operator through `Op<Rhs>` selection, so the
                    // result is that impl's `Output`, known once the
                    // operand is (after literal fallback at the
                    // latest), not the operand itself. `|x| x + 1`
                    // called with a literal into a `u64` is then
                    // `i32 + i32`: a mismatch (rustc E0271).
                    let lang = &self.p.gx.lang;
                    let tr = match op {
                        Add => lang.add,
                        Sub => lang.sub,
                        Mul => lang.mul,
                        Div => lang.div,
                        Rem => lang.rem,
                        BitAnd => lang.bit_and,
                        BitOr => lang.bit_or,
                        _ => lang.bit_xor,
                    };
                    let out = self.new_var(false);
                    if let Some(assoc) = lang.output_of(tr) {
                        let trait_args = self.tys.intern_args(&[GenericArg::Ty(li), GenericArg::Ty(ri)]);
                        self.obl.push(obligations::Obligation::AssocEq { eq: AssocEqData { assoc, trait_args, ty: out }, span });
                    }
                    out
                } else {
                    li
                }
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
            // The flat type table answers below; the binding query is the
            // recorded read of that answer (ARCH 8.2).
            if n != p.known.self_type {
                self.binding(Namespace::Type, n);
            }
            let a = if n == p.known.self_type { self.self_adt() } else { p.type_names.get(&n).copied() };
            match a.filter(|&a| !p.adt(a).is_enum).map(|a| (a, 0u32)) {
                Some(v) => Some(v),
                // An imported struct-like variant (`use E::*; C { .. }`).
                None => match self.pat_ident(n) {
                    PatIdent::Variant(a, v) => Some((a, v)),
                    _ => None,
                },
            }
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
        // A generic Adt literal instantiates its parameters from
        // the written fields (and any turbofish): field types are
        // the template's, substituted with fresh variables.
        let gen_args: Vec<GenericArg> = self.fresh_args(&p.gx.adt_generics[a.0 as usize].clone());
        let variant = &p.adt(a).variants[v as usize];
        // Tuple structs take index fields here (`T { 0: 5, ..a }`); their
        // field names are the index as a synthetic Sym, so the matching
        // below works for both shapes.
        if !matches!(variant.shape, VariantShape::Named | VariantShape::Tuple) && !(variant.fields.is_empty() && fields.is_empty()) {
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
                    let want =
                        if gen_args.is_empty() { variant.fields[i].ty } else { subst(&mut self.tys, variant.fields[i].ty, &gen_args) };
                    self.expect_expr(fe, want);
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
            // A field filled from the base must be visible here too
            // (rustc E0451): building a value with a private field from
            // another module is not allowed even by moving it through.
            for (i, f) in variant.fields.iter().enumerate() {
                if !seen[i] {
                    if variant.shape == VariantShape::Tuple {
                        self.check_tuple_field_vis(a, i as u32, span);
                    } else {
                        self.check_field_vis(a, f.name, span);
                    }
                }
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
        // Forming the type owes its parameter bounds.
        if !gen_args.is_empty() {
            let preds = p.gx.adt_generics[a.0 as usize].predicates.clone();
            if !preds.is_empty() {
                self.push_predicates(&preds, &gen_args, span);
            }
        }
        if gen_args.is_empty() {
            self.tys.adt_ty(a)
        } else {
            let (def, _) = p.gx.adt_info[a.0 as usize];
            self.tys.mk_adt(def, &gen_args)
        }
    }

    fn for_iter(&mut self, for_e: ExprId, iter: ExprId) -> Ty {
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
            _ if self.tys.vec_elem(self.resolve(t)).is_some() => self.tys.vec_elem(self.resolve(t)).unwrap_or(ERROR),
            TyKind::Error => ERROR,
            _ => match self.for_trait_iter(for_e, iter, t) {
                Some(item) => item,
                None => {
                    let s = self.span(iter);
                    let tn = self.tn(t);
                    self.err("L0113", s, format!("cannot iterate over `{tn}`"), "Iterate over a range, `&vec`, or `&mut vec`.");
                    ERROR
                }
            },
        }
    }

    /// A `for` loop through `IntoIterator` (section 2.4 in a
    /// loop head): select the impl, record the two method
    /// instances lowering calls, and answer the item type.
    fn for_trait_iter(&mut self, for_e: ExprId, iter: ExprId, t: Ty) -> Option<Ty> {
        let p = self.p;
        if !p.gx.has_generics {
            return None;
        }
        self.run_obligations(false);
        let span = self.span(iter);
        let args_id = self.tys.intern_args(&[GenericArg::Ty(t)]);
        let tr = TraitRef { def: p.gx.lang.into_iterator, args: args_id, bindings: EMPTY_BINDINGS };
        let lang = &p.gx.lang;
        // The into_iter call: an impl's method, the std blanket's
        // sentinel (no body: lowering uses the receiver as its own
        // iterator), or in a template check the bound's stub.
        let into_local = match self.select_obligation(tr) {
            Selection::Impl { id, args: impl_args, .. } => {
                if p.gx.index.get(id).items.is_empty() {
                    LocalDefId(u32::MAX)
                } else {
                    self.method_instance_for_impl(for_e, id, tr, impl_args, "into_iter", span)?.0
                }
            }
            Selection::ParamEvidence(_) => self.stub_instance(for_e, tr, p.interner.intern("into_iter"), span)?.0,
            _ => return None,
        };
        // The iterator type and item type, normalized.
        let into_iter_proj = self.tys.intern(TyKind::Projection(AssocId(lang.assoc_into_iter), args_id));
        let iter_ty = self.normalize_here(into_iter_proj);
        let item_proj = self.tys.intern(TyKind::Projection(AssocId(lang.assoc_into_item), args_id));
        let item_ty = self.normalize_here(item_proj);
        // next() on the iterator type.
        let iter_args_id = self.tys.intern_args(&[GenericArg::Ty(iter_ty)]);
        let tr2 = TraitRef { def: lang.iterator, args: iter_args_id, bindings: EMPTY_BINDINGS };
        let next_local = match self.select_obligation(tr2) {
            Selection::Impl { id: id2, args: impl_args2, .. } => self.method_instance_for_impl(iter, id2, tr2, impl_args2, "next", span)?.0,
            Selection::ParamEvidence(_) => self.stub_instance(iter, tr2, p.interner.intern("next"), span)?.0,
            _ => return None,
        };
        self.set_res(for_e, Res::ForTrait { into_iter: into_local, next: next_local });
        Some(item_ty)
    }

    /// The method template of one selected impl by name,
    /// instantiated at the impl's args and recorded as an
    /// instance request at `site`. Trait defaults answer when
    /// the impl does not write the method.
    fn method_instance_for_impl(
        &mut self,
        site: ExprId,
        impl_id: crate::traits::ImplId,
        tr: TraitRef,
        impl_args: Vec<GenericArg>,
        name: &str,
        span: Span,
    ) -> Option<(LocalDefId, Vec<Ty>, Ty)> {
        let p = self.p;
        let record = p.gx.index.get(impl_id).clone();
        let local = record.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == name)).or_else(
            || {
                // The trait default, materialized from its template
                // with the trait ref args as its prefix.
                let rec = p.gx.index.trait_record(record.trait_def)?;
                let name_sym = rec.methods.iter().find(|(_, n)| p.name(*n) == name).map(|(d, _)| *d)?;
                p.local_def(name_sym.hash)
            },
        )?;
        let Some(Some(tmpl)) = p.gx.fn_templates.get(local.0 as usize).cloned() else {
            let info = p.fn_info(local);
            return Some((local, info.params.clone(), info.ret));
        };
        // Prefix: impl args for an impl method, trait ref args
        // for a trait default (its template generics are the
        // trait's). A default is the local whose def is a trait
        // method def, not an item of this impl.
        let is_default = !record.items.contains(&p.def_id(local));
        let prefix: Vec<GenericArg> = if is_default {
            let raw: Vec<GenericArg> = self.tys.args(tr.args).to_vec();
            raw.iter()
                .map(|&g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.deep(t)),
                    other => other,
                })
                .collect()
        } else {
            impl_args
        };
        let explicit: Vec<Option<GenericArg>> = prefix.iter().map(|&g| Some(g)).collect();
        let (params, ret, _) = self.instantiate_template(site, local, &tmpl.generics.clone(), &explicit, span);
        Some((local, params, ret))
    }

    /// One format argument against its spec: the kind must exist for
    /// the type, and the flags must fit it, as in Rust. Errors name
    /// the trait a kind needs (`LowerHex` and kin).
    fn check_fmt_arg(&mut self, t: Ty, spec: FmtSpec, span: Span) {
        let (_, base) = self.autoderef(t);
        let bk = self.kind(base);
        let numeric = matches!(bk, TyKind::Int(_) | TyKind::Float(_)) || bk.is_int_infer() || bk.is_float_infer();
        let what = match spec.kind {
            FmtKind::Display => {
                if has_display(self.p, &self.tys, t) || self.kind(t).is_int_infer() {
                    None
                } else {
                    Some("Display")
                }
            }
            FmtKind::Debug => {
                if has_debug(self.p, &self.tys, t) {
                    None
                } else {
                    Some("Debug")
                }
            }
            FmtKind::LowerHex => {
                if matches!(bk, TyKind::Int(_)) || bk.is_int_infer() {
                    None
                } else {
                    Some("LowerHex")
                }
            }
            FmtKind::UpperHex => {
                if matches!(bk, TyKind::Int(_)) || bk.is_int_infer() {
                    None
                } else {
                    Some("UpperHex")
                }
            }
            FmtKind::Octal => {
                if matches!(bk, TyKind::Int(_)) || bk.is_int_infer() {
                    None
                } else {
                    Some("Octal")
                }
            }
            FmtKind::Binary => {
                if matches!(bk, TyKind::Int(_)) || bk.is_int_infer() {
                    None
                } else {
                    Some("Binary")
                }
            }
            FmtKind::LowerExp => {
                if matches!(bk, TyKind::Float(_)) || bk.is_float_infer() {
                    None
                } else {
                    Some("LowerExp")
                }
            }
            FmtKind::UpperExp => {
                if matches!(bk, TyKind::Float(_)) || bk.is_float_infer() {
                    None
                } else {
                    Some("UpperExp")
                }
            }
        };
        if let Some(what) = what {
            if self.kind(t) != TyKind::Error {
                let tn = self.tn(t);
                let fix = match what {
                    "Debug" => "Add #[derive(Debug)] to the type.",
                    "Display" => "Use `{:?}` with #[derive(Debug)], or format the fields yourself.",
                    _ => "This format only applies to integer or float types, as written.",
                };
                self.err("L0112", span, format!("`{tn}` does not implement {what}"), fix);
            }
            return;
        }
        // Flag fit: sign and zero padding are numeric-only, precision
        // applies to numbers and strings, and `#` outside the radix
        // kinds is only a float no-op in Rust.
        let stringy = bk == TyKind::Str || self.tys.is_string_ty(base);
        let bad = (spec.plus && !numeric)
            || (spec.zero && !numeric)
            || (spec.precision.is_some() && !numeric && !stringy && bk != TyKind::Char)
            || (spec.alt && !matches!(spec.kind, FmtKind::LowerHex | FmtKind::UpperHex | FmtKind::Octal | FmtKind::Binary) && !matches!(bk, TyKind::Float(_)));
        if bad && self.kind(t) != TyKind::Error {
            let tn = self.tn(t);
            self.err("L0112", span, format!("invalid format options for `{tn}`"), "Sign, zero padding, and `#` only apply as in Rust: numbers and the radix formats.");
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
            if let FmtPiece::Arg { index, spec, .. } = piece {
                let a = args[*index];
                let t = self.expr(a, None);
                let t = self.deep(t);
                // A still-unbound variable defers the test to
                // finish: its type may be a closure signature
                // that only the second inference pass binds.
                if matches!(self.kind(t), TyKind::Infer(_)) && !self.kind(t).is_int_infer() {
                    self.deferred_fmt.push((t, *spec, self.span(a)));
                    continue;
                }
                let s = self.span(a);
                self.check_fmt_arg(t, *spec, s);
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
        // Edition 2024: once a pattern is implicitly borrowing (a default
        // binding mode shift happened above it), an explicit `ref` borrow
        // in it is an error.
        if by_ref && mode != BindMode::Move {
            self.err(
                "L0122",
                span,
                "cannot explicitly borrow within an implicitly-borrowing pattern",
                "Remove `ref`: the binding already borrows by default. To borrow explicitly, dereference with `&` at the top of the pattern first.",
            );
        }
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

    /// Checks one const pattern value against the scrutinee type:
    /// structural-match (a constant whose Adt type has no derived
    /// `PartialEq` is L0633, as in Rust; a structural value lust
    /// cannot compare yet is the non-scalar unsupported error), then
    /// type equality and refutability outside `match`. Returns true
    /// when the pattern may use the value.
    fn check_const_value(&mut self, cty: Ty, val: &crate::ty::consteval::ConstValue, t: Ty, span: Span, in_match: bool) -> bool {
        use crate::ty::consteval::ConstValue as CV;
        let ct = self.resolve(cty);
        match val {
            CV::Int(_) | CV::Bool(_) | CV::Char(_) | CV::Float(..) | CV::Str(_) => {}
            _ => {
                let nonstructural = matches!(self.tys.local_adt(ct), Some(a) if !self.p.adt(a).derives.partial_eq);
                if nonstructural {
                    let tn = self.tn(ct);
                    self.err(
                        "L0633",
                        span,
                        format!("constant of non-structural type `{tn}` cannot be used in a pattern"),
                        "Derive `PartialEq` on the type, match a field, or compare in a guard instead.",
                    );
                } else {
                    self.errs.push(unsupported(span, "non-scalar const patterns"));
                }
                return false;
            }
        }
        let eff = if matches!(val, CV::Str(_)) && self.kind(t) == TyKind::Str { t } else { ct };
        if !self.unify(eff, t) {
            self.mismatch(span, t, eff);
            return false;
        }
        if !in_match {
            self.errs.push(unsupported(span, "refutable patterns here"));
        }
        true
    }

    /// A free const item used as a pattern, by const index.
    fn const_item_pat(&mut self, pi: usize, idx: u32, t: Ty, span: Span, in_match: bool) {
        // The pattern consumes the const's value: record its `Sig`
        // read so a value edit rechecks this body (ARCH 8.2).
        if let Some(&def) = self.p.const_defs.get(idx as usize) {
            let p = self.p;
            let _ = p.sig_of(&mut self.out.reads, def);
        }
        let c = &self.p.consts[idx as usize];
        let (ct, val) = (c.ty, c.value.clone());
        if self.check_const_value(ct, &val, t, span, in_match) {
            self.out.pat_res[pi] = PatRes::ConstItem(idx);
        }
    }

    /// Tries to read a path pattern as a const pattern. Returns true
    /// when the path named a const (or a static, which errors), so
    /// the caller skips variant handling.
    fn try_const_path_pat(&mut self, pi: usize, segs: &[ast::PathSeg], t: Ty, span: Span, in_match: bool) -> bool {
        let p = self.p;
        if segs.len() == 1 {
            // Free consts and statics in one segment are handled by
            // the pattern-identifier resolution in the Path arm.
            return false;
        }
        // Primitive associated consts (`i64::MAX`, `u32::BITS`), the
        // same table `path_expr` reads for expression positions.
        if segs.len() == 2
            && let Some(it) = p.known.int_ty(segs[0].name)
        {
            let item = self.name(segs[1].name).to_string();
            let item = item.as_str();
            let bits = it.bits();
            let v = match item {
                "MAX" => Some(crate::ty::consteval::truncate_to_int(it.max128() as i128, it)),
                "MIN" => Some(if it.signed() { if bits >= 128 { i128::MIN } else { -(1i128 << (bits - 1)) } } else { 0 }),
                "BITS" => Some(bits as i128),
                _ => None,
            };
            if let Some(v) = v {
                let (ct, val) = if item == "BITS" {
                    (int(IntTy::U32), v)
                } else if it == IntTy::U128 && item == "MAX" {
                    (int(it), -1)
                } else {
                    (int(it), v)
                };
                let cv = crate::ty::consteval::ConstValue::Int(val);
                if self.check_const_value(ct, &cv, t, span, in_match) {
                    self.out.pat_res[pi] = PatRes::PrimConst(val);
                }
                return true;
            }
        }
        if let Some((adt, item)) = self.assoc_const_key(segs) {
            match p.assoc_const_names.get(&(adt, item)) {
                Some(&idx) => {
                    self.const_item_pat(pi, idx, t, span, in_match);
                    return true;
                }
                None => return false,
            }
        }
        false
    }

    /// The (Adt, name) key an associated const path (`Self::A`,
    /// `Type::A`) names, when the owning type is a local Adt.
    fn assoc_const_key(&mut self, segs: &[ast::PathSeg]) -> Option<(AdtId, Sym)> {
        if segs.len() != 2 {
            return None;
        }
        let p = self.p;
        let (ty_name, item) = (segs[0].name, segs[1].name);
        let adt = if ty_name == p.known.self_type {
            self.self_adt()
        } else {
            match self.binding(Namespace::Type, ty_name) {
                BindingRes::Def(def) => p.adt_by_def(def),
                _ => None,
            }
        }?;
        Some((adt, item))
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
                // A string literal or &str const pattern matches `&str` directly.
                let str_pat = matches!(p.ast.pat(pat), Pat::Lit(l) if matches!(p.ast.expr(*l), Expr::Str(_)))
                    || matches!(p.ast.pat(pat), Pat::Path(segs) if segs.len() == 1 && p.const_names.get(&segs[0].name).is_some_and(|&i| matches!(p.consts[i as usize].value, crate::ty::consteval::ConstValue::Str(_))));
                if str_pat && self.kind(inner) == TyKind::Str {
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
        if opt.is_none()
            && let Some(is_ok) = self.result_pattern(pat)
        {
            let (a, b) = (self.new_var(false), self.new_var(false));
            let rt = self.tys.mk_result(a, b);
            if !self.unify(rt, t) {
                self.mismatch(span, t, rt);
                return;
            }
            self.out.pat_res[pi] = PatRes::Res(is_ok);
            if let Pat::TupleStruct { elems, .. } = p.ast.pat(pat) {
                self.pattern_mode(elems[0], if is_ok { a } else { b }, mode, in_match);
            }
            return;
        }
        // A plain name that resolves to a const item, a unit struct, or
        // a unit variant is a path pattern, not a binding (unless a
        // local binding shadows the name). Imports count: resolution
        // goes through the module bindings, as in expressions. The
        // pattern consumes the const's value, so record its `Sig` read
        // (the fingerprint folds the evaluated value): a value edit
        // must recheck this body (ARCH 8.2), like a const in an
        // expression.
        if let Pat::Binding { name, mutable: false, by_ref: false } = p.ast.pat(pat)
            && self.lookup(*name, span.ctxt).is_none()
            && let Some(crate::check::collect::BodyItem::Const(ci)) = self.body_item_of(*name, span.ctxt)
        {
            let c = &p.body_consts[ci as usize];
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
            self.out.pat_res[pi] = PatRes::BodyConst(ci);
            return;
        }
        if let Pat::Binding { name, mutable: false, by_ref: false } = p.ast.pat(pat)
            && self.lookup(*name, span.ctxt).is_none()
        {
            match self.pat_ident(*name) {
                PatIdent::Const(idx) => {
                    self.const_item_pat(pi, idx, t, span, in_match);
                    return;
                }
                PatIdent::Static => {
                    self.err(
                        "L0110",
                        span,
                        "statics cannot be used as patterns",
                        "Use a const item for a pattern, or compare with the static in a guard.",
                    );
                    return;
                }
                PatIdent::Variant(a, v) => {
                    let adt_ty = self.tys.adt_ty(a);
                    if !self.unify(adt_ty, t) {
                        self.mismatch(span, t, adt_ty);
                        return;
                    }
                    if p.adt(a).variants[v as usize].shape != VariantShape::Unit {
                        self.err("L0110", span, "this variant has fields", "Match its fields with `(..)` or `{ .. }`.");
                        return;
                    }
                    self.out.pat_res[pi] = PatRes::Variant(a, v);
                    return;
                }
                PatIdent::Other => {}
            }
        }
        // A const path pattern (`MAX`, `Self::A`, `Type::A`, `m::S`)
        // is not a variant: it compares against the const's value.
        if let Pat::Path(segs) = p.ast.pat(pat) {
            let segs = segs.clone();
            if self.try_const_path_pat(pi, &segs, t, span, in_match) {
                return;
            }
        }
        match p.ast.pat(pat) {
            Pat::Wild => {}
            Pat::Binding { name, mutable, by_ref } => {
                // A plain binding named the same as a variant of the
                // matched enum type is an error (rustc E0170): it can
                // never mean the variant. `mut`, `ref`, and `@` forms
                // are plain bindings and stay legal.
                if !mutable && !by_ref {
                    let (_, base) = self.autoderef(t);
                    if let Some(a) = self.tys.local_adt(self.resolve(base))
                        && p.adt(a).is_enum
                        && p.adt(a).variants.iter().any(|v| v.name == *name)
                        && self.lookup(*name, span.ctxt).is_none()
                        && !matches!(self.pat_ident(*name), PatIdent::Variant(b, _) if b == a)
                    {
                        let (vn, en) = (self.name(*name).to_string(), p.display_path(p.adt(a).name));
                        self.err(
                            "L0110",
                            span,
                            format!("pattern binding `{vn}` is named the same as one of the variants of the type `{en}`"),
                            format!("Rename the binding, or match the variant with `{en}::{vn}` (or `use {en}::{vn};` first)."),
                        );
                        return;
                    }
                }
                self.bind_pattern_local(pi, *name, *mutable, *by_ref, t, mode, span);
            }
            Pat::At { name, mutable, by_ref, inner } => {
                self.bind_pattern_local(pi, *name, *mutable, *by_ref, t, mode, span);
                self.pattern_mode(*inner, t, mode, in_match);
            }
            Pat::Ref { mutable, inner } => match self.kind(t) {
                TyKind::Ref(_, m, inner_ty) => {
                    // Edition 2024: an explicit `&` dereference inside an
                    // implicitly-borrowing pattern is an error.
                    if mode != BindMode::Move {
                        self.err(
                            "L0122",
                            span,
                            "cannot explicitly dereference within an implicitly-borrowing pattern",
                            "Remove the `&`: the pattern already borrows by default, so the binding has the same type without it.",
                        );
                    }
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
            Pat::Range { lo, hi, inclusive } => {
                // The parser only builds two-bound ranges today; a half-open
                // range checks its one bound the same way.
                let mut bound_tys = Vec::new();
                if let Some(lo) = lo {
                    bound_tys.push((*lo, self.expr(*lo, Some(t))));
                }
                if let Some(hi) = hi {
                    bound_tys.push((*hi, self.expr(*hi, Some(t))));
                }
                // An exclusive range `lo..hi` needs lo < hi (rustc E0579);
                // an inclusive one needs lo <= hi (rustc E0030).
                if let [(lo_e, _), (hi_e, _)] = bound_tys[..]
                    && let (Some(lo_v), Some(hi_v)) = (self.const_scalar(lo_e), self.const_scalar(hi_e))
                    && match (self.scalar_key(lo_v, t), self.scalar_key(hi_v, t)) {
                        (Some(a), Some(b)) => a > b || (!inclusive && a == b),
                        _ => lo_v > hi_v || (!inclusive && lo_v == hi_v),
                    }
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
                // A path may also name a const item (`m::K`, rewritten
                // to its flat name) or a primitive associated const
                // (`u8::MAX`): both compare like literal patterns.
                if matches!(p.ast.pat(pat), Pat::Path(_)) {
                    if segs.len() == 1 {
                        match self.pat_ident(segs[0].name) {
                            PatIdent::Const(idx) => {
                                self.const_item_pat(pi, idx, t, span, in_match);
                                return;
                            }
                            PatIdent::Static => {
                                self.err(
                                    "L0110",
                                    span,
                                    "statics cannot be used as patterns",
                                    "Use a const item for a pattern, or compare with the static in a guard.",
                                );
                                return;
                            }
                            PatIdent::Variant(a, v) if p.adt(a).is_enum => {
                                let adt_ty = self.tys.adt_ty(a);
                                if !self.unify(adt_ty, t) {
                                    self.mismatch(span, t, adt_ty);
                                    return;
                                }
                                if p.adt(a).variants[v as usize].shape != VariantShape::Unit {
                                    self.err("L0110", span, "this variant has fields", "Match its fields with `(..)` or `{ .. }`.");
                                    return;
                                }
                                self.out.pat_res[pi] = PatRes::Variant(a, v);
                                return;
                            }
                            _ => {}
                        }
                    } else if let Some((cv, ct)) = self.primitive_const_pattern(segs) {
                        if !self.unify(ct, t) {
                            self.mismatch(span, t, ct);
                            return;
                        }
                        self.out.pat_const[pi] = Some(cv);
                        return;
                    }
                }
                let target = if segs.len() == 1 {
                    let n = segs[0].name;
                    // The flat type table answers below; the binding query
                    // is the recorded read of that answer (ARCH 8.2).
                    if n != p.known.self_type {
                        self.binding(Namespace::Type, n);
                    }
                    let a = if n == p.known.self_type { self.self_adt() } else { p.type_names.get(&n).copied() };
                    match a.filter(|&a| !p.adt(a).is_enum).map(|a| (a, 0)) {
                        Some(v) => Some(v),
                        // An imported variant in a tuple or struct pattern
                        // (`use E::*; B(n)`): resolve through the bindings.
                        None => match self.pat_ident(n) {
                            PatIdent::Variant(a, v) => Some((a, v)),
                            _ => None,
                        },
                    }
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
                // A generic Adt pattern matches the scrutinee's
                // own instance when mono has made it; before that
                // (and in templates) it matches the template with
                // the scrutinee's args substituted into its fields.
                let dt = self.deep(t);
                let scrut_args: Vec<GenericArg> = match self.tys.adt_parts(dt) {
                    Some((d, aa)) if d == p.def_of_adt(a) => self.tys.args(aa).to_vec(),
                    _ => Vec::new(),
                };
                let (a, adt_ty) = match self.tys.local_adt(dt) {
                    Some(inst) if inst != a && p.def_of_adt(inst) == p.def_of_adt(a) => (inst, dt),
                    _ if !scrut_args.is_empty() => (a, dt),
                    _ => (a, self.tys.adt_ty(a)),
                };
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
                        if !p.adt(a).is_enum {
                            self.check_ctor_vis(a, span);
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
                            let ft = if scrut_args.is_empty() { ft } else { subst(&mut self.tys, ft, &scrut_args) };
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
                                    let ft = if scrut_args.is_empty() { ft } else { subst(&mut self.tys, ft, &scrut_args) };
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
            Pat::Path(segs) if segs.len() == 2 && segs[0].name == k.Option && segs[1].name == k.None => Some(false),
            Pat::TupleStruct { path, elems }
                if elems.len() == 1
                    && ((path.len() == 1 && path[0].name == k.Some)
                        || (path.len() == 2 && path[0].name == k.Option && path[1].name == k.Some)) =>
            {
                Some(true)
            }
            _ => None,
        }
    }

    /// `Ok(..)` as `Some(true)`, `Err(..)` as `Some(false)`, in the
    /// prelude spelling and the qualified `Result::Ok(..)` spelling.
    fn result_pattern(&self, pat: PatId) -> Option<bool> {
        let k = self.p.known;
        match self.p.ast.pat(pat) {
            Pat::TupleStruct { path, elems } if elems.len() == 1 => {
                let last = path.last().map(|s| s.name)?;
                if (path.len() == 1 || (path.len() == 2 && path[0].name == k.Result)) && last == k.Ok {
                    Some(true)
                } else if (path.len() == 1 || (path.len() == 2 && path[0].name == k.Result)) && last == k.Err {
                    Some(false)
                } else {
                    None
                }
            }
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
                    .map(|v| format!("{}::{}", p.display_path(p.adt(a).name), self.name(p.adt(a).variants[v].name)))
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
                r @ (PatRes::Variant(..) | PatRes::Opt(_) | PatRes::Res(_)) => r,
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

    /// An order-preserving key for an integer or char scalar at type
    /// `t`: raw bits, with the sign bit flipped for signed types.
    fn scalar_key(&self, v: i128, t: Ty) -> Option<u128> {
        match self.kind(t) {
            TyKind::Int(it) => {
                let bits = if it.bits() >= 128 { v as u128 } else { (v as u128) & ((1u128 << it.bits()) - 1) };
                Some(if it.signed() { bits ^ (1u128 << (it.bits() - 1)) } else { bits })
            }
            TyKind::Char => Some(v as u32 as u128),
            _ => None,
        }
    }

    /// The scalar value a pattern matches as a single point, if it is one.
    fn pat_scalar(&self, pat: PatId) -> Option<i128> {
        let pi = (pat.0 - self.out.pat_base) as usize;
        if let Some(cv) = &self.out.pat_const[pi] {
            return match cv {
                crate::ty::consteval::ConstValue::Int(v) => Some(*v),
                crate::ty::consteval::ConstValue::Char(c) => Some(*c as i128),
                _ => None,
            };
        }
        if let PatRes::ConstItem(idx) = self.out.pat_res[pi] {
            return match &self.p.consts[idx as usize].value {
                crate::ty::consteval::ConstValue::Int(v) => Some(*v),
                crate::ty::consteval::ConstValue::Char(c) => Some(*c as i128),
                _ => None,
            };
        }
        match self.p.ast.pat(self.pat_unwrap(pat)) {
            Pat::Lit(l) => self.const_scalar(*l),
            _ => None,
        }
    }

    /// True when integer or char literal, const, and range patterns
    /// together cover the whole domain of their type. This is the
    /// const-point and u128 companion to `covers_scalar_domain`:
    /// it runs only when that one declines (a const item or
    /// associated const as a point pattern, or a u128 domain).
    fn covers_scalar_ranges(&self, flat: &[PatId]) -> bool {
        if flat.is_empty() {
            return false;
        }
        let t = self.out.pat_ty[(flat[0].0 - self.out.pat_base) as usize];
        let domain: Vec<(u128, u128)> = match self.kind(t) {
            TyKind::Int(it) => vec![(0, if it.bits() >= 128 { u128::MAX } else { (1u128 << it.bits()) - 1 })],
            // The char domain skips the surrogate range.
            TyKind::Char => vec![(0, 0xD7FF), (0xE000, 0x10FFFF)],
            _ => return false,
        };
        let mut ivs: Vec<(u128, u128)> = Vec::new();
        for &x in flat {
            let x = self.pat_unwrap(x);
            match self.p.ast.pat(x) {
                Pat::Range { lo, hi, inclusive } => {
                    let lo_k = match lo {
                        Some(lo) => match self.const_scalar(*lo).and_then(|v| self.scalar_key(v, t)) {
                            Some(k) => k,
                            None => return false,
                        },
                        None => 0,
                    };
                    let hi_k = match hi {
                        Some(hi) => match self.const_scalar(*hi).and_then(|v| self.scalar_key(v, t)) {
                            Some(k) => {
                                if *inclusive {
                                    k
                                } else {
                                    if k == 0 {
                                        continue;
                                    }
                                    k - 1
                                }
                            }
                            None => return false,
                        },
                        None => u128::MAX,
                    };
                    if lo_k <= hi_k {
                        ivs.push((lo_k, hi_k));
                    }
                }
                _ => match self.pat_scalar(x).and_then(|v| self.scalar_key(v, t)) {
                    Some(k) => ivs.push((k, k)),
                    None => return false,
                },
            }
        }
        ivs.sort();
        for (dlo, dhi) in domain {
            let mut next = dlo;
            let mut done = false;
            for &(lo, hi) in &ivs {
                if hi < next {
                    continue;
                }
                if lo > next {
                    break;
                }
                if hi >= dhi {
                    done = true;
                    break;
                }
                next = hi + 1;
            }
            if !done {
                return false;
            }
        }
        true
    }

    /// True if `pats`, all matching values of one type, together match every value.
    fn covers(&self, pats: &[PatId]) -> bool {
        let p = self.p;
        let mut flat = Vec::new();
        pats.iter().for_each(|&x| self.flatten_or(x, &mut flat));
        if flat.iter().any(|&x| self.irrefutable(x)) {
            return true;
        }
        if let Some(res) = self.covers_scalar_domain(&flat) {
            return res;
        }
        if self.covers_scalar_ranges(&flat) {
            return true;
        }
        if !flat.is_empty() && flat.iter().all(|&x| matches!(p.ast.pat(self.pat_unwrap(x)), Pat::Slice { .. })) {
            return self.covers_slice(&flat);
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
                (PatRes::Res(_), _) => {
                    let side = |want: bool| -> Vec<PatId> {
                        flat.iter()
                            .filter_map(|&y| match (self.pres(y), p.ast.pat(self.pat_unwrap(y))) {
                                (PatRes::Res(w), Pat::TupleStruct { elems, .. }) if w == want => Some(elems[0]),
                                _ => None,
                            })
                            .collect()
                    };
                    let (oks, errs) = (side(true), side(false));
                    return !oks.is_empty() && !errs.is_empty() && self.covers(&oks) && self.covers(&errs);
                }
                (PatRes::Variant(a, _), _) if p.adt(a).is_enum => {
                    return (0..p.adt(a).variants.len()).all(|v| self.covers_variant(&flat, a, v as u32));
                }
                (_, Pat::Lit(_)) | (PatRes::ConstItem(_), _)
                    if matches!(self.kind(self.out.pat_ty[(x.0 - self.out.pat_base) as usize]), TyKind::Bool) =>
                {
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
        self.rows_cover(&rows)
    }

    /// Do the rows (one per pattern, `None` is a skipped or wildcard cell)
    /// together match every tuple of values? Conservative, like `covers`:
    /// a fully free row wins, else one column must carry the whole split
    /// while every other column is free in all rows.
    fn rows_cover(&self, rows: &[Vec<Option<PatId>>]) -> bool {
        if rows.is_empty() {
            return false;
        }
        let nf = rows[0].len();
        let free = |c: &Option<PatId>| c.is_none_or(|x| self.irrefutable(x));
        if rows.iter().any(|r| r.iter().all(free)) {
            return true;
        }
        (0..nf).any(|j| {
            rows.iter().all(|r| r.iter().enumerate().all(|(i, c)| i == j || free(c)))
                && rows.iter().all(|r| r[j].is_some())
                && self.covers(&rows.iter().filter_map(|r| r[j]).collect::<Vec<_>>())
        })
    }

    /// Slice and array pattern coverage, split by length. An array has the
    /// one length; a slice needs a `..` pattern, and then every length up
    /// to one past the longest fixed part is checked (a longer slice only
    /// adds wildcard middle cells to the rows that matched there, so the
    /// same row argument keeps holding). With no `..` pattern a slice
    /// match can never be exhaustive: some length is missed, and accepting
    /// it would make the missing length abort at run time.
    fn covers_slice(&self, flat: &[PatId]) -> bool {
        let p = self.p;
        let t = self.out.pat_ty[(flat[0].0 - self.out.pat_base) as usize];
        let arr_len: Option<usize> = match self.kind(t) {
            TyKind::Slice(_) => None,
            TyKind::Array(_, c) => match self.tys.const_kind(c) {
                ConstKind::Int(n) => Some(n as usize),
                _ => return false,
            },
            _ => return false,
        };
        // (prefix, suffix, middle is free over any cells it spans)
        let mut pats: Vec<(Vec<PatId>, Vec<PatId>, Option<bool>)> = Vec::new();
        for &x in flat {
            let Pat::Slice { prefix, middle, suffix } = p.ast.pat(self.pat_unwrap(x)) else { return false };
            let mid = match middle {
                None => None,
                Some(mid) => Some(matches!(p.ast.pat(*mid), Pat::Rest) || self.irrefutable(*mid)),
            };
            pats.push((prefix.clone(), suffix.clone(), mid));
        }
        let lengths: Vec<usize> = match arr_len {
            Some(n) => vec![n],
            None => {
                if pats.iter().all(|(_, _, m)| m.is_none()) {
                    return false;
                }
                let m = pats.iter().map(|(a, b, _)| a.len() + b.len()).max().unwrap_or(0);
                (0..=m + 1).collect()
            }
        };
        for len in lengths {
            let mut rows: Vec<Vec<Option<PatId>>> = Vec::new();
            for (prefix, suffix, mid) in &pats {
                let fixed = prefix.len() + suffix.len();
                match mid {
                    None if len == fixed => {
                        rows.push(prefix.iter().chain(suffix.iter()).map(|&s| Some(s)).collect());
                    }
                    Some(true) if len >= fixed => {
                        let mut row: Vec<Option<PatId>> = prefix.iter().map(|&s| Some(s)).collect();
                        row.resize(len - suffix.len(), None);
                        row.extend(suffix.iter().map(|&s| Some(s)));
                        rows.push(row);
                    }
                    _ => {}
                }
            }
            if !self.rows_cover(&rows) {
                return false;
            }
        }
        true
    }

    /// Integer and char coverage by literal and range patterns: `Some` when
    /// the patterns are all scalar literals or ranges with known bounds on
    /// an int or char type, with the result of merging their intervals
    /// against the type's whole domain (the char domain skips surrogates).
    fn covers_scalar_domain(&self, flat: &[PatId]) -> Option<bool> {
        let p = self.p;
        let first = *flat.first()?;
        let t = self.out.pat_ty[(first.0 - self.out.pat_base) as usize];
        let segments: Vec<(i128, i128)> = match self.kind(t) {
            TyKind::Int(it) => {
                let bits = it.bits();
                if bits >= 128 && !it.signed() {
                    return None; // u128 bounds do not fit the i128 values here.
                }
                if bits >= 128 {
                    vec![(i128::MIN, i128::MAX)]
                } else if it.signed() {
                    vec![(-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)]
                } else {
                    vec![(0, (1i128 << bits) - 1)]
                }
            }
            TyKind::Char => vec![(0, 0xD7FF), (0xE000, 0x10FFFF)],
            _ => return None,
        };
        let (dom_lo, dom_hi) = (segments[0].0, segments[segments.len() - 1].1);
        let mut ivs: Vec<(i128, i128)> = Vec::new();
        for &x in flat {
            match p.ast.pat(self.pat_unwrap(x)) {
                Pat::Lit(l) => {
                    let v = self.const_scalar(*l)?;
                    ivs.push((v, v));
                }
                Pat::Range { lo, hi, inclusive } => {
                    let lo_v = match lo {
                        Some(e) => self.const_scalar(*e)?,
                        None => dom_lo,
                    };
                    let hi_v = match hi {
                        Some(e) => {
                            let v = self.const_scalar(*e)?;
                            if *inclusive { v } else { v.saturating_sub(1) }
                        }
                        None => dom_hi,
                    };
                    if lo_v <= hi_v {
                        ivs.push((lo_v, hi_v));
                    }
                }
                _ => return None,
            }
        }
        ivs.sort_unstable();
        Some(segments.iter().all(|&(slo, shi)| {
            let mut next = slo;
            for &(lo, hi) in &ivs {
                if lo > next {
                    break;
                }
                // An interval that reaches the segment end covers it
                // (saturating_add would hide that at i128::MAX).
                if hi >= shi {
                    return true;
                }
                next = next.max(hi.saturating_add(1));
                if next > shi {
                    return true;
                }
            }
            next > shi
        }))
    }

    fn irrefutable(&self, pat: PatId) -> bool {
        let p = self.p;
        if matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Opt(_) | PatRes::Res(_)) {
            return false;
        }
        match p.ast.pat(pat) {
            Pat::Wild => true,
            // A binding that resolved to a const item can fail; one
            // that resolved to a unit struct cannot.
            Pat::Binding { .. } => match self.out.pat_res[(pat.0 - self.out.pat_base) as usize] {
                PatRes::ConstItem(_) => false,
                PatRes::Variant(a, _) => !p.adt(a).is_enum,
                _ if self.out.pat_const[(pat.0 - self.out.pat_base) as usize].is_some() => false,
                _ => true,
            },
            Pat::Or(alts) => alts.iter().any(|&a| self.irrefutable(a)),
            Pat::Struct { fields, .. } => {
                matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Variant(a, _) if !p.adt(a).is_enum)
                    && fields.iter().all(|&(_, s)| self.irrefutable(s))
            }
            Pat::TupleStruct { elems, .. } => {
                matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Variant(a, _) if !p.adt(a).is_enum)
                    && elems.iter().all(|&s| self.irrefutable(s))
            }
            Pat::Path(_) => {
                self.out.pat_const[(pat.0 - self.out.pat_base) as usize].is_none()
                    && !matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::ConstItem(_))
                    && matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Variant(a, _) if !p.adt(a).is_enum)
            }
            Pat::Tuple(elems) => elems.iter().all(|&s| matches!(p.ast.pat(s), Pat::Rest) || self.irrefutable(s)),
            Pat::Ref { inner, .. } => self.irrefutable(*inner),
            Pat::At { inner, .. } => self.irrefutable(*inner),
            Pat::Slice { prefix, middle, suffix } => {
                // The pattern matches every value only if it matches every
                // length: an array needs an exact-length pattern, or a `..`
                // with at most the array's length fixed; a slice always
                // needs the `..` (`[]` alone matches only the empty slice).
                let t = self.out.pat_ty[(pat.0 - self.out.pat_base) as usize];
                let fixed = (prefix.len() + suffix.len()) as u128;
                let len_ok = match self.kind(t) {
                    TyKind::Array(_, c) => match self.tys.const_kind(c) {
                        ConstKind::Int(n) => {
                            if middle.is_some() {
                                fixed <= n
                            } else {
                                fixed == n
                            }
                        }
                        _ => false,
                    },
                    _ => middle.is_some(),
                };
                len_ok
                    && middle.is_none_or(|m| matches!(p.ast.pat(m), Pat::Rest) || self.irrefutable(m))
                    && prefix.iter().chain(suffix.iter()).all(|&s| self.irrefutable(s))
            }
            Pat::Paren(inner) => self.irrefutable(*inner),
            Pat::Rest => true,
            _ => false,
        }
    }

    fn cover_bools(&self, pat: PatId, t: &mut bool, f: &mut bool) {
        match self.out.pat_res[(pat.0 - self.out.pat_base) as usize] {
            PatRes::ConstItem(idx) => match self.p.consts[idx as usize].value {
                crate::ty::consteval::ConstValue::Bool(true) => *t = true,
                crate::ty::consteval::ConstValue::Bool(false) => *f = true,
                _ => {}
            },
            _ => {}
        }
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

    // ---------- Known-value overflow lint (rustc `arithmetic_overflow`) ----------

    /// The deny-level lints rustc runs over known values, mirrored from
    /// its MIR const-prop behavior (probed against rustc): an arithmetic
    /// operation on operands known at compile time that would overflow
    /// is an error (`arithmetic_overflow`, L0540), and so is an
    /// operation that always panics: division or remainder by a known
    /// zero, `MIN / -1`, and an index known to be out of bounds for an
    /// array type (`unconditional_panic`, L0541). The pass walks the
    /// checked body once, tracking scalar locals whose value is known.
    /// The tracked set follows the probed rules: a local whose address
    /// is taken anywhere is never tracked, knowledge does not survive a
    /// control-flow join for locals assigned on either side, a write
    /// through a field or index place drops the whole aggregate, reads
    /// through references and enum payloads are unknown, and an
    /// operation that stores back into the local it reads
    /// (`a = a + 1`, `a += 1`) does not fire.
    fn overflow_lint(&mut self) {
        let p = self.p;
        let allow_arith = self.f.def.attrs.iter().any(|a| crate::check::allow_attr(a, p.interner, "arithmetic_overflow"));
        let allow_panic = self.f.def.attrs.iter().any(|a| crate::check::allow_attr(a, p.interner, "unconditional_panic"));
        if allow_arith && allow_panic {
            return;
        }
        let Some(body) = self.f.def.body else { return };
        let mut lint = KLint {
            addressed: vec![false; self.out.locals.len()],
            frames: Vec::new(),
            suppress: None,
            dead: false,
            allow_arith,
            allow_panic,
            stmt_allow_arith: 0,
            stmt_allow_panic: 0,
        };
        // A local whose address is taken anywhere in the body is not tracked.
        for i in 0..self.out.expr_ty.len() {
            let e = ExprId(self.out.expr_base + i as u32);
            match p.ast.expr(e) {
                Expr::Ref { expr, .. } => {
                    if let Some(root) = self.k_place_root(*expr) {
                        lint.addressed[root as usize] = true;
                    }
                }
                Expr::MethodCall { recv, .. } => {
                    let res = self.out.expr_res[i];
                    let ar = match res {
                        Res::Method { autoref, .. } | Res::BuiltinMethod { autoref, .. } => autoref,
                        _ => Autoref::None,
                    };
                    if ar != Autoref::None
                        && let Some(root) = self.k_place_root(*recv)
                    {
                        lint.addressed[root as usize] = true;
                    }
                }
                Expr::Macro { kind, args, .. } => {
                    // Format arguments are borrowed (as in `macro_expr`).
                    let borrowed: &[ExprId] = match kind {
                        ast::MacroKind::AssertEq | ast::MacroKind::AssertNe => &args[..args.len().min(2)],
                        ast::MacroKind::Vec | ast::MacroKind::Assert => &[],
                        _ => args,
                    };
                    for &a in borrowed {
                        if matches!(p.ast.expr(a), Expr::Path(_) | Expr::Field { .. } | Expr::TupleField { .. } | Expr::Index { .. })
                            && let Some(root) = self.k_place_root(a)
                        {
                            lint.addressed[root as usize] = true;
                        }
                    }
                }
                _ => {}
            }
        }
        // A captured variable can change behind the closure: do not track it.
        for c in &self.out.closures {
            for cap in &c.captures {
                lint.addressed[cap.root as usize] = true;
            }
        }
        let mut env: KEnv = vec![None; self.out.locals.len()];
        self.k_block(body, &mut env, &mut lint);
        // Each closure body is its own MIR body in rustc: lint it with
        // nothing known on entry.
        let bodies: Vec<ExprId> = self
            .out
            .closures
            .iter()
            .filter_map(|c| match p.ast.expr(c.expr) {
                Expr::Closure { body, .. } => Some(*body),
                _ => None,
            })
            .collect();
        for b in bodies {
            let mut env: KEnv = vec![None; self.out.locals.len()];
            lint.frames.clear();
            lint.dead = false;
            lint.suppress = None;
            self.k_expr(b, &mut env, &mut lint);
        }
    }

    /// Zonks the closure records into `Checked` and rejects the closure
    /// forms outside this slice (ARCH 2.9): a return type holding a
    /// reference, and closure types stored inside an Adt.
    fn finish_closures(&mut self) {
        for mut c in std::mem::take(&mut self.closures) {
            // A signature nothing fixed is an annotation error (rustc
            // E0282), never a silent default.
            if c.inputs.iter().chain([&c.output]).any(|&t| self.has_unbound_var(t) && !self.has_error_kind(t)) {
                let span = self.span(c.expr);
                self.err(
                    "L0610",
                    span,
                    "type annotations needed: cannot infer the closure's signature",
                    "Annotate the closure parameters, or use the closure where an Fn bound fixes them.",
                );
            }
            c.output = self.zonk(c.output);
            for t in c.inputs.iter_mut() {
                *t = self.zonk(*t);
            }
            for cap in c.captures.iter_mut() {
                cap.place_ty = self.zonk(cap.place_ty);
            }
            c.ty = self.zonk(c.ty);
            if contains_ref(&self.tys, c.output) {
                let span = self.span(c.expr);
                self.err(
                    "L0820",
                    span,
                    "closures that return references are not supported yet",
                    "Return an owned value from the closure.",
                );
            }
            self.out.closures.push(c);
        }
        if self.out.closures.is_empty() {
            return;
        }
        for i in 0..self.out.expr_ty.len() {
            let t = self.out.expr_ty[i];
            if self.closure_in_adt(t, false) {
                let span = self.span(ExprId(self.out.expr_base + i as u32));
                self.err(
                    "L0820",
                    span,
                    "closures stored inside a struct, enum, `Option`, or `Vec` are not supported yet",
                    "Call the closure directly, or pass it to a generic parameter.",
                );
                break;
            }
        }
    }

    /// True when a closure type sits inside an Adt's type arguments.
    fn closure_in_adt(&self, t: Ty, in_adt: bool) -> bool {
        match self.tys.kind(t) {
            TyKind::Closure(_, a) => {
                in_adt || self.tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| self.closure_in_adt(e, in_adt)))
            }
            TyKind::Adt(_, a) => self.tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| self.closure_in_adt(e, true))),
            TyKind::Ref(_, _, e) | TyKind::Slice(e) | TyKind::Array(e, _) | TyKind::RawPtr(_, e) => self.closure_in_adt(e, in_adt),
            TyKind::Tuple(ts) => self.tys.tys_of(ts).iter().any(|&e| self.closure_in_adt(e, in_adt)),
            _ => false,
        }
    }

    /// The root local of a place expression, if the place is one.
    fn k_place_root(&self, e: ExprId) -> Option<u32> {
        match self.out.expr_res[self.ei(e)] {
            Res::Local(l) => return Some(l),
            _ => {}
        }
        match self.p.ast.expr(e) {
            Expr::Field { base, .. } | Expr::TupleField { base, .. } | Expr::Index { base, .. } => self.k_place_root(*base),
            _ => None,
        }
    }

    /// True when `t` is the `u128` type, whose known values are bit
    /// patterns rather than mathematical i128 values.
    fn k_is_u128(&self, t: Ty) -> bool {
        matches!(self.tys.kind(t), TyKind::Int(it) if !it.signed() && it.bits() >= 128)
    }

    /// The bit width of an integer type, when `t` is one.
    fn k_bits(&self, t: Ty) -> Option<u32> {
        match self.tys.kind(t) {
            TyKind::Int(it) => Some(it.bits()),
            _ => None,
        }
    }

    /// Orders two known values at integer type `t` (in the u128 domain
    /// for `u128`, where the stored i128 is only the bit pattern).
    fn k_cmp(&self, a: i128, b: i128, t: Ty) -> std::cmp::Ordering {
        if self.k_is_u128(t) {
            (a as u128).cmp(&(b as u128))
        } else {
            a.cmp(&b)
        }
    }

    /// The mathematical value of an i128 seen at integer type `t`. For
    /// `u128` the bits pass through unchanged (see `KVal`).
    fn k_math(&self, v: i128, t: Ty) -> Option<i128> {
        match self.tys.kind(t) {
            TyKind::Int(it) => {
                let bits = it.bits();
                if it.signed() {
                    Some(crate::ty::consteval::truncate_to_int(v, it))
                } else if bits >= 128 {
                    Some(v)
                } else {
                    Some(v & ((1i128 << bits) - 1))
                }
            }
            _ => Some(v),
        }
    }

    /// Wraps an i128 to the range of its integer type (loss is intended:
    /// the value continues as the wrapped result, as in a wrapping op).
    fn k_wrap(&self, v: i128, t: Ty) -> Option<i128> {
        self.k_math(v, t)
    }

    /// The value range of an integer type, when it fits in i128 values.
    fn k_range(&self, t: Ty) -> Option<(IntTy, i128, i128)> {
        match self.tys.kind(t) {
            TyKind::Int(it) => {
                let bits = it.bits();
                if bits >= 128 {
                    if it.signed() { Some((it, i128::MIN, i128::MAX)) } else { None }
                } else if it.signed() {
                    Some((it, -(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1))
                } else {
                    Some((it, 0, (1i128 << bits) - 1))
                }
            }
            _ => None,
        }
    }

    fn k_fire(&mut self, span: Span, lint: &KLint) {
        if lint.allow_arith || lint.stmt_allow_arith > 0 {
            return;
        }
        self.err(
            "L0540",
            span,
            "this arithmetic operation will overflow",
            "Change the values or the type. If the wrap is intended, use a `wrapping_*` operation.",
        );
    }

    /// The `unconditional_panic` fire: an operation on known values
    /// that always panics when it runs.
    fn k_fire_panic(&mut self, span: Span, lint: &KLint, what: &str, fix: &'static str) {
        if lint.allow_panic || lint.stmt_allow_panic > 0 {
            return;
        }
        self.err("L0541", span, format!("{what}: this operation will panic at runtime"), fix);
    }

    /// Reports an out-of-bounds index when the base expression has an
    /// array type (through any number of references) and the index
    /// value is known. Slice and `Vec` bases keep a runtime length
    /// rustc does not const-propagate, so they never fire here.
    fn k_check_index(&mut self, base: ExprId, iv: &Option<KVal>, span: Span, lint: &KLint) {
        let Some(KVal::Int(i)) = iv else { return };
        let mut t = self.out.expr_ty[self.ei(base)];
        loop {
            match self.tys.kind(t) {
                TyKind::Ref(_, _, e) => t = e,
                _ => break,
            }
        }
        let TyKind::Array(_, c) = self.tys.kind(t) else { return };
        let crate::ty::ConstKind::Int(len) = self.tys.const_kind(c) else { return };
        if *i < 0 || *i as u128 >= len {
            self.k_fire_panic(span, lint, "index out of bounds", "Change the index or the array length.");
        }
    }

    /// Places whose writes change a tracked local, found by span within
    /// the given regions (a loop body and its condition).
    fn k_assigned_in(&self, regions: &[Span]) -> Vec<u32> {
        let mut out = Vec::new();
        for i in 0..self.out.expr_ty.len() {
            let e = ExprId(self.out.expr_base + i as u32);
            let lhs = match self.p.ast.expr(e) {
                Expr::Assign { lhs, .. } | Expr::AssignOp { lhs, .. } => *lhs,
                _ => continue,
            };
            let sp = self.p.ast.expr_span(e);
            if regions.iter().any(|r| r.file == sp.file && r.lo <= sp.lo && sp.hi <= r.hi)
                && let Some(root) = self.k_place_root(lhs)
                && !out.contains(&root)
            {
                out.push(root);
            }
        }
        out
    }

    /// Records a value for a local, unless its address is taken.
    fn k_set(env: &mut KEnv, lint: &KLint, local: u32, v: Option<KVal>) {
        if !lint.addressed.get(local as usize).copied().unwrap_or(false) {
            env[local as usize] = v;
        }
    }

    /// Drops the knowledge of every local assigned in the given regions:
    /// after a control-flow join, a local assigned on any side is no
    /// longer known, even if all sides assign the same value.
    fn k_poison(&self, env: &mut KEnv, regions: &[Span]) {
        for r in self.k_assigned_in(regions) {
            env[r as usize] = None;
        }
    }

    /// True when a block cannot complete: a statement or its tail has
    /// type `!` (a return, a panic, a diverging call, a break).
    fn k_block_diverges(&self, b: ast::BlockId) -> bool {
        let block = self.p.ast.block(b);
        let never = |e: ExprId| self.tys.kind(self.out.expr_ty[self.ei(e)]) == TyKind::Never;
        block.stmts.iter().any(|s| match s {
            Stmt::Expr { expr, .. } => never(*expr),
            Stmt::Let { init, .. } => init.is_some_and(|i| never(i)),
            _ => false,
        }) || block.tail.is_some_and(never)
    }

    /// Binds the known value of a scrutinee into a pattern's locals.
    /// Tuple and struct projections keep their component values; enum
    /// payload bindings are unknown (the probed rustc behavior).
    fn k_bind_pat(&mut self, pat: PatId, v: &Option<KVal>, env: &mut KEnv, lint: &KLint) {
        let p = self.p;
        let pres = self.out.pat_res[(pat.0 - self.out.pat_base) as usize];
        match p.ast.pat(pat) {
            Pat::Binding { .. } => {
                if let PatRes::Binding { local, mode } = pres {
                    let val = if mode == BindMode::Move { v.clone() } else { None };
                    Self::k_set(env, lint, local, val);
                }
            }
            Pat::At { inner, .. } => {
                if let PatRes::Binding { local, mode } = pres {
                    let val = if mode == BindMode::Move { v.clone() } else { None };
                    Self::k_set(env, lint, local, val);
                }
                self.k_bind_pat(*inner, v, env, lint);
            }
            Pat::Tuple(elems) => {
                if let Some(KVal::Agg(items)) = v
                    && let Some(map) = map_tuple_elems(p.ast, elems, items.len())
                {
                    for (idx, sub) in map {
                        self.k_bind_pat(sub, &items[idx].clone(), env, lint);
                    }
                } else {
                    for &sub in elems {
                        self.k_bind_pat(sub, &None, env, lint);
                    }
                }
            }
            Pat::TupleStruct { elems, .. } => {
                let struct_val = match pres {
                    PatRes::Variant(a, _) if !p.adt(a).is_enum => v.clone(),
                    _ => None,
                };
                match &struct_val {
                    Some(KVal::Agg(items)) => match map_tuple_elems(p.ast, elems, items.len()) {
                        Some(map) => {
                            for (idx, sub) in map {
                                self.k_bind_pat(sub, &items[idx].clone(), env, lint);
                            }
                        }
                        None => {
                            for &sub in elems {
                                self.k_bind_pat(sub, &None, env, lint);
                            }
                        }
                    },
                    _ => {
                        for &sub in elems {
                            self.k_bind_pat(sub, &None, env, lint);
                        }
                    }
                }
            }
            Pat::Struct { fields, .. } => {
                let struct_fields = match pres {
                    PatRes::Variant(a, var) if !p.adt(a).is_enum => {
                        Some(p.adt(a).variants[var as usize].fields.iter().map(|f| f.name).collect::<Vec<_>>())
                    }
                    _ => None,
                };
                for &(fname, sub) in fields {
                    let slot = match (v, &struct_fields) {
                        (Some(KVal::Agg(items)), Some(names)) => {
                            names.iter().position(|&n| n == fname).and_then(|i| items.get(i)).cloned().unwrap_or(None)
                        }
                        _ => None,
                    };
                    self.k_bind_pat(sub, &slot, env, lint);
                }
            }
            Pat::Slice { prefix, suffix, .. } => match v {
                Some(KVal::Agg(items)) if items.len() >= prefix.len() + suffix.len() => {
                    for (i, &sub) in prefix.iter().enumerate() {
                        self.k_bind_pat(sub, &items[i].clone(), env, lint);
                    }
                    for (j, &sub) in suffix.iter().enumerate() {
                        self.k_bind_pat(sub, &items[items.len() - suffix.len() + j].clone(), env, lint);
                    }
                }
                _ => {
                    for &sub in prefix.iter().chain(suffix.iter()) {
                        self.k_bind_pat(sub, &None, env, lint);
                    }
                }
            },
            Pat::Or(alts) => {
                for &a in alts {
                    self.k_bind_pat(a, v, env, lint);
                }
            }
            Pat::Ref { inner, .. } | Pat::Paren(inner) => self.k_bind_pat(*inner, &None, env, lint),
            _ => {}
        }
    }

    fn k_block(&mut self, b: ast::BlockId, env: &mut KEnv, lint: &mut KLint) -> Option<KVal> {
        let p = self.p;
        if lint.dead {
            return None;
        }
        let block = p.ast.block(b);
        for stmt in &block.stmts {
            if lint.dead {
                return None;
            }
            let diverges = match stmt {
                Stmt::Let { pat, init, els, attrs, .. } => {
                    // A statement-level `#[allow(..)]` covers this let.
                    if attrs.iter().any(|a| crate::check::allow_attr(a, p.interner, "arithmetic_overflow")) {
                        lint.stmt_allow_arith += 1;
                    }
                    if attrs.iter().any(|a| crate::check::allow_attr(a, p.interner, "unconditional_panic")) {
                        lint.stmt_allow_panic += 1;
                    }
                    let v = init.map(|i| self.k_expr(i, env, lint)).unwrap_or(None);
                    self.k_bind_pat(*pat, &v, env, lint);
                    if let Some(els) = els {
                        let mut eenv = env.clone();
                        self.k_block(*els, &mut eenv, lint);
                    }
                    if attrs.iter().any(|a| crate::check::allow_attr(a, p.interner, "arithmetic_overflow")) {
                        lint.stmt_allow_arith -= 1;
                    }
                    if attrs.iter().any(|a| crate::check::allow_attr(a, p.interner, "unconditional_panic")) {
                        lint.stmt_allow_panic -= 1;
                    }
                    init.is_some_and(|i| self.tys.kind(self.out.expr_ty[self.ei(i)]) == TyKind::Never)
                }
                Stmt::Expr { expr, .. } => {
                    self.k_expr(*expr, env, lint);
                    self.tys.kind(self.out.expr_ty[self.ei(*expr)]) == TyKind::Never
                }
                Stmt::Item(_) | Stmt::Macro { .. } => false,
            };
            if diverges {
                return None;
            }
        }
        if lint.dead {
            return None;
        }
        match block.tail {
            Some(tail) => self.k_expr(tail, env, lint),
            None => None,
        }
    }

    /// A recorded const value as a known value, if it is scalar or an
    /// aggregate of knowns.
    fn k_const(&self, cv: &crate::ty::consteval::ConstValue, t: Ty) -> Option<KVal> {
        use crate::ty::consteval::ConstValue as CV;
        match cv {
            CV::Int(v) => self.k_math(*v, t).map(KVal::Int),
            CV::Bool(b) => Some(KVal::Bool(*b)),
            CV::Char(c) => Some(KVal::Int(*c as i128)),
            CV::Variant(v, _) => match self.tys.kind(t) {
                TyKind::Adt(def, _) => match self.p.adt_by_def(def) {
                    Some(a) if self.p.adt(a).is_enum => Some(KVal::Enum(a, *v)),
                    _ => None,
                },
                _ => None,
            },
            CV::Aggregate(vals) => Some(KVal::Agg(vals.iter().map(|v| self.k_const(v, ERROR)).collect())),
            _ => None,
        }
    }

    /// Walks one expression, lints overflowing operations with known
    /// operands, applies assignment effects to `env`, and returns the
    /// expression's known value when there is one.
    fn k_expr(&mut self, e: ExprId, env: &mut KEnv, lint: &mut KLint) -> Option<KVal> {
        let p = self.p;
        let span = self.span(e);
        let ety = self.out.expr_ty[self.ei(e)];
        if let Some(cv) = &self.out.const_exprs[self.ei(e)] {
            return self.k_const(cv, ety);
        }
        match p.ast.expr(e) {
            Expr::Int(v, _) => Some(KVal::Int(*v as u128 as i128)),
            Expr::Bool(b) => Some(KVal::Bool(*b)),
            Expr::Char(c) => Some(KVal::Int(*c as i128)),
            Expr::Path(_) | Expr::SelfValue => match self.out.expr_res[self.ei(e)] {
                Res::Local(l) => env.get(l as usize).cloned().unwrap_or(None),
                Res::Variant(a, v) if p.adt(a).is_enum => Some(KVal::Enum(a, v)),
                _ => None,
            },
            Expr::Block(b) | Expr::UnsafeBlock(b) => self.k_block(*b, env, lint),
            Expr::ConstBlock(_) => None,
            Expr::LabeledBlock { label, body } => {
                lint.frames.push((Some(label.name), Vec::new()));
                let v = self.k_block(*body, env, lint);
                let (_, breaks) = lint.frames.pop().unwrap();
                match (breaks.len(), v) {
                    (0, v) => v,
                    (1, None) => breaks.into_iter().next().unwrap(),
                    _ => None,
                }
            }
            Expr::If { cond, then, els } => {
                let cv = self.k_expr(*cond, env, lint);
                let then_span = p.ast.block(*then).span;
                let els_span = els.map(|x| self.span(x));
                if let Some(KVal::Bool(b)) = cv {
                    // Only the taken side runs (dead-side operations do not
                    // fire); locals it assigns are still lost at the join,
                    // and if it diverges, what follows is unreachable.
                    let saved = lint.dead;
                    lint.dead = false;
                    let side_span = if b {
                        self.k_block(*then, env, lint);
                        then_span
                    } else {
                        match els {
                            Some(els) => {
                                self.k_expr(*els, env, lint);
                                self.span(*els)
                            }
                            None => span,
                        }
                    };
                    let side_diverges = lint.dead
                        || if b {
                            self.k_block_diverges(*then)
                        } else {
                            els.is_some_and(|x| self.tys.kind(self.out.expr_ty[self.ei(x)]) == TyKind::Never)
                        };
                    lint.dead = saved || side_diverges;
                    if els.is_some() || b {
                        self.k_poison(env, &[side_span]);
                    }
                    return None;
                }
                let saved = lint.dead;
                lint.dead = false;
                let mut tenv = env.clone();
                self.k_block(*then, &mut tenv, lint);
                lint.dead = false;
                if let Some(els) = els {
                    let mut eenv = env.clone();
                    self.k_expr(*els, &mut eenv, lint);
                }
                lint.dead = saved;
                match els_span {
                    Some(es) => self.k_poison(env, &[then_span, es]),
                    None => self.k_poison(env, &[then_span]),
                }
                None
            }
            Expr::While { label, cond, body } => {
                let regions = [self.span(*cond), p.ast.block(*body).span];
                let poison = self.k_assigned_in(&regions);
                let mut lenv = env.clone();
                for &r in &poison {
                    lenv[r as usize] = None;
                }
                let saved = lint.dead;
                lint.dead = false;
                let cv = self.k_expr(*cond, &mut lenv, lint);
                if cv != Some(KVal::Bool(false)) {
                    lint.dead = false;
                    lint.frames.push((label.map(|l| l.name), Vec::new()));
                    self.k_block(*body, &mut lenv, lint);
                    lint.frames.pop();
                }
                lint.dead = saved;
                for &r in &poison {
                    env[r as usize] = None;
                }
                None
            }
            Expr::Loop { label, body } => {
                let poison = self.k_assigned_in(&[p.ast.block(*body).span]);
                let mut lenv = env.clone();
                for &r in &poison {
                    lenv[r as usize] = None;
                }
                let saved = lint.dead;
                lint.dead = false;
                lint.frames.push((label.map(|l| l.name), Vec::new()));
                self.k_block(*body, &mut lenv, lint);
                let (_, breaks) = lint.frames.pop().unwrap();
                lint.dead = saved;
                for &r in &poison {
                    env[r as usize] = None;
                }
                if breaks.len() == 1 { breaks.into_iter().next().unwrap() } else { None }
            }
            Expr::For { label, pat, iter, body } => {
                self.k_expr(*iter, env, lint);
                let regions = [self.span(*iter), p.ast.block(*body).span];
                let poison = self.k_assigned_in(&regions);
                let mut lenv = env.clone();
                for &r in &poison {
                    lenv[r as usize] = None;
                }
                let saved = lint.dead;
                lint.dead = false;
                let none = None;
                self.k_bind_pat(*pat, &none, &mut lenv, lint);
                lint.frames.push((label.map(|l| l.name), Vec::new()));
                self.k_block(*body, &mut lenv, lint);
                lint.frames.pop();
                lint.dead = saved;
                for &r in &poison {
                    env[r as usize] = None;
                }
                None
            }
            Expr::Match { scrut, arms } => {
                let sv = self.k_expr(*scrut, env, lint);
                let sty = self.out.expr_ty[self.ei(*scrut)];
                let saved = lint.dead;
                if let Some(arm) = sv.as_ref().and_then(|v| self.k_select_arm(arms, v, sty)) {
                    // Only this arm runs. With several arms its assignments
                    // and its value are still lost at the join; a single
                    // arm is straight-line code.
                    lint.dead = false;
                    self.k_bind_pat(arm.pat, &sv, env, lint);
                    let v = self.k_expr(arm.body, env, lint);
                    let body_dead = lint.dead || self.tys.kind(self.out.expr_ty[self.ei(arm.body)]) == TyKind::Never;
                    lint.dead = saved || body_dead;
                    if arms.len() == 1 {
                        return v;
                    }
                    self.k_poison(env, &[self.span(arm.body)]);
                    return None;
                }
                let mut regions: Vec<Span> = Vec::new();
                let mut single = None;
                for arm in arms {
                    lint.dead = false;
                    let mut aenv = env.clone();
                    self.k_bind_pat(arm.pat, &sv, &mut aenv, lint);
                    if let Some(g) = arm.guard {
                        self.k_expr(g, &mut aenv, lint);
                    }
                    let v = self.k_expr(arm.body, &mut aenv, lint);
                    regions.push(self.span(arm.body));
                    single = Some((aenv, v));
                }
                lint.dead = saved;
                if arms.len() == 1
                    && let Some((aenv, v)) = single
                {
                    *env = aenv;
                    return v;
                }
                self.k_poison(env, &regions);
                None
            }
            Expr::Break { label, value } => {
                let v = value.map(|x| self.k_expr(x, env, lint)).unwrap_or(None);
                let want = label.map(|l| l.name);
                if let Some(frame) = lint.frames.iter_mut().rev().find(|(n, _)| want.is_none() || *n == want) {
                    frame.1.push(v);
                }
                None
            }
            Expr::Continue(_) => None,
            Expr::Return(v) => {
                if let Some(v) = v {
                    self.k_expr(*v, env, lint);
                }
                None
            }
            Expr::Let { pat, scrut } => {
                let v = self.k_expr(*scrut, env, lint);
                self.k_bind_pat(*pat, &v, env, lint);
                None
            }
            Expr::Call { callee, args } => {
                self.k_expr(*callee, env, lint);
                let mut vals = Vec::new();
                for &a in args {
                    vals.push(self.k_expr(a, env, lint));
                }
                match self.out.expr_res[self.ei(e)] {
                    Res::DefaultVal => match self.tys.kind(ety) {
                        TyKind::Int(_) | TyKind::Char => Some(KVal::Int(0)),
                        TyKind::Bool => Some(KVal::Bool(false)),
                        _ => None,
                    },
                    Res::FromCast => match vals.into_iter().next().flatten() {
                        Some(KVal::Int(v)) => self.k_wrap(v, ety).map(KVal::Int),
                        other => other,
                    },
                    _ => match self.out.expr_res[self.ei(*callee)] {
                        Res::ConstUsize(u) => Some(KVal::Int(u as i128)),
                        Res::Variant(a, v) if p.adt(a).is_enum => Some(KVal::Enum(a, v)),
                        Res::Variant(a, _) if !p.adt(a).is_enum => Some(KVal::Agg(vals)),
                        Res::OptSome => Some(KVal::Agg(vals)),
                        _ => None,
                    },
                }
            }
            Expr::MethodCall { recv, args, .. } => {
                self.k_expr(*recv, env, lint);
                for &a in args {
                    self.k_expr(a, env, lint);
                }
                None
            }
            Expr::Field { base, .. } | Expr::TupleField { base, .. } => {
                let bv = self.k_expr(*base, env, lint);
                match (bv, self.out.expr_res[self.ei(e)]) {
                    (Some(KVal::Agg(items)), Res::Field { derefs: 0, index }) => items.get(index as usize).cloned().unwrap_or(None),
                    _ => None,
                }
            }
            Expr::Index { base, index } => {
                let bv = self.k_expr(*base, env, lint);
                let iv = self.k_expr(*index, env, lint);
                self.k_check_index(*base, &iv, span, lint);
                match (bv, iv) {
                    (Some(KVal::Agg(items)), Some(KVal::Int(i))) if i >= 0 => items.get(i as usize).cloned().unwrap_or(None),
                    _ => None,
                }
            }
            Expr::StructLit { fields, update, .. } => {
                let base = update.and_then(|u| self.k_expr(u, env, lint));
                match self.out.expr_res[self.ei(e)] {
                    Res::Variant(a, v) if !p.adt(a).is_enum => {
                        let variant = &p.adt(a).variants[v as usize];
                        let mut items: Vec<Option<KVal>> = match base {
                            Some(KVal::Agg(items)) if items.len() == variant.fields.len() => items,
                            _ => vec![None; variant.fields.len()],
                        };
                        for &(fname, _, fe) in fields {
                            let fv = self.k_expr(fe, env, lint);
                            if let Some(i) = variant.fields.iter().position(|f| f.name == fname) {
                                items[i] = fv;
                            }
                        }
                        Some(KVal::Agg(items))
                    }
                    Res::Variant(a, v) if p.adt(a).is_enum => {
                        for &(_, _, fe) in fields {
                            self.k_expr(fe, env, lint);
                        }
                        Some(KVal::Enum(a, v))
                    }
                    _ => {
                        for &(_, _, fe) in fields {
                            self.k_expr(fe, env, lint);
                        }
                        None
                    }
                }
            }
            Expr::Tuple(elems) => {
                let items = elems.iter().map(|&el| self.k_expr(el, env, lint)).collect();
                Some(KVal::Agg(items))
            }
            Expr::Array(elems) => {
                let items = elems.iter().map(|&el| self.k_expr(el, env, lint)).collect();
                Some(KVal::Agg(items))
            }
            Expr::ArrayRepeat { value, len } => {
                self.k_expr(*value, env, lint);
                self.k_expr(*len, env, lint);
                None
            }
            Expr::Range { lo, hi, .. } => {
                for b in [lo, hi].into_iter().flatten() {
                    self.k_expr(*b, env, lint);
                }
                None
            }
            Expr::Ref { expr, .. } => {
                self.k_expr(*expr, env, lint);
                None
            }
            Expr::Deref(inner) => {
                self.k_expr(*inner, env, lint);
                None
            }
            Expr::Cast { expr, .. } => {
                let v = self.k_expr(*expr, env, lint);
                match (v, self.tys.kind(ety)) {
                    (Some(KVal::Int(x)), TyKind::Int(_) | TyKind::Char) => self.k_wrap(x, ety).map(KVal::Int),
                    (Some(KVal::Bool(b)), TyKind::Int(_)) => Some(KVal::Int(b as i128)),
                    (Some(KVal::Bool(b)), TyKind::Bool) => Some(KVal::Bool(b)),
                    _ => None,
                }
            }
            Expr::OffsetOf { .. } => match self.out.expr_res[self.ei(e)] {
                Res::ConstUsize(u) => Some(KVal::Int(u as i128)),
                _ => None,
            },
            Expr::Macro { args, .. } => {
                for &a in args {
                    self.k_expr(a, env, lint);
                }
                None
            }
            Expr::Binary { op, lhs, rhs } => self.k_binary(e, *op, *lhs, *rhs, span, env, lint),
            Expr::Unary { op, expr } => self.k_unary(e, *op, *expr, span, env, lint),
            Expr::Assign { lhs, rhs } => {
                self.k_place_parts(*lhs, env, lint);
                let whole = if matches!(p.ast.expr(*lhs), Expr::Path(_)) { self.k_place_root(*lhs) } else { None };
                if let Some(root) = whole
                    && matches!(p.ast.expr(*rhs), Expr::Binary { .. } | Expr::Unary { .. })
                {
                    lint.suppress = Some((*rhs, root));
                }
                let v = self.k_expr(*rhs, env, lint);
                lint.suppress = None;
                match whole {
                    Some(root) => Self::k_set(env, lint, root, v),
                    None => {
                        if let Some(root) = self.k_place_root(*lhs) {
                            env[root as usize] = None;
                        }
                    }
                }
                None
            }
            Expr::AssignOp { op, lhs, rhs } => {
                let root = self.k_place_root(*lhs);
                let old = if matches!(p.ast.expr(*lhs), Expr::Path(_)) {
                    root.and_then(|r| env.get(r as usize).cloned().unwrap_or(None))
                } else {
                    self.k_place_parts(*lhs, env, lint);
                    None
                };
                let rv = self.k_expr(*rhs, env, lint);
                // A compound assignment does not fire for its own overflow
                // (probed), but a bad shift amount still does, and a
                // division or remainder that always panics does too.
                if matches!(op, BinOp::Shl | BinOp::Shr)
                    && let Some(KVal::Int(s)) = rv
                {
                    let lt = self.out.expr_ty[self.ei(*lhs)];
                    if let Some(bits) = self.k_bits(lt) {
                        if s < 0 || s >= bits as i128 {
                            self.k_fire(span, lint);
                        }
                    }
                }
                if matches!(op, BinOp::Div | BinOp::Rem)
                    && let Some(KVal::Int(b)) = rv
                {
                    let lt = self.out.expr_ty[self.ei(*lhs)];
                    if let Some(b) = self.k_math(b, lt) {
                        if b == 0 {
                            self.k_fire_panic(span, lint, "attempt to divide by zero", "Change the divisor so it cannot be zero.");
                        } else if b == -1
                            && let Some((_, lo, _)) = self.k_range(lt)
                            && matches!(&old, Some(KVal::Int(a)) if self.k_math(*a, lt) == Some(lo))
                        {
                            self.k_fire_panic(span, lint, "attempt to divide with overflow", "Change the values or the type.");
                        }
                    }
                }
                match root {
                    Some(r) if matches!(p.ast.expr(*lhs), Expr::Path(_)) => {
                        let lt = self.out.expr_ty[self.ei(*lhs)];
                        let nv = match (old, rv) {
                            (Some(KVal::Int(a)), Some(KVal::Int(b))) => self.k_arith(*op, a, b, lt).map(KVal::Int),
                            _ => None,
                        };
                        Self::k_set(env, lint, r, nv);
                    }
                    Some(r) => env[r as usize] = None,
                    None => {}
                }
                None
            }
            Expr::Try(inner) | Expr::Await(inner) => self.k_expr(*inner, env, lint),
            Expr::Closure { params, body, .. } => {
                // A closure body is its own body for the lints: its
                // parameters are unknown, captures keep the knowledge
                // they have here, and nothing it assigns leaks out.
                let mut cenv = env.clone();
                let none = None;
                for param in params {
                    self.k_bind_pat(param.pat, &none, &mut cenv, lint);
                }
                let saved = lint.dead;
                lint.dead = false;
                self.k_expr(*body, &mut cenv, lint);
                lint.dead = saved;
                None
            }
            _ => None,
        }
    }

    /// Walks the sub-expressions of an assignment place (indexes and the
    /// like) so operations inside them are linted.
    fn k_place_parts(&mut self, e: ExprId, env: &mut KEnv, lint: &mut KLint) {
        match self.p.ast.expr(e) {
            Expr::Index { base, index } => {
                self.k_place_parts(*base, env, lint);
                let iv = self.k_expr(*index, env, lint);
                let span = self.span(e);
                self.k_check_index(*base, &iv, span, lint);
            }
            Expr::Field { base, .. } | Expr::TupleField { base, .. } => self.k_place_parts(*base, env, lint),
            Expr::Deref(inner) => {
                self.k_expr(*inner, env, lint);
            }
            _ => {}
        }
    }

    /// The arm a known scrutinee value selects. Arms are read in
    /// order: an arm is selected only when its pattern certainly
    /// matches, it has no guard, and no earlier arm could have
    /// matched. A pattern this pass cannot decide (a guarded arm that
    /// covers, a payload subpattern, a const it cannot read) stops
    /// the selection, so the caller walks every arm instead.
    fn k_select_arm<'x>(&self, arms: &'x [ast::Arm], v: &KVal, sty: Ty) -> Option<&'x ast::Arm> {
        for arm in arms {
            match self.k_covers(arm.pat, v, sty) {
                KCov::Yes if arm.guard.is_none() => return Some(arm),
                KCov::Yes | KCov::Unknown => return None,
                KCov::No => {}
            }
        }
        None
    }

    /// Whether a pattern certainly matches, certainly misses, or may
    /// match the known scrutinee value.
    fn k_covers(&self, pat: PatId, v: &KVal, sty: Ty) -> KCov {
        match v {
            KVal::Int(i) => self.k_scalar_covers(pat, *i, sty),
            KVal::Bool(b) => self.k_scalar_covers(pat, *b as i128, sty),
            KVal::Enum(a, var) => self.k_enum_covers(pat, *a, *var),
            KVal::Agg(_) => KCov::Unknown,
        }
    }

    fn k_scalar_covers(&self, pat: PatId, val: i128, sty: Ty) -> KCov {
        let p = self.p;
        match p.ast.pat(pat) {
            Pat::Wild => KCov::Yes,
            Pat::Binding { .. } => match self.out.pat_res[(pat.0 - self.out.pat_base) as usize] {
                // A const item used as a pattern matches only its value.
                PatRes::ConstItem(_) => match self.pat_scalar(pat) {
                    Some(x) if self.k_cmp(val, x, sty) == std::cmp::Ordering::Equal => KCov::Yes,
                    Some(_) => KCov::No,
                    None => KCov::Unknown,
                },
                PatRes::Binding { .. } => KCov::Yes,
                _ => KCov::Unknown,
            },
            Pat::Path(_) => match self.pat_scalar(pat) {
                Some(x) if self.k_cmp(val, x, sty) == std::cmp::Ordering::Equal => KCov::Yes,
                Some(_) => KCov::No,
                None => KCov::Unknown,
            },
            Pat::Lit(l) => match p.ast.expr(*l) {
                Expr::Bool(b) => {
                    if val == *b as i128 {
                        KCov::Yes
                    } else {
                        KCov::No
                    }
                }
                _ => match self.const_scalar(*l) {
                    Some(x) if self.k_cmp(val, x, sty) == std::cmp::Ordering::Equal => KCov::Yes,
                    Some(_) => KCov::No,
                    None => KCov::Unknown,
                },
            },
            Pat::Range { lo, hi, inclusive } => {
                use std::cmp::Ordering::{Greater, Less};
                let lo_v = match lo {
                    Some(e) => match self.const_scalar(*e) {
                        Some(x) => Some(x),
                        None => return KCov::Unknown,
                    },
                    None => None,
                };
                let hi_v = match hi {
                    Some(e) => match self.const_scalar(*e) {
                        Some(x) => Some(x),
                        None => return KCov::Unknown,
                    },
                    None => None,
                };
                let lo_ok = lo_v.is_none_or(|x| self.k_cmp(val, x, sty) != Less);
                let hi_ok = hi_v.is_none_or(|x| {
                    let c = self.k_cmp(val, x, sty);
                    if *inclusive { c != Greater } else { c == Less }
                });
                if lo_ok && hi_ok {
                    KCov::Yes
                } else {
                    KCov::No
                }
            }
            Pat::Or(alts) => {
                let mut any_unknown = false;
                for &a in alts {
                    match self.k_scalar_covers(a, val, sty) {
                        KCov::Yes => return KCov::Yes,
                        KCov::Unknown => any_unknown = true,
                        KCov::No => {}
                    }
                }
                if any_unknown {
                    KCov::Unknown
                } else {
                    KCov::No
                }
            }
            Pat::At { inner, .. } | Pat::Paren(inner) => self.k_scalar_covers(*inner, val, sty),
            _ => KCov::Unknown,
        }
    }

    fn k_enum_covers(&self, pat: PatId, adt: AdtId, var: u32) -> KCov {
        let p = self.p;
        match self.out.pat_res[(pat.0 - self.out.pat_base) as usize] {
            PatRes::Variant(a, v) if a == adt => {
                if v != var {
                    return KCov::No;
                }
                // The variant matches; payload subpatterns that are
                // plain bindings cannot refuse it.
                let subs_catch = match p.ast.pat(pat) {
                    Pat::TupleStruct { elems, .. } => elems.iter().all(|&s| self.k_pat_catches(s)),
                    Pat::Struct { fields, .. } => fields.iter().all(|&(_, s)| self.k_pat_catches(s)),
                    _ => true,
                };
                if subs_catch {
                    KCov::Yes
                } else {
                    KCov::Unknown
                }
            }
            PatRes::Variant(..) => KCov::Unknown,
            _ => match p.ast.pat(pat) {
                Pat::Wild => KCov::Yes,
                Pat::Binding { .. } => match self.out.pat_res[(pat.0 - self.out.pat_base) as usize] {
                    PatRes::Binding { .. } => KCov::Yes,
                    _ => KCov::Unknown,
                },
                Pat::Or(alts) => {
                    let mut any_unknown = false;
                    for &a in alts {
                        match self.k_enum_covers(a, adt, var) {
                            KCov::Yes => return KCov::Yes,
                            KCov::Unknown => any_unknown = true,
                            KCov::No => {}
                        }
                    }
                    if any_unknown {
                        KCov::Unknown
                    } else {
                        KCov::No
                    }
                }
                Pat::At { inner, .. } | Pat::Paren(inner) => self.k_enum_covers(*inner, adt, var),
                _ => KCov::Unknown,
            },
        }
    }

    /// True when a subpattern accepts any payload (a binding, a
    /// wildcard, or the same nested under `@`, parens, or borrows).
    fn k_pat_catches(&self, pat: PatId) -> bool {
        match self.p.ast.pat(pat) {
            Pat::Wild | Pat::Rest => true,
            Pat::Binding { .. } => matches!(self.out.pat_res[(pat.0 - self.out.pat_base) as usize], PatRes::Binding { .. }),
            Pat::At { inner, .. } | Pat::Paren(inner) | Pat::Ref { inner, .. } => self.k_pat_catches(*inner),
            Pat::Or(alts) => alts.iter().any(|&a| self.k_pat_catches(a)),
            _ => false,
        }
    }

    /// Wrapped arithmetic for continuing a known value (no lint here).
    fn k_arith(&self, op: BinOp, a: i128, b: i128, t: Ty) -> Option<i128> {
        if self.k_is_u128(t) {
            // The stored values are u128 bit patterns; `b` of a shift is
            // the amount in its own type, already range-checked by the
            // caller, so a negative or huge amount just stops tracking.
            let (au, bu) = (a as u128, b as u128);
            let r = match op {
                BinOp::Add => au.wrapping_add(bu),
                BinOp::Sub => au.wrapping_sub(bu),
                BinOp::Mul => au.wrapping_mul(bu),
                BinOp::Div => {
                    if bu == 0 {
                        return None;
                    }
                    au / bu
                }
                BinOp::Rem => {
                    if bu == 0 {
                        return None;
                    }
                    au % bu
                }
                BinOp::BitAnd => au & bu,
                BinOp::BitOr => au | bu,
                BinOp::BitXor => au ^ bu,
                BinOp::Shl => au.checked_shl(u32::try_from(b).ok()?)?,
                BinOp::Shr => au.checked_shr(u32::try_from(b).ok()?)?,
                _ => return None,
            };
            return Some(r as i128);
        }
        let (a, b) = (self.k_math(a, t)?, self.k_math(b, t)?);
        let r = match op {
            BinOp::Add => a.checked_add(b)?,
            BinOp::Sub => a.checked_sub(b)?,
            BinOp::Mul => a.checked_mul(b)?,
            BinOp::Div => {
                if b == 0 {
                    return None;
                }
                a.checked_div(b)?
            }
            BinOp::Rem => {
                if b == 0 {
                    return None;
                }
                a.checked_rem(b)?
            }
            BinOp::BitAnd => a & b,
            BinOp::BitOr => a | b,
            BinOp::BitXor => a ^ b,
            BinOp::Shl => a.checked_shl(u32::try_from(b).ok()?)?,
            BinOp::Shr => a.checked_shr(u32::try_from(b).ok()?)?,
            _ => return None,
        };
        self.k_wrap(r, t)
    }

    fn k_binary(&mut self, e: ExprId, op: BinOp, lhs: ExprId, rhs: ExprId, span: Span, env: &mut KEnv, lint: &mut KLint) -> Option<KVal> {
        let lv = self.k_expr(lhs, env, lint);
        // A known short-circuit skips the right side entirely.
        match (op, &lv) {
            (BinOp::And, Some(KVal::Bool(false))) => return Some(KVal::Bool(false)),
            (BinOp::Or, Some(KVal::Bool(true))) => return Some(KVal::Bool(true)),
            _ => {}
        }
        let rv = self.k_expr(rhs, env, lint);
        if matches!(self.out.expr_res[self.ei(e)], Res::TraitBin { .. }) {
            return None;
        }
        match op {
            BinOp::And => match (lv, rv) {
                (Some(KVal::Bool(a)), Some(KVal::Bool(b))) => Some(KVal::Bool(a && b)),
                _ => None,
            },
            BinOp::Or => match (lv, rv) {
                (Some(KVal::Bool(a)), Some(KVal::Bool(b))) => Some(KVal::Bool(a || b)),
                _ => None,
            },
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let ord = match (&lv, &rv) {
                    (Some(KVal::Int(a)), Some(KVal::Int(b))) => {
                        let lt = self.out.expr_ty[self.ei(lhs)];
                        match (self.k_math(*a, lt), self.k_math(*b, lt)) {
                            (Some(a), Some(b)) => Some(self.k_cmp(a, b, lt)),
                            _ => None,
                        }
                    }
                    (Some(KVal::Bool(a)), Some(KVal::Bool(b))) => Some(a.cmp(b)),
                    _ => None,
                };
                ord.map(|o| {
                    KVal::Bool(match op {
                        BinOp::Eq => o == std::cmp::Ordering::Equal,
                        BinOp::Ne => o != std::cmp::Ordering::Equal,
                        BinOp::Lt => o == std::cmp::Ordering::Less,
                        BinOp::Le => o != std::cmp::Ordering::Greater,
                        BinOp::Gt => o == std::cmp::Ordering::Greater,
                        _ => o != std::cmp::Ordering::Less,
                    })
                })
            }
            BinOp::Shl | BinOp::Shr => {
                let lt = self.out.expr_ty[self.ei(lhs)];
                if let (Some(bits), Some(KVal::Int(s))) = (self.k_bits(lt), &rv)
                    && (*s < 0 || *s >= bits as i128)
                {
                    self.k_fire(span, lint);
                    return None;
                }
                match (lv, rv) {
                    (Some(KVal::Int(a)), Some(KVal::Int(b))) => self.k_arith(op, a, b, lt).map(KVal::Int),
                    _ => None,
                }
            }
            BinOp::Add | BinOp::Sub | BinOp::Mul => {
                let lt = self.out.expr_ty[self.ei(lhs)];
                let (Some(KVal::Int(a)), Some(KVal::Int(b))) = (lv, rv) else { return None };
                if self.k_is_u128(lt) {
                    let (au, bu) = (a as u128, b as u128);
                    let r = match op {
                        BinOp::Add => au.checked_add(bu),
                        BinOp::Sub => au.checked_sub(bu),
                        _ => au.checked_mul(bu),
                    };
                    let suppressed = lint.suppress == Some((e, u32::MAX))
                        || matches!(lint.suppress, Some((se, root)) if se == e && (self.k_place_root(lhs) == Some(root) || self.k_place_root(rhs) == Some(root)));
                    return match r {
                        Some(r) => Some(KVal::Int(r as i128)),
                        None => {
                            if !suppressed {
                                self.k_fire(span, lint);
                            }
                            None
                        }
                    };
                }
                let Some((_, lo, hi)) = self.k_range(lt) else { return None };
                let (Some(a), Some(b)) = (self.k_math(a, lt), self.k_math(b, lt)) else { return None };
                let r = match op {
                    BinOp::Add => a.checked_add(b),
                    BinOp::Sub => a.checked_sub(b),
                    _ => a.checked_mul(b),
                };
                let suppressed = lint.suppress == Some((e, u32::MAX))
                    || matches!(lint.suppress, Some((se, root)) if se == e && (self.k_place_root(lhs) == Some(root) || self.k_place_root(rhs) == Some(root)));
                match r {
                    Some(r) if (lo..=hi).contains(&r) => Some(KVal::Int(r)),
                    _ => {
                        if !suppressed {
                            self.k_fire(span, lint);
                        }
                        None
                    }
                }
            }
            BinOp::Div | BinOp::Rem => {
                let lt = self.out.expr_ty[self.ei(lhs)];
                // A known zero divisor panics whatever the dividend is;
                // `MIN / -1` needs both sides known.
                if let Some(KVal::Int(b)) = &rv
                    && self.k_bits(lt).is_some()
                    && let Some(b) = self.k_math(*b, lt)
                {
                    if b == 0 {
                        self.k_fire_panic(span, lint, "attempt to divide by zero", "Change the divisor so it cannot be zero.");
                        return None;
                    }
                    if b == -1
                        && let Some(KVal::Int(a)) = &lv
                        && let Some((_, lo, _)) = self.k_range(lt)
                        && self.k_math(*a, lt) == Some(lo)
                    {
                        self.k_fire_panic(span, lint, "attempt to divide with overflow", "Change the values or the type.");
                        return None;
                    }
                }
                match (lv, rv) {
                    (Some(KVal::Int(a)), Some(KVal::Int(b))) => self.k_arith(op, a, b, lt).map(KVal::Int),
                    _ => None,
                }
            }
            BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => {
                let lt = self.out.expr_ty[self.ei(lhs)];
                match (lv, rv) {
                    (Some(KVal::Int(a)), Some(KVal::Int(b))) => self.k_arith(op, a, b, lt).map(KVal::Int),
                    _ => None,
                }
            }
        }
    }

    fn k_unary(&mut self, e: ExprId, op: UnOp, inner: ExprId, span: Span, env: &mut KEnv, lint: &mut KLint) -> Option<KVal> {
        let v = self.k_expr(inner, env, lint);
        match op {
            UnOp::Neg => {
                let Some(KVal::Int(x)) = v else { return None };
                let t = self.out.expr_ty[self.ei(e)];
                // A literal under the minus is a magnitude, not a
                // negation of a value: `-128i8` and the `i128::MIN`
                // literal (magnitude 2^127, stored as the MIN bit
                // pattern) wrap to their own value and never fire.
                if matches!(self.p.ast.expr(inner), Expr::Int(..)) {
                    return self.k_wrap(x.wrapping_neg(), t).map(KVal::Int);
                }
                let Some((_, lo, hi)) = self.k_range(t) else { return None };
                let r = x.checked_neg();
                match r {
                    Some(r) if (lo..=hi).contains(&r) => Some(KVal::Int(r)),
                    _ => {
                        let suppressed = matches!(lint.suppress, Some((se, root)) if se == e && self.k_place_root(inner) == Some(root));
                        if !suppressed {
                            self.k_fire(span, lint);
                        }
                        None
                    }
                }
            }
            UnOp::Not => match v {
                Some(KVal::Int(x)) => {
                    let t = self.out.expr_ty[self.ei(e)];
                    let x = self.k_math(x, t)?;
                    self.k_wrap(!x, t).map(KVal::Int)
                }
                Some(KVal::Bool(b)) => Some(KVal::Bool(!b)),
                _ => None,
            },
        }
    }

    // ---------- Finish ----------

    /// True when the type still holds an unbound non-integer inference
    /// variable (an integer variable defaults to i32, as in rustc; any other
    /// one is the E0282 "type annotations needed" case).
    /// True for a type variable that is not an integer or float literal variable.
    fn unbound_general(&self, t: Ty) -> bool {
        matches!(self.kind(t), TyKind::Infer(v) if !v.is_int() && !v.is_float())
    }

    fn has_unbound_var(&self, t: Ty) -> bool {
        if !self.tys.flags(t).contains_infer() {
            return false;
        }
        match self.tys.kind(self.resolve(t)) {
            TyKind::Infer(v) => !v.is_int() && !v.is_float(),
            TyKind::Ref(_, _, e) | TyKind::Slice(e) | TyKind::Array(e, _) => self.has_unbound_var(e),
            TyKind::Tuple(ts) => self.tys.tys_of(ts).iter().any(|&e| self.has_unbound_var(e)),
            TyKind::Adt(_, a) => self.tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| self.has_unbound_var(e))),
            _ => false,
        }
    }

    /// A generic call whose type argument nothing fixed is an
    /// annotation error (rustc E0282 and E0283), never a dropped
    /// instance request. Runs after inference, before the hard
    /// obligation run, which then skips the obligations on the
    /// reported variables (one error per root). Closure sites
    /// have their own check below; a body with an error already
    /// reports nothing here, since its variables may be unbound
    /// only because of that error.
    fn uninferred_site_args(&mut self) {
        self.run_obligations(false);
        if !self.errs.is_empty() {
            return;
        }
        let p = self.p;
        let mut reported: Vec<u32> = Vec::new();
        for i in 0..self.generic_sites.len() {
            let (ei, template, args) = self.generic_sites[i].clone();
            let Some(gi) = args.iter().position(|g| g.as_ty().is_some_and(|t| self.has_unbound_var(t) && !self.has_error_kind(t))) else {
                continue;
            };
            let t = args[gi].as_ty().unwrap_or(ERROR);
            let t = self.deep(t);
            self.unbound_vars(t, &mut reported);
            let param = p.gx.fn_templates.get(template.0 as usize).and_then(|t| t.as_ref()).and_then(|t| t.generics.params.get(gi));
            let pname = param.map_or("_".to_string(), |d| self.name(d.name).to_string());
            let fname = p.display_path(p.fn_info(template).name);
            let span = self.span(ExprId(self.out.expr_base + ei as u32));
            self.err(
                "L0610",
                span,
                format!("type annotations needed: cannot infer the type of the generic parameter `{pname}` of `{fname}`"),
                "Name the type with a turbofish such as `::<i32>`, or annotate the value the call returns.",
            );
        }
        if reported.is_empty() {
            return;
        }
        let pending = self.obl.take();
        for ob in pending {
            let mentions = match ob {
                obligations::Obligation::Trait { trait_ref, .. } => self.args_mention(trait_ref.args, &reported),
                obligations::Obligation::AssocEq { eq, .. } => {
                    self.args_mention(eq.trait_args, &reported) || reported.iter().any(|&v| self.occurs(v, eq.ty))
                }
            };
            if !mentions {
                self.obl.push(ob);
            }
        }
    }

    /// The unbound general variables in one deep-resolved type.
    fn unbound_vars(&self, t: Ty, out: &mut Vec<u32>) {
        if !self.tys.flags(t).contains_infer() {
            return;
        }
        match self.tys.kind(self.resolve(t)) {
            TyKind::Infer(v) if !v.is_int() && !v.is_float() => out.push(v.index()),
            TyKind::Ref(_, _, e) | TyKind::Slice(e) | TyKind::Array(e, _) | TyKind::RawPtr(_, e) => self.unbound_vars(e, out),
            TyKind::Tuple(ts) => {
                for &e in self.tys.tys_of(ts) {
                    self.unbound_vars(e, out);
                }
            }
            TyKind::Adt(_, a) | TyKind::Projection(_, a) | TyKind::Closure(_, a) | TyKind::FnDef(_, a) => {
                for g in self.tys.args(a) {
                    if let Some(e) = g.as_ty() {
                        self.unbound_vars(e, out);
                    }
                }
            }
            _ => {}
        }
    }

    /// True when a type argument list mentions one of `vars`.
    fn args_mention(&self, a: ArgsId, vars: &[u32]) -> bool {
        self.tys.args(a).iter().any(|g| g.as_ty().is_some_and(|t| vars.iter().any(|&v| self.occurs(v, t))))
    }

    /// Resolves every recorded type, defaults integer variables, and checks literal ranges.
    fn finish(&mut self) {
        // rustc's literal fallback runs between the last soft run and
        // the hard one: an obligation that is only ambiguous over a
        // literal's type (`{float}: Tr` with impls for f32 and f64)
        // selects with i32 or f64, the types body end defaults to.
        self.run_obligations(false);
        self.literal_fallback_in_obligations();
        self.uninferred_site_args();
        // ARCH 2.4 run point: the obligation queue runs at body end to a fixpoint.
        // Anything left there is an annotation error, never a silent default.
        self.run_obligations(true);
        method::finish_deferred_methods(self);
        for (e, op, t) in std::mem::take(&mut self.open_binops) {
            use BinOp::*;
            let t = self.deep(t);
            let k = self.kind(t);
            let int = matches!(k, TyKind::Int(_)) || k.is_int_infer();
            let float = matches!(k, TyKind::Float(_)) || k.is_float_infer();
            let ok = match op {
                Add | Sub | Mul | Div | Rem => int || float,
                BitAnd | BitOr | BitXor => int || k == TyKind::Bool,
                Shl | Shr => int,
                Eq | Ne | Lt | Le | Gt | Ge => int || float || matches!(k, TyKind::Bool | TyKind::Char),
                And | Or => true,
            };
            if !ok && k != TyKind::Error {
                let span = self.span(e);
                self.err(
                    "L0610",
                    span,
                    "type annotations needed: the operand types of this operator must be known here",
                    "Annotate the closure parameters.",
                );
            }
        }
        // A local whose element or item type was never decided (`let a = [];`,
        // `let v = Vec::new();`) is an annotation error (rustc E0282). This
        // scan runs before the zonk below defaults those variables away.
        for i in 0..self.out.locals.len() {
            let t = self.out.locals[i].ty;
            if self.has_unbound_var(t) && !self.has_error_kind(t) {
                let span = self.out.locals[i].span;
                let name = self.name(self.out.locals[i].name).to_string();
                self.err(
                    "L0111",
                    span,
                    format!("cannot infer the type of `{name}`"),
                    "Add a type annotation, such as `let v: Vec<i64> = Vec::new();`.",
                );
            }
        }
        // Deferred format tests, with types as bound by now.
        for (t, spec, span) in std::mem::take(&mut self.deferred_fmt) {
            let t = self.deep(t);
            self.check_fmt_arg(t, spec, span);
        }
        // Deferred Clone and PartialEq needs of builtin Vec and
        // slice methods, with types as bound by now.
        for (t, span) in std::mem::take(&mut self.deferred_clone) {
            let t = self.deep(t);
            let t = self.normalize_here(t);
            if !has_clone(self.p, &self.tys, t) && !matches!(self.kind(t), TyKind::Error | TyKind::Infer(_)) {
                let tn = self.tn(t);
                self.err("L0112", span, format!("`{tn}` does not implement Clone"), "Add #[derive(Clone)] to the type.");
            }
        }
        for (t, span) in std::mem::take(&mut self.deferred_eq) {
            let t = self.deep(t);
            let t = self.normalize_here(t);
            if !has_eq(self.p, &self.tys, t) && !matches!(self.kind(t), TyKind::Error | TyKind::Infer(_)) {
                let tn = self.tn(t);
                self.err("L0112", span, format!("type `{tn}` cannot be compared with `==`"), "Add #[derive(PartialEq)] to the type.");
            }
        }
        for i in 0..self.out.expr_ty.len() {
            let t = self.out.expr_ty[i];
            self.out.expr_ty[i] = self.zonk(t);
        }
        for i in 0..self.out.pat_ty.len() {
            let t = self.out.pat_ty[i];
            self.out.pat_ty[i] = self.zonk(t);
        }
        self.finish_closures();
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
        self.overflow_lint();
        // Generic call sites become instance requests for mono,
        // with their args zonked into place for lowering.
        for (ei, template, args) in std::mem::take(&mut self.generic_sites) {
            let zargs: Vec<GenericArg> = args
                .iter()
                .map(|&g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(self.zonk(t)),
                    GenericArg::Const(c) => GenericArg::Const(self.resolve_const(c)),
                    other => other,
                })
                .collect();
            if ei < self.out.generic_args.len() {
                self.out.generic_args[ei] = zargs.clone();
            }
            self.out.inst_requests.push((template, zargs));
        }
        // A generic Adt constructor names the template Adt; the
        // value's type names the instance mono made. Point the
        // resolution at the instance so lowering lays it out.
        for i in 0..self.out.expr_res.len() {
            if let Res::Variant(a, v) = self.out.expr_res[i]
                && let Some(inst) = self.tys.local_adt(self.out.expr_ty[i])
                && inst != a
            {
                self.out.expr_res[i] = Res::Variant(inst, v);
            }
        }
        for i in 0..self.out.pat_res.len() {
            if let PatRes::Variant(a, v) = self.out.pat_res[i]
                && let Some(inst) = self.tys.local_adt(self.out.pat_ty[i])
                && inst != a
            {
                self.out.pat_res[i] = PatRes::Variant(inst, v);
            }
        }
        // Literal range checks (the deny-level overflowing_literals
        // lint, for ints and floats alike).
        let base = self.out.expr_base;
        for i in 0..self.out.expr_ty.len() {
            let e = ExprId(base + i as u32);
            if let Expr::Float(s) = self.p.ast.expr(e)
                && let TyKind::Float(f) = self.tys.kind(self.out.expr_ty[i])
            {
                let text = self.p.ast.strings[*s as usize].as_str();
                if crate::check::collect::float_literal_overflows(text, f) {
                    let sp = self.span(e);
                    self.err(
                        "L0118",
                        sp,
                        format!("literal out of range for `{}`", f.name()),
                        format!("Use a value that fits in `{}`, or a wider type.", f.name()),
                    );
                }
            }
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
        // A const read inside body const evaluation consumes the value:
        // record the const's `Sig` read (its fingerprint folds the
        // value), as `path_expr` does for a plain expression use.
        let p = self.cx.p;
        let &i = p.const_names.get(&name)?;
        let out = {
            let c = &p.consts[i as usize];
            (c.value.clone(), c.ty)
        };
        if let Some(&def) = p.const_defs.get(i as usize) {
            let _ = p.sig_of(&mut self.cx.out.reads, def);
        }
        Some(out)
    }
    fn static_item(&mut self, name: Sym) -> Option<(u32, Ty)> {
        let p = self.cx.p;
        let &i = p.static_names.get(&name)?;
        let ty = p.statics[i as usize].ty;
        if let Some(&def) = p.static_defs.get(i as usize) {
            let _ = p.sig_of(&mut self.cx.out.reads, def);
        }
        Some((i, ty))
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
        // The Result shim sits one below the Option shim (u32::MAX):
        // Ok is variant 0, Err is variant 1.
        if segs.len() == 1 && last == p.known.Ok {
            return CallTarget::VariantCtor { adt: AdtId(u32::MAX - 1), variant: 0, ty: ERROR };
        }
        if segs.len() == 1 && last == p.known.Err {
            return CallTarget::VariantCtor { adt: AdtId(u32::MAX - 1), variant: 1, ty: ERROR };
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
            // The evaluator is about to run this const fn's body and bake
            // the result into the body being checked: that body depends
            // on the const fn's body, not only its signature. A `Checked`
            // read records the edge; its replay never matches, so the
            // reader rechecks whenever it is a walk candidate. Nested
            // const calls inside the evaluated body come back here and
            // record their own edges, so the dependency is transitive.
            self.cx.out.reads.record_checked(p.def_id(f), Fingerprint(0));
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
        if adt.0 >= u32::MAX - 1 {
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
        // A layout answer inside body const evaluation (`size_of` in a
        // const block or array length) is baked into the body: record
        // the layout reads, as `layout_query` does.
        p.record_layout_reads(&mut self.cx.out.reads, &self.cx.tys, t);
        crate::ty::layout::layout_of_ty(&self.cx.tys, p, t).ok()
    }
    fn adt_repr(&self, adt: AdtId) -> crate::ty::layout::Repr {
        self.cx.p.adt(adt).repr
    }
    fn discriminant(&self, adt: AdtId, variant: u32) -> i128 {
        self.cx.p.adt(adt).variants[variant as usize].disc
    }
    fn is_enum(&self, adt: AdtId) -> bool {
        adt.0 < u32::MAX - 1 && self.cx.p.adt(adt).is_enum
    }
}

/// The (Adt, variant) a path denotes in the compat tables.
fn variant_of(p: &Program<'_>, segs: &[ast::PathSeg]) -> Option<(AdtId, u32)> {
    // `std::cmp::Ordering::Less`: the same four-segment path
    // `resolve_assoc` answers, for const contexts.
    if segs.len() == 4
        && matches!(p.interner.get(segs[0].name), "std" | "core")
        && p.interner.get(segs[1].name) == "cmp"
        && p.interner.get(segs[2].name) == "Ordering"
        && let Some(a) = p.tys.local_adt_of(generics::ordering_def())
    {
        let v = p.adt(a).variants.iter().position(|v| v.name == segs[3].name)?;
        return Some((a, v as u32));
    }
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
/// The solver over one body's inference state (see
/// `traits::solve::SolveCx`): probes bind body variables and roll
/// back through the trail `bind_var` records.
impl<'p> SolveCx for Ctx<'p, '_> {
    type Snapshot = usize;
    type Store = Tys<'p>;

    fn tys(&mut self) -> &mut Tys<'p> {
        &mut self.tys
    }
    fn deep_resolve(&mut self, t: Ty) -> Ty {
        self.deep(t)
    }
    fn unify(&mut self, a: Ty, b: Ty) -> bool {
        self.unify(a, b)
    }
    fn fresh_var(&mut self) -> Ty {
        self.new_var(false)
    }
    fn snapshot(&mut self) -> usize {
        self.trail.len()
    }
    fn rollback(&mut self, snap: usize) {
        while self.trail.len() > snap {
            let var = self.trail.pop().unwrap();
            self.vars[var as usize].bound = None;
        }
    }
    fn closure_select(&mut self, obl: TraitRef) -> Option<bool> {
        self.closure_select_impl(obl)
    }
    fn closure_output(&mut self, assoc: DefId, self_ty: Ty) -> Option<Ty> {
        self.closure_output_impl(assoc, self_ty)
    }
    fn record_impl_set(&mut self, trait_def: DefId, self_ty: Ty, _failed: bool) {
        let p = self.p;
        let resolved = self.resolve(self_ty);
        let head = Head::of(&self.tys, resolved);
        p.impl_set(&mut self.out.reads, trait_def, head);
    }
}
