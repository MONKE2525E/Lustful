// The bounded const evaluator (docs/ARCH.md section 2.13, non-generic form).
//
// One evaluator serves `const` and `static` initializers, array repeat
// counts and lengths, enum discriminants (through the scalar entry point in
// collect), inline `const { ... }` blocks, and `const _: () = assert!(...)`
// items. Anything outside the supported forms is an error with the const
// code for "outside the bound"; a call to a function that is not a
// `const fn` gets the non-const-call code instead. No synthetic runtime
// init functions are ever made for statics: a value either evaluates here
// or the program is rejected.
//
// The evaluator is generic over a `ConstCx` that answers name and type
// questions (const items, const fns, struct and variant shapes, layouts),
// so collect and body checking share it. Step cap: 1,000,000 steps per
// const item, then the same outside-the-bound error.
#![allow(dead_code)] // OffsetOf and aggregate statics land with their callers.

use super::FloatTy;
use super::layout::Layout;
use super::{AdtId, BOOL, CHAR, ERROR, IntTy, REF_STR, Ty, TyIntern, TyKind, UNIT, USIZE};
use crate::ast::{self, Ast, BinOp, Expr, ExprId, MacroKind, Pat, PatId, UnOp};
use crate::diag::{Diag, Span};
use crate::intern::Sym;

/// The code for const input outside the bounded evaluator.
pub const C_OUTSIDE: &str = "L0630";
/// The code for a non-const call in a const context.
pub const C_NONCONST: &str = "L0631";

const STEP_CAP: u64 = 1_000_000;

/// One evaluated const value. Aggregates hold their fields in declaration
/// order; a variant payload carries its variant index.
#[derive(Clone, Debug, PartialEq)]
pub enum ConstValue {
    Int(i128),
    /// Float bits (`f32` bits zero-extended into the u64).
    Float(u64, FloatTy),
    Bool(bool),
    Char(char),
    /// A string literal: an index into the AST string table. Its type is `&str`.
    Str(u32),
    Unit,
    Aggregate(Vec<ConstValue>),
    Variant(u32, Vec<ConstValue>),
    /// A repeated element, from `[value; n]` with a const value.
    Repeat(Box<ConstValue>, u64),
    /// A promoted reference to a const value (`&EXPR` in const position).
    Ref(Box<ConstValue>),
    /// A reference to a static item, by index into the program's statics.
    StaticRef(u32),
}

/// A value with its type, as the evaluator produces it.
pub type TypedValue = (ConstValue, Ty);

/// What a call in const position resolves to.
pub enum CallTarget {
    /// A `const fn` or tuple variant constructor the evaluator may run.
    ConstFn(ConstFnBody),
    VariantCtor {
        adt: AdtId,
        variant: u32,
        ty: Ty,
    },
    SizeOf(Ty),
    AlignOf(Ty),
    /// A callable that exists but is not const: the non-const-call error.
    NonConst,
    /// Not a callable the context knows: outside the bound.
    Unknown,
}

/// The parts of a const fn the evaluator runs.
pub struct ConstFnBody {
    /// Parameters as (name, mutable, pattern): a plain `name: Ty` parameter
    /// has no pattern and binds by name.
    pub params: Vec<(Sym, bool, Option<PatId>)>,
    pub param_tys: Vec<Ty>,
    pub ret: Ty,
    pub body: ast::BlockId,
}

/// The questions the evaluator asks its caller.
pub trait ConstCx<'a> {
    type Tys: TyIntern;
    fn tys(&mut self) -> &mut Self::Tys;
    fn tys_ref(&self) -> &Self::Tys;
    fn ast(&self) -> &'a Ast;
    /// A const item or immutable static by name, evaluating it if needed.
    fn const_item(&mut self, name: Sym) -> Option<TypedValue>;
    /// A call target for a callee expression already known to be a path.
    fn call_target(&mut self, callee: ExprId) -> CallTarget;
    /// A path used as a value: a unit variant, if it names one.
    fn unit_variant(&mut self, segs: &[ast::PathSeg], expected: Option<Ty>) -> Option<(AdtId, u32, Ty)>;
    /// A static item by name: its index and type.
    fn static_item(&mut self, name: Sym) -> Option<(u32, Ty)>;
    /// The struct or variant a struct literal names.
    fn struct_target(&mut self, path: &[ast::PathSeg]) -> Option<(AdtId, u32, Ty)>;
    /// Field names and types of one variant, in declaration order. Tuple
    /// fields answer with a dummy name; position is what matters there.
    fn variant_fields(&self, adt: AdtId, variant: u32) -> Vec<(Sym, Ty)>;
    /// The pattern target (Adt, variant) a path pattern names.
    fn pattern_variant(&mut self, segs: &[ast::PathSeg]) -> Option<(AdtId, u32)>;
    /// Resolves a written type (casts, `size_of` arguments).
    fn resolve_ty(&mut self, t: ast::TyId) -> Ty;
    /// The layout of a type, for `size_of` and `align_of`.
    fn layout(&mut self, t: Ty) -> Option<Layout>;
    /// The text of an interned name.
    fn sym_text(&self, s: Sym) -> &str;
    /// The `repr` of an Adt, for `offset_of!` rules.
    fn adt_repr(&self, adt: AdtId) -> super::layout::Repr;
    /// The discriminant of one variant of an enum type.
    fn discriminant(&self, adt: AdtId, variant: u32) -> i128;
}

/// Why evaluation left a block early.
enum Flow {
    Val(TypedValue),
    Break(Option<TypedValue>, Option<Sym>),
    Continue(Option<Sym>),
    Return(TypedValue),
}

type Env = Vec<(Sym, TypedValue, bool)>;

fn outside(span: Span, what: &str) -> Diag {
    Diag::new(
        C_OUTSIDE,
        span,
        format!("{what} is outside the bounded const evaluator"),
        "Use literals, const items, and const fn calls only.",
    )
}

fn nonconst(span: Span, what: &str) -> Diag {
    Diag::new(
        C_NONCONST,
        span,
        format!("cannot call non-const function `{what}` in a const context"),
        "Mark the function `const fn`, or move the call out of the const item.",
    )
}

/// Wraps `v` to the range of an integer type, as an `as` cast does.
pub fn truncate_to_int(v: i128, it: IntTy) -> i128 {
    let bits = it.bits();
    if bits >= 128 {
        return v;
    }
    let mask: i128 = (1i128 << bits) - 1;
    let u = v & mask;
    if it.signed() && (u >> (bits - 1)) & 1 == 1 { u - (1i128 << bits) } else { u }
}

/// True when a value produced as `vt` may stand where `ty` is required in a
/// const item: the types are equal, or they differ only by unsized coercions
/// rustc applies at a reference (`&[T; N]` to `&[T]`), possibly nested inside
/// tuples, arrays, or generic arguments. An `ERROR` on either side passes:
/// that error was already reported where the type was formed.
pub fn const_ty_compatible<T: TyIntern>(tys: &T, vt: Ty, ty: Ty) -> bool {
    if vt == ty || vt == ERROR || ty == ERROR {
        return true;
    }
    match (tys.kind(vt), tys.kind(ty)) {
        (TyKind::Ref(_, m1, a), TyKind::Ref(_, m2, b)) => {
            (!m2.is_mut() || m1.is_mut())
                && (const_ty_compatible(tys, a, b)
                    || matches!((tys.kind(a), tys.kind(b)), (TyKind::Array(e1, _), TyKind::Slice(e2)) if const_ty_compatible(tys, e1, e2)))
        }
        (TyKind::Tuple(a), TyKind::Tuple(b)) => {
            let (a, b) = (tys.tys_of(a), tys.tys_of(b));
            a.len() == b.len() && a.iter().zip(b).all(|(&x, &y)| const_ty_compatible(tys, x, y))
        }
        (TyKind::Array(e1, n1), TyKind::Array(e2, n2)) => n1 == n2 && const_ty_compatible(tys, e1, e2),
        (TyKind::Adt(d1, a1), TyKind::Adt(d2, a2)) if d1 == d2 => {
            let (a, b) = (tys.args(a1), tys.args(a2));
            a.len() == b.len()
                && a.iter().zip(b).all(|(x, y)| match (x, y) {
                    (super::GenericArg::Ty(x), super::GenericArg::Ty(y)) => const_ty_compatible(tys, *x, *y),
                    _ => x == y,
                })
        }
        _ => false,
    }
}

/// The L0110 a const item gets when its value type is not its declared type.
pub fn const_ty_mismatch(span: Span, what: &str) -> Diag {
    Diag::new("L0110", span, format!("mismatched types in {what}"), "Change the value or the declared type.")
}

/// True when `v` fits in the integer type (const overflow is an error).
fn fits(v: i128, it: IntTy) -> bool {
    let bits = it.bits();
    if bits >= 128 {
        return true;
    }
    if it.signed() { v >= -(1i128 << (bits - 1)) && v < (1i128 << (bits - 1)) } else { v >= 0 && v < (1i128 << bits) }
}

/// Evaluates one const expression. `expected` is the type the context wants,
/// used for literal widths and array element types.
pub fn eval<'a, C: ConstCx<'a>>(cx: &mut C, e: ExprId, expected: Option<Ty>) -> Result<TypedValue, Diag> {
    let mut ev = Evaluator { steps: 0 };
    let mut env: Env = Vec::new();
    match ev.expr(cx, &mut env, e, expected)? {
        Flow::Val(v) => Ok(v),
        _ => Err(outside(cx.ast().expr_span(e), "control flow out of a const expression")),
    }
}

struct Evaluator {
    steps: u64,
}

impl Evaluator {
    fn step(&mut self, span: Span) -> Result<(), Diag> {
        self.steps += 1;
        if self.steps > STEP_CAP {
            return Err(outside(span, "this const item (step limit reached)"));
        }
        Ok(())
    }

    fn int_ty_of<'a, C: ConstCx<'a>>(&self, cx: &C, t: Ty) -> Option<IntTy> {
        match cx.tys_ref().kind(t) {
            TyKind::Int(i) => Some(i),
            _ => None,
        }
    }

    fn expr<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId, expected: Option<Ty>) -> Result<Flow, Diag> {
        let span = cx.ast().expr_span(e);
        self.step(span)?;
        let v = match cx.ast().expr(e) {
            Expr::Int(v, suffix) => {
                let t = match suffix {
                    Some(s) => super::int(IntTy::from_suffix(*s)),
                    None => expected.filter(|&t| self.int_ty_of(cx, t).is_some()).unwrap_or(super::I32),
                };
                let val = *v as u128 as i128;
                if let Some(it) = self.int_ty_of(cx, t)
                    && !fits(val, it)
                {
                    return Err(Diag::new(C_OUTSIDE, span, "integer literal out of range in const", "Change the literal or the type."));
                }
                (ConstValue::Int(val), t)
            }
            Expr::Float(i) => {
                let text = cx.ast().strings[*i as usize].as_str();
                match crate::check::collect::parse_float_literal(text) {
                    Some((bits, suffix)) => {
                        let f = suffix.unwrap_or(match expected.map(|t| cx.tys_ref().kind(t)) {
                            Some(TyKind::Float(f)) => f,
                            _ => FloatTy::F64,
                        });
                        let bits =
                            if f == FloatTy::F32 && suffix.is_none() { (f64::from_bits(bits) as f32).to_bits() as u64 } else { bits };
                        let t = cx.tys().float_ty(f);
                        (ConstValue::Float(bits, f), t)
                    }
                    None => return Err(outside(span, "this float literal")),
                }
            }
            Expr::Bool(b) => (ConstValue::Bool(*b), BOOL),
            Expr::Char(c) => (ConstValue::Char(*c), CHAR),
            Expr::Str(i) => (ConstValue::Str(*i), REF_STR),
            Expr::Unit => (ConstValue::Unit, UNIT),
            Expr::Path(segs) => return Ok(Flow::Val(self.path_value(cx, env, segs, span, expected)?)),
            Expr::Block(b) => return self.block(cx, env, *b, expected),
            Expr::ConstBlock(b) => return self.block(cx, env, *b, expected),
            Expr::Tuple(elems) => {
                let exp: Vec<Option<Ty>> = match expected.map(|t| cx.tys_ref().kind(t)) {
                    Some(TyKind::Tuple(ts)) => cx.tys_ref().tys_of(ts).iter().map(|&t| Some(t)).collect(),
                    _ => vec![None; elems.len()],
                };
                let mut vals = Vec::new();
                let mut tys = Vec::new();
                for (i, &el) in elems.iter().enumerate() {
                    let (v, t) = self.value(cx, env, el, exp.get(i).copied().flatten())?;
                    vals.push(v);
                    tys.push(t);
                }
                let ts = cx.tys().intern_tys(&tys);
                (ConstValue::Aggregate(vals), cx.tys().intern(TyKind::Tuple(ts)))
            }
            Expr::Array(elems) => {
                let exp_elem = expected.and_then(|t| match cx.tys_ref().kind(t) {
                    TyKind::Array(el, _) => Some(el),
                    _ => None,
                });
                let mut vals = Vec::new();
                let mut elem_ty = exp_elem;
                for &el in elems {
                    let (v, t) = self.value(cx, env, el, elem_ty)?;
                    elem_ty = Some(t);
                    vals.push(v);
                }
                let elem = elem_ty.unwrap_or(ERROR);
                let c = cx.tys().intern_const(super::ConstKind::Int(elems.len() as u128));
                (ConstValue::Aggregate(vals), cx.tys().intern(TyKind::Array(elem, c)))
            }
            Expr::ArrayRepeat { value, len } => {
                let (nv, _) = self.value(cx, env, *len, Some(USIZE))?;
                let ConstValue::Int(n) = nv else { return Err(outside(span, "this array length")) };
                let n = u64::try_from(n).map_err(|_| outside(span, "this array length"))?;
                let exp_elem = expected.and_then(|t| match cx.tys_ref().kind(t) {
                    TyKind::Array(el, _) => Some(el),
                    _ => None,
                });
                if n == 0 {
                    let elem = exp_elem.unwrap_or(ERROR);
                    let c = cx.tys().intern_const(super::ConstKind::Int(0));
                    (ConstValue::Aggregate(Vec::new()), cx.tys().intern(TyKind::Array(elem, c)))
                } else {
                    let (v, t) = self.value(cx, env, *value, exp_elem)?;
                    let c = cx.tys().intern_const(super::ConstKind::Int(n as u128));
                    (ConstValue::Repeat(Box::new(v), n), cx.tys().intern(TyKind::Array(t, c)))
                }
            }
            Expr::Unary { op, expr } => {
                let (v, t) = self.value(cx, env, *expr, expected)?;
                match (op, v) {
                    (UnOp::Neg, ConstValue::Float(bits, f)) => {
                        let nb = match f {
                            FloatTy::F64 => (-f64::from_bits(bits)).to_bits(),
                            FloatTy::F32 => (-f32::from_bits(bits as u32)).to_bits() as u64,
                        };
                        (ConstValue::Float(nb, f), t)
                    }
                    (UnOp::Neg, ConstValue::Int(i)) => {
                        let r = i.checked_neg().ok_or_else(|| outside(span, "this negation (overflow)"))?;
                        if let Some(it) = self.int_ty_of(cx, t)
                            && !fits(r, it)
                        {
                            return Err(outside(span, "this negation (overflow)"));
                        }
                        (ConstValue::Int(r), t)
                    }
                    (UnOp::Not, ConstValue::Int(i)) => {
                        let r = match self.int_ty_of(cx, t) {
                            Some(it) => truncate_to_int(!i, it),
                            None => !i,
                        };
                        (ConstValue::Int(r), t)
                    }
                    (UnOp::Not, ConstValue::Bool(b)) => (ConstValue::Bool(!b), BOOL),
                    _ => return Err(outside(span, "this unary operation")),
                }
            }
            Expr::Binary { op, lhs, rhs } => return Ok(Flow::Val(self.binary(cx, env, *op, *lhs, *rhs, expected, span)?)),
            Expr::Cast { expr, ty } => {
                let target = cx.resolve_ty(*ty);
                let v = self.value(cx, env, *expr, None)?;
                return Ok(Flow::Val(self.cast(cx, v, target, span)?));
            }
            Expr::Ref { expr, mutable, .. } => {
                // `&STATIC` and `&CONST` keep their identity where the caller
                // can use it; anything else is a promoted temporary.
                if let Expr::Path(segs) = cx.ast().expr(*expr)
                    && segs.len() == 1
                    && let Some((idx, sty)) = cx.static_item(segs[0].name)
                {
                    // `&ARR` where a slice reference is wanted is the unsize
                    // coercion; the value keeps the static's identity and the
                    // wanted type.
                    if let Some(et) = expected
                        && matches!(cx.tys_ref().kind(et), TyKind::Ref(..))
                        && {
                            let rt = cx.tys().mk_ref(*mutable, sty);
                            const_ty_compatible(cx.tys_ref(), rt, et)
                        }
                    {
                        return Ok(Flow::Val((ConstValue::StaticRef(idx), et)));
                    }
                    let rt = cx.tys().mk_ref(*mutable, sty);
                    return Ok(Flow::Val((ConstValue::StaticRef(idx), rt)));
                }
                // A wanted reference type wants its pointee type inside, so an
                // unsuffixed literal takes that width (except the slice form
                // below, which has no single pointee value).
                let inner_expected = expected.and_then(|et| match cx.tys_ref().kind(et) {
                    TyKind::Ref(_, _, inner) if !matches!(cx.tys_ref().kind(inner), TyKind::Slice(_)) => Some(inner),
                    _ => None,
                });
                let (v, t) = self.value(cx, env, *expr, inner_expected)?;
                if let ConstValue::Str(_) = v {
                    (v, t)
                } else if let Some(et) = expected
                    && matches!(cx.tys_ref().kind(et), TyKind::Ref(_, _, s) if matches!(cx.tys_ref().kind(s), TyKind::Slice(_)))
                    && matches!(v, ConstValue::Aggregate(_) | ConstValue::Repeat(..))
                {
                    // `&[1, 2]` at a slice type: the aggregate is the slice
                    // backing; materialization builds the fat value.
                    (v, et)
                } else {
                    let rt = cx.tys().mk_ref(*mutable, t);
                    (ConstValue::Ref(Box::new(v)), rt)
                }
            }
            Expr::Deref(inner) => {
                let (v, t) = self.value(cx, env, *inner, None)?;
                match v {
                    ConstValue::Ref(inner_v) => {
                        let inner_ty = match cx.tys_ref().kind(t) {
                            TyKind::Ref(_, _, it) => it,
                            _ => ERROR,
                        };
                        (*inner_v, inner_ty)
                    }
                    ConstValue::Str(i) => (ConstValue::Str(i), t),
                    _ => return Err(outside(span, "this dereference")),
                }
            }
            Expr::Field { base, name } => {
                let (v, t) = self.value(cx, env, *base, None)?;
                let (v, t) = self.deref_value(cx, v, t);
                let Some(adt) = cx.tys_ref().local_adt(t) else { return Err(outside(span, "this field access")) };
                let fields = cx.variant_fields(adt, 0);
                let Some(i) = fields.iter().position(|(n, _)| n == name) else {
                    return Err(outside(span, "this field access"));
                };
                match v {
                    ConstValue::Aggregate(vals) => (vals.into_iter().nth(i).unwrap(), fields[i].1),
                    _ => return Err(outside(span, "this field access")),
                }
            }
            Expr::TupleField { base, index } => {
                let (v, t) = self.value(cx, env, *base, None)?;
                let (v, t) = self.deref_value(cx, v, t);
                let elem_ty = match cx.tys_ref().kind(t) {
                    TyKind::Tuple(ts) => cx.tys_ref().tys_of(ts).get(*index as usize).copied(),
                    _ => cx.tys_ref().local_adt(t).and_then(|a| cx.variant_fields(a, 0).get(*index as usize).map(|f| f.1)),
                };
                match (v, elem_ty) {
                    (ConstValue::Aggregate(vals), Some(et)) => {
                        (vals.into_iter().nth(*index as usize).ok_or_else(|| outside(span, "this field access"))?, et)
                    }
                    _ => return Err(outside(span, "this field access")),
                }
            }
            Expr::Index { base, index } => {
                let (v, t) = self.value(cx, env, *base, None)?;
                let (v, t) = self.deref_value(cx, v, t);
                let (iv, _) = self.value(cx, env, *index, Some(USIZE))?;
                let ConstValue::Int(i) = iv else { return Err(outside(span, "this index")) };
                let i = usize::try_from(i).map_err(|_| outside(span, "this index"))?;
                let elem = match cx.tys_ref().kind(t) {
                    TyKind::Array(el, _) => el,
                    _ => return Err(outside(span, "this index")),
                };
                let got = match v {
                    ConstValue::Aggregate(vals) => vals.into_iter().nth(i),
                    ConstValue::Repeat(v, n) if (i as u64) < n => Some(*v),
                    _ => None,
                };
                match got {
                    Some(g) => (g, elem),
                    None => return Err(outside(span, "this index (out of bounds)")),
                }
            }
            Expr::StructLit { path, fields, update } => {
                let Some((adt, variant, ty)) = cx.struct_target(path) else {
                    return Err(outside(span, "this struct literal"));
                };
                let field_defs = cx.variant_fields(adt, variant);
                let mut vals: Vec<Option<ConstValue>> = vec![None; field_defs.len()];
                for &(fname, _, fe) in fields {
                    let Some(i) = field_defs.iter().position(|(n, _)| *n == fname) else {
                        return Err(outside(span, "this struct literal"));
                    };
                    let (v, vt) = self.value(cx, env, fe, Some(field_defs[i].1))?;
                    if !const_ty_compatible(cx.tys_ref(), vt, field_defs[i].1) {
                        return Err(const_ty_mismatch(cx.ast().expr_span(fe), "this struct literal field"));
                    }
                    vals[i] = Some(v);
                }
                if let Some(u) = update {
                    let (bv, _) = self.value(cx, env, *u, Some(ty))?;
                    if let ConstValue::Aggregate(bvals) = bv {
                        for (i, b) in bvals.into_iter().enumerate() {
                            if vals[i].is_none() {
                                vals[i] = Some(b);
                            }
                        }
                    }
                }
                let vals: Option<Vec<ConstValue>> = vals.into_iter().collect();
                match vals {
                    Some(vals) if cx.tys_ref().local_adt(ty).is_some() => (ConstValue::Aggregate(vals), ty),
                    _ => return Err(outside(span, "this struct literal")),
                }
            }
            Expr::OffsetOf { ty, fields } => {
                let mut cur = cx.resolve_ty(*ty);
                let mut off: u64 = 0;
                for &fname in fields {
                    let Some(adt) = cx.tys_ref().local_adt(cur) else {
                        return Err(outside(span, "this `offset_of!`"));
                    };
                    if !matches!(
                        cx.adt_repr(adt).kind,
                        super::layout::ReprKind::C | super::layout::ReprKind::Packed | super::layout::ReprKind::Transparent
                    ) {
                        return Err(Diag::new(
                            "L0650",
                            span,
                            "`offset_of!` on a default-repr type is not supported",
                            "Add `#[repr(C)]` to the type, or measure with `size_of`.",
                        ));
                    }
                    let defs = cx.variant_fields(adt, 0);
                    let Some(i) = defs.iter().position(|(n, _)| *n == fname) else {
                        return Err(outside(span, "this `offset_of!` field"));
                    };
                    let Some(l) = cx.layout(cur) else {
                        return Err(Diag::new(
                            "L0652",
                            span,
                            "unsupported layout form in `offset_of!`",
                            "Use a type inside the supported layout grammar.",
                        ));
                    };
                    off += l.field_offsets.get(i).copied().unwrap_or(0);
                    cur = defs[i].1;
                }
                (ConstValue::Int(off as i128), USIZE)
            }
            Expr::Call { callee, args } => return Ok(Flow::Val(self.call(cx, env, *callee, args, span)?)),
            Expr::MethodCall { .. } => return Err(outside(span, "method calls")),
            Expr::If { cond, then, els } => {
                let (cv, _) = self.value(cx, env, *cond, Some(BOOL))?;
                let ConstValue::Bool(b) = cv else { return Err(outside(span, "this condition")) };
                if b {
                    return self.block(cx, env, *then, expected);
                }
                match els {
                    Some(els) => return self.expr(cx, env, *els, expected),
                    None => (ConstValue::Unit, UNIT),
                }
            }
            Expr::Match { scrut, arms } => return self.match_expr(cx, env, *scrut, arms, expected, span),
            Expr::While { label, cond, body } => {
                loop {
                    self.step(span)?;
                    let (cv, _) = self.value(cx, env, *cond, Some(BOOL))?;
                    let ConstValue::Bool(b) = cv else { return Err(outside(span, "this condition")) };
                    if !b {
                        break;
                    }
                    match self.block(cx, env, *body, Some(UNIT))? {
                        Flow::Val(_) => {}
                        Flow::Continue(l) if l.is_none() || l == label.map(|x| x.name) => {}
                        Flow::Break(_, l) if l.is_none() || l == label.map(|x| x.name) => break,
                        other => return Ok(other),
                    }
                }
                (ConstValue::Unit, UNIT)
            }
            Expr::Loop { label, body } => loop {
                self.step(span)?;
                match self.block(cx, env, *body, Some(UNIT))? {
                    Flow::Val(_) => {}
                    Flow::Continue(l) if l.is_none() || l == label.map(|x| x.name) => {}
                    Flow::Break(v, l) if l.is_none() || l == label.map(|x| x.name) => {
                        break v.unwrap_or((ConstValue::Unit, UNIT));
                    }
                    other => return Ok(other),
                }
            },
            Expr::Break { label, value } => {
                let v = match value {
                    Some(v) => Some(self.value(cx, env, *v, None)?),
                    None => None,
                };
                return Ok(Flow::Break(v, label.map(|l| l.name)));
            }
            Expr::Continue(label) => return Ok(Flow::Continue(label.map(|l| l.name))),
            Expr::Return(v) => {
                let v = match v {
                    Some(v) => self.value(cx, env, *v, None)?,
                    None => (ConstValue::Unit, UNIT),
                };
                return Ok(Flow::Return(v));
            }
            Expr::Assign { lhs, rhs } => {
                let (v, _) = self.value(cx, env, *rhs, None)?;
                self.assign_place(cx, env, *lhs, v, span)?;
                (ConstValue::Unit, UNIT)
            }
            Expr::AssignOp { op, lhs, rhs } => {
                let cur = self.value(cx, env, *lhs, None)?;
                let (rv, _) = self.value(cx, env, *rhs, Some(cur.1))?;
                let ct = cur.1;
                let out = self.int_op(cx, *op, cur, (rv, ct), span)?;
                self.assign_place(cx, env, *lhs, out.0, span)?;
                (ConstValue::Unit, UNIT)
            }
            Expr::Macro { kind, args, fmt, .. } => return Ok(Flow::Val(self.macro_(cx, env, *kind, args, fmt, span)?)),
            Expr::LabeledBlock { label, body } => match self.block(cx, env, *body, expected)? {
                Flow::Break(v, l) if l == Some(label.name) => v.unwrap_or((ConstValue::Unit, UNIT)),
                Flow::Val(v) => v,
                other => return Ok(other),
            },
            _ => return Err(outside(span, "this expression")),
        };
        Ok(Flow::Val(v))
    }

    /// Evaluates to a plain value (any control-flow escape is an error here).
    fn value<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId, expected: Option<Ty>) -> Result<TypedValue, Diag> {
        match self.expr(cx, env, e, expected)? {
            Flow::Val(v) => Ok(v),
            _ => Err(outside(cx.ast().expr_span(e), "control flow out of a const expression")),
        }
    }

    /// Peels one promoted reference layer for field and index access.
    fn deref_value<'a, C: ConstCx<'a>>(&self, cx: &C, v: ConstValue, t: Ty) -> (ConstValue, Ty) {
        match (v, cx.tys_ref().kind(t)) {
            (ConstValue::Ref(inner), TyKind::Ref(_, _, it)) => (*inner, it),
            (v, _) => (v, t),
        }
    }

    fn block<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, b: ast::BlockId, expected: Option<Ty>) -> Result<Flow, Diag> {
        let block = cx.ast().block(b);
        let saved = env.len();
        let mut out = (ConstValue::Unit, UNIT);
        for stmt in &block.stmts {
            match stmt {
                ast::Stmt::Let { pat, init, .. } => {
                    let Some(init) = init else { return Err(outside(cx.ast().pat_span(*pat), "an uninitialized binding")) };
                    let v = self.value(cx, env, *init, None)?;
                    let mut binds = Vec::new();
                    if !self.match_pat(cx, env, *pat, &v.0.clone(), v.1, true, &mut binds)? {
                        return Err(outside(cx.ast().pat_span(*pat), "a refutable pattern"));
                    }
                    env.extend(binds);
                }
                ast::Stmt::Expr { expr, .. } => match self.expr(cx, env, *expr, None)? {
                    Flow::Val(_) => {}
                    other => {
                        env.truncate(saved);
                        return Ok(other);
                    }
                },
                ast::Stmt::Item(_) | ast::Stmt::Macro { .. } => {
                    return Err(outside(cx.ast().block(b).span, "items in a const block"));
                }
            }
        }
        if let Some(tail) = block.tail {
            match self.expr(cx, env, tail, expected)? {
                Flow::Val(v) => out = v,
                other => {
                    env.truncate(saved);
                    return Ok(other);
                }
            }
        }
        env.truncate(saved);
        Ok(Flow::Val(out))
    }

    fn path_value<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        segs: &[ast::PathSeg],
        span: Span,
        expected: Option<Ty>,
    ) -> Result<TypedValue, Diag> {
        if segs.len() == 1 {
            let name = segs[0].name;
            if let Some((_, v, _)) = env.iter().rev().find(|(n, _, _)| *n == name) {
                return Ok(v.clone());
            }
            if let Some(v) = cx.const_item(name) {
                return Ok(v);
            }
            if let Some((idx, ty)) = cx.static_item(name) {
                // Reading an immutable static in const gives its value; the
                // context only returns statics it may read this way.
                if let Some(v) = cx.const_item(name) {
                    return Ok(v);
                }
                let _ = idx;
                let _ = ty;
                return Err(outside(span, "a reference to a static"));
            }
        }
        if let Some((adt, variant, ty)) = cx.unit_variant(segs, expected) {
            let _ = adt;
            return Ok((ConstValue::Variant(variant, Vec::new()), ty));
        }
        // Associated consts of integer types: `i64::MAX`, `usize::MAX`, `u8::MIN`, ...
        if segs.len() == 2 {
            if let Some(v) = self.int_assoc_const(cx, segs) {
                return Ok(v);
            }
        }
        Err(outside(span, "this path"))
    }

    /// `i32::MAX` and friends, resolved by written names.
    fn int_assoc_const<'a, C: ConstCx<'a>>(&self, cx: &C, segs: &[ast::PathSeg]) -> Option<TypedValue> {
        let ty_name = cx.sym_text(segs[0].name);
        let it = IntTy::ALL.iter().find(|i| i.name() == ty_name).copied()?;
        let item = cx.sym_text(segs[1].name);
        let bits = it.bits();
        let v = match item {
            "MAX" => {
                if bits >= 128 {
                    if it.signed() { i128::MAX } else { -1 }
                } else if it.signed() {
                    (1i128 << (bits - 1)) - 1
                } else {
                    (1i128 << bits) - 1
                }
            }
            "MIN" => {
                if it.signed() {
                    if bits >= 128 { i128::MIN } else { -(1i128 << (bits - 1)) }
                } else {
                    0
                }
            }
            _ => return None,
        };
        Some((ConstValue::Int(v), super::int(it)))
    }

    fn binary<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
        expected: Option<Ty>,
        span: Span,
    ) -> Result<TypedValue, Diag> {
        match op {
            BinOp::And => {
                let (v, _) = self.value(cx, env, lhs, Some(BOOL))?;
                let ConstValue::Bool(b) = v else { return Err(outside(span, "this condition")) };
                if !b {
                    return Ok((ConstValue::Bool(false), BOOL));
                }
                let (v, _) = self.value(cx, env, rhs, Some(BOOL))?;
                let ConstValue::Bool(b) = v else { return Err(outside(span, "this condition")) };
                return Ok((ConstValue::Bool(b), BOOL));
            }
            BinOp::Or => {
                let (v, _) = self.value(cx, env, lhs, Some(BOOL))?;
                let ConstValue::Bool(b) = v else { return Err(outside(span, "this condition")) };
                if b {
                    return Ok((ConstValue::Bool(true), BOOL));
                }
                let (v, _) = self.value(cx, env, rhs, Some(BOOL))?;
                let ConstValue::Bool(b) = v else { return Err(outside(span, "this condition")) };
                return Ok((ConstValue::Bool(b), BOOL));
            }
            _ => {}
        }
        let (lv, lt) = self.value(cx, env, lhs, expected)?;
        let (rv, _) = self.value(cx, env, rhs, Some(lt))?;
        if op.is_cmp() {
            let eq = values_eq(&lv, &rv);
            let ord = match (&lv, &rv) {
                (ConstValue::Float(a, FloatTy::F64), ConstValue::Float(b, _)) => f64::from_bits(*a).partial_cmp(&f64::from_bits(*b)),
                (ConstValue::Float(a, FloatTy::F32), ConstValue::Float(b, _)) => {
                    f32::from_bits(*a as u32).partial_cmp(&f32::from_bits(*b as u32))
                }
                (ConstValue::Int(a), ConstValue::Int(b)) => Some(a.cmp(b)),
                (ConstValue::Char(a), ConstValue::Char(b)) => Some(a.cmp(b)),
                (ConstValue::Bool(a), ConstValue::Bool(b)) => Some(a.cmp(b)),
                _ => None,
            };
            let r = match op {
                BinOp::Eq => eq,
                BinOp::Ne => !eq,
                BinOp::Lt => ord == Some(std::cmp::Ordering::Less),
                BinOp::Le => matches!(ord, Some(std::cmp::Ordering::Less | std::cmp::Ordering::Equal)),
                BinOp::Gt => ord == Some(std::cmp::Ordering::Greater),
                BinOp::Ge => matches!(ord, Some(std::cmp::Ordering::Greater | std::cmp::Ordering::Equal)),
                _ => unreachable!(),
            };
            if !op.is_cmp() || (matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) && ord.is_none()) {
                return Err(outside(span, "this comparison"));
            }
            return Ok((ConstValue::Bool(r), BOOL));
        }
        match (lv, rv) {
            (ConstValue::Float(a, f), ConstValue::Float(b, _)) => {
                let r = match f {
                    FloatTy::F64 => {
                        let (x, y) = (f64::from_bits(a), f64::from_bits(b));
                        let r = match op {
                            BinOp::Add => x + y,
                            BinOp::Sub => x - y,
                            BinOp::Mul => x * y,
                            BinOp::Div => x / y,
                            BinOp::Rem => x % y,
                            _ => return Err(outside(span, "this operation")),
                        };
                        r.to_bits()
                    }
                    FloatTy::F32 => {
                        let (x, y) = (f32::from_bits(a as u32), f32::from_bits(b as u32));
                        let r = match op {
                            BinOp::Add => x + y,
                            BinOp::Sub => x - y,
                            BinOp::Mul => x * y,
                            BinOp::Div => x / y,
                            BinOp::Rem => x % y,
                            _ => return Err(outside(span, "this operation")),
                        };
                        r.to_bits() as u64
                    }
                };
                Ok((ConstValue::Float(r, f), lt))
            }
            (ConstValue::Int(a), ConstValue::Int(b)) => self.int_op(cx, op, (ConstValue::Int(a), lt), (ConstValue::Int(b), lt), span),
            (ConstValue::Bool(a), ConstValue::Bool(b)) => {
                let r = match op {
                    BinOp::BitAnd => a & b,
                    BinOp::BitOr => a | b,
                    BinOp::BitXor => a ^ b,
                    _ => return Err(outside(span, "this operation")),
                };
                Ok((ConstValue::Bool(r), BOOL))
            }
            _ => Err(outside(span, "this operation")),
        }
    }

    fn int_op<'a, C: ConstCx<'a>>(&self, cx: &C, op: BinOp, a: TypedValue, b: TypedValue, span: Span) -> Result<TypedValue, Diag> {
        let (ConstValue::Int(x), t) = a else { return Err(outside(span, "this operation")) };
        let ConstValue::Int(y) = b.0 else { return Err(outside(span, "this operation")) };
        let r = match op {
            BinOp::Add => x.checked_add(y),
            BinOp::Sub => x.checked_sub(y),
            BinOp::Mul => x.checked_mul(y),
            BinOp::Div => x.checked_div(y),
            BinOp::Rem => x.checked_rem(y),
            BinOp::BitAnd => Some(x & y),
            BinOp::BitOr => Some(x | y),
            BinOp::BitXor => Some(x ^ y),
            BinOp::Shl => u32::try_from(y).ok().and_then(|y| x.checked_shl(y)),
            BinOp::Shr => u32::try_from(y).ok().and_then(|y| x.checked_shr(y)),
            _ => return Err(outside(span, "this operation")),
        };
        let r = r.ok_or_else(|| outside(span, "this operation (overflow or division by zero)"))?;
        // Overflow of the operand type is a const error, never a wrap.
        if let Some(it) = self.int_ty_of(cx, t)
            && !matches!(op, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr)
            && !fits(r, it)
        {
            return Err(outside(span, "this operation (overflow)"));
        }
        let r = match self.int_ty_of(cx, t) {
            Some(it) if matches!(op, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr) => truncate_to_int(r, it),
            _ => r,
        };
        Ok((ConstValue::Int(r), t))
    }

    fn cast<'a, C: ConstCx<'a>>(&self, cx: &C, (v, from_ty): TypedValue, target: Ty, span: Span) -> Result<TypedValue, Diag> {
        let tk = cx.tys_ref().kind(target);
        match (v, tk) {
            (ConstValue::Float(bits, f), TyKind::Float(g)) => {
                let r = match (f, g) {
                    (FloatTy::F64, FloatTy::F32) => (f64::from_bits(bits) as f32).to_bits() as u64,
                    (FloatTy::F32, FloatTy::F64) => (f32::from_bits(bits as u32) as f64).to_bits(),
                    _ => bits,
                };
                Ok((ConstValue::Float(r, g), target))
            }
            (ConstValue::Float(bits, f), TyKind::Int(it)) => {
                let r: i128 = match f {
                    FloatTy::F64 => {
                        let x = f64::from_bits(bits);
                        if it.signed() { (x as i128) } else { (x as u128) as i128 }
                    }
                    FloatTy::F32 => {
                        let x = f32::from_bits(bits as u32);
                        if it.signed() { (x as i128) } else { (x as u128) as i128 }
                    }
                };
                Ok((ConstValue::Int(truncate_to_int(r, it)), target))
            }
            (ConstValue::Int(i), TyKind::Float(g)) => {
                let r = match g {
                    FloatTy::F64 => (i as f64).to_bits(),
                    FloatTy::F32 => (i as f32).to_bits() as u64,
                };
                Ok((ConstValue::Float(r, g), target))
            }
            (ConstValue::Bool(b), TyKind::Float(g)) => {
                let r = match g {
                    FloatTy::F64 => ((b as u8) as f64).to_bits(),
                    FloatTy::F32 => ((b as u8) as f32).to_bits() as u64,
                };
                Ok((ConstValue::Float(r, g), target))
            }
            (ConstValue::Char(c), TyKind::Float(g)) => {
                let r = match g {
                    FloatTy::F64 => ((c as u32) as f64).to_bits(),
                    FloatTy::F32 => ((c as u32) as f32).to_bits() as u64,
                };
                Ok((ConstValue::Float(r, g), target))
            }
            (ConstValue::Float(bits, f), TyKind::Char) => {
                let i: i128 = match f {
                    FloatTy::F64 => f64::from_bits(bits) as i128,
                    FloatTy::F32 => f32::from_bits(bits as u32) as i128,
                };
                match u32::try_from(i).ok().and_then(char::from_u32) {
                    Some(c) => Ok((ConstValue::Char(c), target)),
                    None => Err(outside(span, "this cast (invalid char)")),
                }
            }
            (ConstValue::Int(i), TyKind::Int(it)) => Ok((ConstValue::Int(truncate_to_int(i, it)), target)),
            (ConstValue::Bool(b), TyKind::Int(_)) => Ok((ConstValue::Int(b as i128), target)),
            (ConstValue::Char(c), TyKind::Int(_)) => Ok((ConstValue::Int(c as i128), target)),
            (ConstValue::Int(i), TyKind::Char) => {
                let c = u32::try_from(i).ok().and_then(char::from_u32);
                match c {
                    Some(c) => Ok((ConstValue::Char(c), target)),
                    None => Err(outside(span, "this cast (invalid char)")),
                }
            }
            (ConstValue::Variant(variant, _), TyKind::Int(it)) => match cx.tys_ref().local_adt(from_ty) {
                Some(adt) => Ok((ConstValue::Int(truncate_to_int(cx.discriminant(adt, variant), it)), target)),
                None => Err(outside(span, "this cast")),
            },
            (v, _) if matches!(v, ConstValue::Int(_) | ConstValue::Bool(_)) && tk == TyKind::Bool => Err(outside(span, "this cast")),
            _ => Err(outside(span, "this cast")),
        }
    }

    fn call<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        callee: ExprId,
        args: &[ExprId],
        span: Span,
    ) -> Result<TypedValue, Diag> {
        match cx.call_target(callee) {
            CallTarget::SizeOf(t) => {
                let l = cx.layout(t).ok_or_else(|| {
                    Diag::new("L0652", span, "unsupported layout form in `size_of`", "Use a type inside the supported layout grammar.")
                })?;
                Ok((ConstValue::Int(l.size as i128), USIZE))
            }
            CallTarget::AlignOf(t) => {
                let l = cx.layout(t).ok_or_else(|| {
                    Diag::new("L0652", span, "unsupported layout form in `align_of`", "Use a type inside the supported layout grammar.")
                })?;
                Ok((ConstValue::Int(l.align as i128), USIZE))
            }
            CallTarget::VariantCtor { adt, variant, ty } => {
                // A user variant knows its field types; check each argument
                // against them. The `Some` shim (adt u32::MAX) has none here.
                let fields: Vec<Ty> = if adt.0 == u32::MAX { Vec::new() } else { cx.variant_fields(adt, variant).iter().map(|f| f.1).collect() };
                let mut vals = Vec::new();
                for (i, &a) in args.iter().enumerate() {
                    let want = fields.get(i).copied();
                    let (v, vt) = self.value(cx, env, a, want)?;
                    if let Some(want) = want
                        && !const_ty_compatible(cx.tys_ref(), vt, want)
                    {
                        return Err(const_ty_mismatch(cx.ast().expr_span(a), "this constructor argument"));
                    }
                    vals.push(v);
                }
                Ok((ConstValue::Variant(variant, vals), ty))
            }
            CallTarget::ConstFn(body) => {
                if args.len() != body.params.len() {
                    return Err(outside(span, "this call (wrong number of arguments)"));
                }
                let mut fenv: Env = Vec::new();
                for (i, &a) in args.iter().enumerate() {
                    let (v0, vt) = self.value(cx, env, a, body.param_tys.get(i).copied())?;
                    if let Some(&want) = body.param_tys.get(i)
                        && !const_ty_compatible(cx.tys_ref(), vt, want)
                    {
                        return Err(const_ty_mismatch(cx.ast().expr_span(a), "this call argument"));
                    }
                    // The parameter has its declared type inside the body,
                    // whatever width the argument literal was written at.
                    let v = (v0, body.param_tys.get(i).copied().unwrap_or(vt));
                    let (name, mutable, pat) = body.params[i];
                    match pat {
                        Some(pat) => {
                            let mut binds = Vec::new();
                            if !self.match_pat(cx, &mut fenv, pat, &v.0.clone(), v.1, true, &mut binds)? {
                                return Err(outside(span, "this call (argument pattern)"));
                            }
                            fenv.extend(binds);
                        }
                        None => fenv.push((name, v, mutable)),
                    }
                }
                match self.block(cx, &mut fenv, body.body, Some(body.ret))? {
                    // The fn body is type-checked as a fn; its value has the
                    // declared return type here.
                    Flow::Val(v) | Flow::Return(v) => Ok((v.0, body.ret)),
                    _ => Err(outside(span, "control flow out of a const fn")),
                }
            }
            CallTarget::NonConst => Err(nonconst(span, "this function")),
            CallTarget::Unknown => Err(outside(span, "this call")),
        }
    }

    fn macro_<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        kind: MacroKind,
        args: &[ExprId],
        fmt: &[ast::FmtPiece],
        span: Span,
    ) -> Result<TypedValue, Diag> {
        match kind {
            MacroKind::Assert => {
                let (v, _) = self.value(cx, env, args[0], Some(BOOL))?;
                let ConstValue::Bool(b) = v else { return Err(outside(span, "this assert")) };
                if b {
                    Ok((ConstValue::Unit, UNIT))
                } else {
                    let msg = fmt_text(fmt).unwrap_or_else(|| "assertion failed".into());
                    Err(Diag::new(C_OUTSIDE, span, format!("const assertion failed: {msg}"), "Fix the asserted condition."))
                }
            }
            MacroKind::AssertEq | MacroKind::AssertNe => {
                let (a, t) = self.value(cx, env, args[0], None)?;
                let (b, _) = self.value(cx, env, args[1], Some(t))?;
                let eq = values_eq(&a, &b);
                let pass = if kind == MacroKind::AssertEq { eq } else { !eq };
                if pass {
                    Ok((ConstValue::Unit, UNIT))
                } else {
                    Err(Diag::new(C_OUTSIDE, span, "const assertion failed: values differ", "Fix the asserted values."))
                }
            }
            MacroKind::Panic => {
                let msg = fmt_text(fmt).unwrap_or_else(|| "explicit panic".into());
                Err(Diag::new(C_OUTSIDE, span, format!("const panic: {msg}"), "Remove the panic from the const item."))
            }
            MacroKind::Vec => Err(outside(span, "`vec!`")),
            _ => Err(outside(span, "this macro")),
        }
    }

    fn match_expr<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        scrut: ExprId,
        arms: &[ast::Arm],
        expected: Option<Ty>,
        span: Span,
    ) -> Result<Flow, Diag> {
        let (sv, st) = self.value(cx, env, scrut, None)?;
        for arm in arms {
            let mut binds = Vec::new();
            if self.match_pat(cx, env, arm.pat, &sv, st, true, &mut binds)? {
                let saved = env.len();
                env.extend(binds);
                let guard_ok = match arm.guard {
                    None => true,
                    Some(g) => {
                        let (gv, _) = self.value(cx, env, g, Some(BOOL))?;
                        matches!(gv, ConstValue::Bool(true))
                    }
                };
                if guard_ok {
                    let r = self.expr(cx, env, arm.body, expected);
                    env.truncate(saved);
                    return r;
                }
                env.truncate(saved);
            }
        }
        Err(outside(span, "this match (no arm matched)"))
    }

    /// Matches a pattern against a value. On a match, appends the bindings
    /// (name, value, mutable) to `binds`. `in_match` is kept for parity with
    /// the checker's signature; refutable patterns simply do not match here.
    fn match_pat<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        pat: PatId,
        v: &ConstValue,
        t: Ty,
        _in_match: bool,
        binds: &mut Vec<(Sym, TypedValue, bool)>,
    ) -> Result<bool, Diag> {
        let span = cx.ast().pat_span(pat);
        match cx.ast().pat(pat) {
            Pat::Wild | Pat::Rest => Ok(true),
            Pat::Binding { name, mutable, by_ref } => {
                if *by_ref {
                    return Err(outside(span, "`ref` bindings in const"));
                }
                binds.push((*name, (v.clone(), t), *mutable));
                Ok(true)
            }
            Pat::At { name, mutable, by_ref, inner } => {
                if *by_ref {
                    return Err(outside(span, "`ref` bindings in const"));
                }
                if self.match_pat(cx, env, *inner, v, t, _in_match, binds)? {
                    binds.push((*name, (v.clone(), t), *mutable));
                    Ok(true)
                } else {
                    Ok(false)
                }
            }
            Pat::Paren(inner) => self.match_pat(cx, env, *inner, v, t, _in_match, binds),
            Pat::Ref { inner, .. } => match v {
                ConstValue::Ref(inner_v) => {
                    let it = match cx.tys_ref().kind(t) {
                        TyKind::Ref(_, _, it) => it,
                        _ => ERROR,
                    };
                    let inner_v = (**inner_v).clone();
                    self.match_pat(cx, env, *inner, &inner_v, it, _in_match, binds)
                }
                ConstValue::Str(i) => {
                    let s = ConstValue::Str(*i);
                    self.match_pat(cx, env, *inner, &s, t, _in_match, binds)
                }
                _ => Ok(false),
            },
            Pat::Lit(l) => {
                let (lv, _) = self.value(cx, env, *l, Some(t))?;
                Ok(values_eq(v, &lv))
            }
            Pat::Range { lo, hi, inclusive } => {
                let num = match v {
                    ConstValue::Int(i) => Some(*i),
                    ConstValue::Char(c) => Some(*c as i128),
                    _ => None,
                };
                let Some(n) = num else { return Ok(false) };
                if let Some(lo) = lo {
                    let (lv, _) = self.value(cx, env, *lo, Some(t))?;
                    let ConstValue::Int(l) = lv else { return Ok(false) };
                    if n < l {
                        return Ok(false);
                    }
                }
                if let Some(hi) = hi {
                    let (hv, _) = self.value(cx, env, *hi, Some(t))?;
                    let ConstValue::Int(h) = hv else { return Ok(false) };
                    if *inclusive {
                        if n > h {
                            return Ok(false);
                        }
                    } else if n >= h {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::Or(alts) => {
                for &alt in alts {
                    let before = binds.len();
                    if self.match_pat(cx, env, alt, v, t, _in_match, binds)? {
                        return Ok(true);
                    }
                    binds.truncate(before);
                }
                Ok(false)
            }
            Pat::Tuple(elems) => {
                let vals = match v {
                    ConstValue::Aggregate(vals) => vals,
                    ConstValue::Unit if elems.is_empty() => return Ok(true),
                    _ => return Ok(false),
                };
                let tys: Vec<Ty> = match cx.tys_ref().kind(t) {
                    TyKind::Tuple(ts) => cx.tys_ref().tys_of(ts).to_vec(),
                    _ => vec![ERROR; vals.len()],
                };
                let mapped = map_rest(elems, vals.len(), cx.ast());
                let Some(mapped) = mapped else { return Ok(false) };
                for (i, sub) in mapped {
                    if !self.match_pat(cx, env, sub, &vals[i].clone(), tys.get(i).copied().unwrap_or(ERROR), _in_match, binds)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::Slice { prefix, middle, suffix } => {
                let (vals, repeat): (Vec<ConstValue>, Option<(ConstValue, u64)>) = match v {
                    ConstValue::Aggregate(vals) => (vals.clone(), None),
                    ConstValue::Repeat(x, n) => (Vec::new(), Some(((**x).clone(), *n))),
                    _ => return Ok(false),
                };
                let len = repeat.as_ref().map_or(vals.len() as u64, |(_, n)| *n);
                let fixed = (prefix.len() + suffix.len()) as u64;
                if if middle.is_some() { len < fixed } else { len != fixed } {
                    return Ok(false);
                }
                let elem_ty = match cx.tys_ref().kind(t) {
                    TyKind::Array(e, _) | TyKind::Slice(e) => e,
                    _ => ERROR,
                };
                let at = |i: u64| -> ConstValue {
                    match &repeat {
                        Some((x, _)) => x.clone(),
                        None => vals[i as usize].clone(),
                    }
                };
                for (i, &sub) in prefix.iter().enumerate() {
                    if !self.match_pat(cx, env, sub, &at(i as u64), elem_ty, _in_match, binds)? {
                        return Ok(false);
                    }
                }
                for (j, &sub) in suffix.iter().enumerate() {
                    if !self.match_pat(cx, env, sub, &at(len - suffix.len() as u64 + j as u64), elem_ty, _in_match, binds)? {
                        return Ok(false);
                    }
                }
                if let Some(mid) = middle
                    && matches!(cx.ast().pat(*mid), Pat::Binding { .. })
                {
                    // Owned array middle, built element by element.
                    let mid_vals: Vec<ConstValue> = (prefix.len() as u64..len - suffix.len() as u64).map(at).collect();
                    let n = mid_vals.len() as u128;
                    let mid_ty = {
                        let c = cx.tys().intern_const(super::ConstKind::Int(n));
                        cx.tys().intern(TyKind::Array(elem_ty, c))
                    };
                    if !self.match_pat(cx, env, *mid, &ConstValue::Aggregate(mid_vals), mid_ty, _in_match, binds)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Pat::Path(segs) | Pat::TupleStruct { path: segs, .. } | Pat::Struct { path: segs, .. } => {
                let (v, t) = match v {
                    ConstValue::Ref(inner) => {
                        let it = match cx.tys_ref().kind(t) {
                            TyKind::Ref(_, _, it) => it,
                            _ => ERROR,
                        };
                        ((**inner).clone(), it)
                    }
                    other => (other.clone(), t),
                };
                // Option patterns by name, as the checker resolves them.
                if let ConstValue::Variant(variant, fields) = &v
                    && cx.tys_ref().option_elem(t).is_some()
                {
                    let want_some = matches!(cx.ast().pat(pat), Pat::TupleStruct { .. });
                    if (want_some && *variant == 1) || (!want_some && *variant == 0) {
                        if let Pat::TupleStruct { elems, .. } = cx.ast().pat(pat)
                            && elems.len() == 1
                        {
                            let elem_ty = cx.tys_ref().option_elem(t).unwrap_or(ERROR);
                            return self.match_pat(cx, env, elems[0], &fields[0].clone(), elem_ty, _in_match, binds);
                        }
                        if !want_some {
                            return Ok(true);
                        }
                    }
                }
                let Some((adt, variant)) = cx.pattern_variant(segs) else {
                    // A single name that resolves to a const item compares equal.
                    if segs.len() == 1
                        && let Some((cv, _)) = cx.const_item(segs[0].name)
                    {
                        return Ok(values_eq(&v, &cv));
                    }
                    return Err(outside(span, "this pattern"));
                };
                let field_defs = cx.variant_fields(adt, variant);
                let vals: &Vec<ConstValue> = match &v {
                    ConstValue::Variant(got, vals) => {
                        if *got != variant {
                            return Ok(false);
                        }
                        vals
                    }
                    ConstValue::Aggregate(vals) => vals,
                    _ => return Ok(false),
                };
                match cx.ast().pat(pat) {
                    Pat::Path(_) => Ok(true),
                    Pat::TupleStruct { elems, .. } => {
                        let Some(mapped) = map_rest(elems, vals.len(), cx.ast()) else { return Ok(false) };
                        for (i, sub) in mapped {
                            let ft = field_defs.get(i).map_or(ERROR, |f| f.1);
                            if !self.match_pat(cx, env, sub, &vals[i].clone(), ft, _in_match, binds)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    Pat::Struct { fields, .. } => {
                        for &(fname, sub) in fields {
                            let Some(i) = field_defs.iter().position(|(n, _)| *n == fname) else { return Ok(false) };
                            if !self.match_pat(cx, env, sub, &vals[i].clone(), field_defs[i].1, _in_match, binds)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    _ => Ok(false),
                }
            }
            _ => Err(outside(span, "this pattern")),
        }
    }

    /// The type of a place expression, for field assignment.
    fn place_ty<'a, C: ConstCx<'a>>(&self, cx: &C, env: &Env, e: ExprId) -> Option<Ty> {
        match cx.ast().expr(e) {
            Expr::Path(segs) if segs.len() == 1 => env.iter().rev().find(|(n, _, _)| *n == segs[0].name).map(|(_, v, _)| v.1),
            Expr::Field { base, name } => {
                let bt = self.place_ty(cx, env, *base)?;
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                let adt = cx.tys_ref().local_adt(bt)?;
                cx.variant_fields(adt, 0).iter().find(|(n, _)| n == name).map(|f| f.1)
            }
            Expr::TupleField { base, index } => {
                let bt = self.place_ty(cx, env, *base)?;
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                match cx.tys_ref().kind(bt) {
                    TyKind::Tuple(ts) => cx.tys_ref().tys_of(ts).get(*index as usize).copied(),
                    _ => cx.tys_ref().local_adt(bt).and_then(|a| cx.variant_fields(a, 0).get(*index as usize).map(|f| f.1)),
                }
            }
            Expr::Deref(inner) => match cx.tys_ref().kind(self.place_ty(cx, env, *inner)?) {
                TyKind::Ref(_, _, it) => Some(it),
                _ => None,
            },
            Expr::Index { base, .. } => {
                let bt = self.place_ty(cx, env, *base)?;
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                match cx.tys_ref().kind(bt) {
                    TyKind::Array(el, _) | TyKind::Slice(el) => Some(el),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Assigns `v` into the place `e` denotes in the environment.
    fn assign_place<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId, v: ConstValue, span: Span) -> Result<(), Diag> {
        match cx.ast().expr(e) {
            Expr::Path(segs) if segs.len() == 1 => {
                let name = segs[0].name;
                match env.iter_mut().rev().find(|(n, _, _)| *n == name) {
                    Some(slot) => {
                        if !slot.2 {
                            return Err(outside(span, "assignment to an immutable binding"));
                        }
                        slot.1.0 = v;
                        Ok(())
                    }
                    None => Err(outside(span, "this assignment")),
                }
            }
            Expr::Field { base, name } => {
                let bt = self.place_ty(cx, env, *base).ok_or_else(|| outside(span, "this assignment"))?;
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                let Some(adt) = cx.tys_ref().local_adt(bt) else { return Err(outside(span, "this assignment")) };
                let fields = cx.variant_fields(adt, 0);
                let Some(i) = fields.iter().position(|(n, _)| n == name) else {
                    return Err(outside(span, "this assignment"));
                };
                let slot = self.place_slot(cx, env, *base, span)?;
                let vals = match slot {
                    ConstValue::Aggregate(vals) => vals,
                    ConstValue::Ref(cell) => match &mut **cell {
                        ConstValue::Aggregate(vals) => vals,
                        _ => return Err(outside(span, "this assignment")),
                    },
                    _ => return Err(outside(span, "this assignment")),
                };
                match vals.get_mut(i) {
                    Some(cell) => {
                        *cell = v;
                        Ok(())
                    }
                    None => Err(outside(span, "this assignment")),
                }
            }
            Expr::TupleField { base, index } => {
                let slot = self.place_slot(cx, env, *base, span)?;
                match slot {
                    ConstValue::Aggregate(vals) => {
                        let Some(cell) = vals.get_mut(*index as usize) else {
                            return Err(outside(span, "this assignment"));
                        };
                        *cell = v;
                        Ok(())
                    }
                    _ => Err(outside(span, "this assignment")),
                }
            }
            Expr::Index { base, index } => {
                let (iv, _) = self.value(cx, env, *index, Some(USIZE))?;
                let ConstValue::Int(i) = iv else { return Err(outside(span, "this index")) };
                let slot = self.place_slot(cx, env, *base, span)?;
                match slot {
                    ConstValue::Aggregate(vals) => {
                        let Some(cell) = usize::try_from(i).ok().and_then(|i| vals.get_mut(i)) else {
                            return Err(outside(span, "this assignment (index out of bounds)"));
                        };
                        *cell = v;
                        Ok(())
                    }
                    _ => Err(outside(span, "this assignment")),
                }
            }
            Expr::Deref(inner) => {
                let slot = self.place_slot(cx, env, *inner, span)?;
                match slot {
                    ConstValue::Ref(cell) => {
                        **cell = v;
                        Ok(())
                    }
                    _ => Err(outside(span, "this assignment")),
                }
            }
            _ => Err(outside(span, "this assignment")),
        }
    }

    /// The mutable slot an assignment place base denotes.
    fn place_slot<'a, 'e, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &'e mut Env,
        e: ExprId,
        span: Span,
    ) -> Result<&'e mut ConstValue, Diag> {
        match cx.ast().expr(e) {
            Expr::Path(segs) if segs.len() == 1 => {
                let name = segs[0].name;
                env.iter_mut().rev().find(|(n, _, _)| *n == name).map(|slot| &mut slot.1.0).ok_or_else(|| outside(span, "this assignment"))
            }
            Expr::TupleField { base, index } => {
                let slot = self.place_slot(cx, env, *base, span)?;
                match slot {
                    ConstValue::Aggregate(vals) => vals.get_mut(*index as usize).ok_or_else(|| outside(span, "this assignment")),
                    ConstValue::Ref(cell) => match &mut **cell {
                        ConstValue::Aggregate(vals) => vals.get_mut(*index as usize).ok_or_else(|| outside(span, "this assignment")),
                        _ => Err(outside(span, "this assignment")),
                    },
                    _ => Err(outside(span, "this assignment")),
                }
            }
            Expr::Deref(inner) => {
                let slot = self.place_slot(cx, env, *inner, span)?;
                match slot {
                    ConstValue::Ref(cell) => Ok(&mut **cell),
                    _ => Err(outside(span, "this assignment")),
                }
            }
            _ => Err(outside(span, "this assignment")),
        }
    }
}

/// Maps pattern elements with an optional `..` to value indexes.
fn map_rest(elems: &[PatId], n: usize, ast: &Ast) -> Option<Vec<(usize, PatId)>> {
    let rest = elems.iter().position(|&s| matches!(ast.pat(s), Pat::Rest));
    match rest {
        None => {
            if elems.len() != n {
                return None;
            }
            Some(elems.iter().enumerate().map(|(i, &s)| (i, s)).collect())
        }
        Some(r) => {
            let suffix = elems.len() - r - 1;
            if r + suffix > n {
                return None;
            }
            let mut out: Vec<(usize, PatId)> = elems[..r].iter().enumerate().map(|(i, &s)| (i, s)).collect();
            for (j, &s) in elems[r + 1..].iter().enumerate() {
                out.push((n - suffix + j, s));
            }
            Some(out)
        }
    }
}

/// Value equality for const comparisons.
fn values_eq(a: &ConstValue, b: &ConstValue) -> bool {
    match (a, b) {
        (ConstValue::Float(x, FloatTy::F64), ConstValue::Float(y, _)) => {
            return f64::from_bits(*x) == f64::from_bits(*y);
        }
        (ConstValue::Float(x, FloatTy::F32), ConstValue::Float(y, _)) => {
            return f32::from_bits(*x as u32) == f32::from_bits(*y as u32);
        }
        (ConstValue::Repeat(x, n), ConstValue::Aggregate(vals)) => vals.len() as u64 == *n && vals.iter().all(|v| values_eq(v, x)),
        (ConstValue::Aggregate(vals), ConstValue::Repeat(x, n)) => vals.len() as u64 == *n && vals.iter().all(|v| values_eq(v, x)),
        (ConstValue::Repeat(x, xn), ConstValue::Repeat(y, yn)) => xn == yn && values_eq(x, y),
        _ => a == b,
    }
}

/// The literal text of a format string with no arguments, if it is all literal.
fn fmt_text(fmt: &[ast::FmtPiece]) -> Option<String> {
    let mut out = String::new();
    for p in fmt {
        match p {
            ast::FmtPiece::Lit(s) => out.push_str(s),
            ast::FmtPiece::Arg { .. } => out.push_str("{..}"),
        }
    }
    Some(out)
}
