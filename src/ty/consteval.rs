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
    /// The flat type name `Self` means inside the body: the impl type of
    /// a method or associated fn, None for a free fn.
    pub owner: Option<Sym>,
}

/// The questions the evaluator asks its caller.
pub trait ConstCx<'a> {
    type Tys: TyIntern;
    fn tys(&mut self) -> &mut Self::Tys;
    fn tys_ref(&self) -> &Self::Tys;
    fn ast(&self) -> &'a Ast;
    /// A const item or immutable static by name, evaluating it if needed.
    fn const_item(&mut self, name: Sym) -> Option<TypedValue>;
    /// An inherent associated const by its path (`Type::CONST`,
    /// module segments may lead), evaluating it if needed.
    fn assoc_const_item(&mut self, _segs: &[ast::PathSeg]) -> Option<TypedValue> {
        None
    }
    /// A call target for a callee expression already known to be a path.
    fn call_target(&mut self, callee: ExprId) -> CallTarget;
    /// A path used as a value: a unit variant, if it names one.
    fn unit_variant(&mut self, segs: &[ast::PathSeg], expected: Option<Ty>) -> Option<(AdtId, u32, Ty)>;
    /// A static item by name: its index and type.
    fn static_item(&mut self, name: Sym) -> Option<(u32, Ty)>;
    /// The struct or variant a struct literal names.
    fn struct_target(&mut self, path: &[ast::PathSeg]) -> Option<(AdtId, u32, Ty)>;
    /// Called around a const fn body the evaluator runs: `Self` inside
    /// it means `owner` (the fn's impl type), not the caller's. Contexts
    /// that resolve `Self` some other way keep these no-ops.
    fn enter_const_fn(&mut self, _owner: Option<Sym>) {}
    fn exit_const_fn(&mut self) {}
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
    /// True when the Adt is an enum (a struct literal for it builds a variant).
    fn is_enum(&self, adt: AdtId) -> bool;
    /// True when a named field is private to the module whose const
    /// expression the evaluator runs. The evaluator asks only outside
    /// a called const fn's body: that body is checked in its own
    /// module by the body checker. The default answers false, for
    /// contexts with no module table.
    fn named_field_private(&mut self, _adt: AdtId, _field: Sym) -> bool {
        false
    }
    /// True when a tuple field is private, like `named_field_private`.
    fn tuple_field_private(&mut self, _adt: AdtId, _index: u32) -> bool {
        false
    }
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

/// The L0510 for a private field named in a const expression, with
/// the same text as the body checker's field privacy errors.
fn private_field(span: Span, label: &str) -> Diag {
    Diag::new(
        "L0510",
        span,
        format!("field `{label}` is private"),
        "Make the field `pub(crate)` (the smallest widening that works).",
    )
}

/// The L0510 for a tuple struct constructor with a private field,
/// in call or pattern position.
fn private_ctor(span: Span) -> Diag {
    Diag::new(
        "L0510",
        span,
        "tuple struct constructor is private".to_string(),
        "Make every field `pub(crate)`, or add a public constructor function.",
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

// `ConstValue::Int` stores the canonical form of its typed value:
// sign-extended for signed types below 128 bits, zero-extended for
// unsigned types below 128 bits, and the raw 128 bits for i128 and
// u128 (so u128::MAX is -1). The helpers below convert between that
// storage, the raw bits, and the signed value. Every operation runs
// in its operand type, so u128 values at or above 2^127 compare,
// divide, and shift as unsigned.

/// The raw low bits of a stored integer, at its type's width.
fn int_bits(v: i128, it: IntTy) -> u128 {
    let bits = it.bits();
    if bits >= 128 { v as u128 } else { (v as u128) & ((1u128 << bits) - 1) }
}

/// The stored form of raw bits at a type's width.
fn int_from_bits(u: u128, it: IntTy) -> i128 {
    if it.bits() >= 128 { u as i128 } else { truncate_to_int(u as i128, it) }
}

/// The smallest value of a signed integer type (0 for unsigned).
fn int_min(it: IntTy) -> i128 {
    if !it.signed() {
        0
    } else if it.bits() >= 128 {
        i128::MIN
    } else {
        -(1i128 << (it.bits() - 1))
    }
}

/// Compares two stored integers at a type (signed value or raw bits).
fn cmp_int(a: i128, b: i128, it: Option<IntTy>) -> std::cmp::Ordering {
    match it {
        Some(it) if !it.signed() => int_bits(a, it).cmp(&int_bits(b, it)),
        Some(it) => truncate_to_int(a, it).cmp(&truncate_to_int(b, it)),
        None => a.cmp(&b),
    }
}

/// True when an expression is an unsuffixed int or float literal,
/// possibly negated: the forms whose type a cast target decides.
pub fn is_unsuffixed_lit(ast: &Ast, e: ExprId) -> bool {
    match ast.expr(e) {
        Expr::Int(_, suffix) => suffix.is_none(),
        Expr::Float(i) => {
            let t = ast.strings[*i as usize].trim_end();
            !t.ends_with("f32") && !t.ends_with("f64")
        }
        Expr::Unary { op: UnOp::Neg, expr } => is_unsuffixed_lit(ast, *expr),
        _ => false,
    }
}

/// Evaluates one const expression. `expected` is the type the context wants,
/// used for literal widths and array element types.
pub fn eval<'a, C: ConstCx<'a>>(cx: &mut C, e: ExprId, expected: Option<Ty>) -> Result<TypedValue, Diag> {
    let mut ev = Evaluator { steps: 0, call_depth: 0 };
    let mut env: Env = Vec::new();
    match ev.expr(cx, &mut env, e, expected)? {
        Flow::Val(v) => Ok(v),
        _ => Err(outside(cx.ast().expr_span(e), "control flow out of a const expression")),
    }
}

struct Evaluator {
    steps: u64,
    /// How deep the evaluator is in called const fn bodies. Field
    /// privacy asks run only at depth 0: a called const fn's body is
    /// written in its own module and checked there.
    call_depth: u32,
}

impl Evaluator {
    fn step(&mut self, span: Span) -> Result<(), Diag> {
        self.steps += 1;
        if self.steps > STEP_CAP {
            return Err(outside(span, "this const item (step limit reached)"));
        }
        Ok(())
    }

    /// Rejects a named field the context calls private to this const
    /// expression's module. A no-op inside a called const fn.
    fn check_named_field<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, adt: AdtId, field: Sym, span: Span) -> Result<(), Diag> {
        if self.call_depth == 0 && cx.named_field_private(adt, field) {
            let label = crate::intern::source_name(cx.sym_text(field)).to_string();
            return Err(private_field(span, &label));
        }
        Ok(())
    }

    /// Rejects a tuple field the context calls private.
    fn check_tuple_field<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, adt: AdtId, index: u32, span: Span) -> Result<(), Diag> {
        if self.call_depth == 0 && cx.tuple_field_private(adt, index) {
            return Err(private_field(span, &index.to_string()));
        }
        Ok(())
    }

    /// Rejects a tuple struct constructor (call or pattern) when any
    /// of its `n` fields is private, as rustc does (E0603).
    fn check_tuple_ctor<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, adt: AdtId, n: usize, span: Span) -> Result<(), Diag> {
        if self.call_depth == 0 && (0..n).any(|i| cx.tuple_field_private(adt, i as u32)) {
            return Err(private_ctor(span));
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
                // With no expected type an unsuffixed literal stays wide
                // (i128): a const fn local takes its real type from its
                // uses, which this evaluator does not infer. The value
                // is range-checked again where it meets a declared type
                // (the item coercion in collect, the return coercion in
                // `call`), so a wide literal never escapes unchecked.
                let t = match suffix {
                    Some(s) => super::int(IntTy::from_suffix(*s)),
                    None => expected.filter(|&t| self.int_ty_of(cx, t).is_some()).unwrap_or(super::int(IntTy::I128)),
                };
                let it = self.int_ty_of(cx, t).unwrap_or(IntTy::I128);
                if *v > it.max128() {
                    return Err(Diag::new(C_OUTSIDE, span, "integer literal out of range in const", "Change the literal or the type."));
                }
                (ConstValue::Int(int_from_bits(*v, it)), t)
            }
            Expr::Float(i) => {
                let text = cx.ast().strings[*i as usize].as_str();
                match crate::check::collect::parse_float_literal(text) {
                    Some((_, suffix)) => {
                        let f = suffix.unwrap_or(match expected.map(|t| cx.tys_ref().kind(t)) {
                            Some(TyKind::Float(f)) => f,
                            _ => FloatTy::F64,
                        });
                        // One rounding, straight to the target type.
                        if crate::check::collect::float_literal_overflows(text, f) {
                            return Err(Diag::new(
                                C_OUTSIDE,
                                span,
                                "float literal out of range in const",
                                "Change the literal or the type.",
                            ));
                        }
                        let Some(bits) = crate::check::collect::parse_float_literal_as(text, f) else {
                            return Err(outside(span, "this float literal"));
                        };
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
                // A negated literal is range-checked after the negation,
                // so `-128` is a valid i8: check the magnitude against
                // the type's minimum, not its maximum.
                if *op == UnOp::Neg
                    && let Expr::Int(v, suffix) = cx.ast().expr(*expr)
                {
                    let (v, suffix) = (*v, *suffix);
                    let t = match suffix {
                        Some(s) => super::int(IntTy::from_suffix(s)),
                        None => expected.filter(|&t| self.int_ty_of(cx, t).is_some()).unwrap_or(super::int(IntTy::I128)),
                    };
                    let it = self.int_ty_of(cx, t).unwrap_or(IntTy::I128);
                    if !it.signed() || v > it.max128() + 1 {
                        return Err(Diag::new(
                            C_OUTSIDE,
                            span,
                            "integer literal out of range in const",
                            "Change the literal or the type.",
                        ));
                    }
                    let r = if v == (1u128 << 127) { i128::MIN } else { -(v as i128) };
                    (ConstValue::Int(r), t)
                } else {
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
                            let it = self.int_ty_of(cx, t);
                            if let Some(it) = it
                                && (!it.signed() || i == int_min(it))
                            {
                                return Err(outside(span, "this negation (overflow)"));
                            }
                            let r = i.checked_neg().ok_or_else(|| outside(span, "this negation (overflow)"))?;
                            (ConstValue::Int(r), t)
                        }
                        (UnOp::Not, ConstValue::Int(i)) => {
                            let r = match self.int_ty_of(cx, t) {
                                Some(it) => int_from_bits(!int_bits(i, it), it),
                                None => !i,
                            };
                            (ConstValue::Int(r), t)
                        }
                        (UnOp::Not, ConstValue::Bool(b)) => (ConstValue::Bool(!b), BOOL),
                        _ => return Err(outside(span, "this unary operation")),
                    }
                }
            }
            Expr::Binary { op, lhs, rhs } => return Ok(Flow::Val(self.binary(cx, env, *op, *lhs, *rhs, expected, span)?)),
            Expr::Cast { expr, ty } => {
                let target = cx.resolve_ty(*ty);
                // An unsuffixed literal takes its type from the cast
                // target, so `300 as u8` is out of range, not 44.
                let exp = if is_unsuffixed_lit(cx.ast(), *expr) { Some(target) } else { None };
                let v = self.value(cx, env, *expr, exp)?;
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
                self.check_named_field(cx, adt, *name, span)?;
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
                if !matches!(cx.tys_ref().kind(t), TyKind::Tuple(_))
                    && let Some(adt) = cx.tys_ref().local_adt(t)
                {
                    self.check_tuple_field(cx, adt, *index, span)?;
                }
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
                // A slice value at a `&[T]` type is its backing
                // aggregate, so an index reads the type through the
                // reference as well as off an array or slice directly.
                let elem = match cx.tys_ref().kind(t) {
                    TyKind::Array(el, _) | TyKind::Slice(el) => el,
                    TyKind::Ref(_, _, inner) => match cx.tys_ref().kind(inner) {
                        TyKind::Array(el, _) | TyKind::Slice(el) => el,
                        _ => return Err(outside(span, "this index")),
                    },
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
                // Privacy first: written fields, and every field when
                // `..base` fills the rest (rustc E0451 for both).
                for &(fname, fspan, _) in fields {
                    self.check_named_field(cx, adt, fname, fspan)?;
                }
                if update.is_some() {
                    for &(fname, _) in &field_defs {
                        self.check_named_field(cx, adt, fname, span)?;
                    }
                }
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
                    let bvals = match bv {
                        ConstValue::Aggregate(bvals) => Some(bvals),
                        ConstValue::Variant(_, bvals) => Some(bvals),
                        _ => None,
                    };
                    if let Some(bvals) = bvals {
                        for (i, b) in bvals.into_iter().enumerate() {
                            if vals.get(i).is_some_and(|v| v.is_none()) {
                                vals[i] = Some(b);
                            }
                        }
                    }
                }
                let vals: Option<Vec<ConstValue>> = vals.into_iter().collect();
                match vals {
                    Some(vals) if cx.tys_ref().local_adt(ty).is_some() => {
                        // A struct-like enum variant keeps its variant;
                        // an aggregate would silently become variant 0.
                        if cx.is_enum(adt) { (ConstValue::Variant(variant, vals), ty) } else { (ConstValue::Aggregate(vals), ty) }
                    }
                    _ => return Err(outside(span, "this struct literal")),
                }
            }
            Expr::OffsetOf { ty, fields } => {
                let mut cur = cx.resolve_ty(*ty);
                let mut off: u64 = 0;
                for &ffield in fields {
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
                    // Tuple field defs carry their index text as the name.
                    let found = match ffield {
                        crate::ast::OffsetField::Name(fname) => defs.iter().position(|(n, _)| *n == fname),
                        crate::ast::OffsetField::Index(idx) => {
                            if (idx as usize) < defs.len() && cx.sym_text(defs[idx as usize].0).parse::<u32>() == Ok(idx) {
                                Some(idx as usize)
                            } else {
                                None
                            }
                        }
                    };
                    let Some(i) = found else {
                        return Err(outside(span, "this `offset_of!` field"));
                    };
                    match ffield {
                        crate::ast::OffsetField::Name(fname) => self.check_named_field(cx, adt, fname, span)?,
                        crate::ast::OffsetField::Index(idx) => self.check_tuple_field(cx, adt, idx, span)?,
                    }
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
            Expr::Call { callee, args } => return Ok(Flow::Val(self.call(cx, env, *callee, args, span, expected)?)),
            // Only primitive methods evaluate today (`method_call`
            // below). If user const methods land: run the method
            // body with `call_depth` raised, as the ConstFn call
            // arm does, so its field accesses are not privacy
            // checked against the caller's module.
            Expr::MethodCall { recv, name, args, .. } => {
                return Ok(Flow::Val(self.method_call(cx, env, *recv, *name, args, expected, span)?));
            }
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
                ast::Stmt::Let { pat, ty, init, els, .. } => {
                    let Some(init) = init else { return Err(outside(cx.ast().pat_span(*pat), "an uninitialized binding")) };
                    let exp = ty.map(|t| cx.resolve_ty(t));
                    let v = self.value(cx, env, *init, exp)?;
                    let mut binds = Vec::new();
                    if !self.match_pat(cx, env, *pat, &v.0.clone(), v.1, true, &mut binds)? {
                        // A let-else runs its (diverging) else block
                        // instead; its flow is the block's flow.
                        if let Some(els_b) = els {
                            let flow = self.block(cx, env, *els_b, None)?;
                            env.truncate(saved);
                            return Ok(flow);
                        }
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
            if let Some(v) = self.char_assoc_const(cx, segs) {
                return Ok(v);
            }
        }
        // Inherent associated consts of user types: `Type::CONST`.
        if segs.len() >= 2
            && let Some(v) = cx.assoc_const_item(segs)
        {
            return Ok(v);
        }
        if let Some(v) = self.float_assoc_const(cx, segs) {
            return Ok(v);
        }
        Err(outside(span, "this path"))
    }

    /// `f64::NAN`, `std::f64::consts::PI`, and friends, by written names.
    fn float_assoc_const<'a, C: ConstCx<'a>>(&self, cx: &mut C, segs: &[ast::PathSeg]) -> Option<TypedValue> {
        let names: Vec<&str> = segs.iter().map(|s| cx.sym_text(s.name)).collect();
        let (ty_name, item, module) = match names.as_slice() {
            [t, i] => (*t, *i, false),
            [p, t, c, i] if matches!(*p, "std" | "core" | "alloc") && *c == "consts" => (*t, *i, true),
            _ => return None,
        };
        let f = match ty_name {
            "f32" => FloatTy::F32,
            "f64" => FloatTy::F64,
            _ => return None,
        };
        if module {
            let bits = float_consts_value(f, item)?;
            let t = cx.tys().float_ty(f);
            return Some((ConstValue::Float(bits, f), t));
        }
        match primitive_float_assoc(f, item)? {
            (bits, None) => {
                let t = cx.tys().float_ty(f);
                Some((ConstValue::Float(bits, f), t))
            }
            (v, Some(it)) => Some((ConstValue::Int(v as i128), super::int(it))),
        }
    }

    /// `char::MAX`, `char::REPLACEMENT_CHARACTER`, and
    /// `char::UNICODE_VERSION`, resolved by written names.
    fn char_assoc_const<'a, C: ConstCx<'a>>(&self, cx: &mut C, segs: &[ast::PathSeg]) -> Option<TypedValue> {
        if cx.sym_text(segs[0].name) != "char" {
            return None;
        }
        match cx.sym_text(segs[1].name) {
            "MAX" => Some((ConstValue::Char(char::MAX), CHAR)),
            "MIN" => Some((ConstValue::Char(char::MIN), CHAR)),
            "REPLACEMENT_CHARACTER" => Some((ConstValue::Char(char::REPLACEMENT_CHARACTER), CHAR)),
            "UNICODE_VERSION" => {
                let (maj, min, pat) = char::UNICODE_VERSION;
                let u8t = super::int(IntTy::U8);
                let ts = cx.tys().intern_tys(&[u8t, u8t, u8t]);
                let ty = cx.tys().intern(TyKind::Tuple(ts));
                let parts = vec![ConstValue::Int(maj as i128), ConstValue::Int(min as i128), ConstValue::Int(pat as i128)];
                Some((ConstValue::Aggregate(parts), ty))
            }
            _ => None,
        }
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
            "BITS" => return Some((ConstValue::Int(bits as i128), super::int(IntTy::U32))),
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
                (ConstValue::Int(a), ConstValue::Int(b)) => Some(cmp_int(*a, *b, self.int_ty_of(cx, lt))),
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
        let over = || outside(span, "this operation (overflow or division by zero)");
        // Every operation runs in the operand type: overflow of that
        // type is a const error (rustc E0080), and shifts check the
        // amount against the type's width. Unsigned math runs on the
        // raw bits, so u128 values at or above 2^127 stay correct.
        let Some(it) = self.int_ty_of(cx, t) else {
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
            return Ok((ConstValue::Int(r.ok_or_else(over)?), t));
        };
        // A wide (unsuffixed-literal) operand that does not fit the
        // operation type is an overflow, never a silent wrap. The
        // shift amount is exempt: its own check bounds it.
        let stored_fits = |v: i128| {
            if it.bits() >= 128 {
                true
            } else if it.signed() {
                fits(v, it)
            } else {
                v >= 0 && (v as u128) <= it.max128()
            }
        };
        if !stored_fits(x) || (!matches!(op, BinOp::Shl | BinOp::Shr) && !stored_fits(y)) {
            return Err(over());
        }
        let r: i128 = if it.signed() {
            let (x, y) = (truncate_to_int(x, it), truncate_to_int(y, it));
            let r = match op {
                BinOp::Add => x.checked_add(y),
                BinOp::Sub => x.checked_sub(y),
                BinOp::Mul => x.checked_mul(y),
                BinOp::Div | BinOp::Rem => {
                    if y == 0 || (x == int_min(it) && y == -1) {
                        None
                    } else if op == BinOp::Div {
                        Some(x / y)
                    } else {
                        Some(x % y)
                    }
                }
                BinOp::BitAnd => Some(int_from_bits(int_bits(x, it) & int_bits(y, it), it)),
                BinOp::BitOr => Some(int_from_bits(int_bits(x, it) | int_bits(y, it), it)),
                BinOp::BitXor => Some(int_from_bits(int_bits(x, it) ^ int_bits(y, it), it)),
                BinOp::Shl | BinOp::Shr => {
                    let amt = u32::try_from(y).ok().filter(|&s| s < it.bits());
                    match (op, amt) {
                        (BinOp::Shl, Some(s)) => Some(int_from_bits(int_bits(x, it) << s, it)),
                        (BinOp::Shr, Some(s)) => Some(x >> s),
                        _ => None,
                    }
                }
                _ => return Err(outside(span, "this operation")),
            };
            let r = r.ok_or_else(over)?;
            if !matches!(op, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor | BinOp::Shl | BinOp::Shr) && !fits(r, it) {
                return Err(over());
            }
            r
        } else {
            let (x, y) = (int_bits(x, it), int_bits(y, it));
            let max = it.max128();
            let r = match op {
                BinOp::Add => x.checked_add(y).filter(|&r| r <= max),
                BinOp::Sub => x.checked_sub(y),
                BinOp::Mul => x.checked_mul(y).filter(|&r| r <= max),
                BinOp::Div => x.checked_div(y),
                BinOp::Rem => x.checked_rem(y),
                BinOp::BitAnd => Some(x & y),
                BinOp::BitOr => Some(x | y),
                BinOp::BitXor => Some(x ^ y),
                BinOp::Shl | BinOp::Shr => {
                    let amt = u32::try_from(y).ok().filter(|&s| s < it.bits());
                    match (op, amt) {
                        (BinOp::Shl, Some(s)) => Some((x << s) & max),
                        (BinOp::Shr, Some(s)) => Some(x >> s),
                        _ => None,
                    }
                }
                _ => return Err(outside(span, "this operation")),
            };
            int_from_bits(r.ok_or_else(over)?, it)
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
                // The source type decides the conversion: an unsigned
                // source converts from its raw bits, never as a negative.
                let unsigned = matches!(self.int_ty_of(cx, from_ty), Some(it) if !it.signed());
                let r = match (g, unsigned) {
                    (FloatTy::F64, true) => ((i as u128) as f64).to_bits(),
                    (FloatTy::F32, true) => ((i as u128) as f32).to_bits() as u64,
                    (FloatTy::F64, false) => (i as f64).to_bits(),
                    (FloatTy::F32, false) => (i as f32).to_bits() as u64,
                };
                Ok((ConstValue::Float(r, g), target))
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
        expected: Option<Ty>,
    ) -> Result<TypedValue, Diag> {
        // `AtomicUsize::new(v)` and the other atomics' `new` are const fns
        // (W-THREADS): the value is the atomic's (its C form is the value).
        if let Expr::Path(segs) = cx.ast().expr(callee)
            && segs.len() > 2
            && args.len() == 1
        {
            let names: Vec<&str> = segs.iter().map(|s| cx.sym_text(s.name)).collect();
            if let Some((&"new", ty_path)) = names.split_last()
                && let Some(k) = super::sync::SyncTy::by_path(ty_path)
                && let Some(av) = k.atomic_value()
            {
                let (v, vt) = self.value(cx, env, args[0], Some(av.ty()))?;
                if !const_ty_compatible(cx.tys_ref(), vt, av.ty()) {
                    return Err(outside(span, "this atomic initializer"));
                }
                let t = super::sync::sync_ty(cx.tys(), k, &[]);
                return Ok((v, t));
            }
            // `Mutex::new(v)` and `RwLock::new(v)` are const fns too: an
            // unlocked, unpoisoned lock around the value.
            if let Some((&"new", ty_path)) = names.split_last()
                && let Some(k) = super::sync::SyncTy::by_path(ty_path)
                && k.is_lock()
            {
                let written = segs[segs.len() - 2].type_args();
                let want = match written.first() {
                    Some(_) => return Err(outside(span, "a lock initializer with a turbofish")),
                    None => expected.and_then(|t| cx.tys_ref().adt_first_ty_arg(t)),
                };
                let (v, vt) = self.value(cx, env, args[0], want)?;
                let t = super::sync::sync_ty(cx.tys(), k, &[vt]);
                return Ok((ConstValue::Aggregate(vec![v]), t));
            }
        }
        // `f64::from_bits(n)` and `f32::from_bits(n)` are const fns.
        if let Expr::Path(segs) = cx.ast().expr(callee)
            && segs.len() == 2
            && cx.sym_text(segs[1].name) == "from_bits"
            && args.len() == 1
        {
            let f = match cx.sym_text(segs[0].name) {
                "f64" => Some((FloatTy::F64, super::int(IntTy::U64))),
                "f32" => Some((FloatTy::F32, super::int(IntTy::U32))),
                _ => None,
            };
            if let Some((f, arg_ty)) = f {
                let (v, _) = self.value(cx, env, args[0], Some(arg_ty))?;
                let ConstValue::Int(i) = v else { return Err(outside(span, "this `from_bits` argument")) };
                let bits = i as u128 as u64;
                let bits = if f == FloatTy::F32 { bits & 0xFFFF_FFFF } else { bits };
                let t = cx.tys().float_ty(f);
                return Ok((ConstValue::Float(bits, f), t));
            }
        }
        // `char::from_u32(n)` (also `core::char::from_u32`) is a
        // const fn answering an `Option<char>`.
        if let Expr::Path(segs) = cx.ast().expr(callee) {
            let names: Vec<String> = segs.iter().map(|s| cx.sym_text(s.name).to_string()).collect();
            let tail2: Vec<&str> = names.iter().rev().take(2).rev().map(|s| s.as_str()).collect();
            if tail2 == ["char", "from_u32"] && (names.len() == 2 || (names.len() == 3 && matches!(names[0].as_str(), "std" | "core" | "alloc"))) && args.len() == 1 {
                let n = self.int_arg(cx, env, args[0], super::int(IntTy::U32), span)?;
                let v = u32::try_from(n).ok().and_then(char::from_u32).map(ConstValue::Char);
                return Ok(self.opt_value(cx, CHAR, v));
            }
            // `char::from_digit(d, radix)` is a const fn too; it panics
            // only above radix 36, which rejects here instead of running.
            if tail2 == ["char", "from_digit"]
                && (names.len() == 2 || (names.len() == 3 && matches!(names[0].as_str(), "std" | "core" | "alloc")))
                && args.len() == 2
            {
                let d = self.int_arg(cx, env, args[0], super::int(IntTy::U32), span)?;
                let r = self.int_arg(cx, env, args[1], super::int(IntTy::U32), span)?;
                let (Some(d), Some(r)) = (u32::try_from(d).ok(), u32::try_from(r).ok()) else {
                    return Err(outside(span, "this `from_digit` call"));
                };
                if r > 36 {
                    return Err(outside(span, "this `from_digit` radix (above 36)"));
                }
                let v = char::from_digit(d, r).map(ConstValue::Char);
                return Ok(self.opt_value(cx, CHAR, v));
            }
            if tail2 == ["char", "from_u32_unchecked"]
                && (names.len() == 2 || (names.len() == 3 && matches!(names[0].as_str(), "std" | "core" | "alloc")))
                && args.len() == 1
            {
                let n = self.int_arg(cx, env, args[0], super::int(IntTy::U32), span)?;
                return match u32::try_from(n).ok().and_then(char::from_u32) {
                    Some(c) => Ok((ConstValue::Char(c), CHAR)),
                    None => Err(outside(span, "this `from_u32_unchecked` (invalid char)")),
                };
            }
            // Integer byte-order associated fns: `u32::from_be_bytes`,
            // `i64::from_le`, and friends, by written names.
            if names.len() == 2 && args.len() == 1 {
                if let Some(it) = IntTy::ALL.iter().find(|i| i.name() == names[0].as_str()).copied() {
                    let width = it.bits();
                    let mask: u128 = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
                    let t = super::int(it);
                    match names[1].as_str() {
                        "from_be_bytes" | "from_le_bytes" | "from_ne_bytes" => {
                            let (v, _) = self.value(cx, env, args[0], None)?;
                            let Some(bs) = self.seq_bytes(&v) else { return Err(outside(span, "this call")) };
                            if bs.len() as u32 != width / 8 {
                                return Err(outside(span, "this call"));
                            }
                            let be = names[1] == "from_be_bytes" || (names[1] == "from_ne_bytes" && cfg!(target_endian = "big"));
                            let mut bits: u128 = 0;
                            for (i, &b) in bs.iter().enumerate() {
                                let shift = if be { 8 * (bs.len() - 1 - i) } else { 8 * i };
                                bits |= (b as u128) << shift;
                            }
                            return Ok((ConstValue::Int(int_from_bits(bits & mask, it)), t));
                        }
                        "from_be" | "from_le" => {
                            let n = self.int_arg(cx, env, args[0], t, span)?;
                            let xb = int_bits(n, it);
                            let swap = xb.swap_bytes() >> (128 - width);
                            let want_swap = (names[1] == "from_be") == cfg!(target_endian = "little");
                            return Ok((ConstValue::Int(int_from_bits((if want_swap { swap } else { xb }) & mask, it)), t));
                        }
                        _ => {}
                    }
                }
            }
        }
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
                // against them. The `Some` and `Ok`/`Err` shims (adt
                // u32::MAX and u32::MAX - 1) have none here.
                let fields: Vec<Ty> = if adt.0 >= u32::MAX - 1 { Vec::new() } else { cx.variant_fields(adt, variant).iter().map(|f| f.1).collect() };
                // A tuple struct constructor is private when any field
                // is; enum variant fields take the enum's visibility.
                if adt.0 < u32::MAX - 1 && !cx.is_enum(adt) {
                    self.check_tuple_ctor(cx, adt, fields.len(), span)?;
                }
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
                // A tuple struct builds an aggregate, like its struct
                // literal form; only enum variants (and the shims,
                // whose layout is enum-shaped) build a variant value.
                if adt.0 >= u32::MAX - 1 || cx.is_enum(adt) {
                    Ok((ConstValue::Variant(variant, vals), ty))
                } else {
                    Ok((ConstValue::Aggregate(vals), ty))
                }
            }
            CallTarget::ConstFn(body) => {
                if args.len() != body.params.len() {
                    return Err(outside(span, "this call (wrong number of arguments)"));
                }
                // Arguments evaluate in the caller's module, so they
                // evaluate before the call depth moves.
                let mut arg_vals: Vec<TypedValue> = Vec::new();
                for (i, &a) in args.iter().enumerate() {
                    let (v0, vt) = self.value(cx, env, a, body.param_tys.get(i).copied())?;
                    if let Some(&want) = body.param_tys.get(i)
                        && !const_ty_compatible(cx.tys_ref(), vt, want)
                    {
                        return Err(const_ty_mismatch(cx.ast().expr_span(a), "this call argument"));
                    }
                    // The parameter has its declared type inside the body,
                    // whatever width the argument literal was written at.
                    arg_vals.push((v0, body.param_tys.get(i).copied().unwrap_or(vt)));
                }
                // Parameter patterns and the body are the callee's
                // code, checked in its own module: run both below
                // depth 0 so the privacy hooks stay out.
                self.call_depth += 1;
                let mut fenv: Env = Vec::new();
                let mut bind_err: Option<Diag> = None;
                for (i, v) in arg_vals.into_iter().enumerate() {
                    let (name, mutable, pat) = body.params[i];
                    match pat {
                        Some(pat) => {
                            let mut binds = Vec::new();
                            match self.match_pat(cx, &mut fenv, pat, &v.0.clone(), v.1, true, &mut binds) {
                                Ok(true) => fenv.extend(binds),
                                Ok(false) => {
                                    bind_err = Some(outside(span, "this call (argument pattern)"));
                                    break;
                                }
                                Err(d) => {
                                    bind_err = Some(d);
                                    break;
                                }
                            }
                        }
                        None => fenv.push((name, v, mutable)),
                    }
                }
                cx.enter_const_fn(body.owner);
                let flow = match bind_err {
                    Some(d) => Err(d),
                    None => self.block(cx, &mut fenv, body.body, Some(body.ret)),
                };
                cx.exit_const_fn();
                self.call_depth -= 1;
                match flow? {
                    // The fn body is type-checked as a fn; its value has the
                    // declared return type here. A wide (unsuffixed-literal)
                    // integer result is range-checked against it first:
                    // this is where an untyped local meets its real type.
                    Flow::Val(v) | Flow::Return(v) => {
                        if let (ConstValue::Int(i), Some(it)) = (&v.0, self.int_ty_of(cx, body.ret))
                            && v.1 != body.ret
                        {
                            let ok = if it.bits() >= 128 {
                                true
                            } else if it.signed() {
                                fits(*i, it)
                            } else {
                                *i >= 0 && (*i as u128) <= it.max128()
                            };
                            if !ok {
                                return Err(outside(span, "this const fn result (overflow)"));
                            }
                            return Ok((ConstValue::Int(int_from_bits(int_bits(*i, it), it)), body.ret));
                        }
                        Ok((v.0, body.ret))
                    }
                    _ => Err(outside(span, "control flow out of a const fn")),
                }
            }
            CallTarget::NonConst => Err(nonconst(span, "this function")),
            CallTarget::Unknown => Err(outside(span, "this call")),
        }
    }

    /// The element count of a slice or array const value, through a
    /// promoted reference if the value carries one.
    fn seq_len(&self, v: &ConstValue) -> Option<usize> {
        match v {
            ConstValue::Aggregate(vals) => Some(vals.len()),
            ConstValue::Repeat(_, n) => Some(*n as usize),
            ConstValue::Ref(inner) => self.seq_len(inner),
            _ => None,
        }
    }

    /// The elements of a slice or array const value as bytes, when
    /// every element is a `u8` integer.
    fn seq_bytes(&self, v: &ConstValue) -> Option<Vec<u8>> {
        match v {
            ConstValue::Aggregate(vals) => {
                let mut out = Vec::with_capacity(vals.len());
                for x in vals {
                    match x {
                        ConstValue::Int(i) => out.push(u8::try_from(*i).ok()?),
                        _ => return None,
                    }
                }
                Some(out)
            }
            ConstValue::Repeat(x, n) => match **x {
                ConstValue::Int(i) => Some(vec![u8::try_from(i).ok()?; *n as usize]),
                _ => None,
            },
            ConstValue::Ref(inner) => self.seq_bytes(inner),
            _ => None,
        }
    }

    /// An `Option` const value at a fresh `Option<elem>` type.
    fn opt_value<'a, C: ConstCx<'a>>(&self, cx: &mut C, elem: Ty, v: Option<ConstValue>) -> TypedValue {
        let t = cx.tys().mk_option(elem);
        match v {
            Some(v) => (ConstValue::Variant(1, vec![v]), t),
            None => (ConstValue::Variant(0, Vec::new()), t),
        }
    }

    /// Primitive method calls in const position: the `str`, slice,
    /// integer, char, float, and `Option` methods rustc marks const
    /// (inherent ones; conditionally-const trait methods such as
    /// `Ord::max` and `From::from` stay rejected, as rustc rejects
    /// them in plain constants). Anything else keeps the outside
    /// error, so a wrong receiver or a non-const method never
    /// evaluates to a made-up value.
    fn method_call<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        recv_e: ExprId,
        name: Sym,
        args: &[ExprId],
        expected: Option<Ty>,
        span: Span,
    ) -> Result<TypedValue, Diag> {
        let outside_err = || outside(span, "method calls");
        let name = cx.sym_text(name).to_string();
        let (rv, rt) = self.value(cx, env, recv_e, None)?;
        let no_args = |args: &[ExprId]| args.is_empty();
        match &rv {
            ConstValue::Str(i) => {
                let text = cx.ast().strings[*i as usize].clone();
                let bytes = text.as_bytes();
                match name.as_str() {
                    "len" if no_args(args) => Ok((ConstValue::Int(bytes.len() as i128), USIZE)),
                    "is_empty" if no_args(args) => Ok((ConstValue::Bool(bytes.is_empty()), BOOL)),
                    "is_ascii" if no_args(args) => Ok((ConstValue::Bool(bytes.iter().all(|b| b.is_ascii())), BOOL)),
                    "as_bytes" if no_args(args) => {
                        let vals: Vec<ConstValue> = bytes.iter().map(|&b| ConstValue::Int(b as i128)).collect();
                        let slice = cx.tys().intern(TyKind::Slice(super::int(IntTy::U8)));
                        let t = cx.tys().mk_ref(false, slice);
                        Ok((ConstValue::Aggregate(vals), t))
                    }
                    _ => Err(outside_err()),
                }
            }
            ConstValue::Int(x) => {
                let x = *x;
                self.int_method(cx, env, x, rt, &name, args, expected, span)
            }
            ConstValue::Char(c) => {
                let c = *c;
                self.char_method(cx, env, c, &name, args, span)
            }
            ConstValue::Float(bits, f) => {
                let (bits, f) = (*bits, *f);
                match name.as_str() {
                    "to_bits" if no_args(args) => {
                        let it = if f == FloatTy::F32 { IntTy::U32 } else { IntTy::U64 };
                        Ok((ConstValue::Int(bits as i128), super::int(it)))
                    }
                    "abs" if no_args(args) => {
                        let sign = if f == FloatTy::F32 { 1u64 << 31 } else { 1u64 << 63 };
                        Ok((ConstValue::Float(bits & !sign, f), rt))
                    }
                    "max" | "min" if args.len() == 1 => {
                        let (av, _) = self.value(cx, env, args[0], Some(rt))?;
                        let ConstValue::Float(ab, _) = av else { return Err(outside_err()) };
                        let r = match f {
                            FloatTy::F64 => {
                                let (x, y) = (f64::from_bits(bits), f64::from_bits(ab));
                                if name == "max" { x.max(y).to_bits() } else { x.min(y).to_bits() }
                            }
                            FloatTy::F32 => {
                                let (x, y) = (f32::from_bits(bits as u32), f32::from_bits(ab as u32));
                                if name == "max" { x.max(y).to_bits() as u64 } else { x.min(y).to_bits() as u64 }
                            }
                        };
                        Ok((ConstValue::Float(r, f), rt))
                    }
                    _ => Err(outside_err()),
                }
            }
            ConstValue::Variant(variant, vals) if cx.tys_ref().option_elem(rt).is_some() => {
                let (variant, vals) = (*variant, vals.clone());
                let elem = cx.tys_ref().option_elem(rt).unwrap_or(ERROR);
                match name.as_str() {
                    "is_some" if no_args(args) => Ok((ConstValue::Bool(variant == 1), BOOL)),
                    "is_none" if no_args(args) => Ok((ConstValue::Bool(variant != 1), BOOL)),
                    "unwrap" if no_args(args) => {
                        if variant == 1 && vals.len() == 1 {
                            Ok((vals.into_iter().next().unwrap(), elem))
                        } else {
                            Err(outside(span, "this `unwrap` on `None`"))
                        }
                    }
                    "expect" if args.len() == 1 => {
                        let _ = self.value(cx, env, args[0], None)?;
                        if variant == 1 && vals.len() == 1 {
                            Ok((vals.into_iter().next().unwrap(), elem))
                        } else {
                            Err(outside(span, "this `expect` on `None`"))
                        }
                    }
                    _ => Err(outside_err()),
                }
            }
            ConstValue::Aggregate(_) | ConstValue::Repeat(..) | ConstValue::Ref(_) => {
                // A slice or array receiver. The element type comes
                // from the receiver type, through its reference.
                let elem = match cx.tys_ref().kind(rt) {
                    TyKind::Array(el, _) | TyKind::Slice(el) => Some(el),
                    TyKind::Ref(_, _, inner) => match cx.tys_ref().kind(inner) {
                        TyKind::Array(el, _) | TyKind::Slice(el) => Some(el),
                        _ => None,
                    },
                    _ => None,
                };
                let Some(elem) = elem else { return Err(outside_err()) };
                let _ = elem;
                match name.as_str() {
                    "len" if no_args(args) => match self.seq_len(&rv) {
                        Some(n) => Ok((ConstValue::Int(n as i128), USIZE)),
                        None => Err(outside_err()),
                    },
                    "is_empty" if no_args(args) => match self.seq_len(&rv) {
                        Some(n) => Ok((ConstValue::Bool(n == 0), BOOL)),
                        None => Err(outside_err()),
                    },
                    "is_ascii" if no_args(args) && self.int_ty_of(cx, elem) == Some(IntTy::U8) => match self.seq_bytes(&rv) {
                        Some(bs) => Ok((ConstValue::Bool(bs.iter().all(|b| b.is_ascii())), BOOL)),
                        None => Err(outside_err()),
                    },
                    _ => Err(outside_err()),
                }
            }
            _ => Err(outside_err()),
        }
    }

    /// One integer argument of a const method call, evaluated at
    /// the argument's own type.
    fn int_arg<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        e: ExprId,
        ty: Ty,
        span: Span,
    ) -> Result<i128, Diag> {
        let (v, _) = self.value(cx, env, e, Some(ty))?;
        match v {
            ConstValue::Int(i) => Ok(i),
            _ => Err(outside(span, "method calls")),
        }
    }

    /// Inherent integer methods in const position. Every operation
    /// runs at the receiver's own width, like `int_op`: the plain
    /// forms error on overflow (rustc E0080), the `checked_` forms
    /// answer `None`, and the `saturating_` and `wrapping_` forms
    /// clamp and wrap. Signed-only methods reject unsigned
    /// receivers and the reverse, so a call rustc would not type
    /// never evaluates here either.
    fn int_method<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        x: i128,
        rt: Ty,
        name: &str,
        args: &[ExprId],
        expected: Option<Ty>,
        span: Span,
    ) -> Result<TypedValue, Diag> {
        let outside_err = || outside(span, "method calls");
        // `u8` methods that are not integer methods at all.
        if self.int_ty_of(cx, rt) == Some(IntTy::U8) && (name.starts_with("is_ascii") || name.starts_with("to_ascii")) {
            if args.is_empty() {
                let b = x as u8;
                let bool_v = |v: bool| Ok((ConstValue::Bool(v), BOOL));
                return match name {
                    "is_ascii" => bool_v(b.is_ascii()),
                    "is_ascii_alphabetic" => bool_v(b.is_ascii_alphabetic()),
                    "is_ascii_alphanumeric" => bool_v(b.is_ascii_alphanumeric()),
                    "is_ascii_digit" => bool_v(b.is_ascii_digit()),
                    "is_ascii_whitespace" => bool_v(b.is_ascii_whitespace()),
                    "is_ascii_uppercase" => bool_v(b.is_ascii_uppercase()),
                    "is_ascii_lowercase" => bool_v(b.is_ascii_lowercase()),
                    "is_ascii_hexdigit" => bool_v(b.is_ascii_hexdigit()),
                    "is_ascii_punctuation" => bool_v(b.is_ascii_punctuation()),
                    "is_ascii_graphic" => bool_v(b.is_ascii_graphic()),
                    "is_ascii_control" => bool_v(b.is_ascii_control()),
                    "to_ascii_lowercase" => Ok((ConstValue::Int(b.to_ascii_lowercase() as i128), rt)),
                    "to_ascii_uppercase" => Ok((ConstValue::Int(b.to_ascii_uppercase() as i128), rt)),
                    _ => Err(outside_err()),
                };
            }
        }
        // The receiver type runs the operation. A wide (i128)
        // receiver from an unsuffixed literal keeps running wide,
        // like `int_op`; the item coercion range-checks the result
        // where it meets its declared type.
        let _ = expected;
        let it = self.int_ty_of(cx, rt).unwrap_or(IntTy::I128);
        let signed = it.signed();
        let width = it.bits();
        let mask: u128 = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
        let xb = int_bits(x, it);
        let xs = truncate_to_int(x, it);
        let lo = int_min(it);
        let hi_s: i128 = if width >= 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
        let over = || outside(span, "this method call (overflow or division by zero)");
        let int_v = |v: i128| Ok((ConstValue::Int(v), rt));
        let bits_v = |u: u128| Ok((ConstValue::Int(int_from_bits(u & mask, it)), rt));
        let bool_v = |b: bool| Ok((ConstValue::Bool(b), BOOL));
        let u32_v = |v: u32| Ok((ConstValue::Int(v as i128), super::int(IntTy::U32)));
        // The unsigned counterpart type, for `unsigned_abs` and `abs_diff`.
        let unsigned_it = match it {
            IntTy::I8 => IntTy::U8,
            IntTy::I16 => IntTy::U16,
            IntTy::I32 => IntTy::U32,
            IntTy::I64 => IntTy::U64,
            IntTy::Isize => IntTy::Usize,
            IntTy::I128 => IntTy::U128,
            u => u,
        };
        if args.is_empty() {
            return match name {
                "abs" if signed => {
                    if xs == lo {
                        Err(over())
                    } else {
                        int_v(xs.abs())
                    }
                }
                "unsigned_abs" if signed => Ok((ConstValue::Int(int_from_bits(xs.unsigned_abs(), unsigned_it)), super::int(unsigned_it))),
                "signum" if signed => int_v(xs.signum()),
                "is_positive" if signed => bool_v(xs > 0),
                "is_negative" if signed => bool_v(xs < 0),
                "count_ones" => u32_v(xb.count_ones()),
                "count_zeros" => u32_v(width - xb.count_ones()),
                "leading_zeros" => u32_v(xb.leading_zeros() - (128 - width)),
                "trailing_zeros" => u32_v(if xb == 0 { width } else { xb.trailing_zeros() }),
                "leading_ones" => u32_v((!xb & mask).leading_zeros() - (128 - width)),
                "trailing_ones" => u32_v(if (!xb & mask) == 0 { width } else { (!xb & mask).trailing_zeros() }),
                "reverse_bits" => bits_v(xb.reverse_bits() >> (128 - width)),
                "swap_bytes" => bits_v(xb.swap_bytes() >> (128 - width)),
                "to_be" => bits_v(if cfg!(target_endian = "little") { xb.swap_bytes() >> (128 - width) } else { xb }),
                "to_le" => bits_v(if cfg!(target_endian = "little") { xb } else { xb.swap_bytes() >> (128 - width) }),
                "to_be_bytes" | "to_le_bytes" | "to_ne_bytes" => {
                    let n = (width / 8) as usize;
                    let be = name == "to_be_bytes" || (name == "to_ne_bytes" && cfg!(target_endian = "big"));
                    let vals: Vec<ConstValue> = (0..n)
                        .map(|i| {
                            let shift = if be { 8 * (n - 1 - i) } else { 8 * i };
                            ConstValue::Int(((xb >> shift) & 0xFF) as i128)
                        })
                        .collect();
                    let c = cx.tys().intern_const(super::ConstKind::Int(n as u128));
                    let t = cx.tys().intern(TyKind::Array(super::int(IntTy::U8), c));
                    Ok((ConstValue::Aggregate(vals), t))
                }
                "checked_neg" => {
                    let r = if signed {
                        if xs == lo { None } else { Some(-xs) }
                    } else if xb == 0 {
                        Some(0)
                    } else {
                        None
                    };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                "saturating_neg" => {
                    if signed {
                        int_v(if xs == lo { hi_s } else { -xs })
                    } else {
                        int_v(0)
                    }
                }
                "wrapping_neg" => bits_v(0u128.wrapping_sub(xb)),
                "checked_abs" if signed => {
                    let r = if xs == lo { None } else { Some(xs.abs()) };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                "saturating_abs" if signed => int_v(if xs == lo { hi_s } else { xs.abs() }),
                "wrapping_abs" if signed => int_v(if xs == lo { lo } else { xs.abs() }),
                "isqrt" if !signed => bits_v(xb.isqrt()),
                "is_power_of_two" if !signed => bool_v(xb != 0 && (xb & (xb - 1)) == 0),
                "next_power_of_two" if !signed => {
                    if xb == 0 {
                        bits_v(1)
                    } else {
                        let p = 1u128.checked_shl(128 - (xb - 1).leading_zeros()).unwrap_or(0);
                        if p == 0 || p > mask {
                            Err(over())
                        } else {
                            bits_v(p)
                        }
                    }
                }
                "ilog2" | "ilog10" => {
                    if xb == 0 || (signed && xs < 0) {
                        Err(outside(span, "this method call (logarithm of a non-positive value)"))
                    } else if name == "ilog2" {
                        u32_v(127 - xb.leading_zeros())
                    } else {
                        u32_v(xb.ilog10())
                    }
                }
                "checked_ilog2" | "checked_ilog10" => {
                    let r = if xb == 0 || (signed && xs < 0) {
                        None
                    } else if name == "checked_ilog2" {
                        Some(127 - xb.leading_zeros())
                    } else {
                        Some(xb.ilog10())
                    };
                    Ok(self.opt_value(cx, super::int(IntTy::U32), r.map(|v| ConstValue::Int(v as i128))))
                }
                _ => Err(outside_err()),
            };
        }
        if args.len() != 1 {
            return Err(outside_err());
        }
        self.int_method_arg(cx, env, it, rt, xs, xb, name, args[0], span)
    }

    /// The one-argument integer methods: the arithmetic families,
    /// shifts and rotates, and the euclid and difference forms.
    #[allow(clippy::too_many_arguments)]
    fn int_method_arg<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        it: IntTy,
        rt: Ty,
        xs: i128,
        xb: u128,
        name: &str,
        arg: ExprId,
        span: Span,
    ) -> Result<TypedValue, Diag> {
        let outside_err = || outside(span, "method calls");
        let over = || outside(span, "this method call (overflow or division by zero)");
        let signed = it.signed();
        let width = it.bits();
        let mask: u128 = if width >= 128 { u128::MAX } else { (1u128 << width) - 1 };
        let lo = int_min(it);
        let hi_s: i128 = if width >= 128 { i128::MAX } else { (1i128 << (width - 1)) - 1 };
        let int_v = |v: i128| Ok((ConstValue::Int(v), rt));
        let bits_v = |u: u128| Ok((ConstValue::Int(int_from_bits(u & mask, it)), rt));
        // Shifts, rotates, powers, and logarithms take a `u32`.
        if matches!(
            name,
            "pow" | "checked_pow" | "saturating_pow" | "wrapping_pow" | "checked_shl" | "checked_shr" | "wrapping_shl"
                | "wrapping_shr" | "rotate_left" | "rotate_right" | "ilog" | "checked_ilog"
        ) {
            let a = self.int_arg(cx, env, arg, super::int(IntTy::U32), span)?;
            let amt = u32::try_from(a).map_err(|_| outside_err())?;
            return match name {
                "pow" => {
                    let r = if signed { xs.checked_pow(amt).filter(|&r| fits(r, it)) } else { None };
                    let r = if signed { r } else { xb.checked_pow(amt).filter(|&r| r <= mask).map(|r| int_from_bits(r, it)) };
                    match r {
                        Some(r) => int_v(r),
                        None => Err(over()),
                    }
                }
                "checked_pow" => {
                    let r = if signed {
                        xs.checked_pow(amt).filter(|&r| fits(r, it))
                    } else {
                        xb.checked_pow(amt).filter(|&r| r <= mask).map(|r| int_from_bits(r, it))
                    };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                "saturating_pow" => {
                    if signed {
                        match xs.checked_pow(amt) {
                            Some(r) if fits(r, it) => int_v(r),
                            _ => int_v(if xs < 0 && amt % 2 == 1 { lo } else { hi_s }),
                        }
                    } else {
                        match xb.checked_pow(amt) {
                            Some(r) if r <= mask => bits_v(r),
                            _ => bits_v(mask),
                        }
                    }
                }
                "wrapping_pow" => {
                    let (mut base, mut acc, mut e) = (xb, 1u128, amt);
                    while e > 0 {
                        if e & 1 == 1 {
                            acc = acc.wrapping_mul(base) & mask;
                        }
                        base = base.wrapping_mul(base) & mask;
                        e >>= 1;
                    }
                    bits_v(acc)
                }
                "checked_shl" => {
                    let r = if amt >= width { None } else { Some(int_from_bits(xb << amt, it)) };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                "checked_shr" => {
                    let r = if amt >= width {
                        None
                    } else if signed {
                        Some(xs >> amt)
                    } else {
                        Some(int_from_bits(xb >> amt, it))
                    };
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                }
                "wrapping_shl" => bits_v(xb << (amt % width)),
                "wrapping_shr" => {
                    if signed {
                        int_v(xs >> (amt % width))
                    } else {
                        bits_v(xb >> (amt % width))
                    }
                }
                "rotate_left" | "rotate_right" => {
                    let r = amt % width;
                    if r == 0 {
                        bits_v(xb)
                    } else if name == "rotate_left" {
                        bits_v((xb << r) | (xb >> (width - r)))
                    } else {
                        bits_v((xb >> r) | (xb << (width - r)))
                    }
                }
                "ilog" | "checked_ilog" => {
                    let ok = amt >= 2 && xb != 0 && (!signed || xs > 0);
                    if name == "ilog" {
                        if ok {
                            Ok((ConstValue::Int(xb.ilog(amt as u128) as i128), super::int(IntTy::U32)))
                        } else {
                            Err(outside(span, "this method call (logarithm of a non-positive value)"))
                        }
                    } else {
                        let r = if ok { Some(xb.ilog(amt as u128)) } else { None };
                        Ok(self.opt_value(cx, super::int(IntTy::U32), r.map(|v| ConstValue::Int(v as i128))))
                    }
                }
                _ => Err(outside_err()),
            };
        }
        let y = self.int_arg(cx, env, arg, rt, span)?;
        let yb = int_bits(y, it);
        let ys = truncate_to_int(y, it);
        // One checked operation per family letter: `a`dd, `s`ub,
        // `m`ul, `d`iv, `r`em, each at the receiver width.
        let checked = |op: u8| -> Option<i128> {
            if signed {
                let r = match op {
                    b'a' => xs.checked_add(ys),
                    b's' => xs.checked_sub(ys),
                    b'm' => xs.checked_mul(ys),
                    b'd' => {
                        if ys == 0 || (xs == lo && ys == -1) {
                            None
                        } else {
                            Some(xs / ys)
                        }
                    }
                    b'r' => {
                        if ys == 0 || (xs == lo && ys == -1) {
                            None
                        } else {
                            Some(xs % ys)
                        }
                    }
                    _ => None,
                };
                r.filter(|&r| fits(r, it))
            } else {
                let r = match op {
                    b'a' => xb.checked_add(yb),
                    b's' => xb.checked_sub(yb),
                    b'm' => xb.checked_mul(yb),
                    b'd' => xb.checked_div(yb),
                    b'r' => xb.checked_rem(yb),
                    _ => None,
                };
                r.filter(|&r| r <= mask).map(|r| int_from_bits(r, it))
            }
        };
        let fam = |name: &str| -> Option<(u8, u8)> {
            let (kind, op) = name.split_once('_')?;
            let k = match kind {
                "checked" => b'c',
                "saturating" => b't',
                "wrapping" => b'w',
                _ => return None,
            };
            let o = match op {
                "add" => b'a',
                "sub" => b's',
                "mul" => b'm',
                "div" => b'd',
                "rem" => b'r',
                _ => return None,
            };
            Some((k, o))
        };
        if let Some((kind, op)) = fam(name) {
            return match kind {
                b'c' => Ok(self.opt_value(cx, rt, checked(op).map(ConstValue::Int))),
                b'w' => {
                    match op {
                        b'a' => bits_v(xb.wrapping_add(yb)),
                        b's' => bits_v(xb.wrapping_sub(yb)),
                        b'm' => bits_v(xb.wrapping_mul(yb)),
                        b'd' => {
                            if yb == 0 {
                                Err(over())
                            } else if signed {
                                int_v(if xs == lo && ys == -1 { lo } else { xs / ys })
                            } else {
                                bits_v(xb / yb)
                            }
                        }
                        _ => {
                            if yb == 0 {
                                Err(over())
                            } else if signed {
                                int_v(if xs == lo && ys == -1 { 0 } else { xs % ys })
                            } else {
                                bits_v(xb % yb)
                            }
                        }
                    }
                }
                _ => {
                    // Saturating: division by zero still panics in
                    // rustc, so it stays an error here.
                    if matches!(op, b'd' | b'r') && yb == 0 {
                        return Err(over());
                    }
                    match checked(op) {
                        Some(r) => int_v(r),
                        None => {
                            if signed {
                                // Overflow direction: a negative
                                // operand pairing saturates low.
                                let low = match op {
                                    b'a' => xs < 0,
                                    b's' => xs < 0 || ys > 0 && xs < ys,
                                    b'm' => (xs < 0) != (ys < 0),
                                    b'd' => (xs < 0) != (ys < 0),
                                    _ => false,
                                };
                                int_v(if low { lo } else { hi_s })
                            } else {
                                bits_v(if op == b's' { 0 } else { mask })
                            }
                        }
                    }
                }
            };
        }
        match name {
            "div_euclid" | "rem_euclid" | "checked_div_euclid" | "checked_rem_euclid" => {
                let r: Option<i128> = if yb == 0 || (signed && xs == lo && ys == -1) {
                    None
                } else if signed {
                    Some(if name.ends_with("div_euclid") { xs.div_euclid(ys) } else { xs.rem_euclid(ys) })
                } else {
                    Some(int_from_bits(if name.ends_with("div_euclid") { xb / yb } else { xb % yb }, it))
                };
                if name.starts_with("checked") {
                    Ok(self.opt_value(cx, rt, r.map(ConstValue::Int)))
                } else {
                    match r {
                        Some(r) => int_v(r),
                        None => Err(over()),
                    }
                }
            }
            "abs_diff" => {
                let d = xb.abs_diff(yb);
                // For signed receivers the bits difference equals
                // the value difference, at the unsigned counterpart.
                let d = if signed { xs.abs_diff(ys) } else { d };
                let ut = match it {
                    IntTy::I8 => IntTy::U8,
                    IntTy::I16 => IntTy::U16,
                    IntTy::I32 => IntTy::U32,
                    IntTy::I64 => IntTy::U64,
                    IntTy::Isize => IntTy::Usize,
                    IntTy::I128 => IntTy::U128,
                    u => u,
                };
                Ok((ConstValue::Int(int_from_bits(d, ut)), super::int(ut)))
            }
            "midpoint" => {
                if signed {
                    int_v(xs.midpoint(ys))
                } else {
                    bits_v(xb.midpoint(yb))
                }
            }
            "eq_ignore_ascii_case" if it == IntTy::U8 => Ok((ConstValue::Bool((xb as u8).eq_ignore_ascii_case(&(yb as u8))), BOOL)),
            _ => Err(outside_err()),
        }
    }

    /// `char` and `u8` ASCII predicates and case maps, plus the
    /// other const `char` methods. The host `char` and `u8`
    /// implementations carry rustc's own results.
    fn char_method<'a, C: ConstCx<'a>>(
        &mut self,
        cx: &mut C,
        env: &mut Env,
        c: char,
        name: &str,
        args: &[ExprId],
        span: Span,
    ) -> Result<TypedValue, Diag> {
        let outside_err = || outside(span, "method calls");
        let bool_v = |b: bool| Ok((ConstValue::Bool(b), BOOL));
        match name {
            "is_ascii" if args.is_empty() => bool_v(c.is_ascii()),
            "is_ascii_alphabetic" if args.is_empty() => bool_v(c.is_ascii_alphabetic()),
            "is_ascii_alphanumeric" if args.is_empty() => bool_v(c.is_ascii_alphanumeric()),
            "is_ascii_digit" if args.is_empty() => bool_v(c.is_ascii_digit()),
            "is_ascii_whitespace" if args.is_empty() => bool_v(c.is_ascii_whitespace()),
            "is_ascii_uppercase" if args.is_empty() => bool_v(c.is_ascii_uppercase()),
            "is_ascii_lowercase" if args.is_empty() => bool_v(c.is_ascii_lowercase()),
            "is_ascii_hexdigit" if args.is_empty() => bool_v(c.is_ascii_hexdigit()),
            "is_ascii_punctuation" if args.is_empty() => bool_v(c.is_ascii_punctuation()),
            "is_ascii_graphic" if args.is_empty() => bool_v(c.is_ascii_graphic()),
            "is_ascii_control" if args.is_empty() => bool_v(c.is_ascii_control()),
            // The const Unicode predicates. is_alphabetic, is_numeric, and
            // is_alphanumeric are not const fns in rustc 1.99, so they stay
            // outside the evaluator and reject, as rustc does.
            "is_lowercase" if args.is_empty() => bool_v(c.is_lowercase()),
            "is_uppercase" if args.is_empty() => bool_v(c.is_uppercase()),
            "is_whitespace" if args.is_empty() => bool_v(c.is_whitespace()),
            "is_control" if args.is_empty() => bool_v(c.is_control()),
            "to_ascii_lowercase" if args.is_empty() => Ok((ConstValue::Char(c.to_ascii_lowercase()), CHAR)),
            "to_ascii_uppercase" if args.is_empty() => Ok((ConstValue::Char(c.to_ascii_uppercase()), CHAR)),
            "len_utf8" if args.is_empty() => Ok((ConstValue::Int(c.len_utf8() as i128), USIZE)),
            "len_utf16" if args.is_empty() => Ok((ConstValue::Int(c.len_utf16() as i128), USIZE)),
            "to_digit" if args.len() == 1 => {
                let (av, _) = self.value(cx, env, args[0], Some(super::int(IntTy::U32)))?;
                let ConstValue::Int(r) = av else { return Err(outside_err()) };
                // `to_digit` panics outside radix 2..=36; a const panic is
                // a reject here (and the host call must not run).
                let radix = u32::try_from(r).map_err(|_| outside_err())?;
                if !(2..=36).contains(&radix) {
                    return Err(outside(span, "this `to_digit` radix (outside 2 to 36)"));
                }
                let v = c.to_digit(radix).map(|d| ConstValue::Int(d as i128));
                Ok(self.opt_value(cx, super::int(IntTy::U32), v))
            }
            "is_digit" if args.len() == 1 => {
                let (av, _) = self.value(cx, env, args[0], Some(super::int(IntTy::U32)))?;
                let ConstValue::Int(r) = av else { return Err(outside_err()) };
                let radix = u32::try_from(r).map_err(|_| outside_err())?;
                if !(2..=36).contains(&radix) {
                    return Err(outside(span, "this `is_digit` radix (outside 2 to 36)"));
                }
                bool_v(c.is_digit(radix))
            }
            _ => Err(outside_err()),
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
                // A plain name that resolves to a const item compares
                // against it, as the checker resolves it; a unit
                // struct name matches its only value.
                if !mutable && !env.iter().any(|(n, _, _)| n == name) {
                    if let Some((cv, _)) = cx.const_item(*name) {
                        return Ok(values_eq(v, &cv));
                    }
                    let segs = [ast::PathSeg::plain(*name)];
                    if let Some((_, variant, _)) = cx.unit_variant(&segs, Some(t)) {
                        return Ok(matches!(v, ConstValue::Variant(got, _) if *got == variant)
                            || matches!(v, ConstValue::Aggregate(_)));
                    }
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
                // A float range compares with `partial_cmp`: a NaN
                // scrutinee matches no range, as in rustc.
                if let ConstValue::Float(bits, ft) = v {
                    let n = match ft {
                        FloatTy::F32 => f32::from_bits(*bits as u32) as f64,
                        FloatTy::F64 => f64::from_bits(*bits),
                    };
                    let fbound = |hv: &ConstValue| match hv {
                        ConstValue::Float(b, FloatTy::F32) => Some(f32::from_bits(*b as u32) as f64),
                        ConstValue::Float(b, FloatTy::F64) => Some(f64::from_bits(*b)),
                        _ => None,
                    };
                    if let Some(lo) = lo {
                        let (lv, _) = self.value(cx, env, *lo, Some(t))?;
                        let Some(l) = fbound(&lv) else { return Ok(false) };
                        if !(n >= l) {
                            return Ok(false);
                        }
                    }
                    if let Some(hi) = hi {
                        let (hv, _) = self.value(cx, env, *hi, Some(t))?;
                        let Some(h) = fbound(&hv) else { return Ok(false) };
                        if *inclusive {
                            if !(n <= h) {
                                return Ok(false);
                            }
                        } else if !(n < h) {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
                let num = match v {
                    ConstValue::Int(i) => Some(*i),
                    ConstValue::Char(c) => Some(*c as i128),
                    _ => None,
                };
                let Some(n) = num else { return Ok(false) };
                let it = self.int_ty_of(cx, t);
                let bound = |hv: ConstValue| match hv {
                    ConstValue::Int(h) => Some(h),
                    ConstValue::Char(c) => Some(c as i128),
                    _ => None,
                };
                if let Some(lo) = lo {
                    let (lv, _) = self.value(cx, env, *lo, Some(t))?;
                    let Some(l) = bound(lv) else { return Ok(false) };
                    if cmp_int(n, l, it) == std::cmp::Ordering::Less {
                        return Ok(false);
                    }
                }
                if let Some(hi) = hi {
                    let (hv, _) = self.value(cx, env, *hi, Some(t))?;
                    let Some(h) = bound(hv) else { return Ok(false) };
                    let c = cmp_int(n, h, it);
                    if *inclusive {
                        if c == std::cmp::Ordering::Greater {
                            return Ok(false);
                        }
                    } else if c != std::cmp::Ordering::Less {
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
                // Result patterns by name: Ok is variant 0, Err is 1.
                if let ConstValue::Variant(variant, fields) = &v
                    && let Some((ok_ty, err_ty)) = cx.tys_ref().result_args(t)
                {
                    let want_ok = cx.sym_text(segs[segs.len() - 1].name) == "Ok";
                    let want_err = cx.sym_text(segs[segs.len() - 1].name) == "Err";
                    if (want_ok && *variant == 0) || (want_err && *variant == 1) {
                        if let Pat::TupleStruct { elems, .. } = cx.ast().pat(pat)
                            && elems.len() == 1
                        {
                            let elem_ty = if want_ok { ok_ty } else { err_ty };
                            return self.match_pat(cx, env, elems[0], &fields[0].clone(), elem_ty, _in_match, binds);
                        }
                        return Ok(true);
                    }
                    if want_ok || want_err {
                        return Ok(false);
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
                // Privacy of the fields this pattern names. A tuple
                // struct pattern names its constructor, so any
                // private field rejects, rest or not; a struct
                // pattern names only its written fields.
                match cx.ast().pat(pat) {
                    Pat::TupleStruct { .. } if !cx.is_enum(adt) => {
                        self.check_tuple_ctor(cx, adt, field_defs.len(), span)?;
                    }
                    Pat::Struct { fields, .. } => {
                        for &(fname, _) in fields {
                            self.check_named_field(cx, adt, fname, span)?;
                        }
                    }
                    _ => {}
                }
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

    /// Checks every field step of an assignment place for privacy,
    /// innermost first (a read of each step is what the write does).
    fn check_place_fields<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &Env, e: ExprId, span: Span) -> Result<(), Diag> {
        match cx.ast().expr(e) {
            Expr::Field { base, name } => {
                self.check_place_fields(cx, env, *base, span)?;
                let Some(bt) = self.place_ty(cx, env, *base) else { return Ok(()) };
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                if let Some(adt) = cx.tys_ref().local_adt(bt) {
                    self.check_named_field(cx, adt, *name, span)?;
                }
                Ok(())
            }
            Expr::TupleField { base, index } => {
                self.check_place_fields(cx, env, *base, span)?;
                let Some(bt) = self.place_ty(cx, env, *base) else { return Ok(()) };
                let bt = match cx.tys_ref().kind(bt) {
                    TyKind::Ref(_, _, inner) => inner,
                    _ => bt,
                };
                if !matches!(cx.tys_ref().kind(bt), TyKind::Tuple(_))
                    && let Some(adt) = cx.tys_ref().local_adt(bt)
                {
                    self.check_tuple_field(cx, adt, *index, span)?;
                }
                Ok(())
            }
            Expr::Deref(inner) => self.check_place_fields(cx, env, *inner, span),
            Expr::Index { base, .. } => self.check_place_fields(cx, env, *base, span),
            _ => Ok(()),
        }
    }

    /// Assigns `v` into the place `e` denotes in the environment.
    fn assign_place<'a, C: ConstCx<'a>>(&mut self, cx: &mut C, env: &mut Env, e: ExprId, v: ConstValue, span: Span) -> Result<(), Diag> {
        self.check_place_fields(cx, env, e, span)?;
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
                // A `[x; n]` local starts as a repeat value; writing
                // one element first spreads it into an aggregate.
                if let ConstValue::Repeat(x, n) = &*slot {
                    let agg = ConstValue::Aggregate(vec![(**x).clone(); *n as usize]);
                    *slot = agg;
                }
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

/// A float type's own associated consts (`f64::NAN`, `f32::EPSILON`,
/// `f64::MAX_EXP`). Returns the float bits, or an integer value with
/// its integer type for the count and exponent consts.
pub fn primitive_float_assoc(f: FloatTy, item: &str) -> Option<(u64, Option<IntTy>)> {
    let flt = |v: f64| match f {
        FloatTy::F64 => (v.to_bits(), None),
        FloatTy::F32 => ((v as f32).to_bits() as u64, None),
    };
    let int = |v: i64, signed: bool| (v as u64, Some(if signed { IntTy::I32 } else { IntTy::U32 }));
    // The float consts are taken from the compiler's own std, which
    // carries the same values as the Rust the checked program means.
    let out = match (f, item) {
        (_, "NAN") => flt(f64::NAN),
        (_, "INFINITY") => flt(f64::INFINITY),
        (_, "NEG_INFINITY") => flt(f64::NEG_INFINITY),
        (FloatTy::F64, "MAX") => flt(f64::MAX),
        (FloatTy::F32, "MAX") => flt(f32::MAX as f64),
        (FloatTy::F64, "MIN") => flt(f64::MIN),
        (FloatTy::F32, "MIN") => flt(f32::MIN as f64),
        (FloatTy::F64, "MIN_POSITIVE") => flt(f64::MIN_POSITIVE),
        (FloatTy::F32, "MIN_POSITIVE") => flt(f32::MIN_POSITIVE as f64),
        (FloatTy::F64, "EPSILON") => flt(f64::EPSILON),
        (FloatTy::F32, "EPSILON") => (f32::EPSILON.to_bits() as u64, None),
        (_, "RADIX") => int(2, false),
        (FloatTy::F64, "MANTISSA_DIGITS") => int(f64::MANTISSA_DIGITS as i64, false),
        (FloatTy::F32, "MANTISSA_DIGITS") => int(f32::MANTISSA_DIGITS as i64, false),
        (FloatTy::F64, "DIGITS") => int(f64::DIGITS as i64, false),
        (FloatTy::F32, "DIGITS") => int(f32::DIGITS as i64, false),
        (FloatTy::F64, "MIN_EXP") => int(f64::MIN_EXP as i64, true),
        (FloatTy::F32, "MIN_EXP") => int(f32::MIN_EXP as i64, true),
        (FloatTy::F64, "MAX_EXP") => int(f64::MAX_EXP as i64, true),
        (FloatTy::F32, "MAX_EXP") => int(f32::MAX_EXP as i64, true),
        (FloatTy::F64, "MIN_10_EXP") => int(f64::MIN_10_EXP as i64, true),
        (FloatTy::F32, "MIN_10_EXP") => int(f32::MIN_10_EXP as i64, true),
        (FloatTy::F64, "MAX_10_EXP") => int(f64::MAX_10_EXP as i64, true),
        (FloatTy::F32, "MAX_10_EXP") => int(f32::MAX_10_EXP as i64, true),
        _ => return None,
    };
    Some(out)
}

/// The `std::f32::consts` and `std::f64::consts` values, as bits.
pub fn float_consts_value(f: FloatTy, item: &str) -> Option<u64> {
    use std::f64::consts as d;
    let v = match item {
        "PI" => d::PI,
        "TAU" => d::TAU,
        "FRAC_PI_2" => d::FRAC_PI_2,
        "FRAC_PI_3" => d::FRAC_PI_3,
        "FRAC_PI_4" => d::FRAC_PI_4,
        "FRAC_PI_6" => d::FRAC_PI_6,
        "FRAC_PI_8" => d::FRAC_PI_8,
        "FRAC_1_PI" => d::FRAC_1_PI,
        "FRAC_2_PI" => d::FRAC_2_PI,
        "FRAC_2_SQRT_PI" => d::FRAC_2_SQRT_PI,
        "SQRT_2" => d::SQRT_2,
        "FRAC_1_SQRT_2" => d::FRAC_1_SQRT_2,
        "E" => d::E,
        "LOG2_E" => d::LOG2_E,
        "LOG10_E" => d::LOG10_E,
        "LN_2" => d::LN_2,
        "LN_10" => d::LN_10,
        "LOG2_10" => d::LOG2_10,
        "LOG10_2" => d::LOG10_2,
        _ => return None,
    };
    Some(match f {
        FloatTy::F64 => v.to_bits(),
        // std::f32::consts holds each value rounded to f32, which is
        // the f64 value cast to f32 (the values are not near ties).
        FloatTy::F32 => (v as f32).to_bits() as u64,
    })
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
