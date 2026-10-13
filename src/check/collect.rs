// Collection: builds the item tables (types, functions, methods) and resolves all signatures.
// This is the only stage that runs in sequence. Function bodies are checked after it, in parallel.
use crate::ast::{self, Ast, ItemKind, SelfKind, TyExpr, VariantFields};
use crate::check::generics::{self, GenTables};
pub use crate::def::{CrateId, DefId, DefPathHash, LocalDefId, StableCrateHash};
use crate::def::{CrateIds, DiskDefId};
use crate::diag::{Diag, Span, not_yet, unsupported};
use crate::intern::FxMap as HashMap;
use crate::intern::{Interner, Known, Sym};
use crate::ty::defs::{DefKind as DefsKind, Vis};
use crate::ty::lang::ShippedCrate;
use crate::ty::*;

#[derive(Clone, Copy, Debug, Default)]
pub struct Derives {
    pub debug: bool,
    pub clone: bool,
    pub copy: bool,
    pub partial_eq: bool,
    pub eq: bool,
    pub hash: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VariantShape {
    Unit,
    Tuple,
    Named,
}

pub struct Field {
    pub name: Sym,
    pub ty: Ty,
}

pub struct Variant {
    pub name: Sym,
    pub shape: VariantShape,
    pub fields: Vec<Field>,
    /// The discriminant value (explicit, or the previous variant's plus one).
    pub disc: i128,
}

pub struct AdtDef {
    pub name: Sym,
    pub is_enum: bool,
    /// A struct has exactly one variant, named after the struct.
    pub variants: Vec<Variant>,
    pub derives: Derives,
    pub span: Span,
    /// The `repr` of the type, in layout terms.
    pub repr: crate::ty::layout::Repr,
}

/// One evaluated `const` item.
pub struct ConstItem {
    pub name: Sym,
    pub ty: Ty,
    pub value: crate::ty::consteval::ConstValue,
}

/// What one item inside a function body resolved to, by `Ast::stmt_items`
/// index. Nested statics live in the main statics table; nested consts get
/// their own values table because their names are block-scoped.
#[derive(Clone, Copy, Debug)]
pub enum BodyItem {
    Fn(LocalDefId),
    /// Index into `Program::body_consts`.
    Const(u32),
    /// Index into `Program::statics`.
    Static(u32),
}

/// One evaluated `static` item: its value becomes static data (ARCH 2.13).
pub struct StaticItem {
    pub name: Sym,
    pub ty: Ty,
    pub mutable: bool,
    pub value: crate::ty::consteval::ConstValue,
}

pub struct FnInfo<'a> {
    pub name: Sym,
    pub def: &'a ast::FnDef,
    pub owner: Option<AdtId>,
    pub self_kind: Option<SelfKind>,
    /// Parameter types, including `self` first when present.
    pub params: Vec<Ty>,
    pub ret: Ty,
    /// For a function that returns a reference: the index of the parameter it borrows from.
    pub ret_borrows_from: Option<usize>,
    /// True for a `const fn`, callable from const contexts (ARCH 2.13).
    pub is_const: bool,
}

/// The old name for the session-local function index. New code uses
/// `LocalDefId` (src/def.rs); the alias stays while S3b edits this file in
/// parallel, then goes.
#[allow(dead_code)]
pub type FnId = LocalDefId;

pub struct Program<'a> {
    pub ast: &'a Ast,
    pub interner: &'a Interner,
    pub known: &'a Known,
    pub tys: GlobalTys,
    /// The definition table (ARCH 2.2): kinds, parents, generics, and param envs by
    /// `DefId`, plus the bridge to the session-local `AdtId` compat tables below.
    pub defs: Defs,
    pub adts: Vec<AdtDef>,
    pub fns: Vec<FnInfo<'a>>,
    /// Evaluated const items, and name to index (ARCH 2.13).
    pub consts: Vec<ConstItem>,
    pub const_names: HashMap<Sym, u32>,
    /// Each const item's stable identity, in `consts` order.
    pub const_defs: Vec<DefId>,
    /// Each static item's stable identity, in `statics` order.
    pub static_defs: Vec<DefId>,
    /// Associated consts of inherent impls: (Adt, name) to an index
    /// into `consts`. They are const items like free consts, but not
    /// in `const_names`: a plain name must never find them.
    pub assoc_const_names: HashMap<(AdtId, Sym), u32>,
    /// Evaluated static items, and name to index. Codegen emits these as
    /// static data in the glue unit.
    pub statics: Vec<StaticItem>,
    pub static_names: HashMap<Sym, u32>,
    /// Items inside function bodies, by `Ast::stmt_items` index.
    pub body_items: HashMap<u32, BodyItem>,
    /// Evaluated consts declared inside function bodies.
    pub body_consts: Vec<ConstItem>,
    /// For a nested fn, the stmt item indexes of its containing block:
    /// the sibling items its body may name.
    pub fn_siblings: HashMap<LocalDefId, Vec<u32>>,
    pub type_names: HashMap<Sym, AdtId>,
    /// Non-generic type aliases by (flat) name, fully resolved.
    pub aliases: HashMap<Sym, Ty>,
    pub fn_names: HashMap<Sym, LocalDefId>,
    /// Inherent methods by (template Adt, name), in registration
    /// order. Several inherent impls of one Adt may define the
    /// same name under disjoint Self patterns (`impl W<u8>` and
    /// `impl W<u16>`); the probe unifies the receiver against
    /// each candidate, and the overlap check in `finish_collect`
    /// rejects patterns that can both apply.
    pub methods: HashMap<(AdtId, Sym), Vec<LocalDefId>>,
    pub main: Option<LocalDefId>,
    /// The crate this program was collected as: session-local id and stable hash.
    pub krate: CrateId,
    pub stable_crate: StableCrateHash,
    /// Each function's stable identity, in `fns` order (the `Vec<DefId>` side
    /// table of docs/ARCH.md section 1.7). User Adts carry their `DefId` in
    /// `defs` and in the type store, where `TyKind::Adt(DefId, ArgsId)` reads it.
    pub fn_defs: Vec<DefId>,
    /// The `LocalDefId` of a function by its stable hash (section 1.7).
    pub def_by_hash: HashMap<DefPathHash, LocalDefId>,
    /// Source std fns routed into this compile by the std loader (S5):
    /// full Rust path segments to the local fn that carries the body.
    /// Empty unless the driver spliced std source in. Filled by the
    /// driver after collection, from the loader's decl table.
    pub std_fns: Vec<(Vec<Sym>, LocalDefId)>,
    /// Byte ranges `(lo, hi)` of the root file that belong to a shipped
    /// library crate, with the crate. Spliced std source sits after the
    /// user file, so user spans never fall in a range: this is the
    /// provenance intrinsic privilege keys on (section 3.1 item 1).
    /// Empty when no std source was spliced. Filled by the driver.
    pub shipped_ranges: Vec<(u32, u32, ShippedCrate)>,
    /// The module binding tables of section 1.3, when the crate went
    /// through the resolver. Filled by the driver after collection; the
    /// S7 `Binding` query fns in driver/graph.rs read through it.
    pub resolved: Option<Box<crate::resolve::imports::ResolvedTables>>,
    /// The generic tables (traits, templates, instances) built by
    /// `check::generics` during collection and finished by mono.
    pub gx: GenTables<'a>,
}

impl<'a> Program<'a> {
    pub fn name(&self, s: Sym) -> &str {
        self.interner.get(s)
    }
    /// The source (short) name of a def name, for program output such
    /// as derived `Debug`: strips the resolver's flat-name module
    /// prefix (`m0$Stats` reads `Stats`, as rustc prints). Display
    /// only; lookups keep using `name`.
    pub fn display_name(&self, s: Sym) -> &str {
        crate::intern::source_name(self.interner.get(s))
    }
    /// The source path of a def name, for diagnostics (`m0::Stats`,
    /// `base::inner::Deep` for a source dependency). Reads the
    /// resolver's display table when it is attached; before that (in
    /// collect itself) it falls back to the path carried in the flat
    /// name, which lacks only a dependency's crate name.
    pub fn display_path(&self, s: Sym) -> String {
        if let Some(tables) = &self.resolved
            && let Some(&d) = tables.display_names.get(&s)
        {
            return self.interner.get(d).to_string();
        }
        crate::intern::source_path(self.interner.get(s))
    }
    pub fn adt(&self, id: AdtId) -> &AdtDef {
        &self.adts[id.0 as usize]
    }
    pub fn fn_info(&self, id: LocalDefId) -> &FnInfo<'a> {
        &self.fns[id.0 as usize]
    }
    /// A function's stable identity in this crate.
    #[allow(dead_code)] // First production readers are S3a defs and mono instance keys; tests use it now.
    pub fn def_id(&self, id: LocalDefId) -> DefId {
        self.fn_defs[id.0 as usize]
    }
    /// A function's disk identity: the only form that may enter disk or slot
    /// keys (docs/ARCH.md sections 1.7 and 8.4).
    #[allow(dead_code)] // See `def_id`.
    pub fn disk_id(&self, id: LocalDefId) -> DiskDefId {
        DiskDefId { krate: self.stable_crate, hash: self.def_id(id).hash }
    }
    /// The session-local id of the function with this stable hash, if this
    /// crate defines it.
    #[allow(dead_code)] // See `def_id`.
    pub fn local_def(&self, hash: DefPathHash) -> Option<LocalDefId> {
        self.def_by_hash.get(&hash).copied()
    }
    /// A user Adt's stable identity, as carried by `TyKind::Adt(DefId, ArgsId)`.
    #[allow(dead_code)] // First production readers are generic collect and mono; the store form is used now.
    pub fn def_of_adt(&self, id: AdtId) -> DefId {
        self.defs.def_of_adt(id).expect("ADT defs are recorded during collection")
    }
    /// The session-local index of the user Adt with this def, if this crate defines it.
    #[allow(dead_code)] // See `def_of_adt`.
    pub fn adt_by_def(&self, def: DefId) -> Option<AdtId> {
        self.defs.local_adt(def)
    }
    /// The index of the const item with this def, if this crate defines it.
    pub fn const_by_def(&self, def: DefId) -> Option<u32> {
        self.const_defs.iter().position(|&d| d == def).map(|i| i as u32)
    }
    /// The index of the static item with this def, if this crate defines it.
    pub fn static_by_def(&self, def: DefId) -> Option<u32> {
        self.static_defs.iter().position(|&d| d == def).map(|i| i as u32)
    }
    /// The shipped crate a span's source belongs to, if any. Only spans
    /// in spliced shipped source answer; every user span gets None.
    pub fn shipped_crate_at(&self, span: Span) -> Option<ShippedCrate> {
        if span.file != crate::diag::FileId(0) {
            return None;
        }
        self.shipped_ranges.iter().find(|(lo, hi, _)| span.lo >= *lo && span.lo < *hi).map(|(_, _, k)| *k)
    }
    /// The shipped crate that defines function `f`, if it is a shipped
    /// (spliced std) fn. Codegen runs its intrinsic privilege check
    /// against this, as the second line behind check (section 3.2).
    pub fn fn_shipped_crate(&self, f: LocalDefId) -> Option<ShippedCrate> {
        self.shipped_crate_at(self.fn_info(f).def.name_span)
    }
    /// The local fn a shipped std path (for example
    /// `std::process::exit`) was routed to in this compile, if any.
    pub fn std_fn_for_path(&self, path: &[Sym]) -> Option<LocalDefId> {
        self.std_fns.iter().find(|(p, _)| p.as_slice() == path).map(|(_, f)| *f)
    }
}

/// Human-readable type name, for error messages. Builtin Adts keep their std names
/// through the compat helpers; kinds the subset cannot form yet print their Rust
/// shape so later waves inherit a total printer.
pub fn ty_name(p: &Program, tys: &impl TyIntern, t: Ty) -> String {
    match tys.kind(t) {
        TyKind::Error => "{error}".into(),
        TyKind::Unit => "()".into(),
        TyKind::Bool => "bool".into(),
        TyKind::Char => "char".into(),
        TyKind::Str => "str".into(),
        TyKind::Never => "!".into(),
        TyKind::Int(i) => i.name().into(),
        TyKind::Float(f) => f.name().into(),
        TyKind::Ref(_, m, e) => format!("&{}{}", if m.is_mut() { "mut " } else { "" }, ty_name(p, tys, e)),
        TyKind::RawPtr(m, e) => format!("*{}{}", if m.is_mut() { "mut " } else { "const " }, ty_name(p, tys, e)),
        TyKind::Slice(e) => format!("[{}]", ty_name(p, tys, e)),
        TyKind::Array(e, _) => format!("[{}; _]", ty_name(p, tys, e)),
        TyKind::Tuple(ts) => {
            let parts: Vec<String> = tys.tys_of(ts).iter().map(|&e| ty_name(p, tys, e)).collect();
            format!("({})", parts.join(", "))
        }
        TyKind::Adt(..) => match tys.builtin_of(t) {
            Some(BuiltinTy::String) => "String".into(),
            Some(BuiltinTy::Vec) => format!("Vec<{}>", tys.adt_first_ty_arg(t).map_or("_".into(), |e| ty_name(p, tys, e))),
            Some(BuiltinTy::Option) => {
                format!("Option<{}>", tys.adt_first_ty_arg(t).map_or("_".into(), |e| ty_name(p, tys, e)))
            }
            Some(BuiltinTy::Result) => {
                let (a, b) = tys.result_args(t).unwrap_or((ERROR, ERROR));
                format!("Result<{}, {}>", ty_name(p, tys, a), ty_name(p, tys, b))
            }
            Some(BuiltinTy::Chars) => "std::str::Chars".into(),
            Some(BuiltinTy::Args) => "std::env::Args".into(),
            None => match tys.local_adt(t) {
                Some(a) => p.display_path(p.adt(a).name),
                None => "{unknown}".into(),
            },
        },
        TyKind::FnPtr(_) | TyKind::FnDef(..) => "fn(..)".into(),
        TyKind::Closure(..) => "{closure}".into(),
        TyKind::Dyn(..) => "dyn ..".into(),
        TyKind::Opaque(..) => "impl ..".into(),
        TyKind::Param(param) => format!("T{}", param.0),
        TyKind::Projection(..) => "{projection}".into(),
        TyKind::Infer(v) if v.is_int() => "{integer}".into(),
        TyKind::Infer(v) if v.is_float() => "{float}".into(),
        TyKind::Infer(_) => "_".into(),
    }
}

/// Resolves a written type. `self_ty` is the type that `Self` means, inside an impl.
pub fn resolve_ty(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    type_names: &HashMap<Sym, AdtId>,
    aliases: &HashMap<Sym, Ty>,
    tys: &mut impl TyIntern,
    id: ast::TyId,
    self_ty: Option<Ty>,
) -> Result<Ty, Diag> {
    let span = ast.ty_span(id);
    match ast.ty(id) {
        TyExpr::Unit => Ok(UNIT),
        TyExpr::Never => Ok(NEVER),
        TyExpr::Ref { mutable, inner, .. } => {
            let inner = resolve_ty(ast, interner, known, type_names, aliases, tys, *inner, self_ty)?;
            Ok(tys.mk_ref(*mutable, inner))
        }
        TyExpr::Path(segs) => {
            // Accept `std::...::Name` by looking only at the last segment of std paths.
            let seg = if segs.len() > 1 && segs[0].name == known.std {
                segs.last().unwrap()
            } else if segs.len() == 1 {
                &segs[0]
            } else {
                return Err(not_yet("L0505", span, "module paths in types"));
            };
            let name = seg.name;
            let no_generics = |tys: Ty| -> Result<Ty, Diag> {
                if !seg.has_args() {
                    Ok(tys)
                } else {
                    Err(Diag::new("L0110", span, "this type takes no generic arguments", "Remove the `<...>` part."))
                }
            };
            if let Some(t) = known.int_ty(name) {
                return no_generics(int(t));
            }
            if name == known.bool {
                return no_generics(BOOL);
            }
            if name == known.char {
                return no_generics(CHAR);
            }
            if name == known.str {
                return no_generics(STR);
            }
            if name == known.String {
                return no_generics(STRING);
            }
            if name == known.self_type {
                return self_ty.ok_or_else(|| Diag::new("L0102", span, "`Self` is only valid inside an impl", "Write the type name."));
            }
            if name == known.Vec {
                let args = seg.type_args();
                if args.len() != 1 {
                    return Err(Diag::new("L0110", span, "Vec takes one type argument", "Write `Vec<T>`."));
                }
                let e = resolve_ty(ast, interner, known, type_names, aliases, tys, args[0], self_ty)?;
                return Ok(tys.mk_vec(e));
            }
            if name == known.Option {
                let args = seg.type_args();
                if args.len() != 1 {
                    return Err(Diag::new("L0110", span, "Option takes one type argument", "Write `Option<T>`."));
                }
                let e = resolve_ty(ast, interner, known, type_names, aliases, tys, args[0], self_ty)?;
                return Ok(tys.mk_option(e));
            }
            if name == known.Result {
                let args = seg.type_args();
                if args.len() != 2 {
                    return Err(Diag::new("L0110", span, "Result takes two type arguments", "Write `Result<T, E>`."));
                }
                let t = resolve_ty(ast, interner, known, type_names, aliases, tys, args[0], self_ty)?;
                let e = resolve_ty(ast, interner, known, type_names, aliases, tys, args[1], self_ty)?;
                return Ok(tys.mk_result(t, e));
            }
            if let Some(&adt) = type_names.get(&name) {
                return no_generics(tys.adt_ty(adt));
            }
            if let Some(&t) = aliases.get(&name) {
                return no_generics(t);
            }
            let n = interner.get(name);
            if name == known.f32 {
                return no_generics(tys.float_ty(FloatTy::F32));
            }
            if name == known.f64 {
                return no_generics(tys.float_ty(FloatTy::F64));
            }
            if ["HashMap", "HashSet", "BTreeMap", "Box", "Rc", "Arc", "RefCell", "Cell"].contains(&n) {
                return Err(not_yet("L0641", span, &format!("the `{n}` type")));
            }
            Err(Diag::new("L0102", span, format!("unknown type `{n}`"), "Check the spelling, or define the type."))
        }
        TyExpr::Tuple(elems) => {
            let mut out = Vec::with_capacity(elems.len());
            for &e in elems {
                out.push(resolve_ty(ast, interner, known, type_names, aliases, tys, e, self_ty)?);
            }
            let ts = tys.intern_tys(&out);
            Ok(tys.intern(TyKind::Tuple(ts)))
        }
        TyExpr::Slice(inner) => {
            let e = resolve_ty(ast, interner, known, type_names, aliases, tys, *inner, self_ty)?;
            Ok(tys.intern(TyKind::Slice(e)))
        }
        TyExpr::Array { inner, len } => {
            let e = resolve_ty(ast, interner, known, type_names, aliases, tys, *inner, self_ty)?;
            let n = eval_array_len(ast, interner, known, *len)
                .or_else(|| eval_len_layout_query(ast, interner, known, type_names, aliases, tys, *len))
                .ok_or_else(|| {
                    Diag::new("L0110", span, "array length must be a constant integer", "Write a literal length such as `[u8; 4]`.")
                })?;
            let c = tys.intern_const(ConstKind::Int(n));
            Ok(tys.intern(TyKind::Array(e, c)))
        }
        TyExpr::Paren(inner) => resolve_ty(ast, interner, known, type_names, aliases, tys, *inner, self_ty),
        TyExpr::FnPtr { qual, inputs, variadic, ret, .. } => {
            if *variadic || qual.is_unsafe || qual.is_async || qual.is_const || qual.abi.is_some() {
                return Err(not_yet("L0602", span, "qualified or variadic function pointer types"));
            }
            let mut ins = Vec::with_capacity(inputs.len());
            for p in inputs {
                ins.push(resolve_ty(ast, interner, known, type_names, aliases, tys, p.ty, self_ty)?);
            }
            let out = match ret {
                Some(r) => resolve_ty(ast, interner, known, type_names, aliases, tys, *r, self_ty)?,
                None => UNIT,
            };
            let inputs = tys.intern_tys(&ins);
            let sig = tys.intern_sig(crate::ty::Binder::plain(crate::ty::FnSig {
                inputs,
                output: out,
                is_unsafe: false,
                extern_c: false,
            }));
            Ok(tys.intern(TyKind::FnPtr(sig)))
        }
        _ => Err(not_yet("L0602", span, "this type form")),
    }
}

/// Evaluates an array length expression at collection time. Only literal
/// integer arithmetic is in the bound today; named consts join with the
/// const evaluator (ARCH 2.13) in `ty::consteval`.
pub fn eval_array_len(ast: &Ast, interner: &Interner, known: &Known, e: ast::ExprId) -> Option<u128> {
    u128::try_from(eval_const_int(ast, interner, known, e)?).ok()
}

/// A `size_of::<T>()` or `align_of::<T>()` array length, for types whose
/// layout needs no Adt fields (scalars, tuples, arrays). Adt lengths wait
/// for the full evaluator at the end of collection.
fn eval_len_layout_query(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    type_names: &HashMap<Sym, AdtId>,
    aliases: &HashMap<Sym, Ty>,
    tys: &mut impl TyIntern,
    e: ast::ExprId,
) -> Option<u128> {
    let ast::Expr::Call { callee, args } = ast.expr(e) else { return None };
    if !args.is_empty() {
        return None;
    }
    let ast::Expr::Path(segs) = ast.expr(*callee) else { return None };
    let last = segs.last()?;
    let name = interner.get(last.name);
    if !matches!(name, "size_of" | "align_of") {
        return None;
    }
    let targs = last.type_args();
    if targs.len() != 1 {
        return None;
    }
    let t = resolve_ty(ast, interner, known, type_names, aliases, tys, targs[0], None).ok()?;
    struct NoShapes;
    impl crate::ty::layout::AdtShapes for NoShapes {
        fn adt_shape(&self, _id: AdtId) -> Option<crate::ty::layout::AdtShape> {
            None
        }
    }
    let l = crate::ty::layout::layout_of_ty(tys, &NoShapes, t).ok()?;
    Some(if name == "align_of" { l.align as u128 } else { l.size as u128 })
}

pub fn parse_float_literal(text: &str) -> Option<(u64, Option<FloatTy>)> {
    let clean: String = text.chars().filter(|&c| c != '_').collect();
    if let Some(t) = clean.strip_suffix("f32") {
        return t.parse::<f32>().ok().map(|v| (v.to_bits() as u64, Some(FloatTy::F32)));
    }
    if let Some(t) = clean.strip_suffix("f64") {
        return t.parse::<f64>().ok().map(|v| (v.to_bits(), Some(FloatTy::F64)));
    }
    clean.parse::<f64>().ok().map(|v| (v.to_bits(), None))
}

/// Parses a float literal straight to the target type, with one rounding.
/// The runtime parser in src/runtime/float.c gives the same bits: both are
/// correctly rounded (ties to even) for the target precision. A literal
/// that rounds to infinity is out of range; callers report it through
/// `float_literal_overflows`.
pub fn parse_float_literal_as(text: &str, f: FloatTy) -> Option<u64> {
    let clean: String = text.chars().filter(|&c| c != '_').collect();
    let t = clean.strip_suffix("f32").or_else(|| clean.strip_suffix("f64")).unwrap_or(&clean);
    match f {
        FloatTy::F32 => t.parse::<f32>().ok().map(|v| v.to_bits() as u64),
        FloatTy::F64 => t.parse::<f64>().ok().map(|v| v.to_bits()),
    }
}

/// True when a float literal is out of range for the target type: its
/// correctly rounded value is infinite. Rust literals cannot write inf,
/// so an infinite parse always means overflow (the deny-level
/// `overflowing_literals` lint in rustc).
pub fn float_literal_overflows(text: &str, f: FloatTy) -> bool {
    match parse_float_literal_as(text, f) {
        Some(bits) => match f {
            FloatTy::F32 => f32::from_bits(bits as u32).is_infinite(),
            FloatTy::F64 => f64::from_bits(bits).is_infinite(),
        },
        None => false,
    }
}

/// Evaluates a constant integer expression at collection time: literals,
/// negation and bit-not, integer arithmetic and shifts, and `as` casts
/// between integer types. Returns None for anything else. The full bounded
/// evaluator lives in `ty::consteval` (ARCH 2.13); this is its scalar subset
/// for discriminants and array lengths, which collect needs before bodies run.
pub fn eval_const_int(ast: &Ast, interner: &Interner, known: &Known, e: ast::ExprId) -> Option<i128> {
    let mut env = Vec::new();
    let mut steps = 0u64;
    match eval_scalar(ast, interner, known, e, 0, &mut env, &mut steps) {
        SFlow::V(v) => v,
        _ => None,
    }
}

/// Control flow of the scalar interpreter below.
enum SFlow {
    /// A plain value (None is unit, or not a scalar).
    V(Option<i128>),
    Break(Option<i128>),
    Continue,
    Return(Option<i128>),
}

/// One block of the scalar interpreter: plain binding lets and
/// expression statements, then the tail value.
fn eval_scalar_block(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    b: ast::BlockId,
    depth: u32,
    env: &mut Vec<(Sym, i128)>,
    steps: &mut u64,
) -> SFlow {
    use crate::ast::{Pat, Stmt};
    let saved = env.len();
    let block = ast.block(b);
    for stmt in &block.stmts {
        match stmt {
            Stmt::Let { pat, init, .. } => {
                let (Some(init), Pat::Binding { name, .. }) = (init, ast.pat(*pat)) else {
                    env.truncate(saved);
                    return SFlow::V(None);
                };
                let v = match eval_scalar(ast, interner, known, *init, depth, env, steps) {
                    SFlow::V(Some(v)) => v,
                    _ => {
                        env.truncate(saved);
                        return SFlow::V(None);
                    }
                };
                env.push((*name, v));
            }
            Stmt::Expr { expr, .. } => match eval_scalar(ast, interner, known, *expr, depth, env, steps) {
                SFlow::V(_) => {}
                other => {
                    env.truncate(saved);
                    return other;
                }
            },
            _ => {
                env.truncate(saved);
                return SFlow::V(None);
            }
        }
    }
    let out = match block.tail {
        Some(tail) => eval_scalar(ast, interner, known, tail, depth, env, steps),
        None => SFlow::V(None),
    };
    env.truncate(saved);
    out
}

/// The scalar interpreter behind `eval_const_int`: plain integer
/// arithmetic and comparisons over literals, env-bound names, const
/// items found by scanning the crate's items, and calls to const fns
/// whose bodies stay in this scalar subset (lets, assignments, if,
/// while, and loop). It answers at collection time, before function
/// signatures exist, so it cannot use the full evaluator. Anything
/// outside the subset is None, never a wrong value.
fn eval_scalar(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    e: ast::ExprId,
    depth: u32,
    env: &mut Vec<(Sym, i128)>,
    steps: &mut u64,
) -> SFlow {
    *steps += 1;
    if depth > 32 || *steps > 100_000 {
        return SFlow::V(None);
    }
    use crate::ast::{BinOp, Expr, UnOp};
    let val = |ast: &Ast, interner: &Interner, known: &Known, e: ast::ExprId, depth: u32, env: &mut Vec<(Sym, i128)>, steps: &mut u64| {
        match eval_scalar(ast, interner, known, e, depth, env, steps) {
            SFlow::V(v) => v,
            _ => None,
        }
    };
    match ast.expr(e) {
        Expr::Int(v, _) => SFlow::V(Some(*v as u128 as i128)),
        Expr::Char(c) => SFlow::V(Some(*c as i128)),
        Expr::Bool(b) => SFlow::V(Some(*b as i128)),
        Expr::Unit => SFlow::V(None),
        Expr::Unary { op, expr } => {
            // A negated literal names its magnitude first: 170141183460469231731687303715884105728
            // does not fit i128 alone, but its negation is i128::MIN.
            if *op == UnOp::Neg
                && let Expr::Int(mag, _) = ast.expr(*expr)
            {
                return SFlow::V(if *mag <= (1u128 << 127) { Some((*mag as i128).wrapping_neg()) } else { None });
            }
            let Some(v) = val(ast, interner, known, *expr, depth + 1, env, steps) else { return SFlow::V(None) };
            SFlow::V(match op {
                UnOp::Neg => v.checked_neg(),
                UnOp::Not => Some(!v),
            })
        }
        Expr::Binary { op, lhs, rhs } => {
            if matches!(op, BinOp::And | BinOp::Or) {
                let Some(a) = val(ast, interner, known, *lhs, depth + 1, env, steps) else { return SFlow::V(None) };
                if (*op == BinOp::And && a == 0) || (*op == BinOp::Or && a != 0) {
                    return SFlow::V(Some((a != 0) as i128));
                }
                let b = val(ast, interner, known, *rhs, depth + 1, env, steps);
                return SFlow::V(b.map(|b| (b != 0) as i128));
            }
            let (a, b) = (
                val(ast, interner, known, *lhs, depth + 1, env, steps),
                val(ast, interner, known, *rhs, depth + 1, env, steps),
            );
            let (Some(a), Some(b)) = (a, b) else { return SFlow::V(None) };
            SFlow::V(match op {
                BinOp::Add => a.checked_add(b),
                BinOp::Sub => a.checked_sub(b),
                BinOp::Mul => a.checked_mul(b),
                BinOp::Div => a.checked_div(b),
                BinOp::Rem => a.checked_rem(b),
                BinOp::BitAnd => Some(a & b),
                BinOp::BitOr => Some(a | b),
                BinOp::BitXor => Some(a ^ b),
                BinOp::Shl => u32::try_from(b).ok().and_then(|b| a.checked_shl(b)),
                BinOp::Shr => u32::try_from(b).ok().and_then(|b| a.checked_shr(b)),
                BinOp::Eq => Some((a == b) as i128),
                BinOp::Ne => Some((a != b) as i128),
                BinOp::Lt => Some((a < b) as i128),
                BinOp::Le => Some((a <= b) as i128),
                BinOp::Gt => Some((a > b) as i128),
                BinOp::Ge => Some((a >= b) as i128),
                _ => None,
            })
        }
        Expr::Cast { expr, ty } => {
            let Some(v) = val(ast, interner, known, *expr, depth + 1, env, steps) else { return SFlow::V(None) };
            let target = match ast.ty(*ty) {
                TyExpr::Path(segs) if segs.len() == 1 => known.int_ty(segs[0].name),
                _ => None,
            };
            SFlow::V(match target {
                Some(it) => Some(truncate_to_int(v, it)),
                None if matches!(ast.ty(*ty), TyExpr::Path(segs) if segs.len() == 1 && segs[0].name == known.char) => Some(v),
                _ => None,
            })
        }
        Expr::Block(b) | Expr::ConstBlock(b) => eval_scalar_block(ast, interner, known, *b, depth + 1, env, steps),
        Expr::If { cond, then, els } => {
            let Some(c) = val(ast, interner, known, *cond, depth + 1, env, steps) else { return SFlow::V(None) };
            if c != 0 {
                let b = *then;
                eval_scalar_block(ast, interner, known, b, depth + 1, env, steps)
            } else {
                match els {
                    Some(els) => eval_scalar(ast, interner, known, *els, depth + 1, env, steps),
                    None => SFlow::V(None),
                }
            }
        }
        Expr::While { cond, body, .. } => {
            loop {
                let Some(c) = val(ast, interner, known, *cond, depth + 1, env, steps) else { return SFlow::V(None) };
                if c == 0 {
                    return SFlow::V(None);
                }
                let b = *body;
                match eval_scalar_block(ast, interner, known, b, depth + 1, env, steps) {
                    SFlow::V(_) | SFlow::Continue => {}
                    SFlow::Break(_) => return SFlow::V(None),
                    other => return other,
                }
                if *steps > 100_000 {
                    return SFlow::V(None);
                }
            }
        }
        Expr::Loop { body, .. } => {
            loop {
                let b = *body;
                match eval_scalar_block(ast, interner, known, b, depth + 1, env, steps) {
                    SFlow::V(_) | SFlow::Continue => {}
                    SFlow::Break(v) => return SFlow::V(v),
                    other => return other,
                }
                if *steps > 100_000 {
                    return SFlow::V(None);
                }
            }
        }
        Expr::Break { value, .. } => {
            let v = match value {
                Some(v) => val(ast, interner, known, *v, depth + 1, env, steps),
                None => None,
            };
            SFlow::Break(v)
        }
        Expr::Continue(_) => SFlow::Continue,
        Expr::Return(v) => {
            let v = match v {
                Some(v) => val(ast, interner, known, *v, depth + 1, env, steps),
                None => None,
            };
            SFlow::Return(v)
        }
        Expr::Assign { lhs, rhs } => {
            let Some(v) = val(ast, interner, known, *rhs, depth + 1, env, steps) else { return SFlow::V(None) };
            let Expr::Path(segs) = ast.expr(*lhs) else { return SFlow::V(None) };
            if segs.len() != 1 {
                return SFlow::V(None);
            }
            match env.iter_mut().rev().find(|(n, _)| *n == segs[0].name) {
                Some(slot) => {
                    slot.1 = v;
                    SFlow::V(None)
                }
                None => SFlow::V(None),
            }
        }
        Expr::AssignOp { op, lhs, rhs } => {
            let cur = val(ast, interner, known, *lhs, depth + 1, env, steps);
            let rv = val(ast, interner, known, *rhs, depth + 1, env, steps);
            let (Some(a), Some(b)) = (cur, rv) else { return SFlow::V(None) };
            let r = match op {
                BinOp::Add => a.checked_add(b),
                BinOp::Sub => a.checked_sub(b),
                BinOp::Mul => a.checked_mul(b),
                BinOp::Div => a.checked_div(b),
                BinOp::Rem => a.checked_rem(b),
                BinOp::BitAnd => Some(a & b),
                BinOp::BitOr => Some(a | b),
                BinOp::BitXor => Some(a ^ b),
                BinOp::Shl => u32::try_from(b).ok().and_then(|b| a.checked_shl(b)),
                BinOp::Shr => u32::try_from(b).ok().and_then(|b| a.checked_shr(b)),
                _ => None,
            };
            let Some(r) = r else { return SFlow::V(None) };
            let Expr::Path(segs) = ast.expr(*lhs) else { return SFlow::V(None) };
            if segs.len() != 1 {
                return SFlow::V(None);
            }
            match env.iter_mut().rev().find(|(n, _)| *n == segs[0].name) {
                Some(slot) => {
                    slot.1 = r;
                    SFlow::V(None)
                }
                None => SFlow::V(None),
            }
        }
        Expr::Call { callee, args } => {
            // A call to a const fn found by scanning the crate's items.
            let Expr::Path(segs) = ast.expr(*callee) else { return SFlow::V(None) };
            if segs.len() != 1 {
                return SFlow::V(None);
            }
            let name = segs[0].name;
            let mut argv = Vec::new();
            for &a in args {
                match val(ast, interner, known, a, depth + 1, env, steps) {
                    Some(v) => argv.push(v),
                    None => return SFlow::V(None),
                }
            }
            for item in &ast.items {
                let ItemKind::Fn(def) = &item.kind else { continue };
                if def.name != name || !def.qual.is_const || def.self_param.is_some() || def.params.len() != argv.len() {
                    continue;
                }
                let Some(body) = def.body else { return SFlow::V(None) };
                let mut fenv: Vec<(Sym, i128)> = Vec::new();
                for (param, v) in def.params.iter().zip(argv) {
                    if param.pat.is_some() {
                        return SFlow::V(None);
                    }
                    fenv.push((param.name, v));
                }
                return match eval_scalar_block(ast, interner, known, body, depth + 1, &mut fenv, steps) {
                    SFlow::V(v) | SFlow::Return(v) => SFlow::V(v),
                    _ => SFlow::V(None),
                };
            }
            SFlow::V(None)
        }
        Expr::Path(segs) if segs.len() == 1 => {
            let name = segs[0].name;
            if let Some((_, v)) = env.iter().rev().find(|(n, _)| *n == name) {
                return SFlow::V(Some(*v));
            }
            // A reference to another const item, found by scanning the
            // crate's items (collect evaluates all of them later anyway).
            let mut out = None;
            for item in &ast.items {
                if let ItemKind::Const(c) = &item.kind
                    && c.name == Some(name)
                    && let Some(v) = c.value
                {
                    let mut empty = Vec::new();
                    out = val(ast, interner, known, v, depth + 1, &mut empty, steps);
                    break;
                }
            }
            SFlow::V(out)
        }
        Expr::Path(segs) if segs.len() == 2 => {
            // `i64::MAX` and friends by written name.
            let out = known.int_ty(segs[0].name).and_then(|it| {
                let item = interner.get(segs[1].name);
                let bits = it.bits();
                match item {
                    "MAX" => Some(truncate_to_int(it.max128() as i128, it)),
                    "MIN" => Some(if it.signed() {
                        if bits >= 128 { i128::MIN } else { -(1i128 << (bits - 1)) }
                    } else {
                        0
                    }),
                    "BITS" => Some(bits as i128),
                    _ => None,
                }
            });
            SFlow::V(out)
        }
        _ => SFlow::V(None),
    }
}

/// Wraps `v` to the range of an integer type, as an `as` cast does.
fn truncate_to_int(v: i128, it: IntTy) -> i128 {
    let bits = it.bits();
    if bits >= 128 {
        return v;
    }
    let mask: i128 = (1i128 << bits) - 1;
    let u = v & mask;
    if it.signed() && (u >> (bits - 1)) & 1 == 1 { u - (1i128 << bits) } else { u }
}

/// Parses the `repr` attributes of an item into layout terms. Unknown or
/// unsupported forms are errors: this is where the 4.4 grammar cut lands
/// for `repr(simd)` and `repr(packed(N))` with N other than 1.
fn parse_repr(interner: &Interner, attrs: &[ast::Attr]) -> Result<crate::ty::layout::Repr, Diag> {
    use crate::ast::AttrInput;
    use crate::lexer::{Tok, TokenTree};
    use crate::ty::layout::{Repr, ReprKind};
    let mut repr = Repr::default();
    for attr in attrs {
        if attr.path.len() != 1 || interner.get(attr.path[0].name) != "repr" {
            continue;
        }
        let AttrInput::List(_, trees) = &attr.input else {
            return Err(Diag::new("L0110", attr.span, "`repr` needs a form such as `repr(C)`", "Write the repr in parentheses."));
        };
        let bad = |what: &str| {
            Diag::new(
                "L0652",
                attr.span,
                format!("unsupported layout form: `repr({what})`"),
                "Use a supported repr: C, an integer, transparent, packed, or align.",
            )
        };
        let mut i = 0;
        while i < trees.len() {
            match &trees[i] {
                TokenTree::Token(t) if t.tok == Tok::Comma => i += 1,
                TokenTree::Token(t) => {
                    let Tok::Ident(name) = t.tok else {
                        return Err(bad(".."));
                    };
                    let text = interner.get(name);
                    match text {
                        "C" => repr.kind = ReprKind::C,
                        "Rust" => {}
                        "transparent" => repr.kind = ReprKind::Transparent,
                        "packed" => {
                            repr.kind = ReprKind::Packed;
                            if let Some(TokenTree::Delim(_, inner, _)) = trees.get(i + 1) {
                                let ok = matches!(inner.as_slice(), [TokenTree::Token(t2)] if matches!(t2.tok, Tok::Int(1, _)));
                                if !ok {
                                    return Err(bad("packed(N)"));
                                }
                                i += 1;
                            }
                        }
                        "align" => match trees.get(i + 1) {
                            Some(TokenTree::Delim(_, inner, _)) => match inner.as_slice() {
                                [TokenTree::Token(t2)] => match t2.tok {
                                    Tok::Int(n, _) if n > 0 && n <= (1 << 29) && n.is_power_of_two() => {
                                        repr.align = Some(n as u64);
                                        i += 1;
                                    }
                                    _ => return Err(bad("align(..)")),
                                },
                                _ => return Err(bad("align(..)")),
                            },
                            _ => return Err(bad("align")),
                        },
                        "u8" | "u16" | "u32" | "u64" | "u128" | "usize" | "i8" | "i16" | "i32" | "i64" | "i128" | "isize" => {
                            let signed = text.starts_with('i');
                            let bits: u32 = match text {
                                "u8" | "i8" => 8,
                                "u16" | "i16" => 16,
                                "u32" | "i32" => 32,
                                "u128" | "i128" => 128,
                                _ => 64,
                            };
                            repr.int = Some((bits, signed));
                        }
                        _ => return Err(bad(text)),
                    }
                    i += 1;
                }
                TokenTree::Delim(..) => return Err(bad("..")),
            }
        }
    }
    Ok(repr)
}

/// Converts written variant or struct fields to (shape, (name, type, span) list).
/// Tuple fields get their index text as their name, so `T { 0: 5 }` field
/// matching and field diagnostics work like named fields.
fn variant_fields_src(interner: &Interner, vf: &VariantFields) -> (VariantShape, Vec<(Sym, ast::TyId, Span)>) {
    match vf {
        VariantFields::Unit => (VariantShape::Unit, Vec::new()),
        VariantFields::Tuple(fs) => (
            VariantShape::Tuple,
            fs.iter().enumerate().map(|(i, f)| (interner.intern(&i.to_string()), f.ty, f.span)).collect(),
        ),
        VariantFields::Struct(fs) => (VariantShape::Named, fs.iter().map(|f| (f.name, f.ty, f.span)).collect()),
    }
}

/// Builds the program tables. `crate_ids` names the crate for stable def
/// identity (docs/ARCH.md section 1.7). Returns all collection errors.
pub fn collect<'a>(ast: &'a Ast, interner: &'a Interner, known: &'a Known, crate_ids: CrateIds) -> Result<Program<'a>, Vec<Diag>> {
    collect_mode(ast, interner, known, crate_ids, true)
}

/// `collect` for one command: a build walks every reachable generic
/// instance (mono); `lust check` passes `walk_instances` false and
/// stops at the template checks, like rustc check (ARCH 4.1).
pub fn collect_mode<'a>(
    ast: &'a Ast,
    interner: &'a Interner,
    known: &'a Known,
    crate_ids: CrateIds,
    walk_instances: bool,
) -> Result<Program<'a>, Vec<Diag>> {
    let mut p = Program {
        ast,
        interner,
        known,
        tys: GlobalTys::new(),
        defs: Defs::new(),
        adts: Vec::new(),
        fns: Vec::new(),
        consts: Vec::new(),
        assoc_const_names: HashMap::default(),
        const_names: HashMap::default(),
        const_defs: Vec::new(),
        static_defs: Vec::new(),
        statics: Vec::new(),
        static_names: HashMap::default(),
        body_items: HashMap::default(),
        body_consts: Vec::new(),
        fn_siblings: HashMap::default(),
        type_names: HashMap::default(),
        aliases: HashMap::default(),
        fn_names: HashMap::default(),
        methods: HashMap::default(),
        main: None,
        krate: crate_ids.local,
        stable_crate: crate_ids.stable,
        fn_defs: Vec::new(),
        def_by_hash: HashMap::default(),
        std_fns: Vec::new(),
        shipped_ranges: Vec::new(),
        resolved: None,
        gx: GenTables::default(),
    };
    p.gx.walk_instances = walk_instances;
    // The builtin Adt defs join the table with their one type param where they take
    // one, so `Generics` queries answer for builtins and user types alike. Their
    // code paths stay builtin until source std lands (ARCH 2.1, 9.3).
    {
        let b = p.tys.builtins();
        let dummy = Span::default();
        let one_ty_param = || Generics {
            parent: None,
            params: vec![ParamDef { name: interner.intern("T"), kind: ParamKind::Type, span: dummy }],
            predicates: Vec::new(),
        };
        let insert_builtin = |p: &mut Program<'a>, def: DefId, kind: DefsKind, name: Sym, generics: Generics| {
            let mut data = DefData::skeleton(kind, None, name, Vis::Pub, dummy);
            data.generics = generics;
            p.defs.insert(def, data);
        };
        insert_builtin(&mut p, b.string, DefsKind::Struct, known.String, Generics::default());
        insert_builtin(&mut p, b.vec, DefsKind::Struct, known.Vec, one_ty_param());
        insert_builtin(&mut p, b.option, DefsKind::Enum, known.Option, one_ty_param());
        let two_ty_params = Generics {
            parent: None,
            params: vec![
                ParamDef { name: interner.intern("T"), kind: ParamKind::Type, span: dummy },
                ParamDef { name: interner.intern("E"), kind: ParamKind::Type, span: dummy },
            ],
            predicates: Vec::new(),
        };
        insert_builtin(&mut p, b.result, DefsKind::Enum, known.Result, two_ty_params);
        insert_builtin(&mut p, b.chars, DefsKind::Struct, interner.intern("Chars"), Generics::default());
        insert_builtin(&mut p, b.args, DefsKind::Struct, interner.intern("Args"), Generics::default());
    }
    let mut errs = Vec::new();
    let dup = |span: Span, n: &str| Diag::new("L0106", span, format!("`{n}` is defined more than once"), "Rename one of the definitions.");

    // Generic pass 0: lang traits and user trait defs, so bounds in
    // every later signature can name them.
    generics::init_lang(&mut p);
    generics::collect_trait_defs(&mut p, &mut errs);

    // Pass 1: type names, so fields can refer to types defined later.
    let mut adt_name_counts: HashMap<Sym, u32> = HashMap::default();
    for item in &ast.items {
        let (name, span, is_enum) = match &item.kind {
            ItemKind::Struct(s) => (s.name, s.name_span, false),
            ItemKind::Enum(e) => (e.name, e.name_span, true),
            _ => continue,
        };
        let id = AdtId(p.adts.len() as u32);
        if p.type_names.insert(name, id).is_some() || p.gx.trait_names.contains_key(&name) {
            errs.push(dup(span, interner.get(name)));
        }
        let n_params = match &item.kind {
            ItemKind::Struct(st) => generics::ast_param_count(&st.generics),
            ItemKind::Enum(e) => generics::ast_param_count(&e.generics),
            _ => 0,
        };
        if n_params > 0 {
            p.gx.has_generics = true;
        }
        // The Adt's stable identity (ARCH 1.7): same name earlier in the file is a
        // duplicate definition (the error above), and the disambiguator keeps the
        // two records apart in the def table, as the old dense ids did.
        let disamb = *adt_name_counts.entry(name).and_modify(|c| *c += 1).or_insert(0);
        let hash = crate::def::item_hash(p.stable_crate, &[], crate::def::DefKind::Adt, interner.get(name), disamb);
        let def = DefId { krate: p.krate, hash };
        p.adts.push(AdtDef {
            name,
            is_enum,
            variants: Vec::new(),
            derives: Derives::default(),
            span,
            repr: crate::ty::layout::Repr::default(),
        });
        p.gx.adt_info.push((def, n_params));
        p.gx.adt_generics.push(Generics::default());
        p.gx.adt_envs.push(Vec::new());
        p.gx.adt_scopes.push(generics::Scope::default());
        p.gx.adt_instance_of.push(None);
        p.tys.register_adt(def, id);
        let kind = if is_enum { DefsKind::Enum } else { DefsKind::Struct };
        p.defs.insert_adt(def, id, DefData::skeleton(kind, None, name, Vis::Priv, span));
        p.tys.intern(TyKind::Adt(def, EMPTY_ARGS));
    }

    // Pass 1.5: non-generic type aliases. Resolved by a small fixpoint:
    // an alias whose target still names an unresolved alias defers to
    // the next sweep; a sweep with no progress means a cycle (L0601) or
    // a genuine unknown type (the first error is kept).
    {
        let mut pending: Vec<&ast::TypeAliasDef> = Vec::new();
        for item in &ast.items {
            if let ItemKind::Type(a) = &item.kind {
                if p.type_names.contains_key(&a.name) || p.aliases.contains_key(&a.name) {
                    errs.push(dup(a.name_span, interner.get(a.name)));
                }
                pending.push(a);
                let hash = crate::def::item_hash(p.stable_crate, &[], crate::def::DefKind::TypeAlias, interner.get(a.name), 0);
                let def = DefId { krate: p.krate, hash };
                p.defs.insert(def, DefData::skeleton(DefsKind::TypeAlias, None, a.name, Vis::Priv, a.name_span));
            }
        }
        let total = pending.len();
        for _ in 0..=total {
            if pending.is_empty() {
                break;
            }
            let mut progress = false;
            let mut first_err: Option<Diag> = None;
            pending.retain(|a| match resolve_ty(ast, interner, known, &p.type_names, &p.aliases, &mut p.tys, a.ty, None) {
                Ok(t) => {
                    p.aliases.insert(a.name, t);
                    progress = true;
                    false
                }
                Err(d) => {
                    if first_err.is_none() {
                        first_err = Some(d);
                    }
                    true
                }
            });
            if !progress && !pending.is_empty() {
                // A cycle if every leftover target names another alias.
                let names: Vec<&str> = pending.iter().map(|a| interner.get(a.name)).collect();
                let cyclic = pending.iter().all(|a| match ast.ty(a.ty) {
                    TyExpr::Path(segs) => segs.len() == 1 && names.contains(&interner.get(segs[0].name)),
                    _ => false,
                });
                if cyclic {
                    errs.push(Diag::new(
                        "L0601",
                        pending[0].name_span,
                        format!("cycle detected in type aliases: {}", names.join(", ")),
                        "Break the cycle: an alias must not name itself, directly or through other aliases.",
                    ));
                } else if let Some(d) = first_err {
                    errs.push(d);
                }
                break;
            }
        }
    }

    // Generic pass 1.5: trait generics, method templates. Fields
    // and fn signatures after this can name traits in bounds.
    generics::build_trait_tables(&mut p, &mut errs);

    // Pass 2: fields, variants, derives.
    let mut adt_index = 0;
    for item in &ast.items {
        type FieldSrc = (Sym, ast::TyId, Span);
        type VariantSrc = (Sym, Span, VariantShape, Vec<FieldSrc>, Option<ast::ExprId>);
        let (variants_src, derives_src): (Vec<VariantSrc>, &Vec<(Sym, Span)>) = match &item.kind {
            ItemKind::Struct(s) => {
                let (shape, fields) = variant_fields_src(interner, &s.fields);
                let shape = if shape == VariantShape::Unit { VariantShape::Named } else { shape };
                (vec![(s.name, s.name_span, shape, fields, None)], &s.derives)
            }
            ItemKind::Enum(e) => {
                let vs = e
                    .variants
                    .iter()
                    .map(|v| {
                        let (shape, fs) = variant_fields_src(interner, &v.fields);
                        (v.name, v.span, shape, fs, v.discriminant)
                    })
                    .collect();
                (vs, &e.derives)
            }
            _ => continue,
        };
        let id = AdtId(adt_index);
        adt_index += 1;
        // The Adt's own generics scope its field types.
        {
            let (g_ast, w_ast) = match &item.kind {
                ItemKind::Struct(st) => (st.generics.clone(), st.where_clause.clone()),
                ItemKind::Enum(e) => (e.generics.clone(), e.where_clause.clone()),
                _ => unreachable!(),
            };
            let (adt_generics, adt_scope) = {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                generics::build_generics(ast, interner, known, &cx, &mut p.tys, &g_ast, &w_ast, &mut errs)
            };
            let env = generics::elaborate_env(&mut p.tys, &p.gx.index, &adt_generics.predicates);
            p.gx.adt_generics[id.0 as usize] = adt_generics;
            p.gx.adt_envs[id.0 as usize] = env;
            p.gx.adt_scopes[id.0 as usize] = adt_scope;
            // Mirror the generics into the def table record.
            let def = p.defs.def_of_adt(id).expect("ADT defs are recorded in pass 1");
            let name = p.adts[id.0 as usize].name;
            let is_enum_now = p.adts[id.0 as usize].is_enum;
            let mut data = DefData::skeleton(
                if is_enum_now { DefsKind::Enum } else { DefsKind::Struct },
                None,
                name,
                Vis::Priv,
                p.adts[id.0 as usize].span,
            );
            data.generics = p.gx.adt_generics[id.0 as usize].clone();
            p.defs.insert(def, data);
        }
        let is_enum = p.adts[id.0 as usize].is_enum;
        let mut variants = Vec::new();
        let mut disc_explicit: Vec<bool> = Vec::new();
        let mut next_disc: i128 = 0;
        for (vname, vspan, shape, field_srcs, disc_src) in variants_src {
            let shape = if !is_enum && field_srcs.is_empty() { VariantShape::Unit } else { shape };
            let mut fields = Vec::new();
            for (fname, fty, fspan) in field_srcs {
                if shape == VariantShape::Named && fields.iter().any(|f: &Field| f.name == fname) {
                    errs.push(dup(fspan, interner.get(fname)));
                }
                let resolved = {
                    let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                    let scope = p.gx.adt_scopes[id.0 as usize].clone();
                    generics::resolve_scoped(ast, interner, known, &cx, &mut p.tys, fty, &scope)
                };
                match resolved {
                    Ok(t) => {
                        if contains_ref(&p.tys, t) && !generics::ref_field_ok(ast, interner, fty) {
                            errs.push(Diag::new(
                                "L0201",
                                ast.ty_span(fty),
                                "struct and enum fields cannot hold references",
                                "Store an owned value (for example String instead of &str), or store an index and pass the reference to each method.",
                            ));
                        }
                        fields.push(Field { name: fname, ty: t });
                    }
                    Err(d) => {
                        errs.push(d);
                        fields.push(Field { name: fname, ty: ERROR });
                    }
                }
            }
            if is_enum && variants.iter().any(|v: &Variant| v.name == vname) {
                errs.push(dup(vspan, interner.get(vname)));
            }
            disc_explicit.push(disc_src.is_some());
            let disc = match disc_src {
                Some(de) => match eval_const_int(ast, interner, known, de) {
                    Some(v) => v,
                    None => {
                        errs.push(Diag::new(
                            "L0110",
                            vspan,
                            "enum discriminant must be a constant integer",
                            "Write a literal value such as `A = 3`.",
                        ));
                        next_disc
                    }
                },
                None => next_disc,
            };
            next_disc = disc.wrapping_add(1);
            variants.push(Variant { name: vname, shape, fields, disc });
        }
        let mut d = Derives::default();
        for &(name, span) in derives_src {
            match interner.get(name) {
                "Debug" => d.debug = true,
                "Clone" => d.clone = true,
                "Copy" => d.copy = true,
                "PartialEq" => d.partial_eq = true,
                "Eq" => d.eq = true,
                "Hash" => d.hash = true,
                n @ ("PartialOrd" | "Ord" | "Default") => errs.push(unsupported(span, &format!("#[derive({n})]"))),
                n => errs.push(Diag::new(
                    "L0403",
                    span,
                    format!("cannot derive `{n}`"),
                    "Lust can derive Debug, Clone, Copy, PartialEq, Eq, and Hash.",
                )),
            }
        }
        if d.copy && !d.clone {
            errs.push(Diag::new("L0112", p.adts[id.0 as usize].span, "deriving Copy requires Clone", "Add Clone to the derive list."));
        }
        // A type parameter must occur in a field (rustc E0392's
        // class): an unused parameter has no layout meaning here.
        {
            let agx = &p.gx.adt_generics[id.0 as usize];
            for (i, param) in agx.params.iter().enumerate() {
                if param.kind != ParamKind::Type {
                    continue;
                }
                let used = variants.iter().any(|v| v.fields.iter().any(|f| generics::ty_uses_param(&p.tys, f.ty, i as u32)));
                if !used {
                    errs.push(Diag::new(
                        "L0110",
                        param.span,
                        format!("type parameter `{}` is never used", interner.get(param.name)),
                        "Use the parameter in a field type, or remove it.",
                    ));
                }
            }
        }
        let adt = &mut p.adts[id.0 as usize];
        adt.variants = variants;
        adt.derives = d;
        match parse_repr(interner, &item.attrs) {
            Ok(r) => adt.repr = r,
            Err(dg) => errs.push(dg),
        }
        // Repr and discriminant rules Rust also enforces (ARCH 4.4).
        {
            use crate::ty::layout::ReprKind;
            let adt = &p.adts[id.0 as usize];
            if !adt.is_enum && adt.repr.int.is_some() {
                errs.push(Diag::new(
                    "L0110",
                    adt.span,
                    "`#[repr(...)]` with an integer type can only be used on an enum",
                    "Remove the integer from the repr, or make the type an enum.",
                ));
            }
            if adt.is_enum
                && adt.repr.kind == ReprKind::C
                && adt.repr.int.is_some()
                && adt.variants.iter().all(|v| v.fields.is_empty())
            {
                errs.push(Diag::new(
                    "L0110",
                    adt.span,
                    "conflicting representation hints: `repr(C)` and an integer repr on a fieldless enum",
                    "Use `repr(C)` or the integer repr alone; fieldless enums have no payload for `repr(C)` to order.",
                ));
            }
            if adt.repr.kind == ReprKind::Packed && adt.repr.align.is_some() {
                errs.push(Diag::new(
                    "L0110",
                    adt.span,
                    "`#[repr(packed)]` and `#[repr(align(...))]` conflict",
                    "Remove one of them: a packed type has alignment 1.",
                ));
            }
            if adt.repr.kind == ReprKind::Transparent {
                let non_unit = adt.variants.first().map(|v| v.fields.iter().filter(|f| f.ty != UNIT && f.ty != ERROR).count()).unwrap_or(0);
                if adt.is_enum || non_unit != 1 {
                    errs.push(Diag::new(
                        "L0110",
                        adt.span,
                        "`repr(transparent)` needs a struct with exactly one non-unit field",
                        "Remove the repr, or give the struct one field plus zero-sized fields.",
                    ));
                }
            }
            if let Some((bits, signed)) = adt.repr.int {
                let (lo, hi): (i128, i128) = if signed {
                    if bits >= 128 { (i128::MIN, i128::MAX) } else { (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1) }
                } else if bits >= 128 {
                    (0, i128::MAX)
                } else {
                    (0, (1i128 << bits) - 1)
                };
                for v in &adt.variants {
                    if v.disc < lo || v.disc > hi {
                        errs.push(Diag::new(
                            "L0110",
                            adt.span,
                            format!("discriminant value {} overflows the repr range", v.disc),
                            "Change the discriminant or the repr integer type.",
                        ));
                    }
                }
            }
            if adt.is_enum {
                // With no int repr the discriminant type is `isize`; an
                // implicit discriminant after `isize::MAX` lands outside it.
                if adt.repr.int.is_none() {
                    for v in &adt.variants {
                        if v.disc < i64::MIN as i128 || v.disc > i64::MAX as i128 {
                            errs.push(Diag::new(
                                "L0110",
                                adt.span,
                                format!("discriminant value {} overflows `isize`", v.disc),
                                "Change the discriminant, or add an int repr such as `#[repr(i64)]`.",
                            ));
                        }
                    }
                }
                // Duplicate discriminants, explicit or implicit (rustc E0081).
                for i in 0..adt.variants.len() {
                    if adt.variants[..i].iter().any(|v| v.disc == adt.variants[i].disc) {
                        errs.push(Diag::new(
                            "L0110",
                            adt.span,
                            format!("discriminant value {} is used more than once", adt.variants[i].disc),
                            "Give each variant a different discriminant value.",
                        ));
                    }
                }
                // Explicit discriminants on an enum with data variants need
                // an int repr (rustc E0732).
                let any_explicit = disc_explicit.iter().any(|&x| x);
                let any_data = adt.variants.iter().any(|v| !v.fields.is_empty());
                if any_explicit && any_data && adt.repr.int.is_none() {
                    errs.push(Diag::new(
                        "L0110",
                        adt.span,
                        "enums with explicit discriminants and data variants need an int repr",
                        "Add a repr such as `#[repr(u8)]`, or remove the discriminants.",
                    ));
                }
            }
        }
    }

    // Derived traits need every field type to have the trait too.
    for i in 0..p.adts.len() {
        let adt = &p.adts[i];
        let d = adt.derives;
        for v in &adt.variants {
            for f in &v.fields {
                if p.tys.flags(f.ty).contains_param() {
                    // A generic field: the synthetic derive impl
                    // carries the bound (section 2.2), checked per
                    // instance, not against the abstract field type.
                    continue;
                }
                // Each query runs only for a derive the type asks for: the queries
                // are pure, so skipping the others changes no result.
                let mut checks: [(bool, &str); 4] = [(true, ""); 4];
                let mut n_checks = 0;
                if d.clone {
                    checks[n_checks] = (has_clone(&p, &p.tys, f.ty), "Clone");
                    n_checks += 1;
                }
                if d.copy {
                    checks[n_checks] = (is_copy(&p, &p.tys, f.ty), "Copy");
                    n_checks += 1;
                }
                if d.partial_eq {
                    checks[n_checks] = (has_eq(&p, &p.tys, f.ty), "PartialEq");
                    n_checks += 1;
                }
                if d.debug {
                    checks[n_checks] = (has_debug(&p, &p.tys, f.ty), "Debug");
                    n_checks += 1;
                }
                for &(ok, name) in &checks[..n_checks] {
                    if !ok {
                        errs.push(Diag::new(
                            "L0112",
                            adt.span,
                            format!("cannot derive {name}: field type `{}` does not implement {name}", ty_name(&p, &p.tys, f.ty)),
                            format!("Derive {name} on the field type too, or remove {name} from the derive list."),
                        ));
                    }
                }
            }
        }
    }

    // Fields must be sized: a bare slice or str cannot sit in a struct.
    for adt in &p.adts {
        for v in &adt.variants {
            for f in &v.fields {
                if !is_sized_ty(&p.tys, f.ty) {
                    errs.push(Diag::new(
                        "L0110",
                        adt.span,
                        format!("the size for values of type `{}` cannot be known", ty_name(&p, &p.tys, f.ty)),
                        "Put the value behind a reference, such as `&[T]` or `&str`.",
                    ));
                }
            }
        }
    }

    // A type that contains itself by value has infinite size.
    for i in 0..p.adts.len() {
        let mut seen = vec![false; p.adts.len()];
        if contains_adt_by_value(&p, AdtId(i as u32), AdtId(i as u32), &mut seen) {
            errs.push(Diag::new(
                "L0117",
                p.adts[i].span,
                format!("recursive type `{}` has infinite size", p.display_path(p.adts[i].name)),
                "Put the recursive field in a Vec. Box is not supported yet.",
            ));
        }
    }

    // Functions and methods. Each gets the stable path hash its caller computed
    // (src/def.rs). Hash collisions are checked by the driver when it assigns
    // slots from the same hashes, before `collect` runs on any new def set;
    // here the maps only record the hashes. A duplicate definition keeps the
    // first local id in `def_by_hash`; the dup errors below report it.
    // Functions and methods. Each gets the stable path hash its caller computed
    // (src/def.rs). Hash collisions are checked by the driver when it assigns
    // slots from the same hashes, before `collect` runs on any new def set;
    // here the maps only record the hashes. A duplicate definition keeps the
    // first local id in `def_by_hash`; the dup errors below report it.
    //
    // A fn with generic parameters (its own, or its impl's) is a template:
    // its FnInfo holds the signature over `Param` tys, and mono appends a
    // concrete FnInfo per instance after this pass. Plain fns are their
    // own only instance, exactly as before generics.
    struct ParentGen {
        generics: Generics,
        scope: generics::Scope,
    }
    let plain_parent = || ParentGen { generics: Generics::default(), scope: generics::Scope::default() };
    let add_fn = |p: &mut Program<'a>,
                  def: &'a ast::FnDef,
                  owner: Option<AdtId>,
                  self_ty: Option<Ty>,
                  parent: Option<DefId>,
                  parent_gen: &ParentGen,
                  hash: DefPathHash,
                  errs: &mut Vec<Diag>|
     -> LocalDefId {
        let shift = parent_gen.generics.params.len() as u32;
        let (own_generics, own_scope) = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            generics::build_generics_shifted(ast, interner, known, &cx, &mut p.tys, &def.generics, &def.where_clause, shift, &parent_gen.scope, errs)
        };
        let mut generics = parent_gen.generics.clone();
        generics.params.extend(own_generics.params.iter().cloned());
        generics.predicates.extend(own_generics.predicates.iter().copied());
        generics.parent = parent;
        // A parameter may not reuse a name from the same list or
        // from the enclosing impl or trait (rustc E0403).
        for (i, param) in generics.params.iter().enumerate() {
            if generics.params[..i].iter().any(|q| q.name == param.name) {
                errs.push(Diag::new(
                    "L0106",
                    param.span,
                    format!("the parameter `{}` is already used for a parameter of an enclosing item", interner.get(param.name)),
                    "Rename one of the parameters.",
                ));
            }
        }
        let mut scope = parent_gen.scope.clone();
        scope.type_params.extend(own_scope.type_params.iter().copied());
        scope.const_params.extend(own_scope.const_params.iter().copied());
        scope.param_tys.extend(own_scope.param_tys.iter().copied());
        scope.assoc_srcs.extend(own_scope.assoc_srcs.iter().cloned());
        // Associated sources from every bound in the combined env,
        // so `T::Assoc` resolves in this signature.
        {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            let mut srcs = generics::assoc_srcs_of(&cx, &p.tys, &generics.predicates);
            scope.assoc_srcs.append(&mut srcs);
        }
        let (params, ret, ret_borrows_from, generics, scope) = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            generics::resolve_fn_sig(ast, interner, known, &mut p.tys, &cx, def, generics, &scope, self_ty, errs)
        };
        if def.self_param.is_some() && self_ty.is_none() {
            errs.push(Diag::new("L0001", def.name_span, "`self` parameter outside an impl", "Move this function into an impl block."));
        }
        let env = generics::elaborate_env(&mut p.tys, &p.gx.index, &generics.predicates);
        let is_template = !generics.params.is_empty();
        if is_template {
            p.gx.has_generics = true;
        }
        let id = LocalDefId(p.fns.len() as u32);
        let def_id = DefId { krate: p.krate, hash };
        p.fn_defs.push(def_id);
        p.def_by_hash.entry(hash).or_insert(id);
        // The def table record mirrors `FnInfo` for identity, kind, and generics;
        // body checking still reads `FnInfo` through the compat path.
        let mut data =
            DefData::skeleton(if owner.is_some() { DefsKind::Method } else { DefsKind::Fn }, parent, def.name, Vis::Priv, def.name_span);
        data.generics = generics.clone();
        data.sig = SigData::Fn { params: params.clone(), ret };
        p.defs.insert(def_id, data);
        p.fns.push(FnInfo {
            name: def.name,
            def,
            owner,
            self_kind: def.self_param.as_ref().map(|s| s.kind),
            params,
            ret,
            ret_borrows_from,
            is_const: def.qual.is_const,
        });
        p.gx.fn_templates.push(if is_template { Some(generics::FnTemplate { generics, env: env.clone() }) } else { None });
        // The body scope of a template keeps its parameters (the
        // abstract-instance check substitutes them); of a plain
        // fn it is empty but for Self and assoc sources.
        let mut body_scope = scope;
        if !is_template {
            body_scope.type_params.clear();
            body_scope.const_params.clear();
        }
        p.gx.fn_scopes.push(generics::FnScope { env, scope: body_scope });
        p.gx.fn_class.push(if is_template { generics::FnClass::Template } else { generics::FnClass::Plain });
        id
    };
    let mut impl_ordinals: HashMap<String, u32> = HashMap::default();
    for item in &ast.items {
        match &item.kind {
            ItemKind::Fn(def) => {
                let hash = crate::def::free_fn_hash(p.stable_crate, &[], interner.get(def.name));
                let id = add_fn(&mut p, def, None, None, None, &plain_parent(), hash, &mut errs);
                if p.fn_names.insert(def.name, id).is_some() {
                    errs.push(dup(def.name_span, interner.get(def.name)));
                }
                if def.name == known.main {
                    p.main = Some(id);
                }
            }
            ItemKind::Impl(imp) => {
                if imp.is_negative {
                    errs.push(not_yet("L0614", imp.span, "negative impls"));
                    continue;
                }
                // Impl identity header, computed exactly as the
                // driver's `fn_keys` computes it (self type's first
                // segment name, else "<error>"), with one ordinal
                // sequence per header across all impls.
                let header = match ast.ty(imp.self_ty) {
                    TyExpr::Path(segs) if !segs.is_empty() => interner.get(segs[0].name).to_string(),
                    _ => "<error>".to_string(),
                };
                let ordinal = impl_ordinals.get(&header).copied().unwrap_or(0);
                impl_ordinals.insert(header.clone(), ordinal + 1);
                let parent = crate::def::impl_hash(p.stable_crate, &[], &header, ordinal);
                let impl_def = DefId { krate: p.krate, hash: parent };
                p.defs.insert(impl_def, DefData::skeleton(DefsKind::Impl, None, known.self_type, Vis::Priv, imp.span));

                let (impl_generics, mut impl_scope) = {
                    let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                    generics::build_generics(ast, interner, known, &cx, &mut p.tys, &imp.generics, &imp.where_clause, &mut errs)
                };
                if !impl_generics.params.is_empty() {
                    p.gx.has_generics = true;
                }
                let self_pat = {
                    let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                    match generics::resolve_scoped(ast, interner, known, &cx, &mut p.tys, imp.self_ty, &impl_scope) {
                        Ok(t) => t,
                        Err(d) => {
                            errs.push(d);
                            continue;
                        }
                    }
                };
                // An impl for a projection (`impl Tr for
                // <S as X>::A`) stands for the normalized type
                // when the projection resolves through impls
                // already collected.
                let self_pat = generics::normalize_global(&mut p, self_pat);
                impl_scope.self_ty = Some(self_pat);
                // The owner template Adt, when the Self pattern is a
                // local Adt application (inherent and trait impls).
                let owner: Option<AdtId> = match p.tys.kind(self_pat) {
                    TyKind::Adt(def, _) => p.defs.local_adt(def),
                    _ => None,
                };
                let trait_ref = match &imp.trait_ref {
                    None => None,
                    Some(tref) => {
                        p.gx.has_generics = true;
                        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                        match generics::resolve_trait_ref(ast, interner, known, &cx, &mut p.tys, &impl_scope, self_pat, tref, imp.span) {
                            Ok(tr) => Some(tr),
                            Err(d) => {
                                errs.push(d);
                                continue;
                            }
                        }
                    }
                };
                // An inherent impl parameter must occur in the
                // Self type (rustc E0207's inherent half).
                if trait_ref.is_none() {
                    for (i, param) in impl_generics.params.iter().enumerate() {
                        let used = match param.kind {
                            ParamKind::Type => generics::ty_uses_param(&p.tys, self_pat, i as u32),
                            ParamKind::Const(_) => generics::ty_uses_const_param(&p.tys, self_pat, i as u32),
                            ParamKind::Lifetime => continue,
                        };
                        if !used {
                            errs.push(Diag::new(
                                "L0110",
                                param.span,
                                format!("the parameter `{}` is not used in the impl header", interner.get(param.name)),
                                "Use it in the Self type, or remove it.",
                            ));
                        }
                    }
                }
                if trait_ref.is_none() && owner.is_none() {
                    errs.push(Diag::new(
                        "L0102",
                        ast.ty_span(imp.self_ty),
                        "inherent impls must name a struct or enum defined in this file",
                        "Write `impl MyType { ... }`.",
                    ));
                    continue;
                }
                if trait_ref.is_none() {
                    p.gx.wf_headers.push((self_pat, impl_generics.clone(), imp.span));
                }
                // The impl's trait is an assoc source on the Self
                // pattern inside its method signatures.
                if let Some(tr) = &trait_ref
                    && let Some(rec) = p.gx.index.trait_record(tr.def).cloned()
                {
                    impl_scope.assoc_srcs.push(generics::AssocSrc {
                        self_ty: self_pat,
                        trait_def: tr.def,
                        args: tr.args,
                        assocs: rec.assoc_items.iter().map(|&(d, n, _)| (n, d)).collect(),
                    });
                }
                let parent_gen = ParentGen { generics: impl_generics.clone(), scope: impl_scope };
                let mut method_ids: Vec<LocalDefId> = Vec::new();
                for def in &imp.fns {
                    let hash = crate::def::method_hash(parent, interner.get(def.name));
                    let id = add_fn(&mut p, def, owner, Some(self_pat), Some(impl_def), &parent_gen, hash, &mut errs);
                    method_ids.push(id);
                    if trait_ref.is_none() {
                        // Inherent methods join the compat method
                        // table under the *template* Adt; instances
                        // get their own entries at materialization.
                        if let Some(owner) = owner {
                            p.methods.entry((owner, def.name)).or_default().push(id);
                            let adt_def = p.gx.adt_info[owner.0 as usize].0;
                            p.gx.inherent_methods.entry((adt_def, def.name)).or_default().push(id);
                            p.gx.inherent_self_pats.insert(id, (self_pat, parent_gen.generics.clone()));
                        }
                    }
                }
                if let Some(tr) = trait_ref {
                    generics::finish_trait_impl(
                        &mut p,
                        imp,
                        impl_def,
                        impl_generics,
                        self_pat,
                        tr,
                        &parent_gen.scope,
                        &method_ids,
                        &mut errs,
                    );
                }
                // Inherent associated consts are evaluated by
                // eval_assoc_consts below (W-RESOLVE phase 2).
            }
            _ => {}
        }
    }
    // Items inside function bodies: nested fns join the fn table (their
    // names are block-scoped, so they stay out of `fn_names`); nested
    // consts and statics evaluate with the top-level pass below. Type
    // items in bodies are not in the subset yet.
    for (idx, item) in ast.stmt_items.iter().enumerate() {
        match &item.kind {
            ItemKind::Fn(def) => {
                let path = format!("#nested{idx}");
                let hash = crate::def::free_fn_hash(p.stable_crate, &[path.as_str()], interner.get(def.name));
                let id = add_fn(&mut p, def, None, None, None, &plain_parent(), hash, &mut errs);
                p.body_items.insert(idx as u32, BodyItem::Fn(id));
            }
            ItemKind::Use(_) => {}
            ItemKind::Const(_) | ItemKind::Static(_) => {}
            _ => {
                errs.push(not_yet("L0820", item.span, "type items inside function bodies"));
            }
        }
    }
    // Sibling visibility for nested fns: the items of the block that
    // directly contains each nested fn.
    for block in &ast.blocks {
        let idxs: Vec<u32> = block
            .stmts
            .iter()
            .filter_map(|s| match s {
                ast::Stmt::Item(i) => Some(*i),
                _ => None,
            })
            .collect();
        if idxs.is_empty() {
            continue;
        }
        for &i in &idxs {
            if let Some(BodyItem::Fn(fid)) = p.body_items.get(&i).copied() {
                p.fn_siblings.insert(fid, idxs.clone());
            }
        }
    }
    generics::finish_collect(&mut p, &mut errs);
    if let Some(main) = p.main {
        let f = p.fn_info(main);
        // Rust's Termination for main: (), or Result<(), E> with E: Debug.
        let ret_ok = f.ret == UNIT || matches!(p.tys.result_args(f.ret), Some((ok, e)) if ok == UNIT && has_debug(&p, &p.tys, e));
        if !f.params.is_empty() || !ret_ok {
            errs.push(Diag::new(
                "L0110",
                f.def.name_span,
                "`main` must take no parameters and return () or Result<(), E> with E: Debug",
                "Write `fn main() { ... }` or `fn main() -> Result<(), E> { ... }`.",
            ));
        }
    }
    // Const and static items: register names first, then evaluate with the
    // bounded evaluator (ARCH 2.13). A failed item keeps a placeholder value
    // so one bad item reports once; collection fails anyway on the error.
    eval_const_items(&mut p, &mut errs);
    eval_assoc_consts(&mut p, &mut errs);

    if errs.is_empty() { Ok(p) } else { Err(errs) }
}

/// One const or static item waiting for evaluation.
struct PendingConst {
    name: Option<Sym>,
    /// Set for an item inside a function body: its stmt_items index.
    stmt_idx: Option<u32>,
    ty: Ty,
    expr: ast::ExprId,
    span: Span,
    /// Some(mutable) for a static, None for a const.
    is_static: Option<bool>,
    /// The index in `Program::statics` for a static item.
    static_idx: u32,
}

enum PendingState {
    Todo,
    Doing,
    Done(crate::ty::consteval::ConstValue),
    Failed,
}

/// Registers and evaluates every const and static item in the crate.
fn eval_const_items<'a>(p: &mut Program<'a>, errs: &mut Vec<Diag>) {
    let ast = p.ast;
    let mut pending: Vec<(PendingConst, PendingState)> = Vec::new();
    let mut by_name: HashMap<Sym, usize> = HashMap::default();
    let mut static_count = 0u32;
    for (item, stmt_idx) in ast.items.iter().map(|i| (i, None)).chain(ast.stmt_items.iter().enumerate().map(|(i, it)| (it, Some(i as u32))))
    {
        let (name, ty_id, value, span, is_static) = match &item.kind {
            ItemKind::Const(c) => (c.name, c.ty, c.value, c.span, None),
            ItemKind::Static(s) => (Some(s.name), s.ty, s.value, s.span, Some(s.mutable)),
            _ => continue,
        };
        let Some(value) = value else { continue };
        let ty = match resolve_ty(ast, p.interner, p.known, &p.type_names, &p.aliases, &mut p.tys, ty_id, None) {
            Ok(t) => t,
            Err(d) => {
                errs.push(d);
                continue;
            }
        };
        if !is_sized_ty(&p.tys, ty) {
            errs.push(Diag::new(
                "L0110",
                span,
                format!("the size for values of type `{}` cannot be known", ty_name(p, &p.tys, ty)),
                "Put the value behind a reference, such as `&[T]` or `&str`.",
            ));
            continue;
        }
        let static_idx = if is_static.is_some() {
            let i = static_count;
            static_count += 1;
            i
        } else {
            0
        };
        if let Some(n) = name {
            let dup = if stmt_idx.is_some() {
                // A nested name may shadow a top-level one; the by-name map
                // keeps the first registration for evaluation lookups.
                by_name.entry(n).or_insert(pending.len());
                false
            } else {
                by_name.insert(n, pending.len()).is_some() || p.fn_names.contains_key(&n)
            };
            if dup {
                errs.push(Diag::new(
                    "L0106",
                    span,
                    format!("`{}` is defined more than once", p.display_name(n)),
                    "Rename one of the definitions.",
                ));
            }
        }
        pending.push((PendingConst { name, stmt_idx, ty, expr: value, span, is_static, static_idx }, PendingState::Todo));
    }
    if pending.is_empty() {
        return;
    }
    let n = pending.len();
    let mut cx = CollectCx { p, pending, by_name, errs };
    for i in 0..n {
        cx.eval_pending(i);
    }
    // Move the results into the program tables, in item order.
    let CollectCx { p, pending, .. } = cx;
    let mut statics: Vec<Option<StaticItem>> = (0..static_count).map(|_| None).collect();
    for (item, state) in pending {
        let PendingState::Done(value) = state else { continue };
        match item.is_static {
            None if item.stmt_idx.is_some() => {
                if let Some(name) = item.name {
                    let idx = p.body_consts.len() as u32;
                    p.body_consts.push(ConstItem { name, ty: item.ty, value });
                    p.body_items.insert(item.stmt_idx.unwrap(), BodyItem::Const(idx));
                }
            }
            None => {
                if let Some(name) = item.name {
                    let idx = p.consts.len() as u32;
                    p.const_names.insert(name, idx);
                    let disamb = 0;
                    let hash = crate::def::item_hash(p.stable_crate, &[], crate::def::DefKind::Const, p.interner.get(name), disamb);
                    let def = DefId { krate: p.krate, hash };
                    p.defs.insert(def, DefData::skeleton(DefsKind::Const, None, name, Vis::Priv, item.span));
                    p.const_defs.push(def);
                    p.consts.push(ConstItem { name, ty: item.ty, value });
                }
            }
            Some(mutable) => {
                let name = item.name.unwrap();
                if let Some(sidx) = item.stmt_idx {
                    p.body_items.insert(sidx, BodyItem::Static(item.static_idx));
                }
                // Top-level statics join the crate name tables; nested ones
                // resolve through the checker's block item scopes instead.
                if item.stmt_idx.is_none() {
                    let hash = crate::def::item_hash(p.stable_crate, &[], crate::def::DefKind::Static, p.interner.get(name), 0);
                    let def = DefId { krate: p.krate, hash };
                    p.defs.insert(def, DefData::skeleton(DefsKind::Static, None, name, Vis::Priv, item.span));
                    if p.static_defs.len() <= item.static_idx as usize {
                        p.static_defs.resize(item.static_idx as usize + 1, def);
                    }
                    p.static_defs[item.static_idx as usize] = def;
                    p.static_names.insert(name, item.static_idx);
                } else if p.static_defs.len() <= item.static_idx as usize {
                    p.static_defs.resize(item.static_idx as usize + 1, DefId { krate: p.krate, hash: crate::def::DefPathHash(0) });
                }
                statics[item.static_idx as usize] = Some(StaticItem { name, ty: item.ty, mutable, value });
            }
        }
    }
    p.statics = statics
        .into_iter()
        .map(|s| s.unwrap_or(StaticItem { name: Sym(0), ty: ERROR, mutable: false, value: crate::ty::consteval::ConstValue::Unit }))
        .collect();
}

/// Registers and evaluates the associated consts of inherent impls
/// (W-RESOLVE phase 2, on the merged evaluator). They become const
/// items with child defs under their impl, found through
/// `assoc_const_names` only: initializers read free consts through
/// the same context fallback as other const items, never other
/// associated consts by plain name (Rust requires `Self::` there).
fn eval_assoc_consts<'a>(p: &mut Program<'a>, errs: &mut Vec<Diag>) {
    let ast = p.ast;
    let mut pending: Vec<(PendingConst, PendingState)> = Vec::new();
    let mut owners: Vec<(AdtId, DefId, Sym)> = Vec::new();
    // Impl ordinals must match the fn pass exactly (same iteration,
    // same owner test), so child hashes name the same impl.
    let mut impl_ordinals: HashMap<String, u32> = HashMap::default();
    for item in &ast.items {
        let ItemKind::Impl(imp) = &item.kind else { continue };
        if imp.is_negative || imp.trait_ref.is_some() {
            // The fn pass still consumes an ordinal for these (its
            // header is the self type's first segment, counted before
            // any continue), then handles or rejects them itself.
            let header = match ast.ty(imp.self_ty) {
                TyExpr::Path(segs) if !segs.is_empty() => p.interner.get(segs[0].name).to_string(),
                _ => "<error>".to_string(),
            };
            let o = impl_ordinals.get(&header).copied().unwrap_or(0);
            impl_ordinals.insert(header, o + 1);
            continue;
        }
        let header = match ast.ty(imp.self_ty) {
            TyExpr::Path(segs) if !segs.is_empty() => p.interner.get(segs[0].name).to_string(),
            _ => "<error>".to_string(),
        };
        let ordinal = impl_ordinals.get(&header).copied().unwrap_or(0);
        impl_ordinals.insert(header.clone(), ordinal + 1);
        let owner = match ast.ty(imp.self_ty) {
            TyExpr::Path(segs) if segs.len() == 1 => p.type_names.get(&segs[0].name).copied(),
            _ => None,
        };
        let Some(owner) = owner else { continue };
        if imp.consts.is_empty() {
            continue;
        }
        let parent_hash = crate::def::impl_hash(p.stable_crate, &[], &header, ordinal);
        let impl_def = DefId { krate: p.krate, hash: parent_hash };
        let self_ty = p.tys.adt_ty(owner);
        for c in &imp.consts {
            if owners.iter().any(|&(o, _, n)| o == owner && n == c.name) || p.methods.contains_key(&(owner, c.name)) {
                errs.push(Diag::new(
                    "L0106",
                    c.name_span,
                    format!("`{}` is defined more than once", p.interner.get(c.name)),
                    "Rename one of the definitions.",
                ));
                continue;
            }
            let ty = match resolve_ty(ast, p.interner, p.known, &p.type_names, &p.aliases, &mut p.tys, c.ty, Some(self_ty)) {
                Ok(t) => t,
                Err(d) => {
                    errs.push(d);
                    continue;
                }
            };
            let Some(value) = c.default else {
                errs.push(not_yet("L0632", c.name_span, "associated consts without a value"));
                continue;
            };
            owners.push((owner, impl_def, c.name));
            pending.push((
                PendingConst { name: Some(c.name), ty, expr: value, span: c.span, is_static: None, static_idx: 0, stmt_idx: None },
                PendingState::Todo,
            ));
        }
    }
    if pending.is_empty() {
        return;
    }
    let n = pending.len();
    let mut cx = CollectCx { p, pending, by_name: HashMap::default(), errs };
    for i in 0..n {
        cx.eval_pending(i);
    }
    let CollectCx { p, pending, .. } = cx;
    for ((item, state), (owner, impl_def, name)) in pending.into_iter().zip(owners) {
        let PendingState::Done(value) = state else { continue };
        let idx = p.consts.len() as u32;
        let hash = crate::def::child_hash(impl_def.hash, crate::def::DefKind::Const, p.interner.get(name), 0);
        let def = DefId { krate: p.krate, hash };
        p.defs.insert(def, DefData::skeleton(DefsKind::Const, Some(impl_def), name, Vis::Priv, item.span));
        p.const_defs.push(def);
        p.consts.push(ConstItem { name, ty: item.ty, value });
        p.assoc_const_names.insert((owner, name), idx);
    }
}

/// The const evaluator's context over the collected tables.
struct CollectCx<'x, 'a> {
    p: &'x mut Program<'a>,
    pending: Vec<(PendingConst, PendingState)>,
    by_name: HashMap<Sym, usize>,
    errs: &'x mut Vec<Diag>,
}

impl CollectCx<'_, '_> {
    /// Evaluates one pending item, on demand from other items.
    fn eval_pending(&mut self, idx: usize) -> Option<crate::ty::consteval::ConstValue> {
        match &self.pending[idx].1 {
            PendingState::Done(v) => return Some(v.clone()),
            PendingState::Failed => return None,
            PendingState::Doing => {
                let span = self.pending[idx].0.span;
                self.errs.push(Diag::new(
                    "L0110",
                    span,
                    "const items form a cycle",
                    "Break the cycle: a const item cannot use its own value.",
                ));
                self.pending[idx].1 = PendingState::Failed;
                return None;
            }
            PendingState::Todo => {}
        }
        self.pending[idx].1 = PendingState::Doing;
        let (expr, ty, span) = {
            let it = &self.pending[idx].0;
            (it.expr, it.ty, it.span)
        };
        match crate::ty::consteval::eval(self, expr, Some(ty)) {
            Ok((v, vt)) => {
                if self.pending[idx].0.is_static.is_some() && !static_form(self.p, &v, ty) {
                    self.errs.push(Diag::new(
                        crate::ty::consteval::C_OUTSIDE,
                        span,
                        "this static value form is outside the bounded const evaluator",
                        "Use a tagged enum form the static data emitter supports, or a const item.",
                    ));
                    self.pending[idx].1 = PendingState::Failed;
                    return None;
                }
                let v = match coerce_const_value(self, v, vt, ty, span) {
                    Ok(v) => v,
                    Err(d) => {
                        self.errs.push(d);
                        self.pending[idx].1 = PendingState::Failed;
                        return None;
                    }
                };
                self.pending[idx].1 = PendingState::Done(v.clone());
                Some(v)
            }
            Err(d) => {
                // A name in the message helps when the span is deep inside.
                self.errs.push(d);
                self.pending[idx].1 = PendingState::Failed;
                None
            }
        }
    }
}

/// True when static data emission can write this value as a C
/// initializer. Every variant form qualifies today, niche-filled
/// enums included: the emitter sets the niche scalar through the
/// variant struct's `_s` member in the same designator (W-CGEN).
fn static_form(p: &Program, v: &crate::ty::consteval::ConstValue, ty: Ty) -> bool {
    use crate::ty::consteval::ConstValue as CV;
    match v {
        CV::Variant(variant, vals) => {
            let elem_tys: Vec<Ty> = match p.tys.kind(ty) {
                _ if p.tys.option_elem(ty).is_some() => vec![p.tys.option_elem(ty).unwrap()],
                _ if p.tys.result_args(ty).is_some() => {
                    let (a, b) = p.tys.result_args(ty).unwrap();
                    vec![if *variant == 0 { a } else { b }]
                }
                _ => match p.tys.local_adt(ty) {
                    Some(a) => p.adt(a).variants[*variant as usize].fields.iter().map(|f| f.ty).collect(),
                    None => vec![ERROR; vals.len()],
                },
            };
            vals.iter().enumerate().all(|(i, x)| static_form(p, x, elem_tys.get(i).copied().unwrap_or(ERROR)))
        }
        CV::Aggregate(vals) => {
            let elem_tys: Vec<Ty> = match p.tys.kind(ty) {
                TyKind::Tuple(ts) => p.tys.tys_of(ts).to_vec(),
                TyKind::Array(e, _) => vec![e; vals.len()],
                _ => match p.tys.local_adt(ty) {
                    Some(a) => p.adt(a).variants[0].fields.iter().map(|f| f.ty).collect(),
                    None => vec![ERROR; vals.len()],
                },
            };
            vals.iter().enumerate().all(|(i, x)| static_form(p, x, elem_tys.get(i).copied().unwrap_or(ERROR)))
        }
        CV::Repeat(x, _) => match p.tys.kind(ty) {
            TyKind::Array(e, _) => static_form(p, x, e),
            _ => true,
        },
        CV::Ref(inner) => match p.tys.kind(ty) {
            TyKind::Ref(_, _, it) => static_form(p, inner, it),
            _ => true,
        },
        _ => true,
    }
}

/// Accepts an evaluated value for a declared item type only when the
/// value's type is the declared type, up to the unsized coercions in
/// `const_ty_compatible`. Tuple arity and array length are in the type the
/// evaluator builds, so they are checked here too. One more form passes: a
/// `None` variant, whose type the evaluator cannot name before the declared
/// `Option` type is known.
fn coerce_const_value(
    cx: &mut CollectCx<'_, '_>,
    v: crate::ty::consteval::ConstValue,
    vt: Ty,
    ty: Ty,
    span: Span,
) -> Result<crate::ty::consteval::ConstValue, Diag> {
    use crate::ty::consteval::ConstValue;
    if crate::ty::consteval::const_ty_compatible(&cx.p.tys, vt, ty) {
        return Ok(v);
    }
    if matches!(&v, ConstValue::Variant(0, vals) if vals.is_empty()) && cx.p.tys.option_elem(ty).is_some() {
        return Ok(v);
    }
    Err(Diag::new(
        "L0110",
        span,
        format!("mismatched types: expected `{}`, found `{}`", ty_name(cx.p, &cx.p.tys, ty), ty_name(cx.p, &cx.p.tys, vt)),
        "Change the value or the declared type.",
    ))
}

impl<'a> crate::ty::consteval::ConstCx<'a> for CollectCx<'_, 'a> {
    type Tys = GlobalTys;

    fn tys(&mut self) -> &mut GlobalTys {
        &mut self.p.tys
    }
    fn tys_ref(&self) -> &GlobalTys {
        &self.p.tys
    }
    fn ast(&self) -> &'a Ast {
        self.p.ast
    }
    fn sym_text(&self, s: Sym) -> &str {
        self.p.interner.get(s)
    }
    fn const_item(&mut self, name: Sym) -> Option<crate::ty::consteval::TypedValue> {
        if let Some(&i) = self.by_name.get(&name) {
            let ty = self.pending[i].0.ty;
            return self.eval_pending(i).map(|v| (v, ty));
        }
        self.p.const_names.get(&name).map(|&i| {
            let c = &self.p.consts[i as usize];
            (c.value.clone(), c.ty)
        })
    }
    fn static_item(&mut self, name: Sym) -> Option<(u32, Ty)> {
        if let Some(&i) = self.by_name.get(&name)
            && self.pending[i].0.is_static.is_some()
        {
            let it = &self.pending[i].0;
            return Some((it.static_idx, it.ty));
        }
        self.p.static_names.get(&name).map(|&i| (i, self.p.statics[i as usize].ty))
    }
    fn call_target(&mut self, callee: ast::ExprId) -> crate::ty::consteval::CallTarget {
        use crate::ty::consteval::{CallTarget, ConstFnBody};
        let ast::Expr::Path(segs) = self.p.ast.expr(callee) else { return CallTarget::Unknown };
        let last = segs[segs.len() - 1].name;
        let ltext = self.p.interner.get(last).to_string();
        if ltext == "size_of" || ltext == "align_of" {
            let ok_path = segs.len() == 1
                || (segs.len() == 3
                    && matches!(self.p.interner.get(segs[0].name), "std" | "core")
                    && self.p.interner.get(segs[1].name) == "mem");
            if ok_path {
                let args = segs[segs.len() - 1].type_args();
                if args.len() == 1 {
                    let t = resolve_ty(
                        self.p.ast,
                        self.p.interner,
                        self.p.known,
                        &self.p.type_names,
                        &self.p.aliases,
                        &mut self.p.tys,
                        args[0],
                        None,
                    )
                    .unwrap_or(ERROR);
                    return if ltext == "size_of" { CallTarget::SizeOf(t) } else { CallTarget::AlignOf(t) };
                }
            }
            return CallTarget::Unknown;
        }
        if segs.len() == 1 && last == self.p.known.Some {
            return CallTarget::VariantCtor { adt: AdtId(u32::MAX), variant: 1, ty: ERROR };
        }
        // The Result shim sits one below the Option shim (u32::MAX):
        // Ok is variant 0, Err is variant 1.
        if segs.len() == 1 && last == self.p.known.Ok {
            return CallTarget::VariantCtor { adt: AdtId(u32::MAX - 1), variant: 0, ty: ERROR };
        }
        if segs.len() == 1 && last == self.p.known.Err {
            return CallTarget::VariantCtor { adt: AdtId(u32::MAX - 1), variant: 1, ty: ERROR };
        }
        let fid = if segs.len() == 1 {
            self.p.fn_names.get(&last).copied()
        } else if segs.len() == 2 {
            match self.p.type_names.get(&segs[0].name) {
                Some(&a) => self.p.methods.get(&(a, last)).and_then(|fs| fs.first()).copied(),
                None => None,
            }
        } else {
            None
        };
        if let Some(f) = fid {
            let info = self.p.fn_info(f);
            if !info.is_const {
                return CallTarget::NonConst;
            }
            let Some(body) = info.def.body else { return CallTarget::NonConst };
            let skip = if info.self_kind.is_some() { 1 } else { 0 };
            if skip == 1 {
                return CallTarget::Unknown;
            }
            let params: Vec<(Sym, bool, Option<ast::PatId>)> = info.def.params.iter().map(|pp| (pp.name, pp.mutable, pp.pat)).collect();
            return CallTarget::ConstFn(ConstFnBody { params, param_tys: info.params.clone(), ret: info.ret, body });
        }
        if let Some((adt, variant, ty)) = self.variant_ctor(segs) {
            return CallTarget::VariantCtor { adt, variant, ty };
        }
        // Known std constructors that are not const fn here report NonConst,
        // so `static S: String = String::from(..)` gets the right error.
        if segs.len() == 2 && matches!(self.p.interner.get(segs[0].name), "String" | "Vec") {
            return CallTarget::NonConst;
        }
        CallTarget::Unknown
    }
    fn unit_variant(&mut self, segs: &[ast::PathSeg], expected: Option<Ty>) -> Option<(AdtId, u32, Ty)> {
        if segs.len() == 1 && segs[0].name == self.p.known.None {
            let elem = expected.and_then(|t| self.p.tys.option_elem(t)).unwrap_or(ERROR);
            let ty = self.p.tys.mk_option(elem);
            return Some((AdtId(u32::MAX), 0, ty));
        }
        let (adt, variant) = self.variant_of(segs)?;
        if self.p.adt(adt).variants[variant as usize].shape != VariantShape::Unit {
            return None;
        }
        Some((adt, variant, self.p.tys.adt_ty(adt)))
    }
    fn struct_target(&mut self, path: &[ast::PathSeg]) -> Option<(AdtId, u32, Ty)> {
        let (adt, variant) = self.variant_of(path)?;
        Some((adt, variant, self.p.tys.adt_ty(adt)))
    }
    fn pattern_variant(&mut self, segs: &[ast::PathSeg]) -> Option<(AdtId, u32)> {
        self.variant_of(segs)
    }
    fn variant_fields(&self, adt: AdtId, variant: u32) -> Vec<(Sym, Ty)> {
        if adt.0 >= u32::MAX - 1 {
            return Vec::new();
        }
        self.p.adt(adt).variants[variant as usize].fields.iter().map(|f| (f.name, f.ty)).collect()
    }
    fn resolve_ty(&mut self, t: ast::TyId) -> Ty {
        resolve_ty(self.p.ast, self.p.interner, self.p.known, &self.p.type_names, &self.p.aliases, &mut self.p.tys, t, None)
            .unwrap_or(ERROR)
    }
    fn layout(&mut self, t: Ty) -> Option<crate::ty::layout::Layout> {
        let p: &Program<'_> = self.p;
        crate::ty::layout::layout_of_ty(&p.tys, p, t).ok()
    }
    fn adt_repr(&self, adt: AdtId) -> crate::ty::layout::Repr {
        self.p.adt(adt).repr
    }
    fn discriminant(&self, adt: AdtId, variant: u32) -> i128 {
        self.p.adt(adt).variants[variant as usize].disc
    }
    fn is_enum(&self, adt: AdtId) -> bool {
        adt.0 < u32::MAX - 1 && self.p.adt(adt).is_enum
    }
}

impl CollectCx<'_, '_> {
    /// A tuple variant constructor path, for calls in const position.
    fn variant_ctor(&self, segs: &[ast::PathSeg]) -> Option<(AdtId, u32, Ty)> {
        let (adt, variant) = self.variant_of(segs)?;
        if self.p.adt(adt).variants[variant as usize].shape != VariantShape::Tuple {
            return None;
        }
        Some((adt, variant, self.p.tys.get_adt_ty(adt).unwrap_or(ERROR)))
    }

    /// The (Adt, variant) a two-segment path or a struct name denotes.
    fn variant_of(&self, segs: &[ast::PathSeg]) -> Option<(AdtId, u32)> {
        if segs.len() == 1 {
            let &a = self.p.type_names.get(&segs[0].name)?;
            if self.p.adt(a).is_enum {
                return None;
            }
            return Some((a, 0));
        }
        if segs.len() == 2 {
            let &a = self.p.type_names.get(&segs[0].name)?;
            let v = self.p.adt(a).variants.iter().position(|v| v.name == segs[1].name)?;
            return Some((a, v as u32));
        }
        None
    }
}

pub fn contains_ref(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(..) => true,
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| contains_ref(tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) => contains_ref(tys, e),
        _ if tys.is_chars_ty(t) => true,
        _ => match tys.vec_elem(t).or_else(|| tys.option_elem(t)) {
            Some(e) => contains_ref(tys, e),
            None => match tys.result_args(t) {
                Some((a, b)) => contains_ref(tys, a) || contains_ref(tys, b),
                None => false,
            },
        },
    }
}

fn contains_adt_by_value(p: &Program, root: AdtId, cur: AdtId, seen: &mut Vec<bool>) -> bool {
    if seen[cur.0 as usize] {
        return false;
    }
    seen[cur.0 as usize] = true;
    for v in &p.adt(cur).variants {
        for f in &v.fields {
            if type_holds_adt_by_value(p, root, f.ty, seen) {
                return true;
            }
        }
    }
    false
}

/// True when a type has a known size and may sit in a field, parameter, or
/// return slot. Bare slices, `str`, and `dyn` are unsized; they may only
/// appear behind a reference (ARCH 2.7 `Sized` basics).
pub fn is_sized_ty(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Slice(_) | TyKind::Str | TyKind::Dyn(..) => false,
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| is_sized_ty(tys, e)),
        TyKind::Array(e, _) => is_sized_ty(tys, e),
        TyKind::Adt(..) => match tys.adt_first_ty_arg(t) {
            Some(e) if tys.vec_elem(t).is_some() || tys.option_elem(t).is_some() => is_sized_ty(tys, e),
            _ => match tys.result_args(t) {
                Some((a, b)) => is_sized_ty(tys, a) && is_sized_ty(tys, b),
                None => true,
            },
        },
        _ => true,
    }
}

/// True when a field type holds the root Adt by value, through Option, tuple,
/// and array wrappers (all of which store their elements inline).
fn type_holds_adt_by_value(p: &Program, root: AdtId, t: Ty, seen: &mut Vec<bool>) -> bool {
    match p.tys.kind(t) {
        TyKind::Tuple(ts) => p.tys.tys_of(ts).iter().any(|&e| type_holds_adt_by_value(p, root, e, seen)),
        TyKind::Array(e, _) => type_holds_adt_by_value(p, root, e, seen),
        _ => {
            if let Some(inner) = p.tys.option_elem(t) {
                return type_holds_adt_by_value(p, root, inner, seen);
            }
            if let Some((a, b)) = p.tys.result_args(t) {
                return type_holds_adt_by_value(p, root, a, seen) || type_holds_adt_by_value(p, root, b, seen);
            }
            match p.tys.local_adt(t) {
                Some(a) => a == root || contains_adt_by_value(p, root, a, seen),
                None => false,
            }
        }
    }
}

// Trait queries. Lust has no user traits yet, so these follow fixed rules plus derives.

// The queries below follow the old fixed rules, now read through the v2 compat
// helpers: builtin Adts answer through `BuiltinTy`, user Adts through their derives.

/// True when the param env of the body `tys` belongs to (see
/// `Tys::env`) has the bound `t: trait_def`, with `rhs` as the
/// second trait argument when given. The answer for a `Param` or
/// projection type: it has exactly the traits its bounds give it.
fn env_proves(tys: &impl TyIntern, t: Ty, trait_def: DefId, rhs: Option<Ty>) -> bool {
    tys.param_env().iter().any(|pred| match pred {
        Predicate::Trait(b) if b.count == 0 && b.value.def == trait_def => {
            let a = tys.args(b.value.args);
            a.first().and_then(|g| g.as_ty()) == Some(t) && rhs.is_none_or(|r| a.get(1).and_then(|g| g.as_ty()) == Some(r))
        }
        _ => false,
    })
}

pub fn is_copy(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => env_proves(tys, t, p.gx.lang.copy, None),
        TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Never | TyKind::Error => true,
        // Fn items, fn pointers, and (non-capturing) closures are Copy.
        TyKind::FnDef(..) | TyKind::FnPtr(_) | TyKind::Closure(..) => true,
        TyKind::Infer(v) => v.is_int() || v.is_float(),
        TyKind::Ref(_, m, _) => !m.is_mut(),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| is_copy(p, tys, e)),
        TyKind::Array(e, _) => is_copy(p, tys, e),
        _ => {
            if let Some(e) = tys.option_elem(t) {
                return is_copy(p, tys, e);
            }
            if let Some((a, b)) = tys.result_args(t) {
                return is_copy(p, tys, a) && is_copy(p, tys, b);
            }
            match tys.local_adt(t) {
                Some(a) => {
                    p.adt(a).derives.copy
                        && (p.gx.adt_generics.get(a.0 as usize).is_none_or(|g| g.params.is_empty())
                            && p.gx.adt_instance_of.get(a.0 as usize).is_none_or(|o| o.is_none())
                            || p.adt(a).variants.iter().all(|v| v.fields.iter().all(|f| is_copy(p, tys, f.ty))))
                }
                None => false,
            }
        }
    }
}

pub fn has_clone(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => return env_proves(tys, t, p.gx.lang.clone, None),
        TyKind::Tuple(ts) => return tys.tys_of(ts).iter().all(|&e| has_clone(p, tys, e)),
        TyKind::Array(e, _) => return has_clone(p, tys, e),
        _ => {}
    }
    if tys.is_string_ty(t) {
        return true;
    }
    if let Some(e) = tys.vec_elem(t).or_else(|| tys.option_elem(t)) {
        return has_clone(p, tys, e);
    }
    if let Some((a, b)) = tys.result_args(t) {
        return has_clone(p, tys, a) && has_clone(p, tys, b);
    }
    match tys.local_adt(t) {
        Some(a) => {
            p.adt(a).derives.clone
                && (p.gx.adt_instance_of.get(a.0 as usize).is_none_or(|o| o.is_none())
                    || p.adt(a).variants.iter().all(|v| v.fields.iter().all(|f| has_clone(p, tys, f.ty))))
        }
        None => is_copy(p, tys, t),
    }
}

/// True when the ordering operators apply in the subset today:
/// scalars, strings, and tuples of orderable elements (lowered as a
/// lexicographic expansion). Arrays, slices, and Adts stay rejects.
pub fn has_ord(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => env_proves(tys, t, p.gx.lang.partial_ord, Some(t)),
        TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Str | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int() || v.is_float(),
        TyKind::Ref(_, _, e) => has_ord(p, tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| has_ord(p, tys, e)),
        _ => tys.is_string_ty(t),
    }
}

pub fn has_eq(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => env_proves(tys, t, p.gx.lang.partial_eq, Some(t)),
        // Fn pointers compare by address in Rust; fn items do not.
        TyKind::FnPtr(_) => true,
        TyKind::Float(_) => true,
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Str | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int() || v.is_float(),
        TyKind::Ref(_, _, e) => has_eq(p, tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| has_eq(p, tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) => has_eq(p, tys, e),
        _ => {
            if tys.is_string_ty(t) {
                return true;
            }
            if let Some(e) = tys.vec_elem(t).or_else(|| tys.option_elem(t)) {
                return has_eq(p, tys, e);
            }
            if let Some((a, b)) = tys.result_args(t) {
                return has_eq(p, tys, a) && has_eq(p, tys, b);
            }
            match tys.local_adt(t) {
                Some(a) => {
                    p.adt(a).derives.partial_eq
                        && (p.gx.adt_instance_of.get(a.0 as usize).is_none_or(|o| o.is_none())
                            || p.adt(a).variants.iter().all(|v| v.fields.iter().all(|f| has_eq(p, tys, f.ty))))
                }
                None => false,
            }
        }
    }
}

pub fn has_debug(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => env_proves(tys, t, p.gx.lang.debug, None),
        TyKind::Float(_) => true,
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Str | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int() || v.is_float(),
        TyKind::Ref(_, _, e) => has_debug(p, tys, e),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| has_debug(p, tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) => has_debug(p, tys, e),
        _ => {
            if tys.is_string_ty(t) || tys.builtin_of(t) == Some(BuiltinTy::Args) {
                return true;
            }
            if let Some(e) = tys.vec_elem(t).or_else(|| tys.option_elem(t)) {
                return has_debug(p, tys, e);
            }
            if let Some((a, b)) = tys.result_args(t) {
                return has_debug(p, tys, a) && has_debug(p, tys, b);
            }
            match tys.local_adt(t) {
                Some(a) => {
                    p.adt(a).derives.debug
                        && (p.gx.adt_instance_of.get(a.0 as usize).is_none_or(|o| o.is_none())
                            || p.adt(a).variants.iter().all(|v| v.fields.iter().all(|f| has_debug(p, tys, f.ty))))
                }
                None => false,
            }
        }
    }
}

pub fn has_display(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => env_proves(tys, t, p.gx.lang.display, None),
        TyKind::Float(_) => true,
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Str | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int() || v.is_float(),
        TyKind::Ref(_, _, e) => has_display(p, tys, e),
        _ => tys.is_string_ty(t),
    }
}

/// True if values of this type own heap memory and need a drop call.
/// A `Param` or projection type may (rustc's drop check assumes so).
pub fn needs_drop(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => return true,
        TyKind::Tuple(ts) => return tys.tys_of(ts).iter().any(|&e| needs_drop(p, tys, e)),
        TyKind::Array(e, _) => return needs_drop(p, tys, e),
        _ => {}
    }
    if tys.is_string_ty(t) || tys.vec_elem(t).is_some() {
        return true;
    }
    if let Some(e) = tys.option_elem(t) {
        return needs_drop(p, tys, e);
    }
    if let Some((a, b)) = tys.result_args(t) {
        return needs_drop(p, tys, a) || needs_drop(p, tys, b);
    }
    match tys.local_adt(t) {
        Some(a) => {
            p.gx.drop_methods.contains_key(&a) || p.adt(a).variants.iter().any(|v| v.fields.iter().any(|f| needs_drop(p, &p.tys, f.ty)))
        }
        None => false,
    }
}

/// Layout shapes for the engine in `ty::layout`, read from the collected tables.
impl crate::ty::layout::AdtShapes for Program<'_> {
    fn adt_shape(&self, id: AdtId) -> Option<crate::ty::layout::AdtShape> {
        let adt = self.adts.get(id.0 as usize)?;
        Some(crate::ty::layout::AdtShape {
            repr: adt.repr,
            is_enum: adt.is_enum,
            variants: adt.variants.iter().map(|v| v.fields.iter().map(|f| f.ty).collect()).collect(),
            discs: adt.variants.iter().map(|v| v.disc).collect(),
        })
    }
}
