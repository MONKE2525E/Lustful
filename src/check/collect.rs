// Collection: builds the item tables (types, functions, methods) and resolves all signatures.
// This is the only stage that runs in sequence. Function bodies are checked after it, in parallel.
use crate::ast::{self, Ast, ItemKind, SelfKind, TyExpr, VariantFields};
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
}

/// The old name for the session-local function index. New code uses
/// `LocalDefId` (src/def.rs); the alias stays while S3b edits this file in
/// parallel, then goes.
#[allow(dead_code)]
pub type FnId = LocalDefId;

/// A scalar constant value from the bounded evaluator (ARCH 2.13's
/// non-generic form, landed with W-RESOLVE's item collection). Integers
/// are stored as the low 64 bits of the value in the declared width,
/// sign-extended by readers that know the type.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstValue {
    Int(u64),
    Bool(bool),
    Char(char),
    /// Index into the AST string table.
    Str(u32),
}

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
    pub type_names: HashMap<Sym, AdtId>,
    /// Non-generic type aliases by (flat) name, fully resolved.
    pub aliases: HashMap<Sym, Ty>,
    /// `const` and non-mut `static` scalar values by (flat) name.
    pub consts: HashMap<Sym, (Ty, ConstValue)>,
    pub fn_names: HashMap<Sym, LocalDefId>,
    pub methods: HashMap<(AdtId, Sym), LocalDefId>,
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
}

impl<'a> Program<'a> {
    pub fn name(&self, s: Sym) -> &str {
        self.interner.get(s)
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
            Some(BuiltinTy::Chars) => "std::str::Chars".into(),
            Some(BuiltinTy::Args) => "std::env::Args".into(),
            None => match tys.local_adt(t) {
                Some(a) => p.name(p.adt(a).name).into(),
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
            if let Some(&adt) = type_names.get(&name) {
                return no_generics(tys.adt_ty(adt));
            }
            if let Some(&t) = aliases.get(&name) {
                return no_generics(t);
            }
            let n = interner.get(name);
            if ["HashMap", "HashSet", "BTreeMap", "Result", "Box", "Rc", "Arc", "RefCell", "Cell", "f32", "f64", "i128", "u128"]
                .contains(&n)
            {
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
            let n = eval_array_len(ast, *len).ok_or_else(|| {
                Diag::new("L0110", span, "array length must be a constant integer", "Write a literal length such as `[u8; 4]`.")
            })?;
            let c = tys.intern_const(ConstKind::Int(n));
            Ok(tys.intern(TyKind::Array(e, c)))
        }
        TyExpr::Paren(inner) => resolve_ty(ast, interner, known, type_names, aliases, tys, *inner, self_ty),
        _ => Err(not_yet("L0602", span, "this type form")),
    }
}

/// Evaluates an array length expression at collection time. Only literal
/// integer arithmetic is in the bound today; named consts join with the
/// const evaluator (ARCH 2.13) in `ty::consteval`.
pub fn eval_array_len(ast: &Ast, e: ast::ExprId) -> Option<u128> {
    use crate::ast::{BinOp, Expr, UnOp};
    match ast.expr(e) {
        Expr::Int(v, _) => Some(*v as u128),
        Expr::Unary { op: UnOp::Neg, .. } => None,
        Expr::Binary { op, lhs, rhs } => {
            let (a, b) = (eval_array_len(ast, *lhs)?, eval_array_len(ast, *rhs)?);
            match op {
                BinOp::Add => a.checked_add(b),
                BinOp::Sub => a.checked_sub(b),
                BinOp::Mul => a.checked_mul(b),
                BinOp::Div => a.checked_div(b),
                BinOp::Rem => a.checked_rem(b),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Evaluates a constant integer expression at collection time: literals,
/// negation and bit-not, integer arithmetic and shifts, and `as` casts
/// between integer types. Returns None for anything else. The full bounded
/// evaluator lives in `ty::consteval` (ARCH 2.13); this is its scalar subset
/// for discriminants and array lengths, which collect needs before bodies run.
pub fn eval_const_int(ast: &Ast, interner: &Interner, known: &Known, e: ast::ExprId) -> Option<i128> {
    use crate::ast::{BinOp, Expr, UnOp};
    match ast.expr(e) {
        Expr::Int(v, _) => Some(*v as u128 as i128),
        Expr::Char(c) => Some(*c as i128),
        Expr::Bool(b) => Some(*b as i128),
        Expr::Unary { op, expr } => {
            let v = eval_const_int(ast, interner, known, *expr)?;
            match op {
                UnOp::Neg => v.checked_neg(),
                UnOp::Not => Some(!v),
            }
        }
        Expr::Binary { op, lhs, rhs } => {
            let (a, b) = (eval_const_int(ast, interner, known, *lhs)?, eval_const_int(ast, interner, known, *rhs)?);
            match op {
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
            }
        }
        Expr::Cast { expr, ty } => {
            let v = eval_const_int(ast, interner, known, *expr)?;
            let target = match ast.ty(*ty) {
                TyExpr::Path(segs) if segs.len() == 1 => known.int_ty(segs[0].name),
                _ => None,
            };
            match target {
                Some(it) => Some(truncate_to_int(v, it)),
                None if matches!(ast.ty(*ty), TyExpr::Path(segs) if segs.len() == 1 && segs[0].name == known.char) => Some(v),
                _ => None,
            }
        }
        Expr::Block(b) => match ast.block(*b).tail {
            Some(tail) if ast.block(*b).stmts.is_empty() => eval_const_int(ast, interner, known, tail),
            _ => None,
        },
        _ => {
            let _ = interner;
            None
        }
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
                                    Tok::Int(n, _) if n > 0 && n.is_power_of_two() => {
                                        repr.align = Some(n);
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
/// Tuple fields get their index as a synthetic name, as they had before AST v2.
fn variant_fields_src(vf: &VariantFields) -> (VariantShape, Vec<(Sym, ast::TyId, Span)>) {
    match vf {
        VariantFields::Unit => (VariantShape::Unit, Vec::new()),
        VariantFields::Tuple(fs) => (VariantShape::Tuple, fs.iter().enumerate().map(|(i, f)| (Sym(i as u32), f.ty, f.span)).collect()),
        VariantFields::Struct(fs) => (VariantShape::Named, fs.iter().map(|f| (f.name, f.ty, f.span)).collect()),
    }
}

/// Builds the program tables. `crate_ids` names the crate for stable def
/// identity (docs/ARCH.md section 1.7). Returns all collection errors.
pub fn collect<'a>(ast: &'a Ast, interner: &'a Interner, known: &'a Known, crate_ids: CrateIds) -> Result<Program<'a>, Vec<Diag>> {
    let mut p = Program {
        ast,
        interner,
        known,
        tys: GlobalTys::new(),
        defs: Defs::new(),
        adts: Vec::new(),
        fns: Vec::new(),
        type_names: HashMap::default(),
        aliases: HashMap::default(),
        consts: HashMap::default(),
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
    };
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
        insert_builtin(&mut p, b.chars, DefsKind::Struct, interner.intern("Chars"), Generics::default());
        insert_builtin(&mut p, b.args, DefsKind::Struct, interner.intern("Args"), Generics::default());
    }
    let mut errs = Vec::new();
    let dup = |span: Span, n: &str| Diag::new("L0106", span, format!("`{n}` is defined more than once"), "Rename one of the definitions.");

    // Pass 1: type names, so fields can refer to types defined later.
    for item in &ast.items {
        let (name, span, is_enum) = match &item.kind {
            ItemKind::Struct(s) => (s.name, s.name_span, false),
            ItemKind::Enum(e) => (e.name, e.name_span, true),
            _ => continue,
        };
        let id = AdtId(p.adts.len() as u32);
        if p.type_names.insert(name, id).is_some() {
            errs.push(dup(span, interner.get(name)));
        }
        // The Adt's stable identity (ARCH 1.7): same name earlier in the file is a
        // duplicate definition (the error above), and the disambiguator keeps the
        // two records apart in the def table, as the old dense ids did.
        let disamb = p.adts.iter().filter(|a| a.name == name).count() as u32;
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

    // Pass 2: fields, variants, derives.
    let mut adt_index = 0;
    for item in &ast.items {
        type FieldSrc = (Sym, ast::TyId, Span);
        type VariantSrc = (Sym, Span, VariantShape, Vec<FieldSrc>, Option<ast::ExprId>);
        let (variants_src, derives_src): (Vec<VariantSrc>, &Vec<(Sym, Span)>) = match &item.kind {
            ItemKind::Struct(s) => {
                let (shape, fields) = variant_fields_src(&s.fields);
                let shape = if shape == VariantShape::Unit { VariantShape::Named } else { shape };
                (vec![(s.name, s.name_span, shape, fields, None)], &s.derives)
            }
            ItemKind::Enum(e) => {
                let vs = e
                    .variants
                    .iter()
                    .map(|v| {
                        let (shape, fs) = variant_fields_src(&v.fields);
                        (v.name, v.span, shape, fs, v.discriminant)
                    })
                    .collect();
                (vs, &e.derives)
            }
            _ => continue,
        };
        let id = AdtId(adt_index);
        adt_index += 1;
        let is_enum = p.adts[id.0 as usize].is_enum;
        let mut variants = Vec::new();
        let mut next_disc: i128 = 0;
        for (vname, vspan, shape, field_srcs, disc_src) in variants_src {
            let shape = if !is_enum && field_srcs.is_empty() { VariantShape::Unit } else { shape };
            let mut fields = Vec::new();
            for (fname, fty, fspan) in field_srcs {
                if shape == VariantShape::Named && fields.iter().any(|f: &Field| f.name == fname) {
                    errs.push(dup(fspan, interner.get(fname)));
                }
                match resolve_ty(ast, interner, known, &p.type_names, &p.aliases, &mut p.tys, fty, None) {
                    Ok(t) => {
                        if contains_ref(&p.tys, t) {
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
                "Eq" | "Hash" => {}
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
        }
    }

    // Derived traits need every field type to have the trait too.
    for i in 0..p.adts.len() {
        let adt = &p.adts[i];
        let d = adt.derives;
        for v in &adt.variants {
            for f in &v.fields {
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
                format!("recursive type `{}` has infinite size", p.name(p.adts[i].name)),
                "Put the recursive field in a Vec. Box is not supported yet.",
            ));
        }
    }

    // `const` and `static` items: the bounded evaluator handles scalar
    // literals, references to other consts, and integer arithmetic.
    // Anything else (a call, a mutable static, an aggregate) is L0632.
    // The evaluated value is part of the item's signature (section 8.1).
    {
        // (name, declared ty id, value expr, name span, is_static)
        let mut todo: Vec<(Sym, ast::TyId, Option<ast::ExprId>, Span, bool)> = Vec::new();
        for item in &ast.items {
            match &item.kind {
                ItemKind::Const(c) => {
                    if let Some(name) = c.name {
                        todo.push((name, c.ty, c.value, c.name_span, false));
                        let hash = crate::def::item_hash(p.stable_crate, &[], crate::def::DefKind::Const, interner.get(name), 0);
                        p.defs
                            .insert(DefId { krate: p.krate, hash }, DefData::skeleton(DefsKind::Const, None, name, Vis::Priv, c.name_span));
                    } else if let Some(v) = c.value {
                        // An unnamed const is only an assertion context;
                        // evaluating anything but `()` there is beyond
                        // the bounded evaluator.
                        if !matches!(ast.expr(v), ast::Expr::Unit) {
                            errs.push(not_yet("L0632", c.name_span, "unnamed consts with a computed value"));
                        }
                    }
                }
                ItemKind::Static(s) => {
                    if s.mutable {
                        errs.push(not_yet("L0632", s.name_span, "mutable statics"));
                    } else {
                        todo.push((s.name, s.ty, s.value, s.name_span, true));
                        let hash = crate::def::item_hash(p.stable_crate, &[], crate::def::DefKind::Static, interner.get(s.name), 0);
                        p.defs.insert(
                            DefId { krate: p.krate, hash },
                            DefData::skeleton(DefsKind::Static, None, s.name, Vis::Priv, s.name_span),
                        );
                    }
                }
                _ => {}
            }
        }
        // Evaluate in dependency order by fixpoint (consts are few).
        let total = todo.len();
        for _ in 0..=total {
            if todo.is_empty() {
                break;
            }
            let mut progress = false;
            let mut first_err: Option<Diag> = None;
            let mut deferred = false;
            todo.retain(|(name, ty_id, value, span, _)| {
                let span = *span;
                let declared = match resolve_ty(ast, interner, known, &p.type_names, &p.aliases, &mut p.tys, *ty_id, None) {
                    Ok(t) => t,
                    Err(d) => {
                        if first_err.is_none() {
                            first_err = Some(d);
                        }
                        return false;
                    }
                };
                let Some(v) = value else {
                    if first_err.is_none() {
                        first_err = Some(not_yet("L0632", span, "const and static items without a value"));
                    }
                    return false;
                };
                match eval_const(ast, *v, &p.consts, declared, &p.tys) {
                    Ok(val) => match check_const_ty(&p, declared, val, span, interner, *name) {
                        Ok(val) => {
                            if p.consts.insert(*name, (declared, val)).is_some() {
                                errs.push(dup(span, interner.get(*name)));
                            }
                            progress = true;
                            false
                        }
                        Err(d) => {
                            if first_err.is_none() {
                                first_err = Some(d);
                            }
                            false
                        }
                    },
                    Err(ConstErr::Defer) => {
                        deferred = true;
                        true
                    }
                    Err(ConstErr::Fail(d)) => {
                        if first_err.is_none() {
                            first_err = Some(d);
                        }
                        false
                    }
                }
            });
            if !progress {
                if deferred && !todo.is_empty() {
                    errs.push(not_yet("L0632", todo[0].3, "cyclic consts"));
                } else if let Some(d) = first_err {
                    errs.push(d);
                }
                break;
            }
            if let Some(d) = first_err {
                errs.push(d);
            }
        }
    }

    // Functions and methods. Each gets the stable path hash its caller computed
    // (src/def.rs). Hash collisions are checked by the driver when it assigns
    // slots from the same hashes, before `collect` runs on any new def set;
    // here the maps only record the hashes. A duplicate definition keeps the
    // first local id in `def_by_hash`; the dup errors below report it.
    let add_fn = |p: &mut Program<'a>,
                  def: &'a ast::FnDef,
                  owner: Option<AdtId>,
                  parent: Option<DefId>,
                  hash: DefPathHash,
                  errs: &mut Vec<Diag>|
     -> LocalDefId {
        let self_ty = owner.map(|a| p.tys.adt_ty(a));
        let mut params = Vec::new();
        if let (Some(sp), Some(st)) = (&def.self_param, self_ty) {
            params.push(match sp.kind {
                SelfKind::Value => st,
                SelfKind::Ref => p.tys.mk_ref(false, st),
                SelfKind::RefMut => p.tys.mk_ref(true, st),
                // Typed receivers are rejected by the parser today; treat as by-value.
                SelfKind::Typed => st,
            });
        }
        for param in &def.params {
            match resolve_ty(ast, interner, known, &p.type_names, &p.aliases, &mut p.tys, param.ty, self_ty) {
                Ok(t) => {
                    if !is_sized_ty(&p.tys, t) {
                        errs.push(Diag::new(
                            "L0110",
                            ast.ty_span(param.ty),
                            format!("the size for values of type `{}` cannot be known", ty_name(p, &p.tys, t)),
                            "Put the value behind a reference, such as `&[T]` or `&str`.",
                        ));
                    }
                    params.push(t)
                }
                Err(d) => {
                    errs.push(d);
                    params.push(ERROR);
                }
            }
        }
        let ret = match def.ret {
            None => UNIT,
            Some(t) => resolve_ty(ast, interner, known, &p.type_names, &p.aliases, &mut p.tys, t, self_ty).unwrap_or_else(|d| {
                errs.push(d);
                ERROR
            }),
        };
        if !is_sized_ty(&p.tys, ret) {
            let span = def.ret.map_or(def.name_span, |t| ast.ty_span(t));
            errs.push(Diag::new(
                "L0110",
                span,
                format!("the size for values of type `{}` cannot be known", ty_name(p, &p.tys, ret)),
                "Put the value behind a reference, such as `&[T]` or `&str`.",
            ));
        }
        // Elision: a returned reference borrows from `self`, or from the only reference parameter.
        let mut ret_borrows_from = None;
        if contains_ref(&p.tys, ret) {
            let ref_params: Vec<usize> = (0..params.len()).filter(|&i| contains_ref(&p.tys, params[i])).collect();
            if def.self_param.as_ref().is_some_and(|s| s.kind != SelfKind::Value) {
                ret_borrows_from = Some(0);
            } else if ref_params.len() == 1 {
                ret_borrows_from = Some(ref_params[0]);
            } else {
                let span = def.ret.map_or(def.name_span, |t| ast.ty_span(t));
                errs.push(Diag::new(
                    "L0202",
                    span,
                    "this function returns a reference, but elision cannot tell which parameter it borrows from",
                    "Return an owned value (such as String), or take exactly one reference parameter. Lust has no lifetime names.",
                ));
            }
        }
        if def.self_param.is_some() && owner.is_none() {
            errs.push(Diag::new("L0001", def.name_span, "`self` parameter outside an impl", "Move this function into an impl block."));
        }
        let id = LocalDefId(p.fns.len() as u32);
        let def_id = DefId { krate: p.krate, hash };
        p.fn_defs.push(def_id);
        p.def_by_hash.entry(hash).or_insert(id);
        // The def table record mirrors `FnInfo` for identity, kind, and generics;
        // body checking still reads `FnInfo` through the compat path.
        let mut generics = Generics::default();
        generics.parent = parent;
        let mut data =
            DefData::skeleton(if owner.is_some() { DefsKind::Method } else { DefsKind::Fn }, parent, def.name, Vis::Priv, def.name_span);
        data.generics = generics;
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
        });
        id
    };
    let mut impl_ordinals: HashMap<String, u32> = HashMap::default();
    for item in &ast.items {
        match &item.kind {
            ItemKind::Fn(def) => {
                let hash = crate::def::free_fn_hash(p.stable_crate, &[], interner.get(def.name));
                let id = add_fn(&mut p, def, None, None, hash, &mut errs);
                if p.fn_names.insert(def.name, id).is_some() {
                    errs.push(dup(def.name_span, interner.get(def.name)));
                }
                if def.name == known.main {
                    p.main = Some(id);
                }
            }
            ItemKind::Impl(imp) => {
                let owner = match ast.ty(imp.self_ty) {
                    TyExpr::Path(segs) if segs.len() == 1 && !segs[0].has_args() => p.type_names.get(&segs[0].name).copied(),
                    _ => None,
                };
                let Some(owner) = owner else {
                    errs.push(Diag::new(
                        "L0102",
                        ast.ty_span(imp.self_ty),
                        "inherent impls must name a struct or enum defined in this file",
                        "Write `impl MyType { ... }`.",
                    ));
                    continue;
                };
                let header = interner.get(p.adts[owner.0 as usize].name).to_string();
                let ordinal = impl_ordinals.get(&header).copied().unwrap_or(0);
                impl_ordinals.insert(header.clone(), ordinal + 1);
                let parent = crate::def::impl_hash(p.stable_crate, &[], &header, ordinal);
                let impl_def = DefId { krate: p.krate, hash: parent };
                let owner_name = p.adts[owner.0 as usize].name;
                p.defs.insert(impl_def, DefData::skeleton(DefsKind::Impl, None, owner_name, Vis::Priv, ast.ty_span(imp.self_ty)));
                for def in &imp.fns {
                    let hash = crate::def::method_hash(parent, interner.get(def.name));
                    let id = add_fn(&mut p, def, Some(owner), Some(impl_def), hash, &mut errs);
                    if p.methods.insert((owner, def.name), id).is_some() {
                        errs.push(dup(def.name_span, interner.get(def.name)));
                    }
                }
            }
            _ => {}
        }
    }
    if let Some(main) = p.main {
        let f = p.fn_info(main);
        if !f.params.is_empty() || f.ret != UNIT {
            errs.push(Diag::new("L0110", f.def.name_span, "`main` must take no parameters and return ()", "Write `fn main() { ... }`."));
        }
    }
    if errs.is_empty() { Ok(p) } else { Err(errs) }
}

/// Why a const initializer did not evaluate: it names a const that is
/// not evaluated yet (retry next sweep), or it is outside the bounded
/// evaluator for good.
enum ConstErr {
    Defer,
    Fail(Diag),
}

/// The bounded const evaluator for initializers: scalar literals,
/// references to already-evaluated consts, unary `-`/`!`, and integer
/// arithmetic in i128. Calls, aggregates, and anything else fail with
/// L0632 (W-CORELANG's full evaluator widens this in its own wave).
/// The evaluator's working value: integers stay in i128 so written
/// magnitudes and negated values never alias through u64 bits.
#[derive(Clone, Copy)]
enum EvalVal {
    Int(i128),
    Bool(bool),
    Char(char),
    Str(u32),
}

impl From<ConstValue> for EvalVal {
    fn from(v: ConstValue) -> EvalVal {
        match v {
            ConstValue::Int(x) => EvalVal::Int((x as i64) as i128),
            ConstValue::Bool(b) => EvalVal::Bool(b),
            ConstValue::Char(c) => EvalVal::Char(c),
            ConstValue::Str(s) => EvalVal::Str(s),
        }
    }
}

fn eval_const(
    ast: &Ast,
    e: ast::ExprId,
    consts: &HashMap<Sym, (Ty, ConstValue)>,
    declared: Ty,
    tys: &impl TyIntern,
) -> Result<EvalVal, ConstErr> {
    let fail = |what: &str| ConstErr::Fail(not_yet("L0632", ast.expr_span(e), what));
    match ast.expr(e) {
        ast::Expr::Int(v, _) => Ok(EvalVal::Int(*v as i128)),
        ast::Expr::Bool(b) => Ok(EvalVal::Bool(*b)),
        ast::Expr::Char(c) => Ok(EvalVal::Char(*c)),
        ast::Expr::Str(s) => Ok(EvalVal::Str(*s)),
        ast::Expr::Path(segs) if segs.len() == 1 => match consts.get(&segs[0].name) {
            Some((ref_ty, v)) => {
                // A const reference is type-exact, as in Rust: no
                // implicit conversion between const item types.
                if *ref_ty != declared {
                    return Err(ConstErr::Fail(Diag::new(
                        "L0110",
                        ast.expr_span(e),
                        "this const has a different type than the declared type",
                        "Change the declared type to match, or write the value directly.",
                    )));
                }
                match v {
                    // The stored u64 reads back through the declared
                    // type: unsigned keeps its magnitude, signed
                    // sign-extends from two's complement.
                    ConstValue::Int(x) => {
                        let signed = matches!(tys.kind(declared), TyKind::Int(it) if it.signed());
                        Ok(EvalVal::Int(if signed { (*x as i64) as i128 } else { *x as i128 }))
                    }
                    other => Ok(EvalVal::from(*other)),
                }
            }
            None => Err(ConstErr::Defer),
        },
        ast::Expr::Unary { op, expr } => {
            let v = eval_const(ast, *expr, consts, declared, tys)?;
            match (op, v) {
                (ast::UnOp::Neg, EvalVal::Int(x)) => {
                    Ok(EvalVal::Int(x.checked_neg().ok_or_else(|| fail("this unary operation in a const"))?))
                }
                (ast::UnOp::Not, EvalVal::Int(x)) => Ok(EvalVal::Int(!x)),
                (ast::UnOp::Not, EvalVal::Bool(b)) => Ok(EvalVal::Bool(!b)),
                _ => Err(fail("this unary operation in a const")),
            }
        }
        ast::Expr::Binary { op, lhs, rhs } => {
            let (EvalVal::Int(a), EvalVal::Int(b)) =
                (eval_const(ast, *lhs, consts, declared, tys)?, eval_const(ast, *rhs, consts, declared, tys)?)
            else {
                return Err(fail("non-integer arithmetic in a const"));
            };
            let r = match op {
                ast::BinOp::Add => a.checked_add(b),
                ast::BinOp::Sub => a.checked_sub(b),
                ast::BinOp::Mul => a.checked_mul(b),
                ast::BinOp::Div => {
                    if b == 0 {
                        return Err(ConstErr::Fail(Diag::new(
                            "L0632",
                            ast.expr_span(e),
                            "division by zero in a const initializer",
                            "Fix the divisor.",
                        )));
                    }
                    a.checked_div(b)
                }
                ast::BinOp::Rem => {
                    if b == 0 {
                        return Err(ConstErr::Fail(Diag::new(
                            "L0632",
                            ast.expr_span(e),
                            "remainder by zero in a const initializer",
                            "Fix the divisor.",
                        )));
                    }
                    a.checked_rem(b)
                }
                ast::BinOp::BitAnd => Some(a & b),
                ast::BinOp::BitOr => Some(a | b),
                ast::BinOp::BitXor => Some(a ^ b),
                ast::BinOp::Shl => a.checked_shl(b as u32),
                ast::BinOp::Shr => a.checked_shr(b as u32),
                _ => return Err(fail("this operator in a const")),
            };
            match r {
                Some(v) => Ok(EvalVal::Int(v)),
                None => Err(fail("arithmetic that overflows a const")),
            }
        }
        _ => Err(fail("this const initializer form")),
    }
}

/// Checks an evaluated value against the declared type and stores it
/// in the public form: the kind must match, and an integer must fit
/// the declared width (stored as its low 64 bits).
fn check_const_ty(p: &Program, declared: Ty, val: EvalVal, span: Span, interner: &Interner, name: Sym) -> Result<ConstValue, Diag> {
    let n = interner.get(name);
    let mismatch = |want: &str| {
        Diag::new(
            "L0110",
            span,
            format!("`{n}` is declared as {want} but its value is a different kind"),
            "Change the declared type or the value.",
        )
    };
    match (p.tys.kind(declared), val) {
        (TyKind::Int(it), EvalVal::Int(v)) => {
            let bits = it.bits().min(64);
            let fits = if it.signed() {
                let min = -(1i128 << (bits - 1));
                let max = (1i128 << (bits - 1)) - 1;
                (min..=max).contains(&v)
            } else {
                v >= 0 && (bits == 64 || v < (1i128 << bits))
            };
            if fits {
                Ok(ConstValue::Int(v as u64))
            } else {
                Err(Diag::new(
                    "L0118",
                    span,
                    format!("the value of `{n}` does not fit in `{}`", it.name()),
                    "Pick a wider type or a smaller value.",
                ))
            }
        }
        (TyKind::Bool, EvalVal::Bool(b)) => Ok(ConstValue::Bool(b)),
        (TyKind::Char, EvalVal::Char(c)) => Ok(ConstValue::Char(c)),
        (TyKind::Str, EvalVal::Str(s)) => Ok(ConstValue::Str(s)),
        (TyKind::Ref(_, _, inner), EvalVal::Str(s)) if p.tys.kind(inner) == TyKind::Str => Ok(ConstValue::Str(s)),
        (TyKind::Int(_), _) => Err(mismatch("an integer")),
        (TyKind::Bool, _) => Err(mismatch("`bool`")),
        (TyKind::Char, _) => Err(mismatch("`char`")),
        _ => Err(not_yet("L0632", span, "consts of this type")),
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
            None => false,
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
            _ => true,
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

pub fn is_copy(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Never | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int(),
        TyKind::Ref(_, m, _) => !m.is_mut(),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| is_copy(p, tys, e)),
        TyKind::Array(e, _) => is_copy(p, tys, e),
        _ => {
            if let Some(e) = tys.option_elem(t) {
                return is_copy(p, tys, e);
            }
            match tys.local_adt(t) {
                Some(a) => p.adt(a).derives.copy,
                None => false,
            }
        }
    }
}

pub fn has_clone(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
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
    match tys.local_adt(t) {
        Some(a) => p.adt(a).derives.clone,
        None => is_copy(p, tys, t),
    }
}

pub fn has_eq(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Str | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int(),
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
            match tys.local_adt(t) {
                Some(a) => p.adt(a).derives.partial_eq,
                None => false,
            }
        }
    }
}

pub fn has_debug(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Str | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int(),
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
            match tys.local_adt(t) {
                Some(a) => p.adt(a).derives.debug,
                None => false,
            }
        }
    }
}

pub fn has_display(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Str | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int(),
        TyKind::Ref(_, _, e) => has_display(tys, e),
        _ => tys.is_string_ty(t),
    }
}

/// True if values of this type own heap memory and need a drop call.
pub fn needs_drop(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
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
    match tys.local_adt(t) {
        Some(a) => p.adt(a).variants.iter().any(|v| v.fields.iter().any(|f| needs_drop(p, &p.tys, f.ty))),
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
