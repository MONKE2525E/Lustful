// Collection: builds the item tables (types, functions, methods) and resolves all signatures.
// This is the only stage that runs in sequence. Function bodies are checked after it, in parallel.
use crate::ast::{self, Ast, ItemKind, SelfKind, TyExpr, VariantFields};
use crate::check::generics::{self, GenTables};
pub use crate::def::{CrateId, DefId, DefPathHash, LocalDefId, StableCrateHash};
use crate::def::{CrateIds, DiskDefId};
use crate::diag::{Diag, Span, not_yet};
use crate::intern::FxMap as HashMap;
use crate::intern::{Interner, Known, Sym};
use crate::ty::defs::{DefKind as DefsKind, Vis};
use crate::ty::lang::ShippedCrate;
use crate::ty::*;

/// The derive list of one Adt. Derived impls are synthetic impl
/// records (generics.rs `add_synthetic_impls`); their bodies are
/// codegen glue over the fields (cgen.rs).
#[derive(Clone, Copy, Debug, Default)]
pub struct Derives {
    pub debug: bool,
    pub clone: bool,
    pub copy: bool,
    pub partial_eq: bool,
    pub eq: bool,
    pub hash: bool,
    pub partial_ord: bool,
    pub ord: bool,
    pub default: bool,
    /// The `#[default]` variant of an enum that derives `Default`.
    pub default_variant: Option<u32>,
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
    /// Associated consts of inherent impls: (Adt, name) to the
    /// indexes into `consts` of every impl that defines the name
    /// (disjoint Self patterns may share one). They are const
    /// items like free consts, but not in `const_names`: a plain
    /// name must never find them.
    pub assoc_const_names: HashMap<(AdtId, Sym), Vec<u32>>,
    /// Associated const values of trait impls: (impl def, assoc
    /// def) to an index into `consts`. Filled with the other const
    /// tables in `eval_const_items`, before template checks run.
    pub impl_assoc_consts: HashMap<(DefId, DefId), u32>,
    /// Trait associated const default values: assoc def to an
    /// index into `consts`.
    pub trait_assoc_const_values: HashMap<DefId, u32>,
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
    /// through the resolver. Attached by the driver at collection
    /// (`collect_with_order_resolved`), before any body is checked:
    /// template and instance checks read their defining module and
    /// the visibility tables from it. The S7 `Binding` query fns in
    /// driver/graph.rs read through it.
    pub resolved: Option<Box<crate::resolve::imports::ResolvedTables>>,
    /// The generic tables (traits, templates, instances) built by
    /// `check::generics` during collection and finished by mono.
    pub gx: GenTables<'a>,
    /// False when no later request replays body read sets (a one-shot
    /// process): body checks then use a sink that records nothing. Set by
    /// the driver after collection.
    pub record_reads: bool,
    /// Region signatures for the borrow checker (W-BORROW, ARCH 5): the
    /// signatures with their lifetimes kept, beside the erased ones above.
    pub regions: crate::borrowck::RegionTables,
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
    /// The return type a caller (or the fn's own body) checks against:
    /// `FnInfo::ret`, except that a plain fn whose `impl Trait` return
    /// was revealed for codegen keeps its opaque type here.
    pub fn ret_view(&self, id: LocalDefId) -> Ty {
        self.gx.opaque_ret_of.get(&id).copied().unwrap_or(self.fns[id.0 as usize].ret)
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
    /// True when an `FnDef` over `def` names a fn with a body (a fn
    /// item). The other `FnDef`s are constructor items over an Adt
    /// def: a user tuple struct or variant (`Ctx::ctor_value_ty`), or
    /// a builtin item over a builtin Adt def (`Some`, `Ok`, `Err`,
    /// `Box::new`, `Rc::new`, `String::from`; `Ctx::builtin_item_value`).
    pub fn is_fn_item_def(&self, def: DefId) -> bool {
        self.tys.builtins().kind_of(def).is_none() && self.adt_by_def(def).is_none()
    }
    /// The index of the const item with this def, if this crate defines it.
    pub fn const_by_def(&self, def: DefId) -> Option<u32> {
        self.const_defs.iter().position(|&d| d == def).map(|i| i as u32)
    }
    /// The indexes into `consts` of the inherent associated
    /// consts with this name: one per impl that defines it.
    /// Materialized Adt instances answer through their template:
    /// the value is evaluated once per impl (an initializer that
    /// names the impl's own parameters fails evaluation and never
    /// reaches the table, so one value serves every instance).
    /// The caller picks by the written Self type.
    pub fn inherent_assoc_consts(&self, adt: AdtId, name: Sym) -> &[u32] {
        if let Some(v) = self.assoc_const_names.get(&(adt, name)) {
            return v;
        }
        let Some(def) = self.defs.def_of_adt(adt) else { return &[] };
        let Some(template) = self.defs.local_adt(def) else { return &[] };
        self.assoc_const_names.get(&(template, name)).map_or(&[], |v| v.as_slice())
    }
    /// The index of the static item with this def, if this crate defines it.
    pub fn static_by_def(&self, def: DefId) -> Option<u32> {
        self.static_defs.iter().position(|&d| d == def).map(|i| i as u32)
    }
    /// The shipped crate a span's source belongs to, if any. Only spans
    /// in spliced shipped source, or in a file of a shipped adapter
    /// crate (ARCH 3.6), answer; every user span gets None.
    pub fn shipped_crate_at(&self, span: Span) -> Option<ShippedCrate> {
        if let Some(a) = self.adapter_at(span) {
            return ShippedCrate::ALL.iter().copied().find(|k| k.name() == a.name);
        }
        if span.file != crate::diag::FileId(0) {
            return None;
        }
        self.shipped_ranges.iter().find(|(lo, hi, _)| span.lo >= *lo && span.lo < *hi).map(|(_, _, k)| *k)
    }
    /// The adapter crate whose source file holds `span`, if any. The
    /// resolver records each adapter crate's files (W-DEPS).
    pub fn adapter_at(&self, span: Span) -> Option<&crate::resolve::imports::AdapterCrate> {
        self.resolved.as_ref()?.adapters.iter().find(|a| a.files.contains(&span.file))
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
        TyKind::Ref(r, m, e) => {
            let inner = ty_name(p, tys, e);
            // `&(dyn A + Send)`: the parens are part of the Rust syntax.
            let inner = if matches!(tys.kind(e), TyKind::Dyn(..)) && inner.contains(" + ") { format!("({inner})") } else { inner };
            let lt = if r == Region::Static { "'static " } else { "" };
            format!("&{lt}{}{inner}", if m.is_mut() { "mut " } else { "" })
        }
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
            Some(BuiltinTy::Boxed) => format!("Box<{}>", tys.adt_first_ty_arg(t).map_or("_".into(), |e| ty_name(p, tys, e))),
            Some(BuiltinTy::Rc) => format!("Rc<{}>", tys.adt_first_ty_arg(t).map_or("_".into(), |e| ty_name(p, tys, e))),
            Some(BuiltinTy::Weak) => format!("std::rc::Weak<{}>", tys.adt_first_ty_arg(t).map_or("_".into(), |e| ty_name(p, tys, e))),
            Some(BuiltinTy::RefCell) => format!("RefCell<{}>", tys.adt_first_ty_arg(t).map_or("_".into(), |e| ty_name(p, tys, e))),
            Some(BuiltinTy::Cell) => format!("Cell<{}>", tys.adt_first_ty_arg(t).map_or("_".into(), |e| ty_name(p, tys, e))),
            Some(BuiltinTy::RefGuard) => format!("Ref<'_, {}>", tys.adt_first_ty_arg(t).map_or("_".into(), |e| ty_name(p, tys, e))),
            Some(BuiltinTy::RefMutGuard) => format!("RefMut<'_, {}>", tys.adt_first_ty_arg(t).map_or("_".into(), |e| ty_name(p, tys, e))),
            Some(BuiltinTy::Chars) => "std::str::Chars".into(),
            Some(BuiltinTy::Args) => "std::env::Args".into(),
            Some(BuiltinTy::Fmt(k)) => format!("std::fmt::{}", k.name()),
            Some(BuiltinTy::ExitCode) => "ExitCode".into(),
            Some(BuiltinTy::Sync(k)) => match tys.adt_first_ty_arg(t) {
                Some(e) => format!("{}<{}>", k.display(), ty_name(p, tys, e)),
                None => k.display(),
            },
            Some(BuiltinTy::Iter(k)) => {
                let a = tys.adt_parts(t).map(|(_, a)| tys.args(a).to_vec()).unwrap_or_default();
                let shown: Vec<String> = a.iter().take(k.shown_args()).map(|g| g.as_ty().map_or("_".into(), |e| ty_name(p, tys, e))).collect();
                format!("{}<{}>", k.display(), shown.join(", "))
            }
            None => match tys.local_adt(t) {
                Some(a) => p.display_path(p.adt(a).name),
                None => "{unknown}".into(),
            },
        },
        TyKind::FnPtr(_) | TyKind::FnDef(..) => "fn(..)".into(),
        TyKind::Closure(..) => "{closure}".into(),
        TyKind::Dyn(b, r) => {
            let b = tys.dyn_bounds(b);
            let mut parts: Vec<String> = Vec::new();
            if let Some(pr) = b.principal {
                let name = p.gx.index.trait_record(pr.value.def).map_or("?", |rec| p.name(rec.name));
                let args: Vec<String> = tys.args(pr.value.args)[1..].iter().filter_map(|g| g.as_ty()).map(|e| ty_name(p, tys, e)).collect();
                // The Fn family prints in its sugar: `Fn(A, B) -> R`.
                let fn_sugar = p.gx.lang.is_fn_family(pr.value.def).then(|| {
                    let ins = tys.args(pr.value.args).get(1).and_then(|g| g.as_ty()).map_or_else(Vec::new, |t| match tys.kind(t) {
                        TyKind::Tuple(ts) => tys.tys_of(ts).iter().map(|&e| ty_name(p, tys, e)).collect(),
                        _ => Vec::new(),
                    });
                    let out = tys.bindings(pr.value.bindings).first().and_then(|(_, g)| g.as_ty()).filter(|&t| t != UNIT);
                    let out = out.map_or_else(String::new, |t| format!(" -> {}", ty_name(p, tys, t)));
                    format!("{name}({}){out}", ins.join(", "))
                });
                parts.push(match fn_sugar {
                    Some(s) => s,
                    None if args.is_empty() => name.to_string(),
                    None => format!("{name}<{}>", args.join(", ")),
                });
            }
            for (on, name) in [(b.auto.send, "Send"), (b.auto.sync, "Sync"), (b.auto.unpin, "Unpin")] {
                if on {
                    parts.push(name.to_string());
                }
            }
            if r == Region::Static {
                parts.push("'static".to_string());
            }
            format!("dyn {}", parts.join(" + "))
        }
        TyKind::Opaque(..) => "impl ..".into(),
        TyKind::Param(param) => format!("T{}", param.0),
        TyKind::Projection(..) => "{projection}".into(),
        TyKind::Infer(v) if v.is_int() => "{integer}".into(),
        TyKind::Infer(v) if v.is_float() => "{float}".into(),
        TyKind::Infer(_) => "_".into(),
    }
}

/// The impl's regions (W-BORROW): its regioned Self type and associated
/// types, for the region signatures of its methods. An elided lifetime in
/// the header (`impl Tr for &str`, `impl S<'_>`) is an anonymous lifetime
/// param of the impl; a lifetime hidden in a path (`impl S` for
/// `struct S<'a>`) is rustc E0726. A named impl lifetime that only an
/// associated type uses is unconstrained (rustc E0207).
fn impl_regions(p: &mut Program, imp: &ast::ImplDef, impl_def: DefId, scope: &mut generics::Scope, errs: &mut Vec<Diag>) {
    let (ast, interner, known) = (p.ast, p.interner, p.known);
    if let Some(span) = hidden_lifetime(p, imp.self_ty) {
        errs.push(Diag::new(
            "L0202",
            span,
            "implicit elided lifetime not allowed here: this type has lifetime parameters",
            "Write them, for example `impl S<'_>` or `impl<'a> S<'a>`.",
        ));
        return;
    }
    let named = scope.lifetimes.len() as u32;
    let counter = std::sync::Arc::new(std::sync::atomic::AtomicU32::new(named));
    let mut ks = scope.clone();
    ks.regions = generics::RegionMode::Keep { next: Some(counter.clone()), elided: None };
    let self_r = {
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        match generics::resolve_scoped(ast, interner, known, &cx, &mut p.tys, imp.self_ty, &ks) {
            Ok(t) => t,
            Err(_) => return,
        }
    };
    // The trait ref's lifetime args, for a trait with lifetime params
    // (W-BORROW): calls through the impl and trait selection replay them.
    let mut trait_lts: Vec<Region> = Vec::new();
    if let Some(tref) = &imp.trait_ref
        && let Some(seg) = tref.path.last()
        && let ast::GenericArgs::Angle(args) = &seg.args
    {
        for g in args {
            if let ast::GenericArg::Lifetime(lt) = g {
                match generics::scope_region(interner, &ks, Some(*lt), lt.span) {
                    Ok(r) => trait_lts.push(r),
                    Err(_) => return,
                }
            }
        }
    }
    if !trait_lts.is_empty() {
        let where_lts = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            generics::trait_lts_of(ast, interner, known, &cx, &ks, &imp.generics, &imp.where_clause)
        };
        p.regions.impl_heads.insert(impl_def, crate::borrowck::ImplHead { self_ty: self_r, trait_lifetimes: trait_lts.clone(), where_lts });
    }
    // The header's anonymous lifetimes join the impl's params, so the
    // methods' own lifetimes number after them.
    let total = counter.load(std::sync::atomic::Ordering::Relaxed);
    for k in named..total {
        scope.lifetimes.push((interner.intern(&format!("'_impl{}", k - named)), k));
    }
    scope.self_ty_regioned = Some(self_r);
    ks.lifetimes = scope.lifetimes.clone();
    ks.regions = generics::RegionMode::Keep { next: None, elided: None };
    ks.self_ty_regioned = Some(self_r);
    let mut in_header: Vec<Region> = trait_lts;
    crate::borrowck::regions_of(&p.tys, self_r, &mut in_header);
    if let Some(tref) = &imp.trait_ref {
        for seg in &tref.path {
            if let ast::GenericArgs::Angle(args) = &seg.args {
                for g in args {
                    if let ast::GenericArg::Type(t) = g {
                        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                        if let Ok(r) = generics::resolve_scoped(ast, interner, known, &cx, &mut p.tys, *t, &ks) {
                            crate::borrowck::regions_of(&p.tys, r, &mut in_header);
                        }
                    }
                }
            }
        }
    }
    for at in &imp.types {
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        let Some(aty) = at.default else { continue };
        let Ok(t) = generics::resolve_scoped(ast, interner, known, &cx, &mut p.tys, aty, &ks) else { continue };
        let mut used: Vec<Region> = Vec::new();
        crate::borrowck::regions_of(&p.tys, t, &mut used);
        for &(n, i) in scope.lifetimes.iter().take(named as usize) {
            if used.contains(&Region::Param(i)) && !in_header.contains(&Region::Param(i)) {
                errs.push(Diag::new(
                    "L0110",
                    ast.ty_span(aty),
                    format!("the lifetime parameter `'{}` is not constrained by the impl trait, self type, or predicates", interner.get(n)),
                    "Use the lifetime in the Self type or the trait's arguments, or remove it.",
                ));
            }
        }
        scope.assoc_regioned.push((at.name, t));
    }
}

/// The target of a generic type alias, over its own params (`Param(i)`
/// in declared order, lifetimes left out).
fn resolve_generic_alias(p: &mut Program, a: &ast::TypeAliasDef) -> Result<Ty, Diag> {
    let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
    let mut scope = generics::Scope::default();
    let mut idx = 0u32;
    for g in &a.generics.params {
        match g {
            ast::GenericParam::Type { name, .. } => {
                scope.type_params.push((*name, idx));
                idx += 1;
            }
            ast::GenericParam::Const { name, ty, span, .. } => {
                // The declared type, for the const typing of its uses.
                let t = generics::resolve_scoped(p.ast, p.interner, p.known, &cx, &mut p.tys, *ty, &generics::Scope::default())?;
                if generics::ConstScalar::of(&p.tys, t).is_none() {
                    return Err(Diag::new(
                        "L0110",
                        *span,
                        "this type is forbidden as the type of a const generic parameter",
                        "Use an integer type, `bool`, or `char`.",
                    ));
                }
                scope.const_params.push((*name, idx, t));
                idx += 1;
            }
            ast::GenericParam::Lifetime { lt, .. } => scope.lifetimes.push((lt.name, 0)),
        }
    }
    generics::resolve_scoped(p.ast, p.interner, p.known, &cx, &mut p.tys, a.ty, &scope)
}

/// The rules on generic aliases once their targets resolve: the param
/// default rules (`check::defaults`), and every type param must appear
/// in the target (rustc E0091). Their resolved defaults join
/// `param_defaults` under the alias def.
fn check_generic_aliases(p: &mut Program, errs: &mut Vec<Diag>) {
    let (ast, interner, known) = (p.ast, p.interner, p.known);
    for item in &ast.items {
        let ItemKind::Type(a) = &item.kind else { continue };
        if !a.generics.params.iter().any(|g| !matches!(g, ast::GenericParam::Lifetime { .. })) {
            continue;
        }
        crate::check::defaults::check_written(ast, known, &a.generics, crate::check::defaults::Owner::Type, errs);
        let Some(&target) = p.aliases.get(&a.name) else { continue };
        let used = crate::check::variance::params_in(p, target);
        let mut idx = 0u32;
        for g in &a.generics.params {
            match g {
                ast::GenericParam::Type { name, span, .. } => {
                    if !used.contains(&idx) {
                        errs.push(Diag::new(
                            "L0110",
                            *span,
                            format!("type parameter `{}` is never used", interner.get(*name)),
                            "Use the parameter in the alias's type, or remove it.",
                        ));
                    }
                    idx += 1;
                }
                ast::GenericParam::Const { .. } => idx += 1,
                ast::GenericParam::Lifetime { .. } => {}
            }
        }
        let defaults = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            crate::check::defaults::resolve_all(ast, interner, known, &cx, &mut p.tys, &a.generics, false, errs)
        };
        if defaults.iter().any(Option::is_some) {
            let hash = crate::def::item_hash(p.stable_crate, &[], crate::def::DefKind::TypeAlias, interner.get(a.name), 0);
            p.gx.param_defaults.insert(DefId { krate: p.krate, hash }, defaults);
        }
    }
}

/// A const, static, or associated const item's written type: the plain
/// resolver, else the scoped one (a generic alias with its args and
/// defaults, a generic Adt applied to args).
fn resolve_item_ty(p: &mut Program, id: ast::TyId, self_ty: Option<Ty>) -> Result<Ty, Diag> {
    let (ast, interner, known) = (p.ast, p.interner, p.known);
    // The plain resolver does not know lazy aliases (W-BORROW's generic
    // aliases): their errors (arity, defaults) come from the scoped one.
    let lazy_alias = p.gx.generic_aliases.keys().any(|&n| ty_mentions(ast, id, n));
    resolve_ty(ast, interner, known, &p.type_names, &p.aliases, &mut p.tys, id, self_ty).or_else(|d| {
        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
        let scope = generics::Scope { self_ty, ..generics::Scope::default() };
        let generic_alias = lazy_alias || d.message.contains("needs the scoped resolver");
        generics::resolve_scoped(ast, interner, known, &cx, &mut p.tys, id, &scope).map_err(|e| if generic_alias { e } else { d })
    })
}

/// The span of a path to a user Adt with lifetime params that writes none
/// (a hidden lifetime), anywhere in a written type.
fn hidden_lifetime(p: &Program, id: ast::TyId) -> Option<Span> {
    match p.ast.ty(id) {
        TyExpr::Ref { inner, .. } | TyExpr::Paren(inner) | TyExpr::Slice(inner) => hidden_lifetime(p, *inner),
        TyExpr::Array { inner, .. } | TyExpr::Ptr { inner, .. } => hidden_lifetime(p, *inner),
        TyExpr::Tuple(elems) => elems.iter().find_map(|&e| hidden_lifetime(p, e)),
        TyExpr::Path(segs) => {
            let last = segs.last()?;
            let lts = p
                .type_names
                .get(&last.name)
                .and_then(|&a| p.gx.adt_lifetimes.get(&p.gx.adt_info[a.0 as usize].0))
                .map(|v| v.len())
                .or_else(|| p.gx.generic_aliases.get(&last.name).map(|a| a.lifetimes.len()))
                .unwrap_or(0);
            let written = match &last.args {
                ast::GenericArgs::Angle(a) => a.iter().any(|g| matches!(g, ast::GenericArg::Lifetime(_))),
                _ => false,
            };
            if lts > 0 && !written {
                return Some(p.ast.ty_span(id));
            }
            segs.iter().find_map(|s| match &s.args {
                ast::GenericArgs::Angle(a) => a.iter().find_map(|g| if let ast::GenericArg::Type(t) = g { hidden_lifetime(p, *t) } else { None }),
                _ => None,
            })
        }
        _ => None,
    }
}

/// Lifetime errors in a type alias body (W-BORROW): a reference must name
/// `'static` or one of the alias's lifetime params `lts` (an elided one is
/// rustc E0106, L0202; any other name is undeclared, E0261, L0203).
/// Elided lifetimes inside fn pointer types are the pointer's own; the
/// lifetime args of paths resolve with the body (`GenericAlias`).
fn alias_lifetimes(ast: &Ast, interner: &Interner, id: ast::TyId, lts: &[Sym], errs: &mut Vec<Diag>) {
    match ast.ty(id) {
        TyExpr::Ref { lifetime, inner, .. } => {
            match lifetime.map(|lt| (interner.get(lt.name), lt.span, lt.name)) {
                None | Some(("_", _, _)) => errs.push(Diag::new(
                    "L0202",
                    ast.ty_span(id),
                    "missing lifetime specifier in a type alias",
                    "Write `&'static`, name a lifetime parameter of the alias, or use an owned type.",
                )),
                Some(("static", _, _)) => {}
                Some((_, _, n)) if lts.contains(&n) => {}
                Some((_, span, _)) => errs.push(crate::check::generics::lifetime_diag(span)),
            }
            alias_lifetimes(ast, interner, *inner, lts, errs);
        }
        TyExpr::Tuple(elems) => elems.iter().for_each(|&e| alias_lifetimes(ast, interner, e, lts, errs)),
        TyExpr::Paren(i) | TyExpr::Slice(i) => alias_lifetimes(ast, interner, *i, lts, errs),
        TyExpr::Array { inner, .. } | TyExpr::Ptr { inner, .. } => alias_lifetimes(ast, interner, *inner, lts, errs),
        TyExpr::Path(segs) => {
            for seg in segs {
                if let ast::GenericArgs::Angle(args) = &seg.args {
                    for g in args {
                        if let ast::GenericArg::Type(t) = g {
                            alias_lifetimes(ast, interner, *t, lts, errs);
                        }
                    }
                }
            }
        }
        _ => {}
    }
}

/// True when a written type names `name` as a path's first segment
/// anywhere (an alias's type param is used, rustc E0091).
fn ty_mentions(ast: &Ast, id: ast::TyId, name: Sym) -> bool {
    let seg_args = |seg: &ast::PathSeg| -> bool {
        match &seg.args {
            ast::GenericArgs::Angle(args) => args.iter().any(|g| match g {
                ast::GenericArg::Type(t) => ty_mentions(ast, *t, name),
                ast::GenericArg::Binding { kind: ast::BindingKind::EqTy(t), .. } => ty_mentions(ast, *t, name),
                _ => false,
            }),
            ast::GenericArgs::Parenthesized { inputs, output } => {
                inputs.iter().any(|&t| ty_mentions(ast, t, name)) || output.is_some_and(|t| ty_mentions(ast, t, name))
            }
            ast::GenericArgs::None => false,
        }
    };
    let bounds = |bs: &[ast::TraitBound]| bs.iter().any(|b| matches!(b, ast::TraitBound::Trait { trait_ref, .. } if trait_ref.path.iter().any(seg_args)));
    match ast.ty(id) {
        TyExpr::Path(segs) => segs.first().is_some_and(|s| s.name == name) || segs.iter().any(seg_args),
        TyExpr::Ref { inner, .. } | TyExpr::Paren(inner) | TyExpr::Slice(inner) => ty_mentions(ast, *inner, name),
        TyExpr::Array { inner, .. } | TyExpr::Ptr { inner, .. } => ty_mentions(ast, *inner, name),
        TyExpr::Tuple(elems) => elems.iter().any(|&e| ty_mentions(ast, e, name)),
        TyExpr::FnPtr { inputs, ret, .. } => inputs.iter().any(|i| ty_mentions(ast, i.ty, name)) || ret.is_some_and(|r| ty_mentions(ast, r, name)),
        TyExpr::Dyn { bounds: bs, .. } | TyExpr::ImplTrait { bounds: bs } => bounds(bs),
        TyExpr::QPath { self_ty, trait_path, segs } => ty_mentions(ast, *self_ty, name) || trait_path.iter().any(seg_args) || segs.iter().any(seg_args),
        _ => false,
    }
}

/// Reports each path that starts with a non-prelude std type lust
/// knows by name (`ty::lang::STD_IMPORTED_TYPES`), unless the file
/// defines an item of that name. Only for files with no `use`.
fn std_names_without_use(ast: &Ast, interner: &Interner, errs: &mut Vec<Diag>) {
    // The driver sends a file with any `use` to the resolver; a bare
    // collect (unit tests) can still see one here.
    if ast.items.iter().chain(&ast.stmt_items).any(|it| matches!(it.kind, ItemKind::Use(_))) {
        return;
    }
    let defined = |name: Sym| {
        ast.items.iter().any(|it| match &it.kind {
            ItemKind::Struct(s) => s.name == name,
            ItemKind::Enum(e) => e.name == name,
            ItemKind::Type(a) => a.name == name,
            ItemKind::Trait(t) => t.name == name,
            _ => false,
        })
    };
    let mut report = |first: Sym, span: Span| {
        let n = interner.get(first);
        if crate::ty::lang::needs_std_use(n) && !defined(first) {
            let hint = crate::ty::lang::std_use_hint(n);
            errs.push(Diag::new("L0102", span, format!("cannot find type `{n}` in this scope"), format!("Import it: `use {hint};`.")));
        }
    };
    for (i, t) in ast.tys.iter().enumerate() {
        if let ast::TyExpr::Path(segs) = t
            && let Some(s) = segs.first()
        {
            report(s.name, ast.ty_spans[i]);
        }
    }
    for (i, e) in ast.exprs.iter().enumerate() {
        if let ast::Expr::Path(segs) = e
            && segs.len() > 1
            && let Some(s) = segs.first()
        {
            report(s.name, ast.expr_spans[i]);
        }
    }
    // Variant patterns (`Ordering::Less =>`).
    for (i, pat) in ast.pats.iter().enumerate() {
        if let ast::Pat::Path(segs) | ast::Pat::TupleStruct { path: segs, .. } | ast::Pat::Struct { path: segs, .. } = pat
            && segs.len() > 1
            && let Some(s) = segs.first()
        {
            report(s.name, ast.pat_spans[i]);
        }
    }
}

/// The reject for a canonical std type path that lust cannot mean
/// here: its last segment names no builtin, and a user type of that
/// name must not stand in for std's.
pub(crate) fn std_path_shadowed(interner: &Interner, name: Sym, span: Span) -> Diag {
    let n = interner.get(name);
    if ["HashMap", "HashSet", "BTreeMap", "Arc"].contains(&n) {
        return not_yet("L0641", span, &format!("the `{n}` type"));
    }
    not_yet("L0505", span, &format!("the std path to `{n}` where a user type has the same name"))
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
            // Accept a canonical std type path by its last segment
            // (`std::vec::Vec`); a wrong-module path
            // (`std::option::Vec`) never falls through.
            let std_prefixed = segs.len() > 1 && (segs[0].name == known.std || matches!(interner.get(segs[0].name), "core" | "alloc"));
            let seg = if std_prefixed {
                let path: Vec<&str> = segs.iter().map(|s| interner.get(s.name)).collect();
                if crate::ty::lang::std_path_kind(&path) != Some(crate::ty::lang::StdPathKind::Type)
                    && !crate::ty::lang::std_is_primitive_path(&path)
                {
                    let n = interner.get(segs.last().unwrap().name);
                    return Err(Diag::new("L0102", span, format!("unknown type `{n}`"), "Check the spelling, or define the type."));
                }
                // `std::cmp::Ordering` is the core enum (and the UTF-8
                // error paths the std structs) even where a user type of
                // that name owns the flat name.
                let last = segs.last().unwrap();
                if let Some(def) = generics::std_adt_of_path(&path)
                    && !last.has_args()
                {
                    return Ok(tys.intern(TyKind::Adt(def, EMPTY_ARGS)));
                }
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
            if name == known.Box {
                let args = seg.type_args();
                if args.len() != 1 {
                    return Err(Diag::new("L0110", span, "Box takes one type argument", "Write `Box<T>`."));
                }
                let e = resolve_ty(ast, interner, known, type_names, aliases, tys, args[0], self_ty)?;
                // `Box<[T]>` is the one unsized Box lust has (W-STD-A).
                if matches!(tys.kind(e), TyKind::Str | TyKind::Dyn(..)) {
                    return Err(not_yet("L0641", span, "a Box of an unsized type"));
                }
                return Ok(tys.mk_boxed(e));
            }
            // A user type named `Rc` shadows std's (which needs a `use`),
            // but never on a std path.
            if name == known.Rc && (std_prefixed || !type_names.contains_key(&name)) {
                let args = seg.type_args();
                if args.len() != 1 {
                    return Err(Diag::new("L0110", span, "Rc takes one type argument", "Write `Rc<T>`."));
                }
                let e = resolve_ty(ast, interner, known, type_names, aliases, tys, args[0], self_ty)?;
                if matches!(tys.kind(e), TyKind::Slice(_) | TyKind::Str | TyKind::Dyn(..)) {
                    return Err(not_yet("L0641", span, "an Rc of an unsized type"));
                }
                return Ok(tys.mk_rc(e));
            }
            // The sync and thread types (W-THREADS): by their std path,
            // or by a bare name a module glob of their std module imports.
            if let Some(k) = crate::check::sync::sync_type_named(interner, segs) {
                if k.arity() == 0 && k.regions() == 0 {
                    return no_generics(crate::ty::sync::sync_ty(tys, k, &[]));
                }
                let args = seg.type_args();
                if args.len() != k.arity() {
                    return Err(Diag::new("L0110", span, format!("{} takes one type argument", k.name()), format!("Write `{}<T>`.", k.name())));
                }
                let lts = match &seg.args {
                    crate::ast::GenericArgs::Angle(a) => a.iter().filter(|g| matches!(g, crate::ast::GenericArg::Lifetime(_))).count(),
                    _ => 0,
                };
                if lts != 0 && lts != k.regions() as usize {
                    return Err(Diag::new("L0110", span, format!("`{}` takes {} lifetime argument(s)", k.name(), k.regions()), "Match the number of lifetime parameters."));
                }
                if k.arity() == 0 {
                    return Ok(crate::ty::sync::sync_ty(tys, k, &[]));
                }
                let e = resolve_ty(ast, interner, known, type_names, aliases, tys, args[0], self_ty)?;
                crate::check::sync::check_sync_arg(tys, k, e, span)?;
                return Ok(crate::ty::sync::sync_ty(tys, k, &[e]));
            }
            // `Weak<T>`, `RefCell<T>`, `Cell<T>` (W-STD-A; the import
            // itself is checked where paths resolve).
            if let n @ ("Weak" | "RefCell" | "Cell") = interner.get(name)
                && (std_prefixed || !type_names.contains_key(&name))
            {
                let args = seg.type_args();
                if args.len() != 1 {
                    return Err(Diag::new("L0110", span, format!("{n} takes one type argument"), format!("Write `{n}<T>`.")));
                }
                let e = resolve_ty(ast, interner, known, type_names, aliases, tys, args[0], self_ty)?;
                if matches!(tys.kind(e), TyKind::Slice(_) | TyKind::Str | TyKind::Dyn(..)) {
                    return Err(not_yet("L0641", span, &format!("a {n} of an unsized type")));
                }
                let which: fn(&crate::ty::BuiltinDefs) -> crate::def::DefId = match n {
                    "Weak" => |d| d.weak,
                    "RefCell" => |d| d.refcell,
                    _ => |d| d.cell,
                };
                return Ok(tys.mk_builtin1(which, e));
            }
            if interner.get(name) == "ExitCode" && (std_prefixed || !type_names.contains_key(&name)) {
                return no_generics(tys.exit_code_ty());
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
            // A std path names std's type, never a user type or alias
            // of the same name (std's `Ordering` is the one std Adt).
            if let Some(&adt) = type_names.get(&name)
                && (!std_prefixed || generics::is_std_adt(tys, adt))
            {
                return no_generics(tys.adt_ty(adt));
            }
            if !std_prefixed && let Some(&t) = aliases.get(&name) {
                // A generic alias needs the scoped resolver (its args and
                // defaults): callers fall back to it on this error.
                if tys.flags(t).contains_param() {
                    return Err(Diag::new("L0110", span, "this generic alias needs the scoped resolver", "Write the alias's arguments."));
                }
                return no_generics(t);
            }
            let n = interner.get(name);
            if name == known.f32 {
                return no_generics(tys.float_ty(FloatTy::F32));
            }
            if name == known.f64 {
                return no_generics(tys.float_ty(FloatTy::F64));
            }
            if std_prefixed {
                return Err(std_path_shadowed(interner, name, span));
            }
            if ["HashMap", "HashSet", "BTreeMap", "Arc"].contains(&n) {
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
            let sig = tys.intern_sig(crate::ty::Binder::plain(crate::ty::FnSig { inputs, output: out, is_unsafe: false, extern_c: false }));
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

/// The value expression of a named const found by scanning the
/// crate's items: a free const item for one name, an inherent
/// associated const for two (`Type::CONST`, by flat type name).
/// Signature-form const resolution uses this before the const
/// tables exist; the scan is by written (flat) name, as the
/// scalar interpreter's own lookups are. An associated const
/// answers only from one defining impl without type or const
/// params: same-name consts in disjoint impls (`impl G<u8>`,
/// `impl G<i32>`) and impl params the path must fix need the
/// typed pick, which knows the written type.
fn named_const_expr(ast: &Ast, names: &[Sym]) -> Option<ast::ExprId> {
    match names {
        [name] => {
            for item in &ast.items {
                if let ItemKind::Const(c) = &item.kind
                    && c.name == Some(*name)
                    && let Some(v) = c.value
                {
                    return Some(v);
                }
            }
            None
        }
        [ty_name, name] => {
            let mut found = None;
            for item in &ast.items {
                let ItemKind::Impl(imp) = &item.kind else { continue };
                if imp.trait_ref.is_some() {
                    continue;
                }
                let TyExpr::Path(segs) = ast.ty(imp.self_ty) else { continue };
                if segs.first().map(|s| s.name) != Some(*ty_name) {
                    continue;
                }
                for c in &imp.consts {
                    if c.name == *name
                        && let Some(v) = c.default
                    {
                        let generic = imp.generics.params.iter().any(|g| !matches!(g, ast::GenericParam::Lifetime { .. }));
                        if found.is_some() || generic {
                            return None;
                        }
                        found = Some(v);
                    }
                }
            }
            found
        }
        _ => None,
    }
}

/// The integer value of a named const (see `named_const_expr`),
/// for const generic arguments written as bare paths.
pub fn named_const_int(ast: &Ast, interner: &Interner, known: &Known, names: &[Sym]) -> Option<u128> {
    let e = named_const_expr(ast, names)?;
    u128::try_from(eval_const_int(ast, interner, known, e)?).ok()
}

/// The const-generic value of a free const item by name, in the
/// kind of its declared type: an integer const for the integer
/// types, `Bool` for `bool`, `Char` for `char`.
pub fn named_const_kind(ast: &Ast, interner: &Interner, known: &Known, name: Sym) -> Option<ConstKind> {
    for item in &ast.items {
        let ItemKind::Const(c) = &item.kind else { continue };
        if c.name != Some(name) {
            continue;
        }
        let v = c.value?;
        let scalar = eval_const_int(ast, interner, known, v)?;
        return match ast.ty(c.ty) {
            TyExpr::Path(segs) if segs.len() == 1 && segs[0].name == known.bool => Some(ConstKind::Bool(scalar != 0)),
            TyExpr::Path(segs) if segs.len() == 1 && segs[0].name == known.char => char::from_u32(scalar as u32).map(ConstKind::Char),
            _ => u128::try_from(scalar).ok().map(ConstKind::Int),
        };
    }
    None
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
            let (a, b) = (val(ast, interner, known, *lhs, depth + 1, env, steps), val(ast, interner, known, *rhs, depth + 1, env, steps));
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
        Expr::While { cond, body, .. } => loop {
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
        },
        Expr::Loop { body, .. } => loop {
            let b = *body;
            match eval_scalar_block(ast, interner, known, b, depth + 1, env, steps) {
                SFlow::V(_) | SFlow::Continue => {}
                SFlow::Break(v) => return SFlow::V(v),
                other => return other,
            }
            if *steps > 100_000 {
                return SFlow::V(None);
            }
        },
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
            let out = named_const_expr(ast, &[name]).and_then(|v| {
                let mut empty = Vec::new();
                val(ast, interner, known, v, depth + 1, &mut empty, steps)
            });
            SFlow::V(out)
        }
        Expr::Path(segs) if segs.len() == 2 => {
            // An inherent associated const (`Type::CONST`), found by
            // scanning the crate's impls like a free const above.
            // Written type args (`G::<i32>::N`) need the typed pick.
            if !segs[0].has_args()
                && let Some(v) = named_const_expr(ast, &[segs[0].name, segs[1].name])
            {
                let mut empty = Vec::new();
                let out = val(ast, interner, known, v, depth + 1, &mut empty, steps);
                return SFlow::V(out);
            }
            // `i64::MAX` and friends by written name.
            let out = known.int_ty(segs[0].name).and_then(|it| {
                let item = interner.get(segs[1].name);
                let bits = it.bits();
                match item {
                    "MAX" => Some(truncate_to_int(it.max128() as i128, it)),
                    "MIN" => Some(if it.signed() { if bits >= 128 { i128::MIN } else { -(1i128 << (bits - 1)) } } else { 0 }),
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
                                let ok = matches!(inner.as_slice(), [TokenTree::Token(t2)] if matches!(t2.tok, Tok::Int(1, _, _)));
                                if !ok {
                                    return Err(bad("packed(N)"));
                                }
                                i += 1;
                            }
                        }
                        "align" => match trees.get(i + 1) {
                            Some(TokenTree::Delim(_, inner, _)) => match inner.as_slice() {
                                [TokenTree::Token(t2)] => match t2.tok {
                                    Tok::Int(n, _, _) if n > 0 && n <= (1 << 29) && n.is_power_of_two() => {
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
        VariantFields::Tuple(fs) => {
            (VariantShape::Tuple, fs.iter().enumerate().map(|(i, f)| (interner.intern(&i.to_string()), f.ty, f.span)).collect())
        }
        VariantFields::Struct(fs) => (VariantShape::Named, fs.iter().map(|f| (f.name, f.ty, f.span)).collect()),
    }
}

/// Session-stable numbering state for Adts and statics: every def
/// hash ever numbered in this session, in first-seen order (hashes
/// first seen in the same compile append in hash order, so a fresh
/// session numbers by `DefPathHash` alone, independent of file and
/// item order). A def's session-local index is its rank among the
/// defs present in this compile: adding a def appends it after
/// every def seen before, so present defs keep their indices.
/// Cached output carries those indices (`CTy::Adt(AdtId)` in glue
/// and type sets, static indices in IR), so index stability is
/// what lets an edit that adds a file reuse the rest. The driver
/// session owns one `DefOrder` across requests.
#[derive(Default)]
pub struct DefOrder {
    pub adts: Vec<crate::def::DefPathHash>,
    pub statics: Vec<crate::def::DefPathHash>,
    /// Adt instance ids (see `InstOrder`).
    pub instances: InstOrder,
}

/// Session-stable Adt instance ids (W-PERF): an instance Adt's id is
/// `base` plus the place of its instance key (`Program::instance_key_hash`
/// of template def and args) in first-seen order. Places are never
/// reused, so a new instance never moves the id of another: C names Adts
/// `A<id>`, and cached C, type sets, and glue keep their meaning. Rows
/// from the template Adts up to `base`, and the places of instances a
/// program does not make, are inert placeholder rows. `base` sits past
/// the template Adts with room for more; it moves (and every instance id
/// with it) only when templates outgrow it.
#[derive(Default, Clone)]
pub struct InstOrder {
    pub base: u32,
    pub keys: Vec<u64>,
    pub place: HashMap<u64, u32>,
}

impl InstOrder {
    /// Fits `base` past `templates` Adt rows (before a collect's first instance).
    pub fn fit(&mut self, templates: usize) {
        if (self.base as usize) < templates {
            self.base = (templates + 32 + templates / 8) as u32;
        }
    }

    /// The place of `key`, appended when it is new.
    pub fn place_of(&mut self, key: u64) -> u32 {
        let keys = &mut self.keys;
        *self.place.entry(key).or_insert_with(|| {
            keys.push(key);
            keys.len() as u32 - 1
        })
    }
}

/// The rank of each hash among `hashes`, by position in `order`
/// after appending unseen hashes in hash order. The ranks are
/// dense over `hashes`. `hashes` must hold each def once.
pub(crate) fn stable_ranks(order: &mut Vec<crate::def::DefPathHash>, hashes: &[crate::def::DefPathHash]) -> Vec<u32> {
    let pos: std::collections::HashMap<crate::def::DefPathHash, usize> = order.iter().enumerate().map(|(i, h)| (*h, i)).collect();
    let mut unseen: Vec<crate::def::DefPathHash> = hashes.iter().copied().filter(|h| !pos.contains_key(h)).collect();
    unseen.sort_by_key(|h| h.0);
    unseen.dedup();
    order.extend(unseen);
    stable_ranks_preview(order, hashes)
}

/// The ranks `stable_ranks` would assign, without mutating `order`
/// (the driver predicts this compile's indices before collect runs
/// to decide whether cached output still applies).
pub(crate) fn stable_ranks_preview(order: &[crate::def::DefPathHash], hashes: &[crate::def::DefPathHash]) -> Vec<u32> {
    let mut extended: Vec<crate::def::DefPathHash> = order.to_vec();
    let mut pos: std::collections::HashMap<crate::def::DefPathHash, usize> = extended.iter().enumerate().map(|(i, h)| (*h, i)).collect();
    let mut unseen: Vec<crate::def::DefPathHash> = hashes.iter().copied().filter(|h| !pos.contains_key(h)).collect();
    unseen.sort_by_key(|h| h.0);
    unseen.dedup();
    for h in unseen {
        pos.insert(h, extended.len());
        extended.push(h);
    }
    let mut by_pos: Vec<(usize, crate::def::DefPathHash)> = hashes.iter().map(|h| (pos[h], *h)).collect();
    by_pos.sort_by_key(|(p, _)| *p);
    by_pos.dedup_by_key(|(_, h)| *h);
    let mut rank: std::collections::HashMap<crate::def::DefPathHash, u32> = std::collections::HashMap::default();
    for (r, (_, h)) in by_pos.into_iter().enumerate() {
        rank.insert(h, r as u32);
    }
    hashes.iter().map(|h| rank[h]).collect()
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
    collect_with_order(ast, interner, known, crate_ids, walk_instances, &mut DefOrder::default())
}

/// `collect_mode` with a caller-kept `DefOrder` (the driver session
/// holds one across requests, so Adt and static indices survive
/// edits that add or reorder defs).
pub fn collect_with_order<'a>(
    ast: &'a Ast,
    interner: &'a Interner,
    known: &'a Known,
    crate_ids: CrateIds,
    walk_instances: bool,
    def_order: &mut DefOrder,
) -> Result<Program<'a>, Vec<Diag>> {
    collect_with_order_resolved(ast, interner, known, crate_ids, walk_instances, def_order, None)
}

/// `collect_with_order` with the resolver's module tables (section
/// 1.3) attached from the start. The tables must be in place before
/// collection's body checks run (mono's template checks in
/// `finish_collect`): every checked body reads its defining module
/// and the visibility tables from `Program::resolved`.
#[allow(clippy::too_many_arguments)]
pub fn collect_with_order_resolved<'a>(
    ast: &'a Ast,
    interner: &'a Interner,
    known: &'a Known,
    crate_ids: CrateIds,
    walk_instances: bool,
    def_order: &mut DefOrder,
    resolved: Option<Box<crate::resolve::imports::ResolvedTables>>,
) -> Result<Program<'a>, Vec<Diag>> {
    collect_reuse(ast, interner, known, crate_ids, walk_instances, def_order, resolved, &mut Default::default())
}

/// `collect_with_order_resolved` with the driver session's generic
/// reuse cache (driver/gen_reuse.rs, W-PERF): the cache rides in
/// `GenTables::reuse` for this collect, so template checks and instance
/// discovery skip bodies whose stored results still hold, and it goes
/// back to the caller on every return, with what this collect stored.
#[allow(clippy::too_many_arguments)]
pub fn collect_reuse<'a>(
    ast: &'a Ast,
    interner: &'a Interner,
    known: &'a Known,
    crate_ids: CrateIds,
    walk_instances: bool,
    def_order: &mut DefOrder,
    resolved: Option<Box<crate::resolve::imports::ResolvedTables>>,
    reuse: &mut crate::driver::gen_reuse::GenReuse,
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
        impl_assoc_consts: HashMap::default(),
        trait_assoc_const_values: HashMap::default(),
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
        resolved,
        gx: GenTables::default(),
        record_reads: true,
        regions: Default::default(),
    };
    p.gx.walk_instances = walk_instances;
    p.gx.reuse = std::mem::take(reuse);
    p.gx.inst_order = std::mem::take(&mut def_order.instances);
    p.gx.reuse.begin();
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
        insert_builtin(&mut p, b.boxed, DefsKind::Struct, known.Box, one_ty_param());
        insert_builtin(&mut p, b.rc, DefsKind::Struct, known.Rc, one_ty_param());
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
        for k in crate::ty::fmt::FmtTy::ALL {
            insert_builtin(&mut p, b.fmt_tys[k as usize], DefsKind::Struct, interner.intern(k.name()), Generics::default());
        }
        insert_builtin(&mut p, b.exit_code, DefsKind::Struct, interner.intern("ExitCode"), Generics::default());
        for k in crate::ty::sync::SyncTy::ALL {
            let params = (0..k.arity()).map(|i| ParamDef { name: interner.intern(["T", "U"][i]), kind: ParamKind::Type, span: dummy }).collect();
            let g = Generics { parent: None, params, predicates: Vec::new() };
            insert_builtin(&mut p, b.sync_tys[k as usize], DefsKind::Struct, interner.intern(k.name()), g);
        }
        for (def, n) in [(b.weak, "Weak"), (b.refcell, "RefCell"), (b.cell, "Cell"), (b.ref_guard, "Ref"), (b.ref_mut_guard, "RefMut")] {
            insert_builtin(&mut p, def, DefsKind::Struct, interner.intern(n), one_ty_param());
        }
        for k in crate::ty::iter::IterKind::ALL {
            let params = (0..k.n_args())
                .map(|i| ParamDef { name: interner.intern(["I", "F", "B"][i]), kind: ParamKind::Type, span: dummy })
                .collect();
            let g = Generics { parent: None, params, predicates: Vec::new() };
            insert_builtin(&mut p, b.iters[k as usize], DefsKind::Struct, interner.intern(k.path().1), g);
        }
    }
    let mut errs = Vec::new();
    let dup = |span: Span, n: &str| Diag::new("L0106", span, format!("`{n}` is defined more than once"), "Rename one of the definitions.");
    // Without resolver tables the file has no `use` at all (any `use`
    // routes to the resolver), so a non-prelude std type lust knows by
    // name cannot be in scope (W-STD-A; the resolver checks its paths).
    if p.resolved.is_none() {
        std_names_without_use(ast, interner, &mut errs);
    }

    // Generic pass 0: lang traits and user trait defs, so bounds in
    // every later signature can name them.
    p.gx.item_index = crate::check::defaults::item_index(ast);
    generics::init_lang(&mut p);
    generics::collect_trait_defs(&mut p, &mut errs);

    // Pass 1: type names, so fields can refer to types defined later.
    // AdtIds come from the session DefOrder (rank by DefPathHash
    // history), not from item order: compute every Adt's hash and
    // rank up front, then fill the tables at those indices.
    let adt_base = p.adts.len();
    let mut adt_srcs: Vec<(usize, Sym, Span, bool, crate::def::DefPathHash)> = Vec::new();
    {
        let mut counts: HashMap<Sym, u32> = HashMap::default();
        for (idx, item) in ast.items.iter().enumerate() {
            let (name, span, is_enum) = match &item.kind {
                ItemKind::Struct(s) => (s.name, s.name_span, false),
                ItemKind::Enum(e) => (e.name, e.name_span, true),
                _ => continue,
            };
            let disamb = *counts.entry(name).and_modify(|c| *c += 1).or_insert(0);
            let hash = crate::def::item_hash(crate_ids.stable, &[], crate::def::DefKind::Adt, interner.get(name), disamb);
            adt_srcs.push((idx, name, span, is_enum, hash));
        }
    }
    // The synthetic std Adts (`generics::std_adts`): `core::cmp::Ordering`
    // is an ordinary fieldless enum with a builtin def (lang signatures
    // name it; its variants and derives are the plain enum machinery),
    // `fmt::Error` the unit struct of `fmt::Result` (W-STD-B), and
    // `str::Utf8Error` and `string::FromUtf8Error` plain structs
    // (W-STD-A). They take part in the same stable ranking as user Adts
    // (the driver predicts the same set: see `predicted_def_ids`). A
    // user type, alias, or trait of the same name shadows one in the
    // flat name table, as with any name here; the Adt itself always
    // exists, so `cmp`, `from_utf8`, and the full std paths still name
    // the std type. `fmt::Error` never enters the flat name table (only
    // `fmt::Error` paths reach it; see `generics::resolve_fmt_path`).
    // Index k marks its source as `usize::MAX - k`.
    let std_taken: Vec<Sym> = generics::std_adts()
        .iter()
        .map(|s| interner.intern(s.1))
        .filter(|&n| {
            adt_srcs.iter().any(|s| s.1 == n)
                || p.gx.trait_names.contains_key(&n)
                || ast.items.iter().any(|it| matches!(&it.kind, ItemKind::Type(a) if a.name == n))
        })
        .collect();
    for (k, name, def, is_enum) in generics::std_adts() {
        adt_srcs.push((usize::MAX - k, interner.intern(name), Span::default(), is_enum, def.hash));
    }
    let adt_ranks = {
        let hashes: Vec<crate::def::DefPathHash> = adt_srcs.iter().map(|s| s.4).collect();
        stable_ranks(&mut def_order.adts, &hashes)
    };
    let mut adt_id_of_item: Vec<Option<AdtId>> = vec![None; ast.items.len()];
    {
        let blank_name = interner.intern("");
        for _ in 0..adt_srcs.len() {
            p.adts.push(AdtDef {
                name: blank_name,
                is_enum: false,
                variants: Vec::new(),
                derives: Derives::default(),
                span: Span::default(),
                repr: crate::ty::layout::Repr::default(),
            });
            p.gx.adt_info.push((DefId::PLACEHOLDER, 0));
            p.gx.adt_generics.push(Generics::default());
            p.gx.adt_envs.push(Vec::new());
            p.gx.adt_scopes.push(generics::Scope::default());
            p.gx.adt_instance_of.push(None);
        }
    }
    for (src, &rank) in adt_srcs.iter().zip(&adt_ranks) {
        let (item_idx, name, span, is_enum, hash) = (src.0, src.1, src.2, src.3, src.4);
        if item_idx > usize::MAX - generics::std_adts().len() {
            // A synthetic std Adt (see above): variants, fields, and
            // derives are std's, written here directly (no AST item).
            let id = AdtId(adt_base as u32 + rank);
            let unit = |n: &str, disc: i128| Variant { name: interner.intern(n), shape: VariantShape::Unit, fields: Vec::new(), disc };
            let field = |n: &str, ty: Ty| Field { name: interner.intern(n), ty };
            let named = |fields: Vec<Field>| vec![Variant { name, shape: VariantShape::Named, fields, disc: 0 }];
            let (def, variants, derives) = match usize::MAX - item_idx {
                0 => (
                    generics::ordering_def(),
                    vec![unit("Less", -1), unit("Equal", 0), unit("Greater", 1)],
                    Derives { debug: true, clone: true, copy: true, partial_eq: true, eq: true, hash: true, partial_ord: true, ord: true, ..Derives::default() },
                ),
                // core: `#[derive(Copy, Clone, Debug, Default, Eq, Hash,
                // Ord, PartialEq, PartialOrd)]`; its Display is the runtime's.
                1 => (
                    generics::fmt_error_def(),
                    vec![Variant { name, shape: VariantShape::Unit, fields: Vec::new(), disc: 0 }],
                    Derives {
                        debug: true,
                        clone: true,
                        copy: true,
                        partial_eq: true,
                        eq: true,
                        hash: true,
                        partial_ord: true,
                        ord: true,
                        default: true,
                        default_variant: None,
                    },
                ),
                2 => {
                    let error_len = p.tys.mk_option(int(IntTy::U8));
                    (
                        generics::utf8_error_def(),
                        named(vec![field("valid_up_to", int(IntTy::Usize)), field("error_len", error_len)]),
                        Derives { debug: true, clone: true, copy: true, partial_eq: true, eq: true, ..Derives::default() },
                    )
                }
                // core: `#[derive(Copy, Clone, Debug, Eq, PartialEq,
                // Hash)] #[non_exhaustive] pub enum Ordering` (W-THREADS).
                4 => (
                    generics::atomic_ordering_def(),
                    vec![unit("Relaxed", 0), unit("Release", 1), unit("Acquire", 2), unit("AcqRel", 3), unit("SeqCst", 4)],
                    Derives { debug: true, clone: true, copy: true, partial_eq: true, eq: true, hash: true, ..Derives::default() },
                ),
                // std: `#[derive(PartialEq, Eq, Clone, Copy, Debug)] pub
                // struct RecvError;` and `pub enum TryRecvError { Empty,
                // Disconnected }` with the same derives (W-THREADS).
                5 => (
                    generics::recv_error_def(),
                    vec![Variant { name, shape: VariantShape::Unit, fields: Vec::new(), disc: 0 }],
                    Derives { debug: true, clone: true, copy: true, partial_eq: true, eq: true, ..Derives::default() },
                ),
                6 => (
                    generics::try_recv_error_def(),
                    vec![unit("Empty", 0), unit("Disconnected", 1)],
                    Derives { debug: true, clone: true, copy: true, partial_eq: true, eq: true, ..Derives::default() },
                ),
                _ => {
                    let bytes = p.tys.mk_vec(int(IntTy::U8));
                    let error = p.tys.intern(TyKind::Adt(generics::utf8_error_def(), EMPTY_ARGS));
                    (
                        generics::from_utf8_error_def(),
                        named(vec![field("bytes", bytes), field("error", error)]),
                        Derives { debug: true, clone: true, partial_eq: true, eq: true, ..Derives::default() },
                    )
                }
            };
            p.adts[id.0 as usize] = AdtDef { name, is_enum, variants, derives, span, repr: crate::ty::layout::Repr::default() };
            p.gx.adt_info[id.0 as usize] = (def, 0);
            if generics::std_adt_has_flat_name(usize::MAX - item_idx) && !std_taken.contains(&name) {
                p.type_names.insert(name, id);
            }
            p.tys.register_adt(def, id);
            let kind = if is_enum { DefsKind::Enum } else { DefsKind::Struct };
            p.defs.insert_adt(def, id, DefData::skeleton(kind, None, name, Vis::Pub, span));
            p.tys.intern(TyKind::Adt(def, EMPTY_ARGS));
            continue;
        }
        let item = &ast.items[item_idx];
        let id = AdtId(adt_base as u32 + rank);
        adt_id_of_item[item_idx] = Some(id);
        // The first type of a name owns it; a duplicate keeps its own Adt
        // record (below) but never replaces the name entry.
        if p.type_names.contains_key(&name) || p.gx.trait_names.contains_key(&name) {
            errs.push(dup(span, interner.get(name)));
        } else {
            p.type_names.insert(name, id);
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
        let def = DefId { krate: p.krate, hash };
        p.adts[id.0 as usize] =
            AdtDef { name, is_enum, variants: Vec::new(), derives: Derives::default(), span, repr: crate::ty::layout::Repr::default() };
        p.gx.adt_info[id.0 as usize] = (def, n_params);
        // Lifetime params (W-BORROW): names only; the field pass gives
        // them meaning.
        let lifetimes: Vec<Sym> = match &item.kind {
            ItemKind::Struct(st) => &st.generics.params,
            ItemKind::Enum(e) => &e.generics.params,
            _ => &[][..],
        }
        .iter()
        .filter_map(|g| if let ast::GenericParam::Lifetime { lt, .. } = g { Some(lt.name) } else { None })
        .collect();
        if !lifetimes.is_empty() {
            p.gx.adt_lifetimes.insert(def, lifetimes);
        }
        p.tys.register_adt(def, id);
        let kind = if is_enum { DefsKind::Enum } else { DefsKind::Struct };
        p.defs.insert_adt(def, id, DefData::skeleton(kind, None, name, Vis::Priv, span));
        p.tys.intern(TyKind::Adt(def, EMPTY_ARGS));
    }

    // Pass 1.5: type aliases. Resolved by a small fixpoint: an alias
    // whose target still names an unresolved alias defers to the next
    // sweep; a sweep with no progress means a cycle (L0601) or a genuine
    // unknown type (the first error is kept). A generic alias's target is
    // over its own params (`Param(i)`); each use substitutes its args
    // (`generics::resolve_path_ty`).
    {
        let mut pending: Vec<&ast::TypeAliasDef> = Vec::new();
        // `aliases` fills only in the fixpoint below, so registration needs
        // its own seen set to catch a second alias of one name.
        let mut seen_aliases: Vec<Sym> = Vec::new();
        for item in &ast.items {
            if let ItemKind::Type(a) = &item.kind {
                if p.type_names.contains_key(&a.name) || p.gx.trait_names.contains_key(&a.name) || seen_aliases.contains(&a.name) {
                    errs.push(dup(a.name_span, interner.get(a.name)));
                    continue;
                }
                seen_aliases.push(a.name);
                // W-BORROW: an alias whose generics are lifetimes only
                // resolves at each use (`generics::resolve_generic_alias`);
                // its body is checked once below, after Adts and traits.
                let lts: Vec<Sym> = a
                    .generics
                    .params
                    .iter()
                    .filter_map(|g| if let ast::GenericParam::Lifetime { lt, .. } = g { Some(lt.name) } else { None })
                    .collect();
                // Lifetime and type params resolve at each use; const
                // params stay with the eager path (unsupported there).
                let type_params: Vec<(Sym, Option<ast::TyId>)> = a
                    .generics
                    .params
                    .iter()
                    .filter_map(|g| if let ast::GenericParam::Type { name, default, .. } = g { Some((*name, *default)) } else { None })
                    .collect();
                let generic = !a.generics.params.is_empty() && lts.len() + type_params.len() == a.generics.params.len();
                alias_lifetimes(ast, interner, a.ty, &lts, &mut errs);
                if generic {
                    // rustc E0091: every type param of an alias is used.
                    for (n, _) in &type_params {
                        if !ty_mentions(ast, a.ty, *n) {
                            errs.push(Diag::new(
                                "L0110",
                                a.name_span,
                                format!("type parameter `{}` is never used in this alias", interner.get(*n)),
                                "Use the parameter in the aliased type, or remove it.",
                            ));
                        }
                    }
                    let names: Vec<Sym> = lts.iter().copied().chain(type_params.iter().map(|&(n, _)| n)).collect();
                    for (i, n) in names.iter().enumerate() {
                        if names[..i].contains(n) {
                            errs.push(Diag::new(
                                "L0110",
                                a.name_span,
                                format!("the parameter `{}` is declared twice on this alias", interner.get(*n)),
                                "Give each parameter its own name.",
                            ));
                        }
                    }
                    let body_hash = crate::driver::ast_hash::item_hash(ast, item);
                    p.gx.generic_aliases.insert(a.name, generics::GenericAlias { lifetimes: lts, type_params, ty: a.ty, erased: ERROR, body_hash });
                } else {
                    pending.push(a);
                }
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
            pending.retain(|a| {
                let generic = a.generics.params.iter().any(|g| !matches!(g, ast::GenericParam::Lifetime { .. }));
                let resolved = if generic {
                    resolve_generic_alias(&mut p, a)
                } else {
                    // The scoped resolver covers what the plain one cannot
                    // (a generic Adt applied to arguments, `W<i32>`).
                    resolve_ty(ast, interner, known, &p.type_names, &p.aliases, &mut p.tys, a.ty, None).or_else(|d| {
                        let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                        generics::resolve_scoped(ast, interner, known, &cx, &mut p.tys, a.ty, &generics::Scope::default()).map_err(|_| d)
                    })
                };
                match resolved {
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
                } else {
                    // W-BORROW: an alias this early pass cannot resolve (a
                    // generic Adt target, an alias of a lazy alias) resolves
                    // at each use like a generic alias, and its body is
                    // checked with theirs below. Const params stay errors.
                    let mut reported = false;
                    for a in &pending {
                        if a.generics.params.is_empty()
                            && let Some(item) = ast.items.iter().find(|it| matches!(&it.kind, ItemKind::Type(x) if x.name == a.name))
                        {
                            let body_hash = crate::driver::ast_hash::item_hash(ast, item);
                            p.gx.generic_aliases.insert(
                                a.name,
                                generics::GenericAlias { lifetimes: Vec::new(), type_params: Vec::new(), ty: a.ty, erased: ERROR, body_hash },
                            );
                        } else if !reported && let Some(d) = first_err.take() {
                            errs.push(d);
                            reported = true;
                        }
                    }
                }
                break;
            }
        }
        check_generic_aliases(&mut p, &mut errs);
    }

    // Generic pass 1.5: trait generics, method templates. Fields
    // and fn signatures after this can name traits in bounds.
    generics::build_trait_tables(&mut p, &mut errs);

    // Pass 2: fields, variants, derives.
    for (item_idx, item) in ast.items.iter().enumerate() {
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
        let id = adt_id_of_item[item_idx].expect("pass 1 numbered every Adt item");
        // The Adt's own generics scope its field types.
        {
            let (g_ast, w_ast) = match &item.kind {
                ItemKind::Struct(st) => (st.generics.clone(), st.where_clause.clone()),
                ItemKind::Enum(e) => (e.generics.clone(), e.where_clause.clone()),
                _ => unreachable!(),
            };
            let (adt_generics, adt_scope) = {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                generics::build_adt_generics(ast, interner, known, &cx, &mut p.tys, &g_ast, &w_ast, &mut errs)
            };
            let defaults = {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                crate::check::defaults::resolve_all(ast, interner, known, &cx, &mut p.tys, &g_ast, false, &mut errs)
            };
            if defaults.iter().any(Option::is_some) {
                let def = p.defs.def_of_adt(id).expect("ADT defs are recorded in pass 1");
                p.gx.param_defaults.insert(def, defaults);
            }
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
        // (variant, field, regioned type) for the borrow checker.
        let mut region_fields: Vec<(usize, usize, Ty)> = Vec::new();
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
                        // The field's regions (W-BORROW): every reference
                        // needs a lifetime the Adt declares, or `'static`
                        // (an elided one is rustc E0106).
                        let regioned = {
                            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                            let mut ks = p.gx.adt_scopes[id.0 as usize].clone();
                            ks.regions = generics::RegionMode::Keep { next: None, elided: None };
                            generics::resolve_scoped(ast, interner, known, &cx, &mut p.tys, fty, &ks)
                        };
                        match regioned {
                            Ok(r) => region_fields.push((variants.len(), fields.len(), r)),
                            Err(d) if d.code == "L0202" => errs.push(Diag::new(
                                "L0201",
                                ast.ty_span(fty),
                                "a reference in a struct or enum field needs a lifetime",
                                "Declare a lifetime on the type (`struct S<'a> { x: &'a str }`), use `'static`, or store an owned value.",
                            )),
                            Err(_) => {}
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
                "PartialOrd" => d.partial_ord = true,
                "Ord" => d.ord = true,
                "Default" => d.default = true,
                n => errs.push(Diag::new(
                    "L0403",
                    span,
                    format!("cannot derive `{n}`"),
                    "Lust can derive Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, and Default.",
                )),
            }
        }
        // `Copy` needs a `Clone` impl, derived or written: checked in
        // finish_collect (`check_derive_bounds`), once impls exist.
        // `#[default]` variants (rustc's rules): only with a `Default`
        // derive, exactly one per enum, and only on a unit variant.
        if let ItemKind::Enum(e) = &item.kind {
            let marked: Vec<(u32, Span)> = e
                .variants
                .iter()
                .enumerate()
                .filter_map(|(i, v)| {
                    v.attrs.iter().find(|a| a.path.len() == 1 && interner.get(a.path[0].name) == "default").map(|a| (i as u32, a.span))
                })
                .collect();
            if !d.default {
                if let Some(&(_, sp)) = marked.first() {
                    errs.push(Diag::new(
                        "L0402",
                        sp,
                        "cannot find attribute `default` in this scope",
                        "Add `Default` to the derive list, or remove `#[default]`.",
                    ));
                }
            } else if marked.is_empty() {
                errs.push(Diag::new(
                    "L0403",
                    p.adts[id.0 as usize].span,
                    "`#[derive(Default)]` on enum with no `#[default]`",
                    "Mark one unit variant with `#[default]`.",
                ));
            } else if marked.len() > 1 {
                errs.push(Diag::new("L0403", marked[1].1, "multiple declared defaults", "Keep `#[default]` on one variant only."));
            } else if variants.get(marked[0].0 as usize).is_some_and(|v: &Variant| v.shape != VariantShape::Unit) {
                errs.push(Diag::new(
                    "L0403",
                    marked[0].1,
                    "the `#[default]` attribute may only be used on unit enum variants",
                    "Move `#[default]` to a variant with no fields.",
                ));
            } else {
                d.default_variant = Some(marked[0].0);
            }
        }
        // Regioned field types (W-BORROW). Unused type and lifetime
        // params (rustc E0392) are checked after every Adt has its
        // fields (`variance::check_unused_params`).
        {
            let def = p.gx.adt_info[id.0 as usize].0;
            let mut by_variant: Vec<Vec<Ty>> = variants.iter().map(|v| v.fields.iter().map(|f| f.ty).collect()).collect();
            for &(vi, fi, r) in &region_fields {
                if let Some(slot) = by_variant.get_mut(vi).and_then(|v| v.get_mut(fi)) {
                    *slot = r;
                }
            }
            p.regions.adt_fields.insert(def, by_variant);
            let facts = p.gx.adt_scopes[id.0 as usize].region_facts.clone();
            if !facts.is_empty() {
                p.regions.adt_facts.insert(def, facts);
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
            if adt.is_enum && adt.repr.kind == ReprKind::C && adt.repr.int.is_some() && adt.variants.iter().all(|v| v.fields.is_empty()) {
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

    // Unused type and lifetime params, now that every Adt has its
    // fields (a use through another Adt reads that Adt's own uses).
    {
        let templates: Vec<(AdtId, usize)> = adt_id_of_item.iter().enumerate().filter_map(|(i, a)| a.map(|a| (a, i))).collect();
        crate::check::variance::check_unused_params(&p, &templates, &mut errs);
    }

    // Derived traits need every field type to have the trait too.
    let mut deferred_debug: Vec<(Ty, Span)> = Vec::new();
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
                // `Clone` fields are checked in finish_collect
                // (`check_derive_bounds`): a field type with a written
                // `Clone` impl needs the impl index first.
                if d.copy {
                    checks[n_checks] = (is_copy(&p, &p.tys, f.ty), "Copy");
                    n_checks += 1;
                }
                // `PartialEq` fields are checked in finish_collect too.
                if d.debug {
                    // A field of a type with a written `impl Debug` waits
                    // for the impl index: finish_collect proves it (W-STD-B).
                    let ok = has_debug(&p, &p.tys, f.ty);
                    if !ok && crate::check::fmt::mentions_local_adt(&p.tys, f.ty) {
                        deferred_debug.push((f.ty, adt.span));
                    } else {
                        checks[n_checks] = (ok, "Debug");
                        n_checks += 1;
                    }
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

    p.gx.deferred_debug_fields.extend(deferred_debug);

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
                "Put the recursive field behind a `Box`, in a `Vec`, or behind a reference.",
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
    struct ParentGen<'g> {
        generics: Generics,
        scope: generics::Scope,
        /// The impl's written generics and where clause: their `F: Fn*`
        /// bounds join each method's region signature (W-BORROW).
        ast_generics: Option<(&'g ast::Generics, &'g ast::WhereClause)>,
    }
    let plain_parent = || ParentGen { generics: Generics::default(), scope: generics::Scope::default(), ast_generics: None };
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
            generics::build_generics_shifted(
                ast,
                interner,
                known,
                &cx,
                &mut p.tys,
                &def.generics,
                &def.where_clause,
                shift,
                &parent_gen.scope,
                errs,
            )
        };
        let mut generics = parent_gen.generics.clone();
        generics.params.extend(own_generics.params.iter().cloned());
        generics.predicates.extend(own_generics.predicates.iter().copied());
        generics.parent = parent;
        // A parameter may not reuse a name from the enclosing impl or
        // trait (rustc E0403). Duplicates inside one list are reported by
        // `build_generics_shifted`.
        for param in &own_generics.params {
            if parent_gen.generics.params.iter().any(|q| q.name == param.name) {
                errs.push(Diag::new(
                    "L0106",
                    param.span,
                    format!("the parameter `{}` is already used for a parameter of an enclosing item", interner.get(param.name)),
                    "Rename one of the parameters.",
                ));
            }
        }
        let mut scope = parent_gen.scope.clone();
        scope.lifetimes.extend(own_scope.lifetimes.iter().copied());
        scope.region_facts.extend(own_scope.region_facts.iter().copied());
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
        let (params, ret, ret_borrows_from, generics, scope, region_sig, opaque) = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            let owner = DefId { krate: p.krate, hash };
            generics::resolve_fn_sig(ast, interner, known, &mut p.tys, &cx, def, generics, &scope, self_ty, Some(owner), errs)
        };
        if let Some((od, info)) = opaque {
            p.gx.opaques.insert(od, info);
        }
        if def.self_param.is_some() && self_ty.is_none() {
            errs.push(Diag::new("L0001", def.name_span, "`self` parameter outside an impl", "Move this function into an impl block."));
        }
        let env = generics::body_env(&mut p.tys, &p.gx.index, &generics.predicates);
        let is_template = !generics.params.is_empty();
        if is_template {
            p.gx.has_generics = true;
        }
        let id = LocalDefId(p.fns.len() as u32);
        if let Some(mut rs) = region_sig {
            // The impl's lifetimes are params of the impl: early-bound for
            // its methods (a method does not coerce to a fn pointer that
            // is generic over them).
            for e in rs.early.iter_mut().take(parent_gen.scope.lifetimes.len()) {
                *e = true;
            }
            if let Some((g, w)) = parent_gen.ast_generics {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                rs.fn_bounds.extend(generics::fn_bounds_of(ast, interner, known, &mut p.tys, &cx, &scope, g, w));
                rs.trait_bounds.extend(generics::trait_lts_of(ast, interner, known, &cx, &scope, g, w));
            }
            p.regions.fns.insert(id, rs);
        }
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
    // W-BORROW: each lifetime alias's body, checked once like rustc does
    // (an unused alias with an unknown type is still an error), and its
    // erased form kept for the driver's fingerprints.
    let mut aliases: Vec<(Sym, generics::GenericAlias)> = p.gx.generic_aliases.iter().map(|(&n, a)| (n, a.clone())).collect();
    aliases.sort_by_key(|(_, a)| a.ty.0);
    for (name, la) in aliases {
        let mut scope = generics::Scope { alias_lifetimes: la.lifetimes.iter().map(|&n| (n, Region::Erased)).collect(), alias_depth: 1, ..generics::Scope::default() };
        for (i, &(n, _)) in la.type_params.iter().enumerate() {
            let t = p.tys.intern(TyKind::Param(ParamId(i as u32)));
            scope.param_tys.push((n, t));
        }
        let res = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            let body = generics::resolve_scoped(ast, interner, known, &cx, &mut p.tys, la.ty, &scope);
            // Defaults are types of their own: check them too.
            let mut defaults = Ok(());
            for &(_, d) in &la.type_params {
                if let Some(d) = d
                    && let Err(e) = generics::resolve_scoped(ast, interner, known, &cx, &mut p.tys, d, &scope)
                {
                    defaults = Err(e);
                    break;
                }
            }
            defaults.and(body)
        };
        match res {
            Ok(t) => {
                if let Some(e) = p.gx.generic_aliases.get_mut(&name) {
                    e.erased = t;
                }
            }
            Err(d) => errs.push(d),
        }
    }
    let mut impl_ordinals: HashMap<String, u32> = HashMap::default();
    // Top-level fn and method hashes by body block: the parents of fns
    // nested in bodies (`def::nested_fn_ids`).
    let mut top_hashes: HashMap<ast::BlockId, crate::def::DefPathHash> = HashMap::default();
    // The trait of each trait impl, by item index, for the trait-system
    // key (`gen_reuse::trait_key`).
    let mut impl_traits: HashMap<usize, DefId> = HashMap::default();
    for (item_idx, item) in ast.items.iter().enumerate() {
        match &item.kind {
            ItemKind::Fn(def) => {
                let hash = crate::def::free_fn_hash(p.stable_crate, &[], interner.get(def.name));
                if let Some(b) = def.body {
                    top_hashes.insert(b, hash);
                }
                let id = add_fn(&mut p, def, None, None, None, &plain_parent(), hash, &mut errs);
                // The first value of a name owns it. A unit or tuple struct
                // constructor is a value of the struct's name too, so a fn
                // of that name is a duplicate; a braced struct is not.
                let ctor_taken = p.type_names.get(&def.name).is_some_and(|&a| {
                    !p.adts[a.0 as usize].is_enum && p.adts[a.0 as usize].variants.first().is_some_and(|v| v.shape != VariantShape::Named)
                });
                if p.fn_names.contains_key(&def.name) || ctor_taken {
                    errs.push(dup(def.name_span, interner.get(def.name)));
                } else {
                    p.fn_names.insert(def.name, id);
                }
                if def.name == known.main && p.main.is_none() {
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
                for def in &imp.fns {
                    if let Some(b) = def.body {
                        top_hashes.insert(b, crate::def::method_hash(parent, interner.get(def.name)));
                    }
                }
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
                impl_regions(&mut p, imp, impl_def, &mut impl_scope, &mut errs);
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
                            Ok(tr) => {
                                impl_traits.insert(item_idx, tr.def);
                                Some(tr)
                            }
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
                // `impl dyn Trait { .. }`: inherent methods on a dyn
                // type, found by the dyn receiver probe (check/method.rs).
                let dyn_self = trait_ref.is_none() && matches!(p.tys.kind(self_pat), TyKind::Dyn(..));
                if dyn_self {
                    p.gx.has_generics = true;
                    p.gx.dyn_impl_sites.push((self_pat, ast.ty_span(imp.self_ty)));
                }
                // A header dyn whose object lifetime is `'static` (a dyn
                // Self outside a reference, a dyn trait argument, or a
                // written `dyn Tr + 'static` anywhere in the header).
                let static_dyn = crate::check::object::header_dyn_is_static(ast, interner, imp.self_ty)
                    || p.tys.flags(self_pat).contains_static_region()
                    || trait_ref.is_some_and(|tr| {
                        p.tys.args(tr.args).iter().skip(1).any(|g| {
                            g.as_ty().is_some_and(|t| matches!(p.tys.kind(t), TyKind::Dyn(..)) || p.tys.flags(t).contains_static_region())
                        })
                    });
                if static_dyn {
                    p.gx.static_dyn_impls.push(impl_def);
                }
                // A `&'static` reference to a dyn value in a header: the
                // DynStatic proof covers object lifetimes only, and lust
                // tracks no other reference lifetime.
                let static_ref = crate::check::object::has_static_ref(&p.tys, self_pat)
                    || trait_ref.is_some_and(|tr| {
                        p.tys.args(tr.args).iter().any(|g| g.as_ty().is_some_and(|t| crate::check::object::has_static_ref(&p.tys, t)))
                    });
                if static_ref {
                    errs.push(Diag::new(
                        "L0705",
                        ast.ty_span(imp.self_ty),
                        "lust cannot check a `&'static` reference to a `dyn` value in an impl header",
                        "Implement the trait for `dyn Tr` itself, or for a type without `&'static dyn`.",
                    ));
                }
                if trait_ref.is_none() && owner.is_none() && !dyn_self {
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
                    p.gx.inherent_impl_self.insert(impl_def, (self_pat, impl_generics.clone()));
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
                let parent_gen =
                    ParentGen { generics: impl_generics.clone(), scope: impl_scope, ast_generics: Some((&imp.generics, &imp.where_clause)) };
                let mut method_ids: Vec<LocalDefId> = Vec::new();
                for def in &imp.fns {
                    // Functions in trait impls cannot be declared const
                    // (rustc E0379); inherent impl methods can.
                    if trait_ref.is_some() && def.qual.is_const {
                        errs.push(Diag::new(
                            "L0632",
                            def.name_span,
                            "functions in trait impls cannot be declared const",
                            "Remove the `const`, or move the method to an inherent impl.",
                        ));
                    }
                    let hash = crate::def::method_hash(parent, interner.get(def.name));
                    let id = add_fn(&mut p, def, owner, Some(self_pat), Some(impl_def), &parent_gen, hash, &mut errs);
                    method_ids.push(id);
                    if static_dyn {
                        p.gx.static_dyn_fns.push(id);
                    }
                    if dyn_self {
                        let key = (crate::check::object::erase_dyn_region(&mut p.tys, self_pat), def.name);
                        if p.gx.dyn_inherent.insert(key, id).is_some() {
                            errs.push(dup(def.name_span, interner.get(def.name)));
                        }
                    }
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
                // Associated consts are evaluated with the const
                // items below (W-RESOLVE phase 2).
            }
            _ => {}
        }
    }
    // Items inside function bodies: nested fns join the fn table (their
    // names are block-scoped, so they stay out of `fn_names`); nested
    // consts and statics evaluate with the top-level pass below. Type
    // items in bodies are not in the subset yet. A nested fn's identity
    // is its parent fn's plus its name (section 1.7), as the driver's
    // slot keys compute it.
    let krate = p.stable_crate;
    let nested_hashes = crate::def::nested_fn_ids(
        ast,
        interner,
        |b| top_hashes.get(&b).copied(),
        |&parent, name, disamb| crate::def::child_hash(parent, crate::def::DefKind::Fn, name, disamb),
        |seg, name| crate::def::free_fn_hash(krate, &[seg], name),
    );
    for (idx, item) in ast.stmt_items.iter().enumerate() {
        match &item.kind {
            ItemKind::Fn(def) => {
                let hash = nested_hashes[idx].expect("every nested fn has an identity");
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
        // Items in one block share one value namespace, like items in a
        // module: two of one name in the same block are a duplicate.
        let mut seen: Vec<Sym> = Vec::new();
        for &i in &idxs {
            let (name, span) = match &ast.stmt_items[i as usize].kind {
                ItemKind::Fn(def) => (Some(def.name), def.name_span),
                ItemKind::Const(c) => (c.name, c.name_span),
                ItemKind::Static(s) => (Some(s.name), s.name_span),
                _ => (None, ast.stmt_items[i as usize].span),
            };
            if let Some(name) = name {
                if seen.contains(&name) {
                    errs.push(dup(span, interner.get(name)));
                } else {
                    seen.push(name);
                }
            }
        }
        for &i in &idxs {
            if let Some(BodyItem::Fn(fid)) = p.body_items.get(&i).copied() {
                p.fn_siblings.insert(fid, idxs.clone());
            }
        }
    }
    // Const and static items: register names first, then evaluate with the
    // bounded evaluator (ARCH 2.13). A failed item keeps a placeholder value
    // so one bad item reports once; collection fails anyway on the error.
    // This runs before `finish_collect`: its template checks (and, in a
    // build, the instance checks in mono) read consts, statics, and assoc
    // consts from these tables, in generic and plain bodies alike.
    eval_const_items(&mut p, &mut errs, &mut def_order.statics);
    // The generic reuse cache holds while the trait system does (W-PERF);
    // the key needs the resolved trait of each impl, and the cache serves
    // the template checks and discovery that `finish_collect` runs.
    let key = crate::driver::gen_reuse::trait_key(&p, &impl_traits);
    p.gx.reuse.gate(key);
    generics::finish_collect(&mut p, &mut errs);
    if let Some(main) = p.main {
        let f = p.fn_info(main);
        // Rust's Termination for main: (), ExitCode, or Result<T, E>
        // with T one of those and E: Debug.
        let term = |t: Ty| t == UNIT || p.tys.is_exit_code(t);
        let ret_ok = term(f.ret) || matches!(p.tys.result_args(f.ret), Some((ok, e)) if term(ok) && has_debug(&p, &p.tys, e));
        if !f.params.is_empty() || !ret_ok {
            errs.push(Diag::new(
                "L0110",
                f.def.name_span,
                "`main` must take no parameters and return (), ExitCode, or Result<T, E> with T one of those and E: Debug",
                "Write `fn main() { ... }` or `fn main() -> Result<(), E> { ... }`.",
            ));
        }
    }

    *reuse = std::mem::take(&mut p.gx.reuse);
    def_order.instances = std::mem::take(&mut p.gx.inst_order);
    if errs.is_empty() { Ok(p) } else { Err(errs) }
}

/// Where an associated const's evaluated value lands.
enum PendingAssoc {
    /// An inherent impl const: `assoc_const_names` under its
    /// Adt, with the impl's Self pattern for use-site picks.
    Inherent { owner: AdtId, impl_def: DefId, self_pat: Ty, generics: Generics },
    /// A trait impl const: `impl_assoc_consts` under its impl.
    TraitImpl { impl_def: DefId, assoc: DefId },
    /// A trait default: `trait_assoc_const_values`.
    TraitDefault { trait_def: DefId, assoc: DefId },
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
    /// Set for an associated const (never a plain-name lookup).
    assoc: Option<PendingAssoc>,
}

enum PendingState {
    Todo,
    Doing,
    Done(crate::ty::consteval::ConstValue),
    Failed,
}

/// Registers and evaluates every const and static item in the crate.
/// Static indices come from the session `DefOrder` (see `collect`):
/// top-level statics rank by def hash history, nested statics keep
/// stmt order after them.
fn eval_const_items<'a>(p: &mut Program<'a>, errs: &mut Vec<Diag>, static_order: &mut Vec<crate::def::DefPathHash>) {
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
        let ty = match resolve_item_ty(p, ty_id, None) {
            Ok(t) => generics::normalize_item_ty(p, t),
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
        // A static is shared by every thread: its type must be `Sync`
        // (rustc E0277), proven by the auto trait walk (ARCH 2.7).
        if is_static.is_some() {
            let sync = p.gx.lang.sync;
            let mut tys = crate::ty::Tys::new(&p.tys);
            if crate::check::collect::auto_structural(p, &mut tys, &[], sync, ty, &mut Vec::new()) != Some(true) {
                let tn = ty_name(p, &p.tys, ty);
                errs.push(Diag::new(
                    "L0612",
                    span,
                    format!("`{tn}` cannot be shared between threads safely: a static's type must be `Sync`"),
                    "Use a `Sync` type, such as an atomic or a `Mutex`, or a `thread_local!` for per-thread state.",
                ));
                continue;
            }
        }
        // Static indices are assigned after registration below,
        // once every surviving static is known (stable ranks).
        let static_idx = 0;
        if let Some(n) = name {
            let dup = if stmt_idx.is_some() {
                // A nested name may shadow a top-level one; the by-name map
                // keeps the first registration for evaluation lookups.
                by_name.entry(n).or_insert(pending.len());
                false
            } else {
                // The first value of a name owns it, and a unit or tuple
                // struct constructor is a value of the struct's name.
                let ctor_taken = p.type_names.get(&n).is_some_and(|&a| {
                    !p.adts[a.0 as usize].is_enum && p.adts[a.0 as usize].variants.first().is_some_and(|v| v.shape != VariantShape::Named)
                });
                let taken = by_name.contains_key(&n) || p.fn_names.contains_key(&n) || ctor_taken;
                by_name.entry(n).or_insert(pending.len());
                taken
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
        pending.push((PendingConst { name, stmt_idx, ty, expr: value, span, is_static, static_idx, assoc: None }, PendingState::Todo));
    }
    // Associated consts evaluate in the same pending list, so a
    // free const can read an inherent associated const (and back)
    // with the same cycle detection as free items.
    let mut assoc_by_key: HashMap<(Sym, Sym), Vec<usize>> = HashMap::default();
    register_assoc_consts(p, errs, &mut pending, &mut assoc_by_key);
    if pending.is_empty() {
        return;
    }
    // Assign static indices now that registration is complete:
    // top-level statics by session rank, nested statics in stmt
    // order after them. Evaluation reads these indices, so this
    // runs before any pending item evaluates.
    {
        let top_hashes: Vec<crate::def::DefPathHash> = pending
            .iter()
            .filter(|(it, _)| it.is_static.is_some() && it.stmt_idx.is_none())
            .map(|(it, _)| crate::def::item_hash(p.stable_crate, &[], crate::def::DefKind::Static, p.interner.get(it.name.unwrap()), 0))
            .collect();
        let ranks = stable_ranks(static_order, &top_hashes);
        let mut top = 0usize;
        let mut nested = top_hashes.len() as u32;
        for (it, _) in pending.iter_mut() {
            if it.is_static.is_none() {
                continue;
            }
            if it.stmt_idx.is_none() {
                it.static_idx = ranks[top];
                top += 1;
            } else {
                it.static_idx = nested;
                nested += 1;
            }
        }
        static_count = nested;
    }
    let n = pending.len();
    let mut cx =
        CollectCx { p, pending, by_name, assoc_by_key, self_name: None, self_pat: None, self_stack: Vec::new(), module: None, errs };
    for i in 0..n {
        cx.eval_pending(i);
    }
    // Move the results into the program tables, in item order.
    let CollectCx { p, pending, .. } = cx;
    let mut statics: Vec<Option<StaticItem>> = (0..static_count).map(|_| None).collect();
    for (item, state) in pending {
        let PendingState::Done(value) = state else { continue };
        if let Some(assoc) = item.assoc {
            // An associated const is a const item with a child def,
            // found only through its assoc table.
            let name = item.name.unwrap();
            let idx = p.consts.len() as u32;
            let (parent, parent_hash) = match &assoc {
                PendingAssoc::Inherent { impl_def, .. } | PendingAssoc::TraitImpl { impl_def, .. } => (*impl_def, impl_def.hash),
                PendingAssoc::TraitDefault { trait_def, .. } => (*trait_def, trait_def.hash),
            };
            let hash = crate::def::child_hash(parent_hash, crate::def::DefKind::Const, p.interner.get(name), 0);
            let def = DefId { krate: p.krate, hash };
            p.defs.insert(def, DefData::skeleton(DefsKind::Const, Some(parent), name, Vis::Priv, item.span));
            p.const_defs.push(def);
            p.consts.push(ConstItem { name, ty: item.ty, value });
            match assoc {
                PendingAssoc::Inherent { owner, self_pat, generics, .. } => {
                    p.assoc_const_names.entry((owner, name)).or_default().push(idx);
                    p.gx.inherent_const_self.insert(idx, (self_pat, generics, item.span));
                }
                PendingAssoc::TraitImpl { impl_def, assoc } => {
                    p.impl_assoc_consts.insert((impl_def, assoc), idx);
                }
                PendingAssoc::TraitDefault { assoc, .. } => {
                    p.trait_assoc_const_values.insert(assoc, idx);
                }
            }
            continue;
        }
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

/// Registers the associated consts of inherent impls, trait
/// impls, and trait defaults as pending items of
/// `eval_const_items` (W-RESOLVE phase 2, on the merged
/// evaluator). They become const items with child defs under
/// their impl or trait, found through their assoc tables only:
/// initializers read free consts by plain name and inherent
/// associated consts by `Type::CONST` (the `assoc_by_key`
/// entries, keyed by flat type name), never other associated
/// consts by plain name (Rust requires a qualified path there).
/// Impl ordinals must match the fn pass exactly (same
/// iteration, same owner test), so child hashes name the same
/// impl.
fn register_assoc_consts<'a>(
    p: &mut Program<'a>,
    errs: &mut Vec<Diag>,
    pending: &mut Vec<(PendingConst, PendingState)>,
    assoc_by_key: &mut HashMap<(Sym, Sym), Vec<usize>>,
) {
    let ast = p.ast;
    let mut impl_ordinals: HashMap<String, u32> = HashMap::default();
    let mut inherent_seen: Vec<(DefId, Sym)> = Vec::new();
    for item in &ast.items {
        let ItemKind::Impl(imp) = &item.kind else { continue };
        // The fn pass consumes one ordinal per impl header before
        // any continue, negative and trait impls included.
        let header = match ast.ty(imp.self_ty) {
            TyExpr::Path(segs) if !segs.is_empty() => p.interner.get(segs[0].name).to_string(),
            _ => "<error>".to_string(),
        };
        let ordinal = impl_ordinals.get(&header).copied().unwrap_or(0);
        impl_ordinals.insert(header.clone(), ordinal + 1);
        if imp.is_negative || imp.consts.is_empty() {
            continue;
        }
        let parent_hash = crate::def::impl_hash(p.stable_crate, &[], &header, ordinal);
        let impl_def = DefId { krate: p.krate, hash: parent_hash };
        let owner = match ast.ty(imp.self_ty) {
            TyExpr::Path(segs) if segs.len() == 1 => p.type_names.get(&segs[0].name).copied(),
            _ => None,
        };
        if imp.trait_ref.is_some() {
            // A trait impl const: its trait and assoc def come
            // from the index record the fn pass inserted.
            let Some((_, rec)) = p.gx.index.by_def(impl_def) else { continue };
            let trait_def = rec.trait_def;
            let Some(trec) = p.gx.index.trait_record(trait_def).cloned() else { continue };
            for c in &imp.consts {
                // Unknown and duplicate names are reported by
                // `finish_trait_impl`; only value items register.
                let Some(assoc) = trec.assoc_by_name(c.name).filter(|a| p.gx.trait_assoc_consts.contains_key(a)) else {
                    continue;
                };
                if pending
                    .iter()
                    .any(|(it, _)| matches!(it.assoc, Some(PendingAssoc::TraitImpl { impl_def: d, assoc: a }) if d == impl_def && a == assoc))
                {
                    continue;
                }
                let self_ty = owner.map(|o| p.tys.adt_ty(o));
                let ty = match resolve_item_ty(p, c.ty, self_ty) {
                    Ok(t) => t,
                    Err(d) => match p.gx.trait_assoc_consts.get(&assoc).copied().filter(|&(t, _)| !p.tys.flags(t).contains_param()) {
                        // The scoped check in `finish_trait_impl`
                        // already validated the written type; a
                        // plain resolve failure here only means it
                        // names the impl's parameters, so the
                        // trait's concrete type stands in.
                        Some((t, _)) => t,
                        None => {
                            errs.push(d);
                            continue;
                        }
                    },
                };
                let Some(value) = c.default else {
                    errs.push(not_yet("L0632", c.name_span, "associated consts without a value"));
                    continue;
                };
                pending.push((
                    PendingConst {
                        name: Some(c.name),
                        ty,
                        expr: value,
                        span: c.span,
                        is_static: None,
                        static_idx: 0,
                        stmt_idx: None,
                        assoc: Some(PendingAssoc::TraitImpl { impl_def, assoc }),
                    },
                    PendingState::Todo,
                ));
            }
            continue;
        }
        let Some(owner) = owner else { continue };
        let self_ty = p.tys.adt_ty(owner);
        // Disjoint impls may define the same name (the overlap
        // check in `finish_collect` rejects the ones that can
        // both apply, methods included); two in one impl block
        // cannot.
        let (self_pat, impl_generics) = p.gx.inherent_impl_self.get(&impl_def).cloned().unwrap_or((self_ty, Generics::default()));
        for c in &imp.consts {
            if inherent_seen.contains(&(impl_def, c.name)) {
                errs.push(Diag::new(
                    "L0106",
                    c.name_span,
                    format!("`{}` is defined more than once", p.interner.get(c.name)),
                    "Rename one of the definitions.",
                ));
                continue;
            }
            let ty = match resolve_item_ty(p, c.ty, Some(self_ty)) {
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
            inherent_seen.push((impl_def, c.name));
            assoc_by_key.entry((p.adts[owner.0 as usize].name, c.name)).or_default().push(pending.len());
            pending.push((
                PendingConst {
                    name: Some(c.name),
                    ty,
                    expr: value,
                    span: c.span,
                    is_static: None,
                    static_idx: 0,
                    stmt_idx: None,
                    assoc: Some(PendingAssoc::Inherent { owner, impl_def, self_pat, generics: impl_generics.clone() }),
                },
                PendingState::Todo,
            ));
        }
    }
    // Trait defaults. A default whose type names the trait's
    // parameters has no single value to evaluate here; it stays
    // unregistered and use sites reject, as before.
    for item in &ast.items {
        let ItemKind::Trait(tdef) = &item.kind else { continue };
        let Some(&trait_def) = p.gx.trait_names.get(&tdef.name) else { continue };
        let Some(rec) = p.gx.index.trait_record(trait_def).cloned() else { continue };
        for c in &tdef.consts {
            let Some(value) = c.default else { continue };
            let Some(assoc) = rec.assoc_by_name(c.name) else { continue };
            let Some(&(ty, _)) = p.gx.trait_assoc_consts.get(&assoc) else { continue };
            if p.tys.flags(ty).contains_param() {
                continue;
            }
            if pending.iter().any(|(it, _)| matches!(it.assoc, Some(PendingAssoc::TraitDefault { assoc: a, .. }) if a == assoc)) {
                continue;
            }
            pending.push((
                PendingConst {
                    name: Some(c.name),
                    ty,
                    expr: value,
                    span: c.span,
                    is_static: None,
                    static_idx: 0,
                    stmt_idx: None,
                    assoc: Some(PendingAssoc::TraitDefault { trait_def, assoc }),
                },
                PendingState::Todo,
            ));
        }
    }
}

/// True when an impl Self pattern matches a written instance,
/// binding the impl's parameters to the parts they name. One
/// direction only (the pattern's parameters are variables, the
/// written type is ground), for const evaluation picks before
/// the checker exists.
fn self_pat_matches(tys: &crate::ty::GlobalTys, pat: Ty, target: Ty, map: &mut Vec<(u32, Ty)>, cmap: &mut Vec<(u32, crate::ty::ConstId)>) -> bool {
    use crate::ty::TyIntern;
    if let TyKind::Param(p) = tys.kind(pat) {
        return match map.iter().find(|&&(i, _)| i == p.0) {
            Some(&(_, t)) => t == target,
            None => {
                map.push((p.0, target));
                true
            }
        };
    }
    let mut args_match = |a: crate::ty::ArgsId, b: crate::ty::ArgsId, map: &mut Vec<(u32, Ty)>, cmap: &mut Vec<(u32, crate::ty::ConstId)>| {
        let (xs, ys) = (tys.args(a), tys.args(b));
        xs.len() == ys.len()
            && std::iter::zip(xs.iter(), ys.iter()).all(|(x, y)| match (x, y) {
                (crate::ty::GenericArg::Ty(x), crate::ty::GenericArg::Ty(y)) => self_pat_matches(tys, *x, *y, map, cmap),
                (crate::ty::GenericArg::Const(x), crate::ty::GenericArg::Const(y)) => match tys.const_kind(*x) {
                    crate::ty::ConstKind::Param(i) => match cmap.iter().find(|&&(j, _)| j == i) {
                        Some(&(_, c)) => c == *y,
                        None => {
                            cmap.push((i, *y));
                            true
                        }
                    },
                    _ => x == y,
                },
                _ => x == y,
            })
    };
    match (tys.kind(pat), tys.kind(target)) {
        (TyKind::Adt(d, a), TyKind::Adt(e, b)) => d == e && args_match(a, b, map, cmap),
        (TyKind::Ref(_, m, x), TyKind::Ref(_, n, y)) => m == n && self_pat_matches(tys, x, y, map, cmap),
        (TyKind::RawPtr(m, x), TyKind::RawPtr(n, y)) => m == n && self_pat_matches(tys, x, y, map, cmap),
        (TyKind::Slice(x), TyKind::Slice(y)) => self_pat_matches(tys, x, y, map, cmap),
        (TyKind::Array(x, n), TyKind::Array(y, m)) => {
            (match tys.const_kind(n) {
                crate::ty::ConstKind::Param(i) => match cmap.iter().find(|&&(j, _)| j == i) {
                    Some(&(_, c)) => c == m,
                    None => {
                        cmap.push((i, m));
                        true
                    }
                },
                _ => n == m,
            }) && self_pat_matches(tys, x, y, map, cmap)
        }
        (TyKind::Tuple(x), TyKind::Tuple(y)) => {
            let (xs, ys) = (tys.tys_of(x), tys.tys_of(y));
            xs.len() == ys.len() && std::iter::zip(xs.iter(), ys.iter()).all(|(a, b)| self_pat_matches(tys, *a, *b, map, cmap))
        }
        _ => pat == target,
    }
}

/// True when a named field of `adt` is not visible from module
/// `from`, by the resolver's field table. The const evaluator's
/// privacy hooks in collect and in body checking share this test;
/// it mirrors `check_field_vis` without its read recording.
pub(crate) fn named_field_is_private(p: &Program, adt: AdtId, field: Sym, from: crate::ty::defs::ModuleId) -> bool {
    let Some(tables) = &p.resolved else { return false };
    let Some(def) = p.defs.def_of_adt(adt) else { return false };
    match tables.field_vis.get(&def) {
        Some((def_mod, fields)) => fields.get(&field).is_some_and(|vis| !tables.visible(vis, *def_mod, from, p.interner)),
        None => false,
    }
}

/// True when tuple field `index` of `adt` is not visible from `from`.
pub(crate) fn tuple_field_is_private(p: &Program, adt: AdtId, index: u32, from: crate::ty::defs::ModuleId) -> bool {
    let Some(tables) = &p.resolved else { return false };
    let Some(def) = p.defs.def_of_adt(adt) else { return false };
    match tables.tuple_field_vis.get(&def) {
        Some((def_mod, fields)) => fields.get(index as usize).is_some_and(|vis| !tables.visible(vis, *def_mod, from, p.interner)),
        None => false,
    }
}

/// The const evaluator's context over the collected tables.
struct CollectCx<'x, 'a> {
    p: &'x mut Program<'a>,
    pending: Vec<(PendingConst, PendingState)>,
    by_name: HashMap<Sym, usize>,
    /// Pending inherent associated consts by (flat type name,
    /// const name), for `Type::CONST` reads in initializers.
    assoc_by_key: HashMap<(Sym, Sym), Vec<usize>>,
    /// The flat type name `Self` means while an inherent
    /// associated const evaluates (its owning Adt).
    self_name: Option<Sym>,
    /// The Self pattern of that same inherent impl, so a
    /// `Self::CONST` read picks this impl's const among
    /// same-name consts of disjoint impls.
    self_pat: Option<Ty>,
    /// The (self_name, self_pat) of each const fn body the evaluator
    /// entered (`enter_const_fn`), restored on exit.
    self_stack: Vec<(Option<Sym>, Option<Ty>)>,
    /// The defining module of the item now evaluating, for field
    /// privacy in its initializer. Nested item evaluation (an item
    /// that reads another const) restores the outer module, like
    /// `self_name`. None when the module is unknown (no resolver
    /// tables, or an item the tables do not name): no check then.
    module: Option<crate::ty::defs::ModuleId>,
    errs: &'x mut Vec<Diag>,
}

impl CollectCx<'_, '_> {
    /// The type instance a written `Type<...>` path head names,
    /// for picking among same-name inherent associated consts.
    /// `None` when the arguments are not all written (the pick
    /// is then ambiguous in a const context too).
    fn written_instance(&mut self, ty_name: Sym, seg: &ast::PathSeg) -> Option<Ty> {
        let adt = self.p.type_names.get(&ty_name).copied()?;
        let generics = self.p.gx.adt_generics.get(adt.0 as usize).cloned().unwrap_or_default();
        let n_args = generics.params.iter().filter(|p| p.kind != ParamKind::Lifetime).count();
        if n_args == 0 {
            return Some(self.p.tys.adt_ty(adt));
        }
        let ast::GenericArgs::Angle(written) = &seg.args else { return None };
        let mut args: Vec<crate::ty::GenericArg> = Vec::new();
        for a in written {
            match a {
                ast::GenericArg::Type(t) => {
                    let cx = self.p.gx.resolve_cx(&self.p.type_names, &self.p.aliases);
                    let ty = crate::check::generics::resolve_scoped(
                        self.p.ast,
                        self.p.interner,
                        self.p.known,
                        &cx,
                        &mut self.p.tys,
                        *t,
                        &crate::check::generics::Scope::default(),
                    )
                    .ok()?;
                    args.push(crate::ty::GenericArg::Ty(ty));
                }
                ast::GenericArg::Const(e) => {
                    let v = eval_array_len(self.p.ast, self.p.interner, self.p.known, *e)?;
                    args.push(crate::ty::GenericArg::Const(self.p.tys.intern_const(crate::ty::ConstKind::Int(v))));
                }
                _ => {}
            }
        }
        if args.len() != n_args {
            return None;
        }
        Some(self.p.tys.mk_adt(self.p.def_of_adt(adt), &args))
    }

    /// The defining module of one pending item: the resolver's
    /// span table for module items (anonymous and associated
    /// consts included), else the enclosing function's module for
    /// an item in a body (the smallest fn expression range that
    /// holds the initializer; nested fn items share their outer
    /// function's module, so any holding range gives it).
    fn pending_module(&self, it: &PendingConst) -> Option<crate::ty::defs::ModuleId> {
        let tables = self.p.resolved.as_deref()?;
        if let Some(m) = tables.const_init_module.get(&it.span) {
            return Some(*m);
        }
        if it.stmt_idx.is_none() {
            return None;
        }
        let mut best: Option<(u32, crate::ty::defs::ModuleId)> = None;
        for (i, f) in self.p.fns.iter().enumerate() {
            let (lo, hi) = f.def.exprs;
            if it.expr.0 >= lo && it.expr.0 < hi {
                let size = hi - lo;
                if best.is_none_or(|(b, _)| size < b)
                    && let Some(m) = tables.fn_module.get(i)
                {
                    best = Some((size, *m));
                }
            }
        }
        best.map(|(_, m)| m)
    }

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
        // `Self::CONST` in an inherent associated const's
        // initializer names its owning Adt; every other item
        // evaluates with no `Self`.
        let prev_self = self.self_name;
        let prev_pat = self.self_pat;
        (self.self_name, self.self_pat) = match self.pending[idx].0.assoc {
            Some(PendingAssoc::Inherent { owner, self_pat, .. }) => (Some(self.p.adts[owner.0 as usize].name), Some(self_pat)),
            // A trait impl const over a local Adt: `Self` is that Adt.
            Some(PendingAssoc::TraitImpl { impl_def, .. }) => {
                let self_ty =
                    self.p.gx.index.by_def(impl_def).and_then(|(_, r)| self.p.tys.args(r.trait_ref.args).first().and_then(|g| g.as_ty()));
                match self_ty.and_then(|t| self.p.tys.local_adt(t)) {
                    Some(a) => (Some(self.p.adts[a.0 as usize].name), self_ty),
                    None => (None, None),
                }
            }
            _ => (None, None),
        };
        let prev_module = self.module;
        self.module = self.pending_module(&self.pending[idx].0);
        let evaluated = crate::ty::consteval::eval(self, expr, Some(ty));
        self.module = prev_module;
        self.self_name = prev_self;
        self.self_pat = prev_pat;
        match evaluated {
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
    fn assoc_const_item(&mut self, segs: &[ast::PathSeg]) -> Option<crate::ty::consteval::TypedValue> {
        // The last two segments name the type and the const;
        // earlier segments are module anchors the resolver has
        // already folded into the flat type name where it can.
        let [.., ty_seg, item_seg] = segs else { return None };
        let self_form = ty_seg.name == self.p.known.self_type;
        let ty_name = if self_form { self.self_name? } else { ty_seg.name };
        if let Some(cands) = self.assoc_by_key.get(&(ty_name, item_seg.name)).cloned() {
            // Several disjoint impls may define the name: pick
            // by the written instance (`Self` is the evaluating
            // impl's own pattern), exactly one must match.
            let pick = if cands.len() == 1 {
                Some(cands[0])
            } else {
                let written = if self_form { self.self_pat } else { self.written_instance(ty_name, ty_seg) };
                let written = written?;
                let hits: Vec<usize> = cands
                    .iter()
                    .copied()
                    .filter(|&i| match self.pending[i].0.assoc {
                        Some(PendingAssoc::Inherent { self_pat, .. }) => {
                            self_pat_matches(&self.p.tys, self_pat, written, &mut Vec::new(), &mut Vec::new())
                        }
                        _ => false,
                    })
                    .collect();
                if hits.len() == 1 { Some(hits[0]) } else { None }
            };
            let i = pick?;
            let ty = self.pending[i].0.ty;
            return self.eval_pending(i).map(|v| (v, ty));
        }
        let adt = self.p.type_names.get(&ty_name).copied()?;
        let &[idx] = self.p.inherent_assoc_consts(adt, item_seg.name) else { return None };
        let c = &self.p.consts[idx as usize];
        Some((c.value.clone(), c.ty))
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
                    // Scoped resolution, not the plain one: the queried
                    // type can apply a generic Adt (`size_of::<W<u32>>()`),
                    // whose arguments the plain resolver rejects. A const
                    // context has no params in scope here.
                    let cx = self.p.gx.resolve_cx(&self.p.type_names, &self.p.aliases);
                    let t = crate::check::generics::resolve_scoped(
                        self.p.ast,
                        self.p.interner,
                        self.p.known,
                        &cx,
                        &mut self.p.tys,
                        args[0],
                        &crate::check::generics::Scope::default(),
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
            // `Self::f(..)` names the impl type `Self` means here.
            let head = if segs[0].name == self.p.known.self_type { self.self_name.unwrap_or(segs[0].name) } else { segs[0].name };
            match self.p.type_names.get(&head) {
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
            let owner = info.owner.map(|a| self.p.adt(a).name);
            return CallTarget::ConstFn(ConstFnBody { params, param_tys: info.params.clone(), ret: info.ret, body, owner });
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
    fn enter_const_fn(&mut self, owner: Option<Sym>) {
        self.self_stack.push((self.self_name, self.self_pat));
        self.self_name = owner;
        self.self_pat = None;
    }
    fn exit_const_fn(&mut self) {
        if let Some((name, pat)) = self.self_stack.pop() {
            self.self_name = name;
            self.self_pat = pat;
        }
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
        crate::ty::layout::layout_of_ty(&p.tys, &UserLayout(p), t).ok()
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
    fn named_field_private(&mut self, adt: AdtId, field: Sym) -> bool {
        match self.module {
            Some(m) => named_field_is_private(self.p, adt, field, m),
            None => false,
        }
    }
    fn tuple_field_private(&mut self, adt: AdtId, index: u32) -> bool {
        match self.module {
            Some(m) => tuple_field_is_private(self.p, adt, index, m),
            None => false,
        }
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
        // `Self` in an inherent associated const's initializer names the
        // owning Adt (`Self(1)`, `Self::A`, `Self { .. }`).
        let head = |n: Sym| if n == self.p.known.self_type { self.self_name.unwrap_or(n) } else { n };
        // `std::cmp::Ordering::Less`: the same std variant paths
        // `resolve_assoc` answers, for const contexts.
        if segs.len() >= 4 {
            let path: Vec<&str> = segs.iter().map(|s| self.p.interner.get(s.name)).collect();
            return generics::std_variant_of(self.p, &path);
        }
        if segs.len() == 1 {
            let &a = self.p.type_names.get(&head(segs[0].name))?;
            if self.p.adt(a).is_enum {
                return None;
            }
            return Some((a, 0));
        }
        if segs.len() == 2 {
            let &a = self.p.type_names.get(&head(segs[0].name))?;
            let v = self.p.adt(a).variants.iter().position(|v| v.name == segs[1].name)?;
            return Some((a, v as u32));
        }
        None
    }
}

/// The capture types of a closure type (its args, ARCH 2.9): the
/// closure value is a tuple of these.
pub fn closure_fields(tys: &impl TyIntern, a: ArgsId) -> Vec<Ty> {
    tys.args(a).iter().filter_map(|g| g.as_ty()).collect()
}

pub fn contains_ref(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(..) => true,
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| contains_ref(tys, e)),
        TyKind::Closure(_, a) => closure_fields(tys, a).iter().any(|&e| contains_ref(tys, e)),
        TyKind::Array(e, _) | TyKind::Slice(e) => contains_ref(tys, e),
        _ if tys.is_chars_ty(t) => true,
        // A `RefCell` guard holds its borrow of the cell.
        _ if tys.guard_elem(t).is_some() => true,
        _ => match tys.vec_elem(t).or_else(|| tys.option_elem(t)).or_else(|| tys.smart_elem(t)).or_else(|| tys.weak_elem(t)).or_else(|| tys.arc_weak_elem(t)).or_else(|| tys.refcell_elem(t)).or_else(|| tys.cell_elem(t)) {
            Some(e) => contains_ref(tys, e),
            None => match tys.result_args(t) {
                Some((a, b)) => contains_ref(tys, a) || contains_ref(tys, b),
                None => match crate::ty::iter::iter_parts(tys, t) {
                    Some((k, a)) => crate::ty::iter::iter_holds_ref(k, &a, &|e| contains_ref(tys, e)),
                    None => false,
                },
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
        TyKind::FnDef(..) | TyKind::FnPtr(_) => true,
        TyKind::Infer(v) => v.is_int() || v.is_float(),
        TyKind::Ref(_, m, _) => !m.is_mut(),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| is_copy(p, tys, e)),
        TyKind::Closure(_, a) => closure_fields(tys, a).iter().all(|&e| is_copy(p, tys, e)),
        TyKind::Array(e, _) => is_copy(p, tys, e),
        _ => {
            if tys.is_exit_code(t) {
                return true;
            }
            if let Some(Ok(b)) = crate::check::sync::sync_glue(tys, t, crate::check::sync::SyncGlue::Copy) {
                return b;
            }
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
    glue_clone(p, tys, t, &mut Vec::new())
}

/// The walk behind `has_clone`; `seen` stops recursive generic types.
fn glue_clone(p: &Program, tys: &impl TyIntern, t: Ty, seen: &mut Vec<Ty>) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => return env_proves(tys, t, p.gx.lang.clone, None),
        TyKind::Tuple(ts) => return tys.tys_of(ts).iter().all(|&e| glue_clone(p, tys, e, seen)),
        // A closure is Clone when its captures are; only the Copy
        // case is supported (a clone of a closure is a copy then).
        TyKind::Closure(..) => return is_copy(p, tys, t),
        TyKind::Array(e, _) => return glue_clone(p, tys, e, seen),
        _ => {}
    }
    if tys.is_string_ty(t) || tys.is_exit_code(t) {
        return true;
    }
    if tys.rc_elem(t).is_some() || tys.weak_elem(t).is_some() || tys.arc_weak_elem(t).is_some() {
        return true;
    }
    if let Some(Ok(b)) = crate::check::sync::sync_glue(tys, t, crate::check::sync::SyncGlue::Clone) {
        return b;
    }
    // `Ref`/`RefMut` are not Clone (`Ref::clone` is an associated fn);
    // `Cell<T>` is Clone for `T: Copy`, `RefCell<T>` for `T: Clone`.
    if tys.guard_elem(t).is_some() {
        return false;
    }
    if let Some(e) = tys.cell_elem(t) {
        return is_copy(p, tys, e);
    }
    // `Box<[T]>` clones its elements.
    if let Some(e) = tys.boxed_slice_elem(t) {
        return has_clone(p, tys, e);
    }
    if let Some(e) = tys.vec_elem(t).or_else(|| tys.option_elem(t)).or_else(|| tys.smart_elem(t)).or_else(|| tys.refcell_elem(t)) {
        return glue_clone(p, tys, e, seen);
    }
    if let Some((a, b)) = tys.result_args(t) {
        return glue_clone(p, tys, a, seen) && glue_clone(p, tys, b, seen);
    }
    match tys.local_adt(t) {
        Some(a) => {
            // A written non-generic impl: the glue calls its method.
            if p.gx.glue_methods.contains_key(&(a, p.gx.lang.clone)) {
                return true;
            }
            p.adt(a).derives.clone && adt_instance_fields_all(p, a, t, seen, &mut |f, seen| glue_clone(p, tys, f, seen))
        }
        None => is_copy(p, tys, t),
    }
}

/// True when the ordering operators and `partial_cmp` apply by
/// structure: scalars, strings, tuples, arrays, slices, `Vec`,
/// `Option`, `Result`, `Box`, `Rc`, references, and Adts that
/// derive `PartialOrd` with fields of such types (codegen compares
/// them with the `cmp` glue; tuples of scalars expand in lowering).
/// A field type whose `PartialOrd` impl is written by hand needs
/// that impl's method, which the glue cannot call: false.
pub fn has_ord(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    glue_cmp(p, tys, t, false, &mut Vec::new())
}

/// `has_ord` for `Ord`: the same shapes without floats, and Adts
/// that derive `Ord`.
pub fn has_total_ord(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    glue_cmp(p, tys, t, true, &mut Vec::new())
}

/// The structural walk behind `has_ord` and `has_total_ord`. `seen`
/// holds the Adt types on the walk (a recursive type through `Box`
/// or `Vec` compares by the same glue: the cycle adds no field type).
fn glue_cmp(p: &Program, tys: &impl TyIntern, t: Ty, total: bool, seen: &mut Vec<Ty>) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => {
            if total {
                env_proves(tys, t, p.gx.lang.ord, None)
            } else {
                env_proves(tys, t, p.gx.lang.partial_ord, Some(t))
            }
        }
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Str | TyKind::Error => true,
        TyKind::Float(_) => !total,
        TyKind::Infer(v) => v.is_int() || (v.is_float() && !total),
        TyKind::Ref(_, _, e) | TyKind::Array(e, _) | TyKind::Slice(e) => glue_cmp(p, tys, e, total, seen),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| glue_cmp(p, tys, e, total, seen)),
        _ => {
            if tys.is_string_ty(t) {
                return true;
            }
            // A guard (`Ref`, `MutexGuard`) has no `PartialOrd` or `Hash`.
            if tys.guard_elem(t).is_some() {
                return false;
            }
            if let Some(e) = tys.vec_elem(t).or_else(|| tys.option_elem(t)).or_else(|| tys.smart_elem(t)) {
                return glue_cmp(p, tys, e, total, seen);
            }
            if let Some((a, b)) = tys.result_args(t) {
                return glue_cmp(p, tys, a, total, seen) && glue_cmp(p, tys, b, total, seen);
            }
            match tys.local_adt(t) {
                // A written non-generic `PartialOrd` (and no `Ord`): the
                // glue calls its `partial_cmp`.
                Some(a) if !total && p.gx.glue_methods.contains_key(&(a, p.gx.lang.partial_ord)) => true,
                Some(a) => {
                    let d = p.adt(a).derives;
                    if !(if total { d.ord } else { d.partial_ord }) {
                        return false;
                    }
                    // rustc's derived `partial_cmp` on a non-generic
                    // type that also derives `Ord` is `Some(self.cmp(
                    // other))`: its fields must then order by `Ord`.
                    let generic = p.gx.adt_instance_of.get(a.0 as usize).is_some_and(|o| o.is_some())
                        || p.gx.adt_generics.get(a.0 as usize).is_some_and(|g| !g.params.is_empty());
                    let fields_total = total || (d.ord && !generic);
                    adt_fields_all(p, a, t, seen, &mut |f, seen| glue_cmp(p, tys, f, fields_total, seen))
                }
                None => false,
            }
        }
    }
}

/// True when `ok` holds for every field type of a materialized
/// generic Adt instance `a` (type `t`); a non-generic Adt or a
/// template answers true (collect checked the derive's fields, and
/// a template's instances answer for themselves). `seen` stops
/// recursion through recursive generic types.
fn adt_instance_fields_all(p: &Program, a: AdtId, t: Ty, seen: &mut Vec<Ty>, ok: &mut dyn FnMut(Ty, &mut Vec<Ty>) -> bool) -> bool {
    let instance = p.gx.adt_instance_of.get(a.0 as usize).is_some_and(|o| o.is_some());
    if !instance || seen.contains(&t) {
        return true;
    }
    seen.push(t);
    let all = p.adt(a).variants.iter().all(|v| v.fields.iter().all(|f| ok(f.ty, seen)));
    seen.pop();
    all
}

/// True when `ok` holds for every field type of Adt `a` (the Adt of
/// type `t`), or when the fields are a generic template's (a template
/// body: its instances answer with their own substituted fields).
/// `seen` stops recursion through recursive types.
fn adt_fields_all(p: &Program, a: AdtId, t: Ty, seen: &mut Vec<Ty>, ok: &mut dyn FnMut(Ty, &mut Vec<Ty>) -> bool) -> bool {
    let template = p.gx.adt_instance_of.get(a.0 as usize).is_none_or(|o| o.is_none())
        && p.gx.adt_generics.get(a.0 as usize).is_some_and(|g| !g.params.is_empty());
    if template || seen.contains(&t) {
        return true;
    }
    seen.push(t);
    let all = p.adt(a).variants.iter().all(|v| v.fields.iter().all(|f| ok(f.ty, seen)));
    seen.pop();
    all
}

/// An auto trait (`Send`, `Sync`, `Unpin`) of `t` by structure (ARCH
/// 2.7), shared by body checks (`Ctx::auto_holds`, on resolved
/// types) and collect-time proofs: a parameter answers from `env`,
/// references and raw pointers by the fixed table, compound types
/// and Adts through their parts (a generic Adt's fields substituted
/// with this application's args), closures through their captures,
/// `dyn` through its bounds, and the builtin std types by std's own
/// impls (`Rc` and `env::Args` are neither Send nor Sync; `Vec`,
/// `Box`, and `Rc` are Unpin for every element type). None when an
/// inference variable, a projection, or another form leaves it open.
/// `seen` holds the (trait, type) pairs on the walk: a cycle counts as
/// holding. The trait is part of the key: `&T: Send` asks `T: Sync`.
pub fn auto_structural(p: &Program, tys: &mut impl TyIntern, env: &[Predicate], trait_def: DefId, t: Ty, seen: &mut Vec<(DefId, Ty)>) -> Option<bool> {
    let lang = &p.gx.lang;
    if seen.contains(&(trait_def, t)) {
        return Some(true);
    }
    let all = |tys: &mut _, parts: Vec<Ty>, seen: &mut Vec<(DefId, Ty)>| -> Option<bool> {
        let mut unknown = false;
        for e in parts {
            match auto_structural(p, tys, env, trait_def, e, seen) {
                Some(false) => return Some(false),
                None => unknown = true,
                _ => {}
            }
        }
        if unknown { None } else { Some(true) }
    };
    match tys.kind(t) {
        TyKind::Error => Some(true),
        // Every integer and float type has every auto trait, so a
        // literal not yet fixed does too (`vec![1, 2]` moved into a
        // `Send` closure).
        TyKind::Infer(v) if v.is_int() || v.is_float() => Some(true),
        TyKind::Infer(_) | TyKind::Projection(..) => None,
        TyKind::Param(_) => Some(env.iter().any(|pred| {
            matches!(pred, Predicate::Trait(b) if b.value.def == trait_def && tys.args(b.value.args)[0].as_ty() == Some(t))
        })),
        TyKind::RawPtr(..) => Some(trait_def == lang.unpin),
        TyKind::Dyn(..) => {
            let a = crate::check::object::dyn_auto(p, tys, t);
            Some(if trait_def == lang.send {
                a.send
            } else if trait_def == lang.sync {
                a.sync
            } else {
                a.unpin
            })
        }
        TyKind::Ref(_, m, e) => {
            if trait_def == lang.unpin {
                return Some(true);
            }
            seen.push((trait_def, t));
            // `&T: Send` needs `T: Sync`; every other pair keeps the trait.
            let need = if trait_def == lang.send && !m.is_mut() { lang.sync } else { trait_def };
            auto_structural(p, tys, env, need, e, seen)
        }
        TyKind::Slice(e) | TyKind::Array(e, _) => {
            seen.push((trait_def, t));
            auto_structural(p, tys, env, trait_def, e, seen)
        }
        TyKind::Tuple(ts) => {
            seen.push((trait_def, t));
            let elems = tys.tys_of(ts).to_vec();
            all(tys, elems, seen)
        }
        TyKind::Closure(_, a) => {
            seen.push((trait_def, t));
            let caps = closure_fields(tys, a);
            all(tys, caps, seen)
        }
        TyKind::Int(_)
        | TyKind::Float(_)
        | TyKind::Bool
        | TyKind::Char
        | TyKind::Unit
        | TyKind::Str
        | TyKind::Never
        | TyKind::FnDef(..)
        | TyKind::FnPtr(_) => Some(true),
        _ => {
            // The std types' own facts (check/sync.rs keeps the table).
            if let Some(r) = crate::check::sync::builtin_auto(p, tys, env, trait_def, t, seen) {
                return r;
            }
            if let Some(e) = tys.vec_elem(t).or_else(|| tys.option_elem(t)).or_else(|| tys.boxed_elem(t)) {
                seen.push((trait_def, t));
                return auto_structural(p, tys, env, trait_def, e, seen);
            }
            if let Some((a, b)) = tys.result_args(t) {
                seen.push((trait_def, t));
                return all(tys, vec![a, b], seen);
            }
            if let Some(a) = tys.local_adt(t) {
                // Written `unsafe impl Send for S {}` replaces the
                // structural rule (W-THREADS).
                if let Some(r) = crate::check::sync::explicit_auto_impl(p, tys, t, trait_def) {
                    return Some(r);
                }
                seen.push((trait_def, t));
                let args: Vec<GenericArg> = tys.adt_parts(t).map(|(_, a)| tys.args(a).to_vec()).unwrap_or_default();
                let raw: Vec<Ty> = p.adt(a).variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
                let fields: Vec<Ty> =
                    raw.into_iter().map(|f| if args.is_empty() || !tys.flags(f).contains_param() { f } else { subst(tys, f, &args) }).collect();
                return all(tys, fields, seen);
            }
            None
        }
    }
}

/// True when `t` implements `Hash` by structure: scalars other than
/// floats, strings, references, tuples, arrays, slices, the builtin
/// containers of such types, and Adts that derive `Hash` with
/// fields of such types. (Lust has no `Hasher` yet: this answers
/// bounds, no hashing code exists.)
pub fn has_hash(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    glue_hash(p, tys, t, &mut Vec::new())
}

fn glue_hash(p: &Program, tys: &impl TyIntern, t: Ty, seen: &mut Vec<Ty>) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => env_proves(tys, t, p.gx.lang.hash, None),
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Str | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int(),
        TyKind::Ref(_, _, e) | TyKind::Array(e, _) | TyKind::Slice(e) => glue_hash(p, tys, e, seen),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| glue_hash(p, tys, e, seen)),
        _ => {
            if tys.is_string_ty(t) {
                return true;
            }
            if tys.guard_elem(t).is_some() {
                return false;
            }
            if let Some(e) = tys.vec_elem(t).or_else(|| tys.option_elem(t)).or_else(|| tys.smart_elem(t)) {
                return glue_hash(p, tys, e, seen);
            }
            if let Some((a, b)) = tys.result_args(t) {
                return glue_hash(p, tys, a, seen) && glue_hash(p, tys, b, seen);
            }
            match tys.local_adt(t) {
                Some(a) if p.adt(a).derives.hash => adt_fields_all(p, a, t, seen, &mut |f, seen| glue_hash(p, tys, f, seen)),
                _ => false,
            }
        }
    }
}

/// True when `Default::default()` builds a value of `t` by
/// structure (the `default` glue): scalars, `String`, `Vec`,
/// `Option`, tuples, arrays of at most 32 elements, `Box` and `Rc`
/// of such types, `&str` and `&[T]`, and Adts that derive `Default`
/// with fields of such types.
pub fn has_default(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    glue_default(p, tys, t, &mut Vec::new())
}

fn glue_default(p: &Program, tys: &impl TyIntern, t: Ty, seen: &mut Vec<Ty>) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => env_proves(tys, t, p.gx.lang.default, None),
        TyKind::Int(_) | TyKind::Float(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int() || v.is_float(),
        TyKind::Ref(_, _, e) => matches!(tys.kind(e), TyKind::Str | TyKind::Slice(_)),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| glue_default(p, tys, e, seen)),
        TyKind::Array(e, n) => match tys.const_kind(n) {
            ConstKind::Int(0) => true,
            ConstKind::Int(k) if k <= 32 => glue_default(p, tys, e, seen),
            _ => false,
        },
        _ => {
            if tys.is_string_ty(t) || tys.vec_elem(t).is_some() || tys.option_elem(t).is_some() {
                return true;
            }
            match crate::check::sync::sync_glue(tys, t, crate::check::sync::SyncGlue::Default) {
                Some(Ok(b)) => return b,
                Some(Err(e)) => return glue_default(p, tys, e, seen),
                None => {}
            }
            if tys.guard_elem(t).is_some() {
                return false;
            }
            if let Some(e) = tys.smart_elem(t) {
                return glue_default(p, tys, e, seen);
            }
            match tys.local_adt(t) {
                Some(a) => {
                    // A written non-generic impl: the glue calls its method.
                    if p.gx.glue_methods.contains_key(&(a, p.gx.lang.default)) {
                        return true;
                    }
                    let adt = p.adt(a);
                    if !adt.derives.default {
                        return false;
                    }
                    // An enum's default is its unit `#[default]` variant.
                    adt.is_enum || adt_fields_all(p, a, t, seen, &mut |f, seen| glue_default(p, tys, f, seen))
                }
                None => false,
            }
        }
    }
}

pub fn has_eq(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    glue_eq(p, tys, t, &mut Vec::new())
}

/// The walk behind `has_eq`; `seen` stops recursive generic types.
fn glue_eq(p: &Program, tys: &impl TyIntern, t: Ty, seen: &mut Vec<Ty>) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => env_proves(tys, t, p.gx.lang.partial_eq, Some(t)),
        // Fn pointers compare by address in Rust; fn items do not.
        TyKind::FnPtr(_) => true,
        TyKind::Float(_) => true,
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Str | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int() || v.is_float(),
        TyKind::Ref(_, _, e) => glue_eq(p, tys, e, seen),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| glue_eq(p, tys, e, seen)),
        TyKind::Array(e, _) | TyKind::Slice(e) => glue_eq(p, tys, e, seen),
        _ => {
            if tys.is_string_ty(t) || tys.is_exit_code(t) {
                return true;
            }
            if let Some(Ok(b)) = crate::check::sync::sync_glue(tys, t, crate::check::sync::SyncGlue::PartialEq) {
                return b;
            }
            if tys.guard_elem(t).is_some() {
                return false;
            }
            if let Some(e) = tys.vec_elem(t).or_else(|| tys.option_elem(t)).or_else(|| tys.smart_elem(t)) {
                return glue_eq(p, tys, e, seen);
            }
            if let Some((a, b)) = tys.result_args(t) {
                return glue_eq(p, tys, a, seen) && glue_eq(p, tys, b, seen);
            }
            match tys.local_adt(t) {
                // A written non-generic impl: the glue calls its `eq`.
                Some(a) if p.gx.glue_methods.contains_key(&(a, p.gx.lang.partial_eq)) => true,
                Some(a) => p.adt(a).derives.partial_eq && adt_instance_fields_all(p, a, t, seen, &mut |f, seen| glue_eq(p, tys, f, seen)),
                None => false,
            }
        }
    }
}

pub fn has_debug(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    glue_debug(p, tys, t, &mut Vec::new())
}

/// The walk behind `has_debug`; `seen` stops recursive generic types.
fn glue_debug(p: &Program, tys: &impl TyIntern, t: Ty, seen: &mut Vec<Ty>) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => env_proves(tys, t, p.gx.lang.debug, None),
        TyKind::Float(_) => true,
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Str | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int() || v.is_float(),
        TyKind::Ref(_, _, e) => glue_debug(p, tys, e, seen),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().all(|&e| glue_debug(p, tys, e, seen)),
        TyKind::Array(e, _) | TyKind::Slice(e) => glue_debug(p, tys, e, seen),
        _ => {
            // `env::Args` prints `Args { inner: [..] }` in Rust; lust has
            // no such rendering, so it is not Debug here (a reject).
            if tys.is_string_ty(t) || tys.is_exit_code(t) || tys.weak_elem(t).is_some() || tys.arc_weak_elem(t).is_some() {
                return true;
            }
            match crate::check::sync::sync_glue(tys, t, crate::check::sync::SyncGlue::Debug) {
                Some(Ok(b)) => return b,
                Some(Err(e)) => return glue_debug(p, tys, e, seen),
                None => {}
            }
            if let Some(e) = tys.cell_elem(t) {
                return is_copy(p, tys, e) && glue_debug(p, tys, e, seen);
            }
            if let Some(e) = tys.vec_elem(t).or_else(|| tys.option_elem(t)).or_else(|| tys.smart_elem(t)).or_else(|| tys.refcell_elem(t)) {
                return glue_debug(p, tys, e, seen);
            }
            if let Some((a, b)) = tys.result_args(t) {
                return glue_debug(p, tys, a, seen) && glue_debug(p, tys, b, seen);
            }
            match tys.local_adt(t) {
                Some(a) => {
                    (p.adt(a).derives.debug && adt_instance_fields_all(p, a, t, seen, &mut |f, seen| glue_debug(p, tys, f, seen)))
                        || crate::check::fmt::user_impl_holds(p, tys, t, p.gx.lang.debug)
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
        _ => {
            tys.is_string_ty(t)
                || tys.smart_elem(t).is_some_and(|e| has_display(p, tys, e))
                || tys.poison_elem(t).is_some()
                || matches!(crate::ty::sync::sync_kind(tys, t), Some(crate::ty::sync::SyncTy::SendError | crate::ty::sync::SyncTy::TryLockError))
                || tys.adt_parts(t).is_some_and(|(d, _)| {
                    d == crate::check::generics::fmt_error_def()
                        || d == generics::utf8_error_def()
                        || d == generics::from_utf8_error_def()
                        || d == generics::recv_error_def()
                        || d == generics::try_recv_error_def()
                })
                || (tys.local_adt(t).is_some() && crate::check::fmt::user_impl_holds(p, tys, t, p.gx.lang.display))
        }
    }
}

/// True if values of this type own heap memory and need a drop call.
/// A `Param` or projection type may (rustc's drop check assumes so).
pub fn needs_drop(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Param(_) | TyKind::Projection(..) => return true,
        TyKind::Tuple(ts) => return tys.tys_of(ts).iter().any(|&e| needs_drop(p, tys, e)),
        TyKind::Closure(_, a) => return closure_fields(tys, a).iter().any(|&e| needs_drop(p, tys, e)),
        TyKind::Array(e, _) => return needs_drop(p, tys, e),
        _ => {}
    }
    if tys.is_string_ty(t) || tys.vec_elem(t).is_some() || tys.smart_elem(t).is_some() || tys.weak_elem(t).is_some() || tys.arc_weak_elem(t).is_some() {
        return true;
    }
    // A join handle detaches (or frees) its thread; a `Thread` is counted.
    if matches!(
        crate::ty::sync::sync_kind(tys, t),
        Some(
            crate::ty::sync::SyncTy::JoinHandle
                | crate::ty::sync::SyncTy::ScopedJoinHandle
                | crate::ty::sync::SyncTy::Thread
                | crate::ty::sync::SyncTy::Sender
                | crate::ty::sync::SyncTy::SyncSender
                | crate::ty::sync::SyncTy::Receiver
        )
    ) {
        return true;
    }
    if let Some(e) = tys.refcell_elem(t).or_else(|| tys.cell_elem(t)).or_else(|| tys.lock_elem(t).map(|l| l.1)).or_else(|| tys.poison_elem(t)).or_else(|| {
        matches!(crate::ty::sync::sync_kind(tys, t), Some(crate::ty::sync::SyncTy::SendError | crate::ty::sync::SyncTy::OnceLock))
            .then(|| tys.adt_first_ty_arg(t))
            .flatten()
    }) {
        return needs_drop(p, tys, e);
    }
    if let Some(e) = tys.option_elem(t) {
        return needs_drop(p, tys, e);
    }
    if let Some((a, b)) = tys.result_args(t) {
        return needs_drop(p, tys, a) || needs_drop(p, tys, b);
    }
    if let Some((k, a)) = crate::ty::iter::iter_parts(tys, t) {
        // `vec::IntoIter` owns its buffer. Other kinds drop what their
        // args hold (an over-count for the `Map` item arg is harmless:
        // the drop glue only drops stored fields).
        return matches!(k, crate::ty::iter::IterKind::VecIntoIter | crate::ty::iter::IterKind::RecvIntoIter) || a.iter().any(|&e| needs_drop(p, tys, e));
    }
    match tys.local_adt(t) {
        Some(a) => {
            p.gx.drop_methods.contains_key(&a) || p.adt(a).variants.iter().any(|v| v.fields.iter().any(|f| needs_drop(p, &p.tys, f.ty)))
        }
        None => false,
    }
}

/// Layout shapes for the layout answers user code can observe
/// (`size_of`, `align_of`, `size_of_val`, `offset_of!`, const
/// evaluation): `Program`'s shapes, except that an adapter type whose
/// manifest does not list it as exact-layout (ARCH 3.6) has none, so
/// the query rejects with L0652 instead of answering with a size the
/// real crate does not have. Codegen keeps using `Program` itself.
pub struct UserLayout<'p, 'a>(pub &'p Program<'a>);

impl crate::ty::layout::AdtShapes for UserLayout<'_, '_> {
    fn adt_shape(&self, id: AdtId) -> Option<crate::ty::layout::AdtShape> {
        let p = self.0;
        let adt = p.adts.get(id.0 as usize)?;
        if let Some(a) = p.adapter_at(adt.span) {
            let path = p.display_path(adt.name);
            if !a.exact_layout.iter().any(|t| *t == path) {
                return None;
            }
        }
        p.adt_shape(id)
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
