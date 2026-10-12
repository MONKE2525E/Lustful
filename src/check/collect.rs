// Collection: builds the item tables (types, functions, methods) and resolves all signatures.
// This is the only stage that runs in sequence. Function bodies are checked after it, in parallel.
use crate::ast::{self, Ast, ItemKind, SelfKind, TyExpr, VariantFields};
pub use crate::def::{CrateId, DefId, DefPathHash, LocalDefId, StableCrateHash};
use crate::def::{CrateIds, DiskDefId};
use crate::diag::{Diag, Span, not_yet, unsupported};
use crate::intern::FxMap as HashMap;
use crate::intern::{Interner, Known, Sym};
use crate::ty::defs::{DefKind as DefsKind, Vis};
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
}

pub struct AdtDef {
    pub name: Sym,
    pub is_enum: bool,
    /// A struct has exactly one variant, named after the struct.
    pub variants: Vec<Variant>,
    pub derives: Derives,
    pub span: Span,
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
    tys: &mut impl TyIntern,
    id: ast::TyId,
    self_ty: Option<Ty>,
) -> Result<Ty, Diag> {
    let span = ast.ty_span(id);
    match ast.ty(id) {
        TyExpr::Unit => Ok(UNIT),
        TyExpr::Ref { mutable, inner, .. } => {
            let inner = resolve_ty(ast, interner, known, type_names, tys, *inner, self_ty)?;
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
                let e = resolve_ty(ast, interner, known, type_names, tys, args[0], self_ty)?;
                return Ok(tys.mk_vec(e));
            }
            if name == known.Option {
                let args = seg.type_args();
                if args.len() != 1 {
                    return Err(Diag::new("L0110", span, "Option takes one type argument", "Write `Option<T>`."));
                }
                let e = resolve_ty(ast, interner, known, type_names, tys, args[0], self_ty)?;
                return Ok(tys.mk_option(e));
            }
            if let Some(&adt) = type_names.get(&name) {
                return no_generics(tys.adt_ty(adt));
            }
            let n = interner.get(name);
            if ["HashMap", "HashSet", "BTreeMap", "Result", "Box", "Rc", "Arc", "RefCell", "Cell", "f32", "f64", "i128", "u128"]
                .contains(&n)
            {
                return Err(not_yet("L0641", span, &format!("the `{n}` type")));
            }
            Err(Diag::new("L0102", span, format!("unknown type `{n}`"), "Check the spelling, or define the type."))
        }
        // AST v2 type forms: the parser rejects each one today, so this is
        // only a reject path for completeness.
        _ => Err(not_yet("L0602", span, "this type form")),
    }
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
        fn_names: HashMap::default(),
        methods: HashMap::default(),
        main: None,
        krate: crate_ids.local,
        stable_crate: crate_ids.stable,
        fn_defs: Vec::new(),
        def_by_hash: HashMap::default(),
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
        p.adts.push(AdtDef { name, is_enum, variants: Vec::new(), derives: Derives::default(), span });
        p.tys.register_adt(def, id);
        let kind = if is_enum { DefsKind::Enum } else { DefsKind::Struct };
        p.defs.insert_adt(def, id, DefData::skeleton(kind, None, name, Vis::Priv, span));
        p.tys.intern(TyKind::Adt(def, EMPTY_ARGS));
    }

    // Pass 2: fields, variants, derives.
    let mut adt_index = 0;
    for item in &ast.items {
        type FieldSrc = (Sym, ast::TyId, Span);
        type VariantSrc = (Sym, Span, VariantShape, Vec<FieldSrc>);
        let (variants_src, derives_src): (Vec<VariantSrc>, &Vec<(Sym, Span)>) = match &item.kind {
            ItemKind::Struct(s) => {
                let (shape, fields) = variant_fields_src(&s.fields);
                let shape = if shape == VariantShape::Unit { VariantShape::Named } else { shape };
                (vec![(s.name, s.name_span, shape, fields)], &s.derives)
            }
            ItemKind::Enum(e) => {
                let vs = e
                    .variants
                    .iter()
                    .map(|v| {
                        let (shape, fs) = variant_fields_src(&v.fields);
                        (v.name, v.span, shape, fs)
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
        for (vname, vspan, shape, field_srcs) in variants_src {
            let shape = if !is_enum && field_srcs.is_empty() { VariantShape::Unit } else { shape };
            let mut fields = Vec::new();
            for (fname, fty, fspan) in field_srcs {
                if shape == VariantShape::Named && fields.iter().any(|f: &Field| f.name == fname) {
                    errs.push(dup(fspan, interner.get(fname)));
                }
                match resolve_ty(ast, interner, known, &p.type_names, &mut p.tys, fty, None) {
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
            variants.push(Variant { name: vname, shape, fields });
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
    }

    // Derived traits need every field type to have the trait too.
    for i in 0..p.adts.len() {
        let adt = &p.adts[i];
        let d = adt.derives;
        for v in &adt.variants {
            for f in &v.fields {
                let checks = [
                    (d.clone, has_clone(&p, &p.tys, f.ty), "Clone"),
                    (d.copy, is_copy(&p, &p.tys, f.ty), "Copy"),
                    (d.partial_eq, has_eq(&p, &p.tys, f.ty), "PartialEq"),
                    (d.debug, has_debug(&p, &p.tys, f.ty), "Debug"),
                ];
                for (wanted, ok, name) in checks {
                    if wanted && !ok {
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
            match resolve_ty(ast, interner, known, &p.type_names, &mut p.tys, param.ty, self_ty) {
                Ok(t) => params.push(t),
                Err(d) => {
                    errs.push(d);
                    params.push(ERROR);
                }
            }
        }
        let ret = match def.ret {
            None => UNIT,
            Some(t) => resolve_ty(ast, interner, known, &p.type_names, &mut p.tys, t, self_ty).unwrap_or_else(|d| {
                errs.push(d);
                ERROR
            }),
        };
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

pub fn contains_ref(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(..) => true,
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
            // Option<T> holds T by value.
            let mut t = f.ty;
            while let Some(inner) = p.tys.option_elem(t) {
                t = inner;
            }
            if let Some(a) = p.tys.local_adt(t)
                && (a == root || contains_adt_by_value(p, root, a, seen))
            {
                return true;
            }
        }
    }
    false
}

// Trait queries. Lust has no user traits yet, so these follow fixed rules plus derives.

// The queries below follow the old fixed rules, now read through the v2 compat
// helpers: builtin Adts answer through `BuiltinTy`, user Adts through their derives.

pub fn is_copy(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Never | TyKind::Error => true,
        TyKind::Infer(v) => v.is_int(),
        TyKind::Ref(_, m, _) => !m.is_mut(),
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
