// Collection: builds the item tables (types, functions, methods) and resolves all signatures.
// This is the only stage that runs in sequence. Function bodies are checked after it, in parallel.
use crate::ast::{self, Ast, ItemKind, SelfKind, TyExpr, VariantFields};
use crate::diag::{Diag, Span, unsupported};
use crate::intern::FxMap as HashMap;
use crate::intern::{Interner, Known, Sym};
use crate::types::*;

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

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct FnId(pub u32);

pub struct Program<'a> {
    pub ast: &'a Ast,
    pub interner: &'a Interner,
    pub known: &'a Known,
    pub tys: GlobalTys,
    pub adts: Vec<AdtDef>,
    pub fns: Vec<FnInfo<'a>>,
    pub type_names: HashMap<Sym, AdtId>,
    pub fn_names: HashMap<Sym, FnId>,
    pub methods: HashMap<(AdtId, Sym), FnId>,
    pub main: Option<FnId>,
}

impl<'a> Program<'a> {
    pub fn name(&self, s: Sym) -> &str {
        self.interner.get(s)
    }
    pub fn adt(&self, id: AdtId) -> &AdtDef {
        &self.adts[id.0 as usize]
    }
    pub fn fn_info(&self, id: FnId) -> &FnInfo<'a> {
        &self.fns[id.0 as usize]
    }
}

/// Human-readable type name, for error messages.
pub fn ty_name(p: &Program, tys: &impl TyIntern, t: Ty) -> String {
    match tys.kind(t) {
        TyKind::Error => "{error}".into(),
        TyKind::Unit => "()".into(),
        TyKind::Bool => "bool".into(),
        TyKind::Char => "char".into(),
        TyKind::Str => "str".into(),
        TyKind::String => "String".into(),
        TyKind::Never => "!".into(),
        TyKind::Int(i) => i.name().into(),
        TyKind::Vec(e) => format!("Vec<{}>", ty_name(p, tys, e)),
        TyKind::Option(e) => format!("Option<{}>", ty_name(p, tys, e)),
        TyKind::Chars => "std::str::Chars".into(),
        TyKind::Ref(m, e) => format!("&{}{}", if m { "mut " } else { "" }, ty_name(p, tys, e)),
        TyKind::Adt(a) => p.name(p.adt(a).name).into(),
        TyKind::Args => "std::env::Args".into(),
        TyKind::Var(_, true) => "{integer}".into(),
        TyKind::Var(..) => "_".into(),
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
        TyExpr::Ref { mutable, inner } => {
            let inner = resolve_ty(ast, interner, known, type_names, tys, *inner, self_ty)?;
            Ok(tys.intern(TyKind::Ref(*mutable, inner)))
        }
        TyExpr::Path(segs) => {
            // Accept `std::...::Name` by looking only at the last segment of std paths.
            let seg = if segs.len() > 1 && segs[0].name == known.std {
                segs.last().unwrap()
            } else if segs.len() == 1 {
                &segs[0]
            } else {
                return Err(unsupported(span, "module paths in types"));
            };
            let name = seg.name;
            let no_generics = |tys: Ty| -> Result<Ty, Diag> {
                if seg.generics.is_empty() {
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
                if seg.generics.len() != 1 {
                    return Err(Diag::new("L0110", span, "Vec takes one type argument", "Write `Vec<T>`."));
                }
                let e = resolve_ty(ast, interner, known, type_names, tys, seg.generics[0], self_ty)?;
                return Ok(tys.intern(TyKind::Vec(e)));
            }
            if name == known.Option {
                if seg.generics.len() != 1 {
                    return Err(Diag::new("L0110", span, "Option takes one type argument", "Write `Option<T>`."));
                }
                let e = resolve_ty(ast, interner, known, type_names, tys, seg.generics[0], self_ty)?;
                return Ok(tys.intern(TyKind::Option(e)));
            }
            if let Some(&adt) = type_names.get(&name) {
                return no_generics(tys.intern(TyKind::Adt(adt)));
            }
            let n = interner.get(name);
            if ["HashMap", "HashSet", "BTreeMap", "Result", "Box", "Rc", "Arc", "RefCell", "Cell", "f32", "f64", "i128", "u128"]
                .contains(&n)
            {
                return Err(unsupported(span, &format!("`{n}`")));
            }
            Err(Diag::new("L0102", span, format!("unknown type `{n}`"), "Check the spelling, or define the type."))
        }
    }
}

/// Builds the program tables. Returns all collection errors.
pub fn collect<'a>(ast: &'a Ast, interner: &'a Interner, known: &'a Known) -> Result<Program<'a>, Vec<Diag>> {
    let mut p = Program {
        ast,
        interner,
        known,
        tys: GlobalTys::new(),
        adts: Vec::new(),
        fns: Vec::new(),
        type_names: HashMap::default(),
        fn_names: HashMap::default(),
        methods: HashMap::default(),
        main: None,
    };
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
        p.adts.push(AdtDef { name, is_enum, variants: Vec::new(), derives: Derives::default(), span });
        p.tys.intern(TyKind::Adt(id));
    }

    // Pass 2: fields, variants, derives.
    let mut adt_index = 0;
    for item in &ast.items {
        type FieldSrc = (Sym, ast::TyId, Span);
        type VariantSrc = (Sym, Span, VariantShape, Vec<FieldSrc>);
        let (variants_src, derives_src): (Vec<VariantSrc>, &Vec<(Sym, Span)>) = match &item.kind {
            ItemKind::Struct(s) => {
                let fields = s.fields.iter().map(|f| (f.name, f.ty, f.span)).collect();
                (vec![(s.name, s.name_span, VariantShape::Named, fields)], &s.derives)
            }
            ItemKind::Enum(e) => {
                let vs = e
                    .variants
                    .iter()
                    .map(|v| {
                        let (shape, fs): (VariantShape, Vec<FieldSrc>) = match &v.fields {
                            VariantFields::Unit => (VariantShape::Unit, Vec::new()),
                            VariantFields::Tuple(ts) => {
                                (VariantShape::Tuple, ts.iter().enumerate().map(|(i, &t)| (Sym(i as u32), t, ast.ty_span(t))).collect())
                            }
                            VariantFields::Struct(fs) => (VariantShape::Named, fs.iter().map(|f| (f.name, f.ty, f.span)).collect()),
                        };
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

    // Functions and methods.
    let add_fn = |p: &mut Program<'a>, def: &'a ast::FnDef, owner: Option<AdtId>, errs: &mut Vec<Diag>| -> FnId {
        let self_ty = owner.map(|a| p.tys.intern(TyKind::Adt(a)));
        let mut params = Vec::new();
        if let (Some(sp), Some(st)) = (&def.self_param, self_ty) {
            params.push(match sp.kind {
                SelfKind::Value => st,
                SelfKind::Ref => p.tys.intern(TyKind::Ref(false, st)),
                SelfKind::RefMut => p.tys.intern(TyKind::Ref(true, st)),
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
        let id = FnId(p.fns.len() as u32);
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
    for item in &ast.items {
        match &item.kind {
            ItemKind::Fn(def) => {
                let id = add_fn(&mut p, def, None, &mut errs);
                if p.fn_names.insert(def.name, id).is_some() {
                    errs.push(dup(def.name_span, interner.get(def.name)));
                }
                if def.name == known.main {
                    p.main = Some(id);
                }
            }
            ItemKind::Impl(imp) => {
                let owner = match ast.ty(imp.self_ty) {
                    TyExpr::Path(segs) if segs.len() == 1 && segs[0].generics.is_empty() => p.type_names.get(&segs[0].name).copied(),
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
                for def in &imp.fns {
                    let id = add_fn(&mut p, def, Some(owner), &mut errs);
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
        TyKind::Vec(e) | TyKind::Option(e) => contains_ref(tys, e),
        TyKind::Chars => true,
        _ => false,
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
            while let TyKind::Option(inner) = p.tys.kind(t) {
                t = inner;
            }
            if let TyKind::Adt(a) = p.tys.kind(t)
                && (a == root || contains_adt_by_value(p, root, a, seen))
            {
                return true;
            }
        }
    }
    false
}

// Trait queries. Lust has no user traits yet, so these follow fixed rules plus derives.

pub fn is_copy(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::Never | TyKind::Error | TyKind::Var(_, true) => true,
        TyKind::Ref(m, _) => !m,
        TyKind::Option(e) => is_copy(p, tys, e),
        TyKind::Adt(a) => p.adt(a).derives.copy,
        _ => false,
    }
}

pub fn has_clone(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::String => true,
        TyKind::Vec(e) | TyKind::Option(e) => has_clone(p, tys, e),
        TyKind::Adt(a) => p.adt(a).derives.clone,
        _ => is_copy(p, tys, t),
    }
}

pub fn has_eq(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::String | TyKind::Str | TyKind::Error => true,
        TyKind::Var(_, true) => true,
        TyKind::Ref(_, e) | TyKind::Vec(e) | TyKind::Option(e) => has_eq(p, tys, e),
        TyKind::Adt(a) => p.adt(a).derives.partial_eq,
        _ => false,
    }
}

pub fn has_debug(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::Unit | TyKind::String | TyKind::Str | TyKind::Error => true,
        TyKind::Var(_, true) => true,
        TyKind::Ref(_, e) | TyKind::Vec(e) | TyKind::Option(e) => has_debug(p, tys, e),
        TyKind::Adt(a) => p.adt(a).derives.debug,
        TyKind::Args => true,
        _ => false,
    }
}

pub fn has_display(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Int(_) | TyKind::Bool | TyKind::Char | TyKind::String | TyKind::Str | TyKind::Error => true,
        TyKind::Var(_, true) => true,
        TyKind::Ref(_, e) => has_display(tys, e),
        _ => false,
    }
}

/// True if values of this type own heap memory and need a drop call.
pub fn needs_drop(p: &Program, tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::String | TyKind::Vec(_) => true,
        TyKind::Option(e) => needs_drop(p, tys, e),
        TyKind::Adt(a) => p.adt(a).variants.iter().any(|v| v.fields.iter().any(|f| needs_drop(p, &p.tys, f.ty))),
        _ => false,
    }
}
