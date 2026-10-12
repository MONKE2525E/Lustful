// Generic collection (docs/ARCH.md sections 2.1 to 2.3, W-TRAITS-CORE):
// lang trait defs, scoped type resolution over generic parameters,
// bounds to predicates, param environments, and the templates mono
// materializes instances from.
//
// A *template* is a generic Adt, fn, or trait method in signature
// form: types may contain `Param` and `Projection`, never `Infer`.
// Non-generic items are templates with no parameters, and their one
// instance is themselves, so the old concrete pipeline is the
// degenerate case of this one. Check, lower, and codegen only ever
// see concrete instances (mono materializes them into the compat
// `AdtDef`/`FnInfo` tables), plus one abstract instance per
// template that checking uses and codegen never sees.
use crate::ast::{self, Ast, GenericArg as AstArg, GenericArgs, TraitBound, TyExpr};
use crate::check::collect::Program;
use crate::def::{DefId, LocalDefId};
use crate::diag::{Diag, Span, not_yet};
use crate::intern::{FxMap, Interner, Known, Sym};
use crate::traits::index::{ImplIndex, TraitRecord};
use crate::ty::*;

/// The defs of the lang traits lust knows without source std: the
/// derive and marker traits, the operator traits, and the iterator
/// family the trait corpus and the MGP use by name. Their records
/// live in the impl index like user traits; their impls for builtin
/// types are synthetic index entries (see `synthetic_lang_impls` in
/// collect), and user impls of them are ordinary impls. Source std
/// (wave A2) replaces these defs with real ones under the same
/// names.
#[derive(Clone, Copy, Debug)]
pub struct LangTraits {
    pub sized: DefId,
    pub copy: DefId,
    pub clone: DefId,
    pub debug: DefId,
    pub display: DefId,
    pub partial_eq: DefId,
    pub eq: DefId,
    pub partial_ord: DefId,
    pub ord: DefId,
    pub hash: DefId,
    pub default: DefId,
    pub drop: DefId,
    pub send: DefId,
    pub sync: DefId,
    pub unpin: DefId,
    pub add: DefId,
    pub sub: DefId,
    pub mul: DefId,
    pub div: DefId,
    pub rem: DefId,
    pub neg: DefId,
    pub not: DefId,
    pub bit_and: DefId,
    pub bit_or: DefId,
    pub bit_xor: DefId,
    pub shl: DefId,
    pub shr: DefId,
    pub add_assign: DefId,
    pub sub_assign: DefId,
    pub mul_assign: DefId,
    pub div_assign: DefId,
    pub rem_assign: DefId,
    pub bit_and_assign: DefId,
    pub bit_or_assign: DefId,
    pub bit_xor_assign: DefId,
    pub shl_assign: DefId,
    pub shr_assign: DefId,
    pub index: DefId,
    pub index_mut: DefId,
    pub deref: DefId,
    pub deref_mut: DefId,
    pub iterator: DefId,
    pub into_iterator: DefId,
    pub from_iterator: DefId,
    pub from: DefId,
    pub into: DefId,
    pub fn_: DefId,
    pub fn_mut: DefId,
    pub fn_once: DefId,
    pub exact_size_iterator: DefId,
    /// `Iterator::Item`.
    pub assoc_item: DefId,
    /// `IntoIterator::IntoIter` (its `Item` is a distinct def).
    pub assoc_into_iter: DefId,
    pub assoc_into_item: DefId,
    /// `ops::*::Output`, one def per operator trait is not needed:
    /// projections key on the assoc def, so each operator trait
    /// gets its own entry in `outputs` below instead.
    pub outputs: [(DefId, DefId); 14],
    /// `Deref::Target` and `Index::Output`-style single assocs.
    pub assoc_target: DefId,
    pub assoc_index_output: DefId,
}

/// One lang def under the builtin crate identity, hashed from its
/// std path like the builtin Adt defs in `ty`.
fn lang_def(module: &[&str], kind: crate::def::DefKind, name: &str) -> DefId {
    let hash = crate::def::stable_crate_hash("lust-builtin-v1", "lib", "builtin", false);
    DefId { krate: BUILTIN_CRATE, hash: crate::def::item_hash(hash, module, kind, name, 0) }
}

fn lang_trait(module: &[&str], name: &str) -> DefId {
    lang_def(module, crate::def::DefKind::Trait, name)
}

fn lang_assoc(trait_def: DefId, name: &str) -> DefId {
    DefId { krate: BUILTIN_CRATE, hash: crate::def::child_hash(trait_def.hash, crate::def::DefKind::Assoc, name, 0) }
}

impl LangTraits {
    /// All lang trait and assoc defs, deterministic across sessions.
    pub fn new() -> LangTraits {
        let marker = &["core", "marker"];
        let ops = &["core", "ops"];
        let sized = lang_trait(marker, "Sized");
        let copy = lang_trait(marker, "Copy");
        let send = lang_trait(marker, "Send");
        let sync = lang_trait(marker, "Sync");
        let unpin = lang_trait(marker, "Unpin");
        let clone = lang_trait(&["core", "clone"], "Clone");
        let debug = lang_trait(&["core", "fmt"], "Debug");
        let display = lang_trait(&["core", "fmt"], "Display");
        let partial_eq = lang_trait(&["core", "cmp"], "PartialEq");
        let eq = lang_trait(&["core", "cmp"], "Eq");
        let partial_ord = lang_trait(&["core", "cmp"], "PartialOrd");
        let ord = lang_trait(&["core", "cmp"], "Ord");
        let hash = lang_trait(&["core", "hash"], "Hash");
        let default = lang_trait(&["core", "default"], "Default");
        let drop = lang_trait(ops, "Drop");
        let add = lang_trait(ops, "Add");
        let sub = lang_trait(ops, "Sub");
        let mul = lang_trait(ops, "Mul");
        let div = lang_trait(ops, "Div");
        let rem = lang_trait(ops, "Rem");
        let neg = lang_trait(ops, "Neg");
        let not = lang_trait(ops, "Not");
        let bit_and = lang_trait(ops, "BitAnd");
        let bit_or = lang_trait(ops, "BitOr");
        let bit_xor = lang_trait(ops, "BitXor");
        let shl = lang_trait(ops, "Shl");
        let shr = lang_trait(ops, "Shr");
        let add_assign = lang_trait(ops, "AddAssign");
        let sub_assign = lang_trait(ops, "SubAssign");
        let mul_assign = lang_trait(ops, "MulAssign");
        let div_assign = lang_trait(ops, "DivAssign");
        let rem_assign = lang_trait(ops, "RemAssign");
        let bit_and_assign = lang_trait(ops, "BitAndAssign");
        let bit_or_assign = lang_trait(ops, "BitOrAssign");
        let bit_xor_assign = lang_trait(ops, "BitXorAssign");
        let shl_assign = lang_trait(ops, "ShlAssign");
        let shr_assign = lang_trait(ops, "ShrAssign");
        let index = lang_trait(ops, "Index");
        let index_mut = lang_trait(ops, "IndexMut");
        let deref = lang_trait(ops, "Deref");
        let deref_mut = lang_trait(ops, "DerefMut");
        let fn_ = lang_trait(ops, "Fn");
        let fn_mut = lang_trait(ops, "FnMut");
        let fn_once = lang_trait(ops, "FnOnce");
        let iterator = lang_trait(&["core", "iter"], "Iterator");
        let into_iterator = lang_trait(&["core", "iter"], "IntoIterator");
        let from_iterator = lang_trait(&["core", "iter"], "FromIterator");
        let exact_size_iterator = lang_trait(&["core", "iter"], "ExactSizeIterator");
        let from = lang_trait(&["core", "convert"], "From");
        let into = lang_trait(&["core", "convert"], "Into");
        let assoc_out = |t: DefId| lang_assoc(t, "Output");
        LangTraits {
            sized,
            copy,
            clone,
            debug,
            display,
            partial_eq,
            eq,
            partial_ord,
            ord,
            hash,
            default,
            drop,
            send,
            sync,
            unpin,
            add,
            sub,
            mul,
            div,
            rem,
            neg,
            not,
            bit_and,
            bit_or,
            bit_xor,
            shl,
            shr,
            add_assign,
            sub_assign,
            mul_assign,
            div_assign,
            rem_assign,
            bit_and_assign,
            bit_or_assign,
            bit_xor_assign,
            shl_assign,
            shr_assign,
            index,
            index_mut,
            deref,
            deref_mut,
            iterator,
            into_iterator,
            from_iterator,
            from,
            into,
            fn_,
            fn_mut,
            fn_once,
            exact_size_iterator,
            assoc_item: lang_assoc(iterator, "Item"),
            assoc_into_iter: lang_assoc(into_iterator, "IntoIter"),
            assoc_into_item: lang_assoc(into_iterator, "Item"),
            outputs: [
                (add, assoc_out(add)),
                (sub, assoc_out(sub)),
                (mul, assoc_out(mul)),
                (div, assoc_out(div)),
                (rem, assoc_out(rem)),
                (neg, assoc_out(neg)),
                (not, assoc_out(not)),
                (bit_and, assoc_out(bit_and)),
                (bit_or, assoc_out(bit_or)),
                (bit_xor, assoc_out(bit_xor)),
                (shl, assoc_out(shl)),
                (shr, assoc_out(shr)),
                (fn_, assoc_out(fn_)),
                (fn_mut, assoc_out(fn_mut)),
            ],
            assoc_target: lang_assoc(deref, "Target"),
            assoc_index_output: lang_assoc(index, "Output"),
        }
    }

    /// The `Output` assoc def of an operator or `Fn` trait.
    pub fn output_of(&self, trait_def: DefId) -> Option<DefId> {
        if trait_def == self.fn_once {
            // FnOnce::Output is its own assoc in std; Fn and FnMut
            // inherit it. One shared def is enough here because
            // projections still differ by their trait args.
            return Some(self.outputs[12].1);
        }
        self.outputs.iter().find(|(t, _)| *t == trait_def).map(|(_, a)| *a)
    }

    /// A lang trait by its Rust name, for bound resolution.
    pub fn by_name(&self, name: &str) -> Option<DefId> {
        Some(match name {
            "Sized" => self.sized,
            "Copy" => self.copy,
            "Clone" => self.clone,
            "Debug" => self.debug,
            "Display" => self.display,
            "PartialEq" => self.partial_eq,
            "Eq" => self.eq,
            "PartialOrd" => self.partial_ord,
            "Ord" => self.ord,
            "Hash" => self.hash,
            "Default" => self.default,
            "Drop" => self.drop,
            "Send" => self.send,
            "Sync" => self.sync,
            "Unpin" => self.unpin,
            "Add" => self.add,
            "Sub" => self.sub,
            "Mul" => self.mul,
            "Div" => self.div,
            "Rem" => self.rem,
            "Neg" => self.neg,
            "Not" => self.not,
            "BitAnd" => self.bit_and,
            "BitOr" => self.bit_or,
            "BitXor" => self.bit_xor,
            "Shl" => self.shl,
            "Shr" => self.shr,
            "AddAssign" => self.add_assign,
            "SubAssign" => self.sub_assign,
            "MulAssign" => self.mul_assign,
            "DivAssign" => self.div_assign,
            "RemAssign" => self.rem_assign,
            "BitAndAssign" => self.bit_and_assign,
            "BitOrAssign" => self.bit_or_assign,
            "BitXorAssign" => self.bit_xor_assign,
            "ShlAssign" => self.shl_assign,
            "ShrAssign" => self.shr_assign,
            "Index" => self.index,
            "IndexMut" => self.index_mut,
            "Deref" => self.deref,
            "DerefMut" => self.deref_mut,
            "Iterator" => self.iterator,
            "IntoIterator" => self.into_iterator,
            "FromIterator" => self.from_iterator,
            "ExactSizeIterator" => self.exact_size_iterator,
            "From" => self.from,
            "Into" => self.into,
            "Fn" => self.fn_,
            "FnMut" => self.fn_mut,
            "FnOnce" => self.fn_once,
            _ => return None,
        })
    }

    /// True for the auto traits, which selection answers
    /// structurally, never through the impl index (section 2.7).
    pub fn is_auto(&self, def: DefId) -> bool {
        def == self.send || def == self.sync || def == self.unpin
    }
}

/// Builds the index records of the lang traits. A record's
/// generics start with `Self` (the module convention in
/// `traits/mod.rs`); supertrait predicates name that Self.
/// Method defs are synthetic: user impl methods are matched to
/// trait methods by name, so these defs only carry identity for
/// normalization and diagnostics.
pub fn lang_trait_records(lang: &LangTraits, interner: &Interner, tys: &mut impl TyIntern) -> Vec<TraitRecord> {
    let sym = |n: &str| interner.intern(n);
    // A supertrait predicate over this trait's own parameters:
    // `extra` lists the parameter indexes after Self (for example
    // `Eq: PartialEq<Self>` is [0], `IndexMut<I>: Index<I>` is [1]).
    let self_pred = |tys: &mut dyn TyIntern, trait_def: DefId, extra: &[u32]| -> Predicate {
        let mut all = vec![GenericArg::Ty(tys.intern(TyKind::Param(ParamId(0))))];
        for &i in extra {
            all.push(GenericArg::Ty(tys.intern(TyKind::Param(ParamId(i)))));
        }
        let args = tys.intern_args(&all);
        Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }))
    };
    let rec = |def: DefId, name: &str, n_inputs: usize, supers: Vec<Predicate>, assocs: Vec<(DefId, &str)>, methods: &[&str]| {
        let mut params: Vec<ParamDef> =
            (0..=n_inputs).map(|_| ParamDef { name: sym("T"), kind: ParamKind::Type, span: Span::default() }).collect();
        params[0].name = sym("Self");
        TraitRecord {
            def,
            name: sym(name),
            generics: Generics { parent: None, params, predicates: supers },
            assoc_items: assocs.iter().map(|&(d, n)| (d, sym(n), true)).collect(),
            methods: methods.iter().map(|&m| (lang_assoc(def, m), sym(m))).collect(),
            local: false,
            span: Span::default(),
        }
    };
    let binop = |def: DefId, name: &str, method: &str| rec(def, name, 1, vec![], vec![(lang.output_of(def).unwrap(), "Output")], &[method]);
    let unop = |def: DefId, name: &str, method: &str| rec(def, name, 0, vec![], vec![(lang.output_of(def).unwrap(), "Output")], &[method]);
    let assign = |def: DefId, name: &str, method: &str| rec(def, name, 1, vec![], vec![], &[method]);
    vec![
        rec(lang.sized, "Sized", 0, vec![], vec![], &[]),
        rec(lang.copy, "Copy", 0, vec![self_pred(tys, lang.clone, &[])], vec![], &[]),
        rec(lang.clone, "Clone", 0, vec![], vec![], &["clone"]),
        rec(lang.debug, "Debug", 0, vec![], vec![], &["fmt"]),
        rec(lang.display, "Display", 0, vec![], vec![], &["fmt"]),
        rec(lang.partial_eq, "PartialEq", 1, vec![], vec![], &["eq", "ne"]),
        rec(lang.eq, "Eq", 0, vec![self_pred(tys, lang.partial_eq, &[0])], vec![], &[]),
        rec(lang.partial_ord, "PartialOrd", 1, vec![self_pred(tys, lang.partial_eq, &[0])], vec![], &["partial_cmp"]),
        rec(lang.ord, "Ord", 0, vec![self_pred(tys, lang.eq, &[]), self_pred(tys, lang.partial_ord, &[0])], vec![], &["cmp"]),
        rec(lang.hash, "Hash", 0, vec![], vec![], &["hash"]),
        rec(lang.default, "Default", 0, vec![], vec![], &["default"]),
        rec(lang.drop, "Drop", 0, vec![], vec![], &["drop"]),
        rec(lang.send, "Send", 0, vec![], vec![], &[]),
        rec(lang.sync, "Sync", 0, vec![], vec![], &[]),
        rec(lang.unpin, "Unpin", 0, vec![], vec![], &[]),
        binop(lang.add, "Add", "add"),
        binop(lang.sub, "Sub", "sub"),
        binop(lang.mul, "Mul", "mul"),
        binop(lang.div, "Div", "div"),
        binop(lang.rem, "Rem", "rem"),
        unop(lang.neg, "Neg", "neg"),
        unop(lang.not, "Not", "not"),
        binop(lang.bit_and, "BitAnd", "bitand"),
        binop(lang.bit_or, "BitOr", "bitor"),
        binop(lang.bit_xor, "BitXor", "bitxor"),
        binop(lang.shl, "Shl", "shl"),
        binop(lang.shr, "Shr", "shr"),
        assign(lang.add_assign, "AddAssign", "add_assign"),
        assign(lang.sub_assign, "SubAssign", "sub_assign"),
        assign(lang.mul_assign, "MulAssign", "mul_assign"),
        assign(lang.div_assign, "DivAssign", "div_assign"),
        assign(lang.rem_assign, "RemAssign", "rem_assign"),
        assign(lang.bit_and_assign, "BitAndAssign", "bitand_assign"),
        assign(lang.bit_or_assign, "BitOrAssign", "bitor_assign"),
        assign(lang.bit_xor_assign, "BitXorAssign", "bitxor_assign"),
        assign(lang.shl_assign, "ShlAssign", "shl_assign"),
        assign(lang.shr_assign, "ShrAssign", "shr_assign"),
        rec(lang.index, "Index", 1, vec![], vec![(lang.assoc_index_output, "Output")], &["index"]),
        rec(lang.index_mut, "IndexMut", 1, vec![self_pred(tys, lang.index, &[1])], vec![], &["index_mut"]),
        rec(lang.deref, "Deref", 0, vec![], vec![(lang.assoc_target, "Target")], &["deref"]),
        rec(lang.deref_mut, "DerefMut", 0, vec![self_pred(tys, lang.deref, &[])], vec![], &["deref_mut"]),
        rec(lang.iterator, "Iterator", 0, vec![], vec![(lang.assoc_item, "Item")], &["next"]),
        rec(
            lang.into_iterator,
            "IntoIterator",
            0,
            vec![],
            vec![(lang.assoc_into_item, "Item"), (lang.assoc_into_iter, "IntoIter")],
            &["into_iter"],
        ),
        rec(lang.from_iterator, "FromIterator", 1, vec![], vec![], &["from_iter"]),
        rec(lang.exact_size_iterator, "ExactSizeIterator", 0, vec![self_pred(tys, lang.iterator, &[])], vec![], &["len"]),
        rec(lang.from, "From", 1, vec![], vec![], &["from"]),
        rec(lang.into, "Into", 1, vec![], vec![], &["into"]),
        rec(lang.fn_, "Fn", 1, vec![self_pred(tys, lang.fn_mut, &[1])], vec![(lang.output_of(lang.fn_).unwrap(), "Output")], &["call"]),
        rec(
            lang.fn_mut,
            "FnMut",
            1,
            vec![self_pred(tys, lang.fn_once, &[1])],
            vec![(lang.output_of(lang.fn_mut).unwrap(), "Output")],
            &["call_mut"],
        ),
        rec(lang.fn_once, "FnOnce", 1, vec![], vec![(lang.output_of(lang.fn_once).unwrap(), "Output")], &["call_once"]),
    ]
}

/// One type that associated types can be projected from in a
/// signature: a Self type pattern, the trait, its full args
/// (Self first), and that trait's assoc items by name. Used to
/// resolve `Self::Assoc` and `T::Assoc` while signatures form.
#[derive(Clone, Debug)]
pub struct AssocSrc {
    pub self_ty: Ty,
    pub trait_def: DefId,
    pub args: ArgsId,
    pub assocs: Vec<(Sym, DefId)>,
}

/// The naming scope one signature resolves types under: generic
/// parameters by name, the `Self` type, and the associated-type
/// sources of `Self` and the parameters' bounds.
#[derive(Clone, Debug, Default)]
pub struct Scope {
    /// Type parameter name to index in the item's `Generics`.
    pub type_params: Vec<(Sym, u32)>,
    /// Const parameter name to index in the item's `Generics`.
    pub const_params: Vec<(Sym, u32)>,
    pub self_ty: Option<Ty>,
    pub assoc_srcs: Vec<AssocSrc>,
}

impl Scope {
    /// The scope of today's non-generic signatures.
    pub fn plain(self_ty: Option<Ty>) -> Scope {
        Scope { type_params: Vec::new(), const_params: Vec::new(), self_ty, assoc_srcs: Vec::new() }
    }
    /// The parameter index of a type parameter name.
    pub fn param_of(&self, name: Sym) -> Option<u32> {
        self.type_params.iter().find(|(n, _)| *n == name).map(|(_, i)| *i)
    }
}

/// What scoped resolution needs from the program being built.
pub struct ResolveCx<'x> {
    /// User Adt name to its session-local (template) index.
    pub type_names: &'x FxMap<Sym, AdtId>,
    /// User Adt template def and declared type/const parameter
    /// count, by session-local index.
    pub adt_info: &'x [(DefId, usize)],
    /// User trait name to its def. Lang traits answer after it.
    pub trait_names: &'x FxMap<Sym, DefId>,
    /// Non-generic type aliases by name (collect pass 1.5).
    pub aliases: &'x FxMap<Sym, Ty>,
    pub index: &'x ImplIndex,
    pub lang: &'x LangTraits,
}

impl ResolveCx<'_> {
    /// A trait def by its written name: user traits, then lang.
    pub fn trait_by_name(&self, interner: &Interner, name: Sym) -> Option<DefId> {
        self.trait_names.get(&name).copied().or_else(|| self.lang.by_name(interner.get(name)))
    }
    /// The template def and parameter count of one user Adt.
    pub fn adt_info_of(&self, adt: AdtId) -> (DefId, usize) {
        self.adt_info[adt.0 as usize]
    }
}

/// The lifetime-names reject (same code and text as the parser's).
pub fn lifetime_diag(span: Span) -> Diag {
    Diag::new(
        "L0203",
        span,
        "lifetime names are not supported",
        "Remove the lifetime. Lust uses Rust's elision rules only. If elision is ambiguous, return an owned value or an index.",
    )
}

/// Checks one written lifetime name: this milestone erases
/// regions, so `'static` and `'_` are accepted and every other
/// name is the subset's lifetime reject. Returns the region to
/// record (always erased).
fn check_lifetime(interner: &Interner, lt: ast::Lifetime) -> Result<Region, Diag> {
    match interner.get(lt.name) {
        "static" | "_" => Ok(Region::Erased),
        _ => Err(lifetime_diag(lt.span)),
    }
}

/// Resolves one generic argument list against a declared parameter
/// list. Written arguments follow declared order (lifetime
/// parameters do not exist in this subset's generics, so written
/// lifetimes only appear on types whose parameters are all
/// erased, like `Formatter<'_>`, where they are checked and
/// dropped). Missing trailing arguments are an error: parameter
/// defaults are not supported yet.
fn resolve_generic_args(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    args: &[AstArg],
    n_params: usize,
    span: Span,
    what: &str,
) -> Result<Vec<GenericArg>, Diag> {
    let mut out: Vec<GenericArg> = Vec::new();
    for a in args {
        match a {
            AstArg::Type(t) => out.push(GenericArg::Ty(resolve_scoped(ast, interner, known, cx, tys, *t, scope)?)),
            AstArg::Lifetime(lt) => {
                check_lifetime(interner, *lt)?;
                out.push(GenericArg::Lifetime(Region::Erased));
            }
            AstArg::Const(e) => out.push(GenericArg::Const(resolve_const_arg(ast, tys, scope, *e, span)?)),
            AstArg::Binding { span, .. } => {
                return Err(Diag::new(
                    "L0110",
                    *span,
                    format!("associated bindings are not allowed on `{what}`"),
                    "Write the binding on a trait bound instead.",
                ));
            }
        }
    }
    // Erased lifetime arguments do not count against the declared
    // type/const parameters (declared lifetimes are rejected when
    // the item's generics are built).
    let n_value_args = out.iter().filter(|g| !matches!(g, GenericArg::Lifetime(_))).count();
    if n_value_args != n_params {
        return Err(Diag::new(
            "L0110",
            span,
            format!("`{what}` takes {n_params} generic argument(s), but {n_value_args} were given"),
            "Match the number of parameters in the definition.",
        ));
    }
    Ok(out)
}

/// A const generic argument or array length in signature form:
/// a literal value, or a const parameter reference.
fn resolve_const_arg(ast: &Ast, tys: &mut impl TyIntern, scope: &Scope, e: ast::ExprId, span: Span) -> Result<ConstId, Diag> {
    match ast.expr(e) {
        ast::Expr::Path(segs) if segs.len() == 1 => {
            if let Some(&(_, i)) = scope.const_params.iter().find(|(n, _)| *n == segs[0].name) {
                return Ok(tys.intern_const(ConstKind::Param(i)));
            }
            Err(Diag::new("L0110", span, "const argument must be a literal or a const parameter", "Use a literal such as `3`."))
        }
        ast::Expr::Bool(b) => Ok(tys.intern_const(ConstKind::Bool(*b))),
        ast::Expr::Char(c) => Ok(tys.intern_const(ConstKind::Char(*c))),
        _ => match crate::check::collect::eval_array_len(ast, e) {
            Some(v) => Ok(tys.intern_const(ConstKind::Int(v))),
            None => Err(Diag::new("L0110", span, "const argument must be a constant integer", "Write a literal such as `3`.")),
        },
    }
}

/// The trait a written trait path names, by its last segment:
/// user traits first, then lang traits. `std::` and `core::`
/// prefixes are accepted and ignored, as type paths do today.
fn trait_def_of_path(cx: &ResolveCx, interner: &Interner, known: &Known, segs: &[ast::PathSeg], span: Span) -> Result<DefId, Diag> {
    let last = segs.last().ok_or_else(|| Diag::new("L0102", span, "expected a trait name", "Write a trait name."))?;
    if segs.len() > 1 && segs[0].name != known.std && interner.get(segs[0].name) != "core" && interner.get(segs[0].name) != "alloc" {
        return Err(not_yet("L0505", span, "module paths in trait references"));
    }
    cx.trait_by_name(interner, last.name).ok_or_else(|| {
        Diag::new("L0102", span, format!("unknown trait `{}`", interner.get(last.name)), "Check the spelling, or define the trait.")
    })
}

/// The bindings of one trait path's last segment, resolved to
/// assoc defs of the trait. Plain type arguments are returned too,
/// in written order after Self.
fn resolve_trait_path_args(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    trait_def: DefId,
    seg: &ast::PathSeg,
    self_ty: Ty,
    span: Span,
) -> Result<TraitRef, Diag> {
    let rec = cx.index.trait_record(trait_def);
    let n_inputs = rec.map_or(0, |r| r.generics.params.len().saturating_sub(1));
    let (input_args, bindings): (Vec<GenericArg>, Vec<(DefId, GenericArg)>) = match &seg.args {
        GenericArgs::None => (Vec::new(), Vec::new()),
        GenericArgs::Parenthesized { inputs, output } => {
            // Fn sugar: one tuple input argument, Output binding.
            let mut parts = Vec::new();
            for t in inputs {
                parts.push(resolve_scoped(ast, interner, known, cx, tys, *t, scope)?);
            }
            let tuple = if parts.len() == 1 {
                let ts = tys.intern_tys(&parts);
                tys.intern(TyKind::Tuple(ts))
            } else {
                let ts = tys.intern_tys(&parts);
                tys.intern(TyKind::Tuple(ts))
            };
            let mut bindings = Vec::new();
            if let Some(out) = output {
                let assoc = cx
                    .lang
                    .output_of(trait_def)
                    .ok_or_else(|| Diag::new("L0110", span, "parenthesized trait sugar is only for Fn traits", "Use angle arguments."))?;
                bindings.push((assoc, GenericArg::Ty(resolve_scoped(ast, interner, known, cx, tys, *out, scope)?)));
            }
            (vec![GenericArg::Ty(tuple)], bindings)
        }
        GenericArgs::Angle(args) => {
            let mut inputs: Vec<GenericArg> = Vec::new();
            let mut bindings: Vec<(DefId, GenericArg)> = Vec::new();
            for a in args {
                match a {
                    AstArg::Type(t) => inputs.push(GenericArg::Ty(resolve_scoped(ast, interner, known, cx, tys, *t, scope)?)),
                    AstArg::Lifetime(lt) => {
                        check_lifetime(interner, *lt)?;
                    }
                    AstArg::Const(e) => inputs.push(GenericArg::Const(resolve_const_arg(ast, tys, scope, *e, span)?)),
                    AstArg::Binding { name, span: bspan, kind } => {
                        let assoc = rec.and_then(|r| r.assoc_by_name(*name)).ok_or_else(|| {
                            Diag::new(
                                "L0102",
                                *bspan,
                                format!("trait has no associated item named `{}`", interner.get(*name)),
                                "Check the spelling against the trait definition.",
                            )
                        })?;
                        let bound = match kind {
                            ast::BindingKind::EqTy(t) => GenericArg::Ty(resolve_scoped(ast, interner, known, cx, tys, *t, scope)?),
                            ast::BindingKind::EqConst(e) => GenericArg::Const(resolve_const_arg(ast, tys, scope, *e, *bspan)?),
                            ast::BindingKind::Constraint(_) => {
                                return Err(not_yet("L0621", *bspan, "associated binding constraints in this position"));
                            }
                        };
                        bindings.push((assoc, bound));
                    }
                }
            }
            (inputs, bindings)
        }
    };
    if input_args.len() != n_inputs {
        return Err(Diag::new(
            "L0110",
            span,
            format!("trait takes {n_inputs} input argument(s), but {} were given", input_args.len()),
            "Match the trait definition's parameters.",
        ));
    }
    let mut all = vec![GenericArg::Ty(self_ty)];
    all.extend(input_args);
    let args = tys.intern_args(&all);
    let bindings = tys.intern_bindings(&bindings);
    Ok(TraitRef { def: trait_def, args, bindings })
}

/// Resolves a written trait reference (a bound or an impl header)
/// for one Self type.
pub fn resolve_trait_ref(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    self_ty: Ty,
    tref: &ast::TraitRefExpr,
    span: Span,
) -> Result<TraitRef, Diag> {
    let trait_def = trait_def_of_path(cx, interner, known, &tref.path, span)?;
    let seg = tref.path.last().unwrap();
    resolve_trait_path_args(ast, interner, known, cx, tys, scope, trait_def, seg, self_ty, span)
}

/// Scoped type resolution: `resolve_ty` plus generic parameters,
/// generic Adt applications, projections, and qualified paths.
/// Everything `resolve_ty` accepts resolves the same way here
/// under an empty scope.
pub fn resolve_scoped(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    id: ast::TyId,
    scope: &Scope,
) -> Result<Ty, Diag> {
    let span = ast.ty_span(id);
    match ast.ty(id) {
        TyExpr::Unit => Ok(UNIT),
        TyExpr::Never => Ok(NEVER),
        TyExpr::Ref { lifetime, mutable, inner } => {
            if let Some(lt) = lifetime {
                check_lifetime(interner, *lt)?;
            }
            let inner = resolve_scoped(ast, interner, known, cx, tys, *inner, scope)?;
            Ok(tys.mk_ref(*mutable, inner))
        }
        TyExpr::Tuple(elems) => {
            let mut out = Vec::with_capacity(elems.len());
            for &e in elems {
                out.push(resolve_scoped(ast, interner, known, cx, tys, e, scope)?);
            }
            let ts = tys.intern_tys(&out);
            Ok(tys.intern(TyKind::Tuple(ts)))
        }
        TyExpr::Paren(inner) => resolve_scoped(ast, interner, known, cx, tys, *inner, scope),
        TyExpr::Slice(inner) => {
            let e = resolve_scoped(ast, interner, known, cx, tys, *inner, scope)?;
            Ok(tys.intern(TyKind::Slice(e)))
        }
        TyExpr::Array { inner, len } => {
            let e = resolve_scoped(ast, interner, known, cx, tys, *inner, scope)?;
            let n = resolve_const_arg(ast, tys, scope, *len, span)?;
            Ok(tys.intern(TyKind::Array(e, n)))
        }
        TyExpr::Ptr { mutable, inner } => {
            let e = resolve_scoped(ast, interner, known, cx, tys, *inner, scope)?;
            Ok(tys.intern(TyKind::RawPtr(Mut::from_bool(*mutable), e)))
        }
        TyExpr::Infer => Err(not_yet("L0602", span, "inferred types (`_`) in signatures")),
        TyExpr::ImplTrait { .. } => Err(not_yet("L0602", span, "`impl Trait` types in this position")),
        TyExpr::Dyn { bounds, .. } => resolve_dyn(ast, interner, known, cx, tys, scope, bounds, span),
        TyExpr::QPath { self_ty, trait_path, segs } => {
            let base = resolve_scoped(ast, interner, known, cx, tys, *self_ty, scope)?;
            if trait_path.is_empty() {
                return assoc_projection(cx, tys, scope, base, segs, span, interner);
            }
            let trait_def = trait_def_of_path(cx, interner, known, trait_path, span)?;
            let seg = trait_path.last().unwrap();
            let tr = resolve_trait_path_args(ast, interner, known, cx, tys, scope, trait_def, seg, base, span)?;
            projection_of(cx, tys, tr, segs, span, interner)
        }
        TyExpr::Path(segs) => resolve_path_ty(ast, interner, known, cx, tys, scope, segs, span),
        _ => Err(not_yet("L0602", span, "this type form")),
    }
}

/// `<T>::Assoc` and `T::Assoc`: the trait comes from the scope's
/// associated sources for that Self type. Exactly one source may
/// name the assoc item, as in Rust without disambiguation.
fn assoc_projection(
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    base: Ty,
    segs: &[ast::PathSeg],
    span: Span,
    interner: &Interner,
) -> Result<Ty, Diag> {
    if segs.len() != 1 {
        return Err(not_yet("L0505", span, "module paths in types"));
    }
    let name = segs[0].name;
    let mut hits: Vec<&AssocSrc> = Vec::new();
    for src in &scope.assoc_srcs {
        if src.self_ty == base && src.assocs.iter().any(|(n, _)| *n == name) {
            hits.push(src);
        }
    }
    match hits.len() {
        1 => {
            let src = hits[0];
            let tr = TraitRef { def: src.trait_def, args: src.args, bindings: EMPTY_BINDINGS };
            projection_of(cx, tys, tr, segs, span, interner)
        }
        0 => Err(Diag::new(
            "L0102",
            span,
            format!("no associated item named `{}` is in scope for this type", interner.get(name)),
            "Name the trait: write `<Type as Trait>::Item`, or add the bound.",
        )),
        _ => Err(Diag::new(
            "L0110",
            span,
            format!("`{}` is ambiguous: more than one bound names it", interner.get(name)),
            "Name the trait: write `<Type as Trait>::Item`.",
        )),
    }
}

/// The projection type for the assoc item `segs[0]` of one trait ref.
fn projection_of(
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    tr: TraitRef,
    segs: &[ast::PathSeg],
    span: Span,
    interner: &Interner,
) -> Result<Ty, Diag> {
    if segs.len() != 1 || segs[0].has_args() {
        return Err(not_yet("L0621", span, "qualified paths with more than one segment"));
    }
    let assoc = cx.index.trait_record(tr.def).and_then(|r| r.assoc_by_name(segs[0].name)).ok_or_else(|| {
        Diag::new(
            "L0102",
            span,
            format!("trait has no associated item named `{}`", interner.get(segs[0].name)),
            "Check the spelling against the trait definition.",
        )
    })?;
    Ok(tys.intern(TyKind::Projection(AssocId(assoc), tr.args)))
}

/// A `dyn` type in signature form. The principal trait ref keeps
/// its bindings; supertraits come from the index; auto bounds
/// become the bound bits. Dyn compatibility errors are collect's
/// (they need the trait's methods); this only forms the type.
fn resolve_dyn(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    bounds: &[TraitBound],
    span: Span,
) -> Result<Ty, Diag> {
    let mut principal: Option<Binder<TraitRef>> = None;
    let mut auto = AutoTraits::default();
    for b in bounds {
        match b {
            TraitBound::Lifetime(lt) => {
                check_lifetime(interner, *lt)?;
            }
            TraitBound::Trait { binder, trait_ref, maybe } => {
                if *maybe {
                    return Err(not_yet("L0602", span, "`?Trait` bounds on dyn types"));
                }
                let trait_def = trait_def_of_path(cx, interner, known, &trait_ref.path, span)?;
                if cx.lang.is_auto(trait_def) {
                    if trait_def == cx.lang.send {
                        auto.send = true;
                    } else if trait_def == cx.lang.sync {
                        auto.sync = true;
                    } else {
                        auto.unpin = true;
                    }
                    continue;
                }
                if principal.is_some() {
                    return Err(Diag::new("L0110", span, "a dyn type has at most one principal trait", "Keep one trait plus auto traits."));
                }
                // The Self of a dyn principal is the dyn type itself;
                // in signature form it is written with the trait's
                // own Self parameter. Bindings carry the meaning.
                let self_param = tys.intern(TyKind::Param(ParamId(0)));
                let seg = trait_ref.path.last().unwrap();
                let tr = resolve_trait_path_args(ast, interner, known, cx, tys, scope, trait_def, seg, self_param, span)?;
                principal = Some(Binder { count: binder.len() as u32, value: tr });
            }
        }
    }
    let supertraits: Vec<Binder<TraitRef>> = match &principal {
        Some(p) => cx
            .index
            .supertraits_of(tys, &p.value)
            .into_iter()
            .filter_map(|pred| match pred {
                Predicate::Trait(b) => Some(b),
                _ => None,
            })
            .collect(),
        None => Vec::new(),
    };
    // Auto traits a supertrait requires join the bits: a lang
    // supertrait chain into Send/Sync is visible in the records.
    let bounds_id = tys.intern_dyn_bounds(DynBounds { principal, supertraits: supertraits.into(), auto });
    Ok(tys.intern(TyKind::Dyn(bounds_id, Region::Erased)))
}

/// A path type: parameters, primitives, builtin Adts, user Adts
/// with generic arguments, and `Self`/parameter projections.
fn resolve_path_ty(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    segs: &[ast::PathSeg],
    span: Span,
) -> Result<Ty, Diag> {
    if segs.len() > 1 {
        // `Self::Assoc` and `Param::Assoc` projections.
        if segs[0].name == known.self_type
            && let Some(base) = scope.self_ty
        {
            return assoc_projection(cx, tys, scope, base, &segs[1..], span, interner);
        }
        if let Some(i) = scope.param_of(segs[0].name) {
            let base = tys.intern(TyKind::Param(ParamId(i)));
            return assoc_projection(cx, tys, scope, base, &segs[1..], span, interner);
        }
        if segs[0].name == known.std || interner.get(segs[0].name) == "core" || interner.get(segs[0].name) == "alloc" {
            // Fall through with the last segment, as resolve_ty does.
        } else {
            return Err(not_yet("L0505", span, "module paths in types"));
        }
    }
    let seg = segs.last().unwrap();
    let name = seg.name;
    if segs.len() == 1 {
        if let Some(i) = scope.param_of(name) {
            if seg.has_args() {
                return Err(Diag::new("L0110", span, "a type parameter takes no generic arguments", "Remove the `<...>` part."));
            }
            return Ok(tys.intern(TyKind::Param(ParamId(i))));
        }
        if name == known.self_type {
            if seg.has_args() {
                return Err(Diag::new("L0110", span, "`Self` takes no generic arguments", "Remove the `<...>` part."));
            }
            return scope
                .self_ty
                .ok_or_else(|| Diag::new("L0102", span, "`Self` is only valid inside an impl or trait", "Write the type name."));
        }
    }
    let no_generics = |t: Ty| -> Result<Ty, Diag> {
        if !seg.has_args() {
            Ok(t)
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
    if name == known.Vec || name == known.Option {
        let args = match &seg.args {
            GenericArgs::Angle(a) => resolve_generic_args(ast, interner, known, cx, tys, scope, a, 1, span, interner.get(name))?,
            _ => {
                return Err(Diag::new(
                    "L0110",
                    span,
                    format!("`{}` takes one type argument", interner.get(name)),
                    "Write it with its element type.",
                ));
            }
        };
        let elem = args.iter().find_map(|g| g.as_ty()).unwrap_or(ERROR);
        return Ok(if name == known.Vec { tys.mk_vec(elem) } else { tys.mk_option(elem) });
    }
    if segs.len() == 1
        && let Some(&alias_ty) = cx.aliases.get(&name)
    {
        return if seg.has_args() {
            Err(Diag::new("L0110", span, "this alias takes no generic arguments", "Remove the `<...>` part."))
        } else {
            Ok(alias_ty)
        };
    }
    if let Some(&adt) = cx.type_names.get(&name) {
        let (def, n_params) = cx.adt_info_of(adt);
        let gargs: Vec<GenericArg> = match &seg.args {
            GenericArgs::None => {
                if n_params == 0 {
                    Vec::new()
                } else {
                    return Err(Diag::new(
                        "L0110",
                        span,
                        format!("`{}` takes {n_params} generic argument(s)", interner.get(name)),
                        "Write the arguments, for example with `_` where inference should fill them in a body.",
                    ));
                }
            }
            GenericArgs::Angle(a) => resolve_generic_args(ast, interner, known, cx, tys, scope, a, n_params, span, interner.get(name))?,
            GenericArgs::Parenthesized { .. } => {
                return Err(Diag::new("L0110", span, "parenthesized arguments are only for Fn traits", "Use angle arguments."));
            }
        };
        // Drop erased lifetime arguments before interning: declared
        // parameters count only types and consts in this subset.
        let gargs: Vec<GenericArg> = gargs.into_iter().filter(|g| !matches!(g, GenericArg::Lifetime(_))).collect();
        return Ok(tys.mk_adt(def, &gargs));
    }
    let n = interner.get(name);
    if ["HashMap", "HashSet", "BTreeMap", "Result", "Box", "Rc", "Arc", "RefCell", "Cell", "f32", "f64", "i128", "u128"].contains(&n) {
        return Err(not_yet("L0641", span, &format!("the `{n}` type")));
    }
    Err(Diag::new("L0102", span, format!("unknown type `{n}`"), "Check the spelling, or define the type."))
}

/// Converts one written bound on `lhs` into predicates. `?Sized`
/// records the parameter index in `relaxed` instead of a
/// predicate (the implicit `Sized` predicate is then withheld by
/// `build_generics`). Lifetime bounds on named lifetimes are the
/// subset's lifetime reject; `'static` bounds are erased and
/// dropped, as all regions are in this milestone.
#[allow(clippy::too_many_arguments)]
pub(crate) fn bound_predicates(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    scope: &Scope,
    lhs: Ty,
    bound: &TraitBound,
    out: &mut Vec<Predicate>,
    relaxed: &mut Vec<u32>,
    errs: &mut Vec<Diag>,
) {
    match bound {
        TraitBound::Lifetime(lt) => {
            if let Err(d) = check_lifetime(interner, *lt) {
                errs.push(d);
            }
        }
        TraitBound::Trait { binder, trait_ref, maybe } => {
            let span = trait_ref.path.last().map_or(Span::default(), |_| Span::default());
            let trait_def = match trait_def_of_path(cx, interner, known, &trait_ref.path, span) {
                Ok(d) => d,
                Err(d) => {
                    errs.push(d);
                    return;
                }
            };
            if *maybe {
                if trait_def != cx.lang.sized {
                    errs.push(Diag::new("L0110", span, "only `Sized` may be relaxed with `?`", "Remove the `?`."));
                    return;
                }
                if let TyKind::Param(p) = tys.kind(lhs) {
                    relaxed.push(p.0);
                }
                return;
            }
            match resolve_trait_ref(ast, interner, known, cx, tys, scope, lhs, trait_ref, span) {
                Ok(tr) => out.push(Predicate::Trait(Binder { count: binder.len() as u32, value: tr })),
                Err(d) => errs.push(d),
            }
        }
    }
}

/// The elaborated param env of one item from its written
/// predicates (section 2.1), through the index's supertraits.
pub fn elaborate_env(tys: &mut impl TyIntern, index: &ImplIndex, written: &[Predicate]) -> Vec<Predicate> {
    crate::traits::solve::elaborate_in(tys, index, written)
}

/// The associated sources a set of predicates gives a scope: one
/// per trait predicate, for `Self::Assoc` and `T::Assoc`
/// resolution in the item's other signatures.
pub fn assoc_srcs_of(cx: &ResolveCx, tys: &impl TyIntern, preds: &[Predicate]) -> Vec<AssocSrc> {
    let mut out = Vec::new();
    for p in preds {
        if let Predicate::Trait(b) = p
            && let Some(rec) = cx.index.trait_record(b.value.def)
            && !rec.assoc_items.is_empty()
        {
            out.push(AssocSrc {
                self_ty: tys.args(b.value.args)[0].as_ty().unwrap_or(ERROR),
                trait_def: b.value.def,
                args: b.value.args,
                assocs: rec.assoc_items.iter().map(|&(d, n, _)| (n, d)).collect(),
            });
        }
    }
    out
}

/// Builds the semantic `Generics` of one item (params without the
/// `Self` a trait prepends; traits go through `build_trait_generics`)
/// and the scope its signatures resolve under. Lifetime parameters
/// are the subset's lifetime reject, as are parameter defaults.
#[allow(clippy::too_many_arguments)]
pub fn build_generics(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    g: &ast::Generics,
    w: &ast::WhereClause,
    errs: &mut Vec<Diag>,
) -> (Generics, Scope) {
    build_generics_shifted(ast, interner, known, cx, tys, g, w, 0, errs)
}

/// `build_generics` with parameter indexes shifted by `shift`
/// (a trait's synthetic `Self` at 0, or an impl's parameters
/// before a method's own).
#[allow(clippy::too_many_arguments)]
pub fn build_generics_shifted(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    g: &ast::Generics,
    w: &ast::WhereClause,
    shift: u32,
    errs: &mut Vec<Diag>,
) -> (Generics, Scope) {
    let mut params: Vec<ParamDef> = Vec::new();
    let mut scope = Scope::default();
    // Pass 1: parameter list and names. Indexes count type and
    // const parameters together, in written order.
    for p in &g.params {
        match p {
            ast::GenericParam::Lifetime { lt, .. } => errs.push(lifetime_diag(lt.span)),
            ast::GenericParam::Type { name, span, default, .. } => {
                if default.is_some() {
                    errs.push(not_yet("L0614", *span, "generic parameter defaults"));
                }
                let idx = shift + params.len() as u32;
                scope.type_params.push((*name, idx));
                params.push(ParamDef { name: *name, kind: ParamKind::Type, span: *span });
            }
            ast::GenericParam::Const { name, span, ty, default, .. } => {
                if default.is_some() {
                    errs.push(not_yet("L0614", *span, "generic parameter defaults"));
                }
                let idx = shift + params.len() as u32;
                let cty = resolve_scoped(ast, interner, known, cx, tys, *ty, &scope).unwrap_or_else(|d| {
                    errs.push(d);
                    ERROR
                });
                scope.const_params.push((*name, idx));
                params.push(ParamDef { name: *name, kind: ParamKind::Const(cty), span: *span });
            }
        }
    }
    // Pass 2: bounds on parameters, then where predicates. Each
    // parameter's sources join the scope as they are built, so a
    // later bound may name an earlier parameter's assoc types.
    let mut predicates: Vec<Predicate> = Vec::new();
    let mut relaxed: Vec<u32> = Vec::new();
    let mut type_param_tys: Vec<(u32, Ty)> = Vec::new();
    for (name, idx) in &scope.type_params {
        let t = tys.intern(TyKind::Param(ParamId(*idx)));
        type_param_tys.push((*idx, t));
        let _ = name;
    }
    for p in &g.params {
        if let ast::GenericParam::Type { name, bounds, .. } = p
            && let Some(idx) = scope.param_of(*name)
        {
            let lhs = tys.intern(TyKind::Param(ParamId(idx)));
            for b in bounds {
                bound_predicates(ast, interner, known, cx, tys, &scope, lhs, b, &mut predicates, &mut relaxed, errs);
            }
            scope.assoc_srcs = assoc_srcs_of(cx, tys, &predicates);
        }
    }
    for pred in &w.preds {
        match pred {
            ast::WherePred::Lifetime { lt, .. } => errs.push(lifetime_diag(lt.span)),
            ast::WherePred::Type { ty, bounds, .. } => match resolve_scoped(ast, interner, known, cx, tys, *ty, &scope) {
                Ok(lhs) => {
                    for b in bounds {
                        bound_predicates(ast, interner, known, cx, tys, &scope, lhs, b, &mut predicates, &mut relaxed, errs);
                    }
                    scope.assoc_srcs = assoc_srcs_of(cx, tys, &predicates);
                }
                Err(d) => errs.push(d),
            },
        }
    }
    // The implicit `Sized` bound on every type parameter that did
    // not write `?Sized` (section 2.7).
    for (idx, t) in &type_param_tys {
        if !relaxed.contains(idx) {
            let args = tys.intern_args(&[GenericArg::Ty(*t)]);
            predicates.push(Predicate::Trait(Binder::plain(TraitRef { def: cx.lang.sized, args, bindings: EMPTY_BINDINGS })));
        }
    }
    (Generics { parent: None, params, predicates }, scope)
}

/// A trait's generics: the synthetic `Self` parameter at index 0,
/// then the written parameters. The returned scope resolves the
/// trait's own items (its `Self` type is `Param(0)` and its assoc
/// sources are its supertraits, filled in by collect once the
/// trait record exists).
#[allow(clippy::too_many_arguments)]
pub fn build_trait_generics(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    cx: &ResolveCx,
    tys: &mut impl TyIntern,
    g: &ast::Generics,
    w: &ast::WhereClause,
    supertraits: &[TraitBound],
    errs: &mut Vec<Diag>,
) -> (Generics, Scope) {
    let (mut generics, mut scope) = build_generics_shifted(ast, interner, known, cx, tys, g, w, 1, errs);
    let self_ty = tys.intern(TyKind::Param(ParamId(0)));
    generics.params.insert(0, ParamDef { name: known.self_type, kind: ParamKind::Type, span: Span::default() });
    scope.self_ty = Some(self_ty);
    // Supertrait bounds are predicates on Self, in source order,
    // ahead of the parameter bounds built above.
    let mut preds: Vec<Predicate> = Vec::new();
    let mut relaxed: Vec<u32> = Vec::new();
    for b in supertraits {
        bound_predicates(ast, interner, known, cx, tys, &scope, self_ty, b, &mut preds, &mut relaxed, errs);
    }
    preds.extend(std::mem::take(&mut generics.predicates));
    generics.predicates = preds;
    scope.assoc_srcs = assoc_srcs_of(cx, tys, &generics.predicates);
    (generics, scope)
}

/// The checking scope of one fn: its elaborated param env and the
/// naming scope its body annotations resolve under. For an
/// instance both are substituted with the instance args, so a
/// body never sees a `Param` type outside its template check.
#[derive(Clone, Debug, Default)]
pub struct FnScope {
    pub env: Vec<Predicate>,
    pub scope: Scope,
}

/// One generic fn or method in template form: combined generics
/// (parent impl/trait params first, then its own) and the
/// elaborated env. The signature tys themselves live in the
/// template's `FnInfo` (for AST fns) or `TraitMethodTemplate`.
#[derive(Clone, Debug)]
pub struct FnTemplate {
    pub generics: Generics,
    pub env: Vec<Predicate>,
}

/// One trait method in template form. Trait methods are not AST
/// fns in the driver's count, so they live here, not in `fns`;
/// mono materializes them into `fns` per instance when an impl
/// uses a default body, and checks signatures against them.
#[derive(Clone)]
pub struct TraitMethodTemplate<'a> {
    pub def: &'a ast::FnDef,
    pub name: Sym,
    pub self_kind: Option<ast::SelfKind>,
    /// Parameter types including `self` first, over the combined
    /// generics (trait params with Self at 0, then method params).
    pub params: Vec<Ty>,
    pub ret: Ty,
    pub ret_borrows_from: Option<usize>,
    pub generics: Generics,
    pub env: Vec<Predicate>,
    pub scope: Scope,
}

/// What one entry of `Program::fns` is, for the driver: only
/// `Plain` and `Instance` fns are checked, lowered, and codegen'd
/// by the driver. Templates are checked once per template by
/// mono (through abstract instances), stubs only carry
/// signatures for abstract checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum FnClass {
    #[default]
    Plain,
    Template,
    Instance,
    Abstract,
    Stub,
}

/// One materialized fn instance: its template and concrete args
/// (combined parent+own order).
#[derive(Clone, Copy, Debug)]
pub struct InstanceInfo {
    pub template_def: DefId,
    pub template_local: Option<LocalDefId>,
    pub args: ArgsId,
}

/// The generic tables of one program, built by collect and read
/// by check, mono, and the driver. Parallel vecs are indexed by
/// the session-local `AdtId` / `LocalDefId` of the compat tables
/// in `Program`, including the instances mono appends.
pub struct GenTables<'a> {
    pub lang: LangTraits,
    pub index: ImplIndex,
    pub trait_names: FxMap<Sym, DefId>,
    pub trait_scopes: FxMap<DefId, Scope>,
    pub trait_methods: FxMap<DefId, TraitMethodTemplate<'a>>,
    /// Associated type defaults from trait definitions, in trait
    /// signature form (over the trait's params, Self at 0).
    pub trait_assoc_defaults: FxMap<DefId, Ty>,
    /// Per user Adt (templates first, instances appended): the
    /// template def and declared parameter count.
    pub adt_info: Vec<(DefId, usize)>,
    pub adt_generics: Vec<Generics>,
    pub adt_envs: Vec<Vec<Predicate>>,
    pub adt_scopes: Vec<Scope>,
    /// The (template def, concrete args) a materialized Adt is an
    /// instance of. None for templates and plain Adts.
    pub adt_instance_of: Vec<Option<(DefId, ArgsId)>>,
    pub fn_templates: Vec<Option<FnTemplate>>,
    pub fn_scopes: Vec<FnScope>,
    pub fn_class: Vec<FnClass>,
    pub instances: FxMap<LocalDefId, InstanceInfo>,
    pub instance_by_key: FxMap<(DefId, ArgsId), LocalDefId>,
    /// The `Drop::drop` instance to call for one concrete Adt,
    /// for cgen's drop glue (iface: W-CGEN reads this).
    pub drop_methods: FxMap<AdtId, LocalDefId>,
    /// True when the program uses any generic or trait form. The
    /// driver then assigns instance slots and forces a full work
    /// set (iface: W-DRIVER reads this).
    pub has_generics: bool,
    /// (abstract instances checked, concrete instances made).
    pub mono_counts: (usize, usize),
}

impl Default for GenTables<'_> {
    fn default() -> Self {
        GenTables {
            lang: LangTraits::new(),
            index: ImplIndex::new(),
            trait_names: FxMap::default(),
            trait_scopes: FxMap::default(),
            trait_methods: FxMap::default(),
            trait_assoc_defaults: FxMap::default(),
            adt_info: Vec::new(),
            adt_generics: Vec::new(),
            adt_envs: Vec::new(),
            adt_scopes: Vec::new(),
            adt_instance_of: Vec::new(),
            fn_templates: Vec::new(),
            fn_scopes: Vec::new(),
            fn_class: Vec::new(),
            instances: FxMap::default(),
            instance_by_key: FxMap::default(),
            drop_methods: FxMap::default(),
            has_generics: false,
            mono_counts: (0, 0),
        }
    }
}

impl GenTables<'_> {
    /// The resolve context over the tables built so far.
    pub fn resolve_cx<'x>(&'x self, type_names: &'x FxMap<Sym, AdtId>, aliases: &'x FxMap<Sym, Ty>) -> ResolveCx<'x> {
        ResolveCx { type_names, adt_info: &self.adt_info, trait_names: &self.trait_names, aliases, index: &self.index, lang: &self.lang }
    }
}

/// True when `Param(idx)` occurs anywhere in a type.
pub fn ty_uses_param(tys: &impl TyIntern, t: Ty, idx: u32) -> bool {
    if !tys.flags(t).contains_param() {
        return false;
    }
    match tys.kind(t) {
        TyKind::Param(p) => p.0 == idx,
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => ty_uses_param(tys, e, idx),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| ty_uses_param(tys, e, idx)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => {
            tys.args(a).iter().any(|g| g.as_ty().is_some_and(|e| ty_uses_param(tys, e, idx)))
        }
        _ => false,
    }
}

/// Inserts the lang trait records into the program's index and
/// def table. Runs first in generic collection.
pub fn init_lang(p: &mut Program) {
    let records = lang_trait_records(&p.gx.lang, p.interner, &mut p.tys);
    for rec in records {
        let mut data =
            crate::ty::defs::DefData::skeleton(crate::ty::defs::DefKind::Trait, None, rec.name, crate::ty::defs::Vis::Pub, Span::default());
        data.generics = rec.generics.clone();
        p.defs.insert(rec.def, data);
        p.gx.index.insert_trait(rec);
    }
}

/// How many type/const parameters an AST generics list declares
/// (lifetime parameters are rejected when generics are built, and
/// are not counted).
pub fn ast_param_count(g: &ast::Generics) -> usize {
    g.params.iter().filter(|p| matches!(p, ast::GenericParam::Type { .. } | ast::GenericParam::Const { .. })).count()
}

/// The def of one user trait: hashed from its name and its
/// ordinal among same-named traits (duplicates are errors, the
/// ordinal only keeps their records apart).
fn trait_def_id(p: &Program, interner: &Interner, name: Sym, ordinal: u32) -> DefId {
    DefId { krate: p.krate, hash: crate::def::item_hash(p.stable_crate, &[], crate::def::DefKind::Trait, interner.get(name), ordinal) }
}

/// The def of one associated item or method of a trait or impl,
/// hashed under its parent's path hash.
pub fn child_def_id(krate: crate::def::CrateId, parent: DefId, interner: &Interner, name: Sym, kind: crate::def::DefKind) -> DefId {
    DefId { krate, hash: crate::def::child_hash(parent.hash, kind, interner.get(name), 0) }
}

/// Pass 0 of generic collection: every user trait gets its def
/// and a placeholder index record with its associated item and
/// method defs, so bounds elsewhere can name the trait and its
/// assoc items before signatures resolve. `build_trait_tables`
/// fills the records in.
pub fn collect_trait_defs(p: &mut Program, errs: &mut Vec<Diag>) {
    let mut ordinals: FxMap<Sym, u32> = FxMap::default();
    for item in &p.ast.items {
        let ast::ItemKind::Trait(tdef) = &item.kind else { continue };
        p.gx.has_generics = true;
        let ordinal = ordinals.get(&tdef.name).copied().unwrap_or(0);
        ordinals.insert(tdef.name, ordinal + 1);
        let def = trait_def_id(p, p.interner, tdef.name, ordinal);
        if p.gx.trait_names.insert(tdef.name, def).is_some() {
            errs.push(Diag::new(
                "L0106",
                tdef.name_span,
                format!("`{}` is defined more than once", p.name(tdef.name)),
                "Rename one of the definitions.",
            ));
        }
        let mut assoc_items: Vec<(DefId, Sym, bool)> = Vec::new();
        for at in &tdef.types {
            assoc_items.push((child_def_id(p.krate, def, p.interner, at.name, crate::def::DefKind::Assoc), at.name, true));
        }
        for ac in &tdef.consts {
            assoc_items.push((child_def_id(p.krate, def, p.interner, ac.name, crate::def::DefKind::Assoc), ac.name, false));
        }
        let mut methods: Vec<(DefId, Sym)> = Vec::new();
        for f in &tdef.fns {
            methods.push((child_def_id(p.krate, def, p.interner, f.name, crate::def::DefKind::Method), f.name));
        }
        // Placeholder generics with the right parameter count, so
        // bounds that name this trait resolve before its own
        // generics are built.
        let mut placeholder = Generics::default();
        for _ in 0..=ast_param_count(&tdef.generics) {
            placeholder.params.push(ParamDef { name: tdef.name, kind: ParamKind::Type, span: tdef.name_span });
        }
        p.gx.index.insert_trait(TraitRecord {
            def,
            name: tdef.name,
            generics: placeholder,
            assoc_items,
            methods,
            local: true,
            span: tdef.span,
        });
        p.defs.insert(
            def,
            crate::ty::defs::DefData::skeleton(
                crate::ty::defs::DefKind::Trait,
                None,
                tdef.name,
                crate::ty::defs::Vis::Priv,
                tdef.name_span,
            ),
        );
    }
}

/// Resolves one fn signature in template form: self parameter,
/// params, and return, under the combined scope. Handles
/// `impl Trait` argument sugar by growing the generics. Returns
/// (params with self first, ret, ret_borrows_from).
#[allow(clippy::too_many_arguments)]
pub fn resolve_fn_sig(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    tys: &mut impl TyIntern,
    cx: &ResolveCx,
    def: &ast::FnDef,
    mut generics: Generics,
    scope: &Scope,
    self_ty: Option<Ty>,
    errs: &mut Vec<Diag>,
) -> (Vec<Ty>, Ty, Option<usize>, Generics, Scope) {
    let mut scope = scope.clone();
    if scope.self_ty.is_none() {
        scope.self_ty = self_ty;
    }
    let mut params: Vec<Ty> = Vec::new();
    if let (Some(sp), Some(st)) = (&def.self_param, self_ty) {
        if let Some(lt) = sp.lifetime
            && let Err(d) = check_lifetime(interner, lt)
        {
            errs.push(d);
        }
        params.push(match sp.kind {
            ast::SelfKind::Value => st,
            ast::SelfKind::Ref => tys.mk_ref(false, st),
            ast::SelfKind::RefMut => tys.mk_ref(true, st),
            ast::SelfKind::Typed => match sp.ty {
                Some(t) => resolve_scoped(ast, interner, known, cx, tys, t, &scope).unwrap_or_else(|d| {
                    errs.push(d);
                    ERROR
                }),
                None => st,
            },
        });
    }
    for param in &def.params {
        // `impl Trait` in argument position is a fresh type
        // parameter with those bounds (section 2.11).
        if let TyExpr::ImplTrait { bounds } = ast.ty(param.ty) {
            let idx = generics.params.len() as u32;
            let name = interner.intern(&format!("impl#{idx}"));
            generics.params.push(ParamDef { name, kind: ParamKind::Type, span: param.span });
            scope.type_params.push((name, idx));
            let lhs = tys.intern(TyKind::Param(ParamId(idx)));
            let mut preds: Vec<Predicate> = Vec::new();
            let mut relaxed: Vec<u32> = Vec::new();
            for b in bounds {
                bound_predicates(ast, interner, known, cx, tys, &scope, lhs, b, &mut preds, &mut relaxed, errs);
            }
            if !relaxed.contains(&idx) {
                let args = tys.intern_args(&[GenericArg::Ty(lhs)]);
                preds.push(Predicate::Trait(Binder::plain(TraitRef { def: cx.lang.sized, args, bindings: EMPTY_BINDINGS })));
            }
            generics.predicates.extend(preds);
            params.push(lhs);
            continue;
        }
        match resolve_scoped(ast, interner, known, cx, tys, param.ty, &scope) {
            Ok(t) => {
                if !crate::check::collect::is_sized_ty(tys, t) {
                    errs.push(Diag::new(
                        "L0110",
                        ast.ty_span(param.ty),
                        "the size for values of this type cannot be known",
                        "Put the value behind a reference, such as `&[T]` or `&str`.",
                    ));
                }
                params.push(t);
            }
            Err(d) => {
                errs.push(d);
                params.push(ERROR);
            }
        }
    }
    let ret = match def.ret {
        None => UNIT,
        Some(t) => resolve_scoped(ast, interner, known, cx, tys, t, &scope).unwrap_or_else(|d| {
            errs.push(d);
            ERROR
        }),
    };
    if !crate::check::collect::is_sized_ty(tys, ret) {
        let span = def.ret.map_or(def.name_span, |t| ast.ty_span(t));
        errs.push(Diag::new(
            "L0110",
            span,
            "the size for values of this type cannot be known",
            "Put the value behind a reference, such as `&[T]` or `&str`.",
        ));
    }
    // Elision, as in the plain path: a returned reference borrows
    // from `self`, or from the only reference parameter.
    let mut ret_borrows_from = None;
    if crate::check::collect::contains_ref(tys, ret) {
        let ref_params: Vec<usize> = (0..params.len()).filter(|&i| crate::check::collect::contains_ref(tys, params[i])).collect();
        if def.self_param.as_ref().is_some_and(|s| s.kind != ast::SelfKind::Value) {
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
    (params, ret, ret_borrows_from, generics, scope)
}

/// True when a written field type holds only `'static` (or
/// elided-in-name `'_`) references: the one reference field form
/// this subset stores, since declared lifetimes on Adts are
/// rejected. Elided references in fields are invalid Rust and
/// keep the old reject.
pub fn ref_field_ok(ast: &Ast, interner: &Interner, id: ast::TyId) -> bool {
    match ast.ty(id) {
        TyExpr::Ref { lifetime, .. } => lifetime.is_some_and(|lt| interner.get(lt.name) == "static"),
        TyExpr::Tuple(elems) => elems.iter().all(|&e| ref_field_ok(ast, interner, e)),
        TyExpr::Paren(inner) => ref_field_ok(ast, interner, *inner),
        TyExpr::Array { inner, .. } | TyExpr::Slice(inner) => ref_field_ok(ast, interner, *inner),
        TyExpr::Path(segs) => segs.iter().all(|seg| match &seg.args {
            GenericArgs::Angle(args) => args.iter().all(|a| match a {
                AstArg::Type(t) => ref_field_ok(ast, interner, *t),
                _ => true,
            }),
            _ => true,
        }),
        _ => true,
    }
}

/// Fills in every user trait: its generics and supertraits, its
/// method signature templates, and its associated type defaults.
/// Runs after Adt names exist (signatures name Adts) and before
/// fields and fns resolve (bounds name traits).
pub fn build_trait_tables(p: &mut Program, errs: &mut Vec<Diag>) {
    let trait_items: Vec<(usize, DefId)> = p
        .ast
        .items
        .iter()
        .enumerate()
        .filter_map(|(i, item)| match &item.kind {
            ast::ItemKind::Trait(tdef) => p.gx.trait_names.get(&tdef.name).map(|&d| (i, d)),
            _ => None,
        })
        .collect();
    for (item_i, trait_def) in trait_items {
        let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
        // Clone the AST-side pieces the build needs, so the mutable
        // program borrows below stay simple.
        let tdef_generics = tdef.generics.clone();
        let tdef_where = tdef.where_clause.clone();
        let tdef_bounds = tdef.bounds.clone();
        let (mut generics, mut scope) = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            build_trait_generics(p.ast, p.interner, p.known, &cx, &mut p.tys, &tdef_generics, &tdef_where, &tdef_bounds, errs)
        };
        // The trait's own associated items are sources on its Self.
        {
            let rec = p.gx.index.trait_record(trait_def).cloned();
            if let Some(rec) = rec {
                let self_args: Vec<GenericArg> = (0..generics.params.len() as u32)
                    .map(|i| {
                        let t = p.tys.intern(TyKind::Param(ParamId(i)));
                        GenericArg::Ty(t)
                    })
                    .collect();
                let args = p.tys.intern_args(&self_args);
                scope.assoc_srcs.push(AssocSrc {
                    self_ty: scope.self_ty.unwrap_or(ERROR),
                    trait_def,
                    args,
                    assocs: rec.assoc_items.iter().map(|&(d, n, _)| (n, d)).collect(),
                });
            }
        }
        // Associated types: bounds become predicates on the
        // projection; defaults resolve under the trait scope.
        let assoc_defs: Vec<(usize, DefId)> = {
            let rec = p.gx.index.trait_record(trait_def).unwrap();
            tdef.types
                .iter()
                .enumerate()
                .map(|(i, at)| (i, rec.assoc_by_name(at.name).expect("assoc defs were recorded in pass 0")))
                .collect()
        };
        for (at_i, assoc_def) in assoc_defs {
            let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
            let at = &tdef.types[at_i];
            if !at.generics.params.is_empty() {
                errs.push(not_yet("L0621", at.generics.span, "generic associated types"));
            }
            let self_args: Vec<GenericArg> = (0..generics.params.len() as u32)
                .map(|i| {
                    let t = p.tys.intern(TyKind::Param(ParamId(i)));
                    GenericArg::Ty(t)
                })
                .collect();
            let trait_args = p.tys.intern_args(&self_args);
            let proj = p.tys.intern(TyKind::Projection(AssocId(assoc_def), trait_args));
            let at_bounds = at.bounds.clone();
            let at_where = at.where_clause.clone();
            let at_default = at.default;
            {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                let mut relaxed: Vec<u32> = Vec::new();
                let mut preds: Vec<Predicate> = Vec::new();
                for b in &at_bounds {
                    bound_predicates(p.ast, p.interner, p.known, &cx, &mut p.tys, &scope, proj, b, &mut preds, &mut relaxed, errs);
                }
                generics.predicates.extend(preds);
                let _ = at_where;
                if let Some(d) = at_default {
                    match resolve_scoped(p.ast, p.interner, p.known, &cx, &mut p.tys, d, &scope) {
                        Ok(t) => {
                            p.gx.trait_assoc_defaults.insert(assoc_def, t);
                        }
                        Err(diag) => errs.push(diag),
                    }
                }
            }
        }
        // Associated consts: resolve the type for validation. The
        // values ride the const evaluator when a use needs them.
        let const_tys: Vec<ast::TyId> = {
            let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
            tdef.consts.iter().map(|ac| ac.ty).collect()
        };
        for ty in const_tys {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            if let Err(d) = resolve_scoped(p.ast, p.interner, p.known, &cx, &mut p.tys, ty, &scope) {
                errs.push(d);
            }
        }
        // Method signature templates over trait ++ own generics.
        let fn_count = {
            let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
            tdef.fns.len()
        };
        let env = elaborate_env(&mut p.tys, &p.gx.index, &generics.predicates);
        for fn_i in 0..fn_count {
            let (fdef, method_def) = {
                let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
                let f = &tdef.fns[fn_i];
                let rec = p.gx.index.trait_record(trait_def).unwrap();
                (f, rec.method_by_name(f.name).expect("method defs were recorded in pass 0"))
            };
            let shift = generics.params.len() as u32;
            let (own_generics, own_scope) = {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                build_generics_shifted(p.ast, p.interner, p.known, &cx, &mut p.tys, &fdef.generics, &fdef.where_clause, shift, errs)
            };
            let mut combined = generics.clone();
            combined.params.extend(own_generics.params.iter().cloned());
            combined.predicates.extend(own_generics.predicates.iter().copied());
            let mut mscope = scope.clone();
            mscope.type_params.extend(own_scope.type_params.iter().copied());
            mscope.const_params.extend(own_scope.const_params.iter().copied());
            let (params, ret, ret_borrows_from, combined, mscope) = {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                resolve_fn_sig(p.ast, p.interner, p.known, &mut p.tys, &cx, fdef, combined, &mscope, scope.self_ty, errs)
            };
            let menv = elaborate_env(&mut p.tys, &p.gx.index, &combined.predicates);
            p.gx.trait_methods.insert(
                method_def,
                TraitMethodTemplate {
                    def: fdef,
                    name: fdef.name,
                    self_kind: fdef.self_param.as_ref().map(|s| s.kind),
                    params,
                    ret,
                    ret_borrows_from,
                    generics: combined,
                    env: menv,
                    scope: mscope,
                },
            );
        }
        // Replace the placeholder record with the full one.
        {
            let old = p.gx.index.trait_record(trait_def).unwrap().clone();
            p.gx.index.insert_trait(TraitRecord { generics: generics.clone(), ..old });
            let mut data =
                crate::ty::defs::DefData::skeleton(crate::ty::defs::DefKind::Trait, None, old.name, crate::ty::defs::Vis::Priv, old.span);
            data.generics = generics;
            p.defs.insert(trait_def, data);
        }
        scope.assoc_srcs = {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            assoc_srcs_of(&cx, &p.tys, &env)
        };
        p.gx.trait_scopes.insert(trait_def, scope);
    }
}

/// One synthetic (derive or lang) impl def, minted under the
/// local crate so slot and cache identity stay inside it.
fn synthetic_impl_def(p: &Program, ordinal: u32) -> DefId {
    DefId { krate: p.krate, hash: crate::def::item_hash(p.stable_crate, &["<synthetic>"], crate::def::DefKind::Impl, "impl", ordinal) }
}

/// Builds the next synthetic impl record in the index. Returns
/// its id, or None when the Self pattern has no indexed head.
fn insert_synthetic(
    p: &mut Program,
    ordinal: &mut u32,
    trait_def: DefId,
    self_pat: Ty,
    rest: &[Ty],
    generics: Generics,
    assoc_tys: Vec<(DefId, Ty)>,
    synthetic: crate::traits::index::Synthetic,
    local: bool,
    span: Span,
) -> Option<crate::traits::ImplId> {
    use crate::traits::index::{ImplRecord, pattern_head};
    let mut all = vec![GenericArg::Ty(self_pat)];
    all.extend(rest.iter().map(|&t| GenericArg::Ty(t)));
    let args = p.tys.intern_args(&all);
    let (head, blanket) = pattern_head(&p.tys, self_pat, &[])?;
    let def = synthetic_impl_def(p, *ordinal);
    *ordinal += 1;
    Some(p.gx.index.insert_impl(ImplRecord {
        def,
        trait_def,
        trait_ref: TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS },
        generics,
        assoc_tys,
        assoc_consts: Vec::new(),
        items: Vec::new(),
        synthetic,
        local,
        span,
        head,
        blanket,
    }))
}

/// Finishes one trait impl: associated bindings, the index
/// record, the orphan check, and method signature validation
/// against the trait. Called from collect's fn pass after the
/// impl's methods are in `fns`.
#[allow(clippy::too_many_arguments)]
pub fn finish_trait_impl(
    p: &mut Program,
    imp: &ast::ImplDef,
    impl_def: DefId,
    impl_generics: Generics,
    self_pat: Ty,
    tr: TraitRef,
    scope: &Scope,
    method_ids: &[LocalDefId],
    errs: &mut Vec<Diag>,
) {
    use crate::traits::index::{ImplRecord, Synthetic, pattern_head};
    let Some(rec) = p.gx.index.trait_record(tr.def).cloned() else { return };
    // Associated types: resolve the written bindings, fill the
    // rest from trait defaults, and require every assoc type.
    let mut assoc_tys: Vec<(DefId, Ty)> = Vec::new();
    for at in &imp.types {
        let Some(assoc) = rec.assoc_by_name(at.name) else {
            errs.push(Diag::new(
                "L0102",
                at.name_span,
                format!("trait has no associated type named `{}`", p.name(at.name)),
                "Check the spelling against the trait definition.",
            ));
            continue;
        };
        match at.default {
            Some(d) => {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                match resolve_scoped(p.ast, p.interner, p.known, &cx, &mut p.tys, d, scope) {
                    Ok(t) => assoc_tys.push((assoc, t)),
                    Err(diag) => errs.push(diag),
                }
            }
            None => errs.push(Diag::new(
                "L0110",
                at.name_span,
                "an associated type in an impl must be assigned a type",
                format!("Write `type {} = Type;`.", p.name(at.name)),
            )),
        }
    }
    for &(assoc, _name, is_type) in &rec.assoc_items {
        if !is_type || assoc_tys.iter().any(|(d, _)| *d == assoc) {
            continue;
        }
        match p.gx.trait_assoc_defaults.get(&assoc).copied() {
            Some(default) => {
                let args: Vec<GenericArg> = p.tys.args(tr.args).to_vec();
                let t = subst(&mut p.tys, default, &args);
                assoc_tys.push((assoc, t));
            }
            None => errs.push(Diag::new(
                "L0110",
                imp.span,
                "the impl does not bind every associated type of the trait",
                "Add the missing `type Name = Type;` items.",
            )),
        }
    }
    // Associated consts: presence is required the same way. Their
    // values are const-evaluated at use sites.
    for ac in &imp.consts {
        if rec.assoc_by_name(ac.name).is_none() {
            errs.push(Diag::new(
                "L0102",
                ac.name_span,
                format!("trait has no associated const named `{}`", p.name(ac.name)),
                "Check the spelling against the trait definition.",
            ));
        }
    }
    let Some((head, blanket)) = pattern_head(&p.tys, self_pat, &[]) else {
        errs.push(not_yet("L0614", imp.span, "impls for this Self type form"));
        return;
    };
    let items: Vec<DefId> = method_ids.iter().map(|&id| p.def_id(id)).collect();
    let impl_id = p.gx.index.insert_impl(ImplRecord {
        def: impl_def,
        trait_def: tr.def,
        trait_ref: tr,
        generics: impl_generics.clone(),
        assoc_tys: assoc_tys.clone(),
        assoc_consts: Vec::new(),
        items,
        synthetic: Synthetic::None,
        local: true,
        span: imp.span,
        head,
        blanket,
    });
    // The orphan rule (section 2.3).
    {
        let rec_scoped = p.gx.index.get(impl_id).clone();
        let is_local = |d: DefId| d.krate == p.krate;
        if !p.gx.index.orphan_ok(&p.tys, &rec_scoped, &[], &is_local) {
            errs.push(Diag::new(
                "L0616",
                imp.span,
                "this impl is not allowed here: neither the trait nor the type is defined in this file",
                "Implement the trait for a local type, or define the trait locally.",
            ));
        }
    }
    // Method validation against the trait's templates.
    let impl_parent_n = impl_generics.params.len();
    for (method_def, mname) in &rec.methods {
        let Some(tmpl) = p.gx.trait_methods.get(method_def).cloned() else { continue };
        let found = method_ids.iter().copied().find(|&id| p.fn_info(id).name == *mname);
        let Some(local) = found else {
            if tmpl.def.body.is_none() {
                errs.push(Diag::new(
                    "L0110",
                    imp.span,
                    format!("the impl is missing the trait method `{}`", p.name(*mname)),
                    "Add the method to the impl.",
                ));
            }
            continue;
        };
        validate_method_sig(p, &tmpl, local, tr, impl_parent_n, imp.span, errs);
    }
    for &local in method_ids {
        let name = p.fn_info(local).name;
        if rec.method_by_name(name).is_none() {
            errs.push(Diag::new(
                "L0110",
                p.fn_info(local).def.name_span,
                format!("`{}` is not a member of the trait being implemented", p.name(name)),
                "Move it to an inherent impl, or add it to the trait.",
            ));
        }
    }
}

/// Checks one impl method signature against its trait method
/// template: substitute the trait template with the impl's trait
/// ref, normalize both sides (associated types through this
/// impl), and compare.
fn validate_method_sig(
    p: &mut Program,
    tmpl: &TraitMethodTemplate,
    local: LocalDefId,
    tr: TraitRef,
    impl_parent_n: usize,
    span: Span,
    errs: &mut Vec<Diag>,
) {
    use crate::traits::solve::{PureCx, Solver, normalize};
    let (f_self_kind, f_params_len, f_name_span) = {
        let f = p.fn_info(local);
        (f.self_kind, f.params.len(), f.def.name_span)
    };
    if f_self_kind != tmpl.self_kind {
        // Typed receivers compare by their resolved type below;
        // plain forms must match here.
        if !(matches!(f_self_kind, Some(ast::SelfKind::Typed)) || matches!(tmpl.self_kind, Some(ast::SelfKind::Typed))) {
            errs.push(Diag::new(
                "L0110",
                f_name_span,
                "method receiver does not match the trait method",
                "Match the receiver form in the trait definition.",
            ));
            return;
        }
    }
    if f_params_len != tmpl.params.len() {
        errs.push(Diag::new(
            "L0110",
            f_name_span,
            "method takes a different number of parameters than the trait method",
            "Match the signature in the trait definition.",
        ));
        return;
    }
    // Substitution for the trait template: trait params from the
    // impl's trait ref, method params onto the impl's own.
    let trait_n = p.gx.index.trait_record(tr.def).map_or(0, |r| r.generics.params.len());
    let mut subst_args: Vec<GenericArg> = p.tys.args(tr.args).to_vec();
    let own = tmpl.generics.params.len().saturating_sub(trait_n);
    for j in 0..own {
        let t = p.tys.intern(TyKind::Param(ParamId((impl_parent_n + j) as u32)));
        subst_args.push(GenericArg::Ty(t));
    }
    let want_params: Vec<Ty> = tmpl.params.iter().map(|&t| subst(&mut p.tys, t, &subst_args)).collect();
    let want_ret = subst(&mut p.tys, tmpl.ret, &subst_args);
    let got_params = p.fn_info(local).params.clone();
    let got_ret = p.fn_info(local).ret;
    let mut cx = PureCx::new(&p.tys);
    let mut solver = Solver::new();
    let same = want_params.len() == got_params.len()
        && want_params
            .iter()
            .zip(&got_params)
            .all(|(&w, &g)| normalize(&mut solver, &mut cx, &p.gx.index, &[], w) == normalize(&mut solver, &mut cx, &p.gx.index, &[], g))
        && normalize(&mut solver, &mut cx, &p.gx.index, &[], want_ret) == normalize(&mut solver, &mut cx, &p.gx.index, &[], got_ret);
    if !same {
        errs.push(Diag::new(
            "L0110",
            f_name_span,
            "method signature does not match the trait method",
            "Match the parameter and return types in the trait definition, after associated types are substituted.",
        ));
    }
    let _ = span;
}

/// Derives and lang facts as synthetic impls (sections 2.2 and
/// 2.6), inserted after every written impl so coherence sees one
/// impl set. Bodies stay in the builtin derive paths until
/// source std replaces them; these records carry selection and
/// coherence only.
pub fn add_synthetic_impls(p: &mut Program) {
    use crate::traits::index::Synthetic;
    let lang = p.gx.lang;
    let mut ordinal = 0u32;
    let span = Span::default();
    // Derives: one record per (Adt template, derived trait), with
    // a bound per type parameter, as rustc writes them.
    let n_adts = p.gx.adt_info.len();
    for a in 0..n_adts {
        let adt = AdtId(a as u32);
        let (def, n_params) = p.gx.adt_info[a];
        let derives = p.adt(adt).derives;
        let wanted: [(bool, DefId, &str); 4] = [
            (derives.clone, lang.clone, "Clone"),
            (derives.copy, lang.copy, "Copy"),
            (derives.debug, lang.debug, "Debug"),
            (derives.partial_eq, lang.partial_eq, "PartialEq"),
        ];
        for (on, trait_def, dname) in wanted {
            if !on {
                continue;
            }
            let param_args: Vec<GenericArg> = (0..n_params as u32)
                .map(|i| {
                    let t = p.tys.intern(TyKind::Param(ParamId(i)));
                    GenericArg::Ty(t)
                })
                .collect();
            let self_pat = p.tys.mk_adt(def, &param_args);
            let rest: Vec<Ty> = if trait_def == lang.partial_eq { vec![self_pat] } else { Vec::new() };
            let mut preds: Vec<Predicate> = Vec::new();
            for i in 0..n_params as u32 {
                let t = p.tys.intern(TyKind::Param(ParamId(i)));
                let mut tr_args = vec![GenericArg::Ty(t)];
                if trait_def == lang.partial_eq {
                    tr_args.push(GenericArg::Ty(t));
                }
                let args = p.tys.intern_args(&tr_args);
                preds.push(Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS })));
            }
            let generics = Generics { parent: None, params: p.gx.adt_generics[a].params.clone(), predicates: preds };
            insert_synthetic(
                p,
                &mut ordinal,
                trait_def,
                self_pat,
                &rest,
                generics,
                Vec::new(),
                Synthetic::Derive(p.interner.intern(dname)),
                true,
                span,
            );
        }
    }
    // Lang facts for builtin types.
    let g0 = Generics::default();
    let scalar_traits = [lang.copy, lang.clone, lang.debug, lang.eq, lang.hash, lang.default];
    let mut scalars: Vec<Ty> = IntTy::ALL_SUPPORTED.iter().map(|&i| int(i)).collect();
    scalars.extend([BOOL, CHAR, UNIT]);
    for t in scalars {
        for tr in scalar_traits {
            insert_synthetic(p, &mut ordinal, tr, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        }
        insert_synthetic(p, &mut ordinal, lang.partial_eq, t, &[t], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.partial_ord, t, &[t], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
        insert_synthetic(p, &mut ordinal, lang.ord, t, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    let p0 = p.tys.intern(TyKind::Param(ParamId(0)));
    let p1 = p.tys.intern(TyKind::Param(ParamId(1)));
    let one = Generics {
        parent: None,
        params: vec![ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span }],
        predicates: Vec::new(),
    };
    let pred_on_p0 = |p: &mut Program, trait_def: DefId| -> Vec<Predicate> {
        let t = p.tys.intern(TyKind::Param(ParamId(0)));
        let mut a = vec![GenericArg::Ty(t)];
        if trait_def == lang.partial_eq || trait_def == lang.partial_ord {
            a.push(GenericArg::Ty(t));
        }
        let args = p.tys.intern_args(&a);
        vec![Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS }))]
    };
    // &T: Copy + Clone unconditionally, the rest through T.
    let ref_p0 = p.tys.mk_ref(false, p0);
    insert_synthetic(p, &mut ordinal, lang.copy, ref_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    insert_synthetic(p, &mut ordinal, lang.clone, ref_p0, &[], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    // String and the generic builtin containers.
    for tr in [lang.clone, lang.debug, lang.eq, lang.hash, lang.default] {
        insert_synthetic(p, &mut ordinal, tr, STRING, &[], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
    }
    insert_synthetic(p, &mut ordinal, lang.partial_eq, STRING, &[STRING], g0.clone(), Vec::new(), Synthetic::Lang, false, span);
    insert_synthetic(p, &mut ordinal, lang.deref, STRING, &[], g0.clone(), vec![(lang.assoc_target, STR)], Synthetic::Lang, false, span);
    let vec_p0 = p.tys.mk_vec(p0);
    let opt_p0 = p.tys.mk_option(p0);
    for (self_pat, with_copy) in [(vec_p0, false), (opt_p0, true)] {
        for tr in [lang.clone, lang.debug, lang.eq, lang.hash, lang.default] {
            let preds = pred_on_p0(p, tr);
            let mut g1 = one.clone();
            g1.predicates = preds;
            insert_synthetic(p, &mut ordinal, tr, self_pat, &[], g1, Vec::new(), Synthetic::Lang, false, span);
        }
        let preds = pred_on_p0(p, lang.partial_eq);
        let mut g1 = one.clone();
        g1.predicates = preds;
        insert_synthetic(p, &mut ordinal, lang.partial_eq, self_pat, &[self_pat], g1, Vec::new(), Synthetic::Lang, false, span);
        if with_copy {
            let preds = pred_on_p0(p, lang.copy);
            let mut g1 = one.clone();
            g1.predicates = preds;
            insert_synthetic(p, &mut ordinal, lang.copy, self_pat, &[], g1, Vec::new(), Synthetic::Lang, false, span);
        }
    }
    // From<T> for T, and Into through From.
    insert_synthetic(p, &mut ordinal, lang.from, p0, &[p0], one.clone(), Vec::new(), Synthetic::Lang, false, span);
    {
        // impl<T, U> Into<U> for T where U: From<T>
        let args = p.tys.intern_args(&[GenericArg::Ty(p1), GenericArg::Ty(p0)]);
        let g2 = Generics {
            parent: None,
            params: vec![
                ParamDef { name: p.interner.intern("T"), kind: ParamKind::Type, span },
                ParamDef { name: p.interner.intern("U"), kind: ParamKind::Type, span },
            ],
            predicates: vec![Predicate::Trait(Binder::plain(TraitRef { def: lang.from, args, bindings: EMPTY_BINDINGS }))],
        };
        insert_synthetic(p, &mut ordinal, lang.into, p0, &[p1], g2, Vec::new(), Synthetic::Lang, false, span);
    }
    // The IntoIterator blanket: impl<I: Iterator> IntoIterator
    // for I, Item = I::Item, IntoIter = I.
    {
        let preds = pred_on_p0(p, lang.iterator);
        let mut g1 = one.clone();
        g1.predicates = preds;
        let item_args = p.tys.intern_args(&[GenericArg::Ty(p0)]);
        let item_proj = p.tys.intern(TyKind::Projection(AssocId(lang.assoc_item), item_args));
        insert_synthetic(
            p,
            &mut ordinal,
            lang.into_iterator,
            p0,
            &[],
            g1,
            vec![(lang.assoc_into_item, item_proj), (lang.assoc_into_iter, p0)],
            Synthetic::Lang,
            false,
            span,
        );
    }
}

/// The last collect step before mono: synthetic impls, then
/// coherence over the whole index (section 2.6).
pub fn finish_collect(p: &mut Program, errs: &mut Vec<Diag>) {
    add_synthetic_impls(p);
    let is_local = |d: DefId| d.krate == p.krate;
    let pairs = p.gx.index.coherence_overlaps(&mut p.tys, &[], &is_local);
    for (_, later) in pairs {
        let rec = p.gx.index.get(later);
        let trait_name = p.gx.index.trait_record(rec.trait_def).map_or("?", |r| p.name(r.name));
        errs.push(Diag::new(
            "L0615",
            rec.span,
            format!("this impl of `{trait_name}` overlaps with another impl"),
            "Remove one of the impls, or narrow its types so they cannot both apply.",
        ));
    }
}
