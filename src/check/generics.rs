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
use crate::traits::solve::{Selection, Solver};
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

    /// True for lang traits whose last input defaults to Self
    /// (`PartialEq<Rhs = Self>`, the binary operators).
    pub fn input_defaults_to_self(&self, def: DefId) -> bool {
        [
            self.partial_eq,
            self.partial_ord,
            self.add,
            self.sub,
            self.mul,
            self.div,
            self.rem,
            self.bit_and,
            self.bit_or,
            self.bit_xor,
            self.shl,
            self.shr,
        ]
        .contains(&def)
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
/// Inference variable ids at or above this base in a resolved
/// signature type are `_` markers from `resolve_scoped`, which
/// the checker replaces with real body variables on sight.
pub const INFER_MARKER_BASE: u32 = 1 << 29;

#[derive(Clone, Debug, Default)]
pub struct Scope {
    /// Type parameter name to index in the item's `Generics`.
    pub type_params: Vec<(Sym, u32)>,
    /// Const parameter name to index in the item's `Generics`.
    pub const_params: Vec<(Sym, u32)>,
    pub self_ty: Option<Ty>,
    pub assoc_srcs: Vec<AssocSrc>,
    /// Parameter names to their types in this scope instance:
    /// `Param` types in a template, concrete types in an
    /// instance. `T::assoc` paths resolve through this.
    pub param_tys: Vec<(Sym, Ty)>,
    /// When set, `_` in a written type resolves to a marker
    /// inference variable (body annotations). The counter holds
    /// the next marker id, from `INFER_MARKER_BASE`. An atomic
    /// behind an `Arc` keeps `Program` shareable across the
    /// parallel body checks.
    pub infer_cell: Option<std::sync::Arc<std::sync::atomic::AtomicU32>>,
}

impl Scope {
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
            AstArg::Const(e) => out.push(GenericArg::Const(resolve_const_arg(ast, interner, known, tys, scope, *e, span)?)),
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
fn resolve_const_arg(
    ast: &Ast,
    interner: &Interner,
    known: &Known,
    tys: &mut impl TyIntern,
    scope: &Scope,
    e: ast::ExprId,
    span: Span,
) -> Result<ConstId, Diag> {
    match ast.expr(e) {
        ast::Expr::Path(segs) if segs.len() == 1 => {
            if let Some(&(_, i)) = scope.const_params.iter().find(|(n, _)| *n == segs[0].name) {
                return Ok(tys.intern_const(ConstKind::Param(i)));
            }
            // A named const item evaluates like the literal forms below.
            match crate::check::collect::eval_array_len(ast, interner, known, e) {
                Some(v) => Ok(tys.intern_const(ConstKind::Int(v))),
                None => Err(Diag::new(
                    "L0110",
                    span,
                    "const argument must be a literal or a const parameter",
                    "Use a literal such as `3`.",
                )),
            }
        }
        ast::Expr::Bool(b) => Ok(tys.intern_const(ConstKind::Bool(*b))),
        ast::Expr::Char(c) => Ok(tys.intern_const(ConstKind::Char(*c))),
        _ => match crate::check::collect::eval_array_len(ast, interner, known, e) {
            Some(v) => Ok(tys.intern_const(ConstKind::Int(v))),
            None => Err(Diag::new("L0110", span, "const argument must be a constant integer", "Write a literal such as `3`.")),
        },
    }
}

/// The trait a written trait path names, by its last segment:
/// user traits first, then lang traits. `std::` and `core::`
/// prefixes are accepted and ignored, as type paths do today.
pub(crate) fn trait_def_of_path(
    cx: &ResolveCx,
    interner: &Interner,
    known: &Known,
    segs: &[ast::PathSeg],
    span: Span,
) -> Result<DefId, Diag> {
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
                    AstArg::Const(e) => inputs.push(GenericArg::Const(resolve_const_arg(ast, interner, known, tys, scope, *e, span)?)),
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
                            ast::BindingKind::EqConst(e) => {
                                GenericArg::Const(resolve_const_arg(ast, interner, known, tys, scope, *e, *bspan)?)
                            }
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
    // Lang traits with a `Rhs = Self` default (the comparison and
    // binary operator families) accept the input omitted.
    let mut input_args = input_args;
    if input_args.len() + 1 == n_inputs && cx.lang.input_defaults_to_self(trait_def) {
        input_args.push(GenericArg::Ty(self_ty));
    }
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
            let n = resolve_const_arg(ast, interner, known, tys, scope, *len, span)?;
            Ok(tys.intern(TyKind::Array(e, n)))
        }
        TyExpr::Ptr { mutable, inner } => {
            let e = resolve_scoped(ast, interner, known, cx, tys, *inner, scope)?;
            Ok(tys.intern(TyKind::RawPtr(Mut::from_bool(*mutable), e)))
        }
        TyExpr::Infer => match &scope.infer_cell {
            Some(cell) => {
                let id = cell.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                Ok(tys.intern(TyKind::Infer(InferId(id, InferKind::General))))
            }
            None => Err(not_yet("L0602", span, "inferred types (`_`) in signatures")),
        },
        TyExpr::ImplTrait { .. } => Err(not_yet("L0602", span, "`impl Trait` types in this position")),
        TyExpr::Dyn { bounds, .. } => resolve_dyn(ast, interner, known, cx, tys, scope, bounds, span),
        TyExpr::FnPtr { qual, inputs, variadic, ret, .. } => {
            if *variadic || qual.is_unsafe || qual.is_async || qual.is_const || qual.abi.is_some() {
                return Err(not_yet("L0602", span, "qualified or variadic function pointer types"));
            }
            let mut ins = Vec::with_capacity(inputs.len());
            for p in inputs {
                ins.push(resolve_scoped(ast, interner, known, cx, tys, p.ty, scope)?);
            }
            let out = match ret {
                Some(r) => resolve_scoped(ast, interner, known, cx, tys, *r, scope)?,
                None => UNIT,
            };
            let inputs = tys.intern_tys(&ins);
            let sig = tys.intern_sig(Binder::plain(FnSig { inputs, output: out, is_unsafe: false, extern_c: false }));
            Ok(tys.intern(TyKind::FnPtr(sig)))
        }
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
        if let Some((_, t)) = scope.param_tys.iter().find(|(n, _)| *n == name) {
            if seg.has_args() {
                return Err(Diag::new("L0110", span, "a type parameter takes no generic arguments", "Remove the `<...>` part."));
            }
            return Ok(*t);
        }
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
    if name == known.f32 {
        return no_generics(tys.float_ty(FloatTy::F32));
    }
    if name == known.f64 {
        return no_generics(tys.float_ty(FloatTy::F64));
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
    if ["HashMap", "HashSet", "BTreeMap", "Result", "Box", "Rc", "Arc", "RefCell", "Cell"].contains(&n) {
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
    build_generics_shifted(ast, interner, known, cx, tys, g, w, 0, &Scope::default(), errs)
}

/// `build_generics` with parameter indexes shifted by `shift`
/// (a trait's synthetic `Self` at 0, or an impl's parameters
/// before a method's own). `seed` is the enclosing scope (an
/// impl's or trait's parameters): bounds on these parameters
/// may name the seed's parameters, so pass 2 resolves through
/// seed ++ own. The returned scope holds only the own
/// parameters; callers merge as before.
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
    seed: &Scope,
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
    // Resolution runs through the seed ++ own scope (`rscope`);
    // the returned `scope` keeps only the own parameters.
    let mut rscope = seed.clone();
    rscope.type_params.extend(scope.type_params.iter().copied());
    rscope.const_params.extend(scope.const_params.iter().copied());
    rscope.param_tys.extend(scope.type_params.iter().map(|&(n, i)| (n, tys.intern(TyKind::Param(ParamId(i))))));
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
                bound_predicates(ast, interner, known, cx, tys, &rscope, lhs, b, &mut predicates, &mut relaxed, errs);
            }
            scope.assoc_srcs = assoc_srcs_of(cx, tys, &predicates);
            rscope.assoc_srcs.clone_from(&seed.assoc_srcs);
            rscope.assoc_srcs.extend(scope.assoc_srcs.iter().cloned());
        }
    }
    for pred in &w.preds {
        match pred {
            ast::WherePred::Lifetime { lt, .. } => errs.push(lifetime_diag(lt.span)),
            ast::WherePred::Type { ty, bounds, .. } => match resolve_scoped(ast, interner, known, cx, tys, *ty, &rscope) {
                Ok(lhs) => {
                    for b in bounds {
                        bound_predicates(ast, interner, known, cx, tys, &rscope, lhs, b, &mut predicates, &mut relaxed, errs);
                    }
                    scope.assoc_srcs = assoc_srcs_of(cx, tys, &predicates);
                    rscope.assoc_srcs.clone_from(&seed.assoc_srcs);
                    rscope.assoc_srcs.extend(scope.assoc_srcs.iter().cloned());
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
    scope.param_tys = type_param_tys
        .iter()
        .map(|(idx, t)| {
            let name = scope.type_params.iter().find(|(_, i)| i == idx).map_or(Sym(0), |(n, _)| *n);
            (name, *t)
        })
        .collect();
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
    let (mut generics, mut scope) = build_generics_shifted(ast, interner, known, cx, tys, g, w, 1, &Scope::default(), errs);
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

/// One closure template or instance fn: the AST closure
/// expression whose body it checks and lowers. The fn's generics
/// are the enclosing fn's generics followed by one type
/// parameter per closure parameter and one for the return type,
/// so a closure instance key carries its whole signature.
#[derive(Clone, Copy, Debug)]
pub struct ClosureFn {
    pub expr: crate::ast::ExprId,
}

/// One materialized fn instance: its template and concrete args
/// (combined parent+own order). Lowering reads `template_local`
/// today; the rest is the instance's identity for slot and
/// cache keys, kept with the record it belongs to.
#[allow(dead_code)]
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
    /// User traits written `unsafe trait`: their impls must be
    /// `unsafe impl`, and no other impl may be.
    pub trait_unsafe: FxMap<DefId, bool>,
    /// Associated consts of user traits: the written type (over
    /// the trait's params) and whether a default value is given.
    pub trait_assoc_consts: FxMap<DefId, (Ty, bool)>,
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
    /// Closure fns (templates and their instances) by local id.
    pub closure_fns: FxMap<LocalDefId, ClosureFn>,
    /// The closure template fn for each closure expression.
    pub closure_by_expr: FxMap<crate::ast::ExprId, LocalDefId>,
    /// The closure template fn for each closure def (the def a
    /// `TyKind::Closure` names).
    pub closure_by_def: FxMap<DefId, LocalDefId>,
    pub instance_by_key: FxMap<(DefId, ArgsId), LocalDefId>,
    /// Abstract (template-check) instances by the same key.
    pub abstract_by_key: FxMap<(DefId, ArgsId), LocalDefId>,
    /// Inherent method templates by (Adt template def, name), in
    /// registration order; disjoint Self patterns may share a name.
    pub inherent_methods: FxMap<(DefId, Sym), Vec<LocalDefId>>,
    /// Each inherent method's impl Self pattern and impl generics,
    /// for the inherent overlap check in `finish_collect`.
    pub inherent_self_pats: FxMap<LocalDefId, (Ty, Generics)>,
    /// Trait defs that declare a method of this name.
    pub traits_by_method: FxMap<Sym, Vec<DefId>>,
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
            trait_unsafe: FxMap::default(),
            trait_assoc_consts: FxMap::default(),
            adt_info: Vec::new(),
            adt_generics: Vec::new(),
            adt_envs: Vec::new(),
            adt_scopes: Vec::new(),
            adt_instance_of: Vec::new(),
            fn_templates: Vec::new(),
            fn_scopes: Vec::new(),
            fn_class: Vec::new(),
            instances: FxMap::default(),
            closure_fns: FxMap::default(),
            closure_by_expr: FxMap::default(),
            closure_by_def: FxMap::default(),
            instance_by_key: FxMap::default(),
            abstract_by_key: FxMap::default(),
            inherent_methods: FxMap::default(),
            inherent_self_pats: FxMap::default(),
            traits_by_method: FxMap::default(),
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
        for (_, mname) in &rec.methods {
            p.gx.traits_by_method.entry(*mname).or_default().push(rec.def);
        }
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
        for f in &tdef.fns {
            p.gx.traits_by_method.entry(f.name).or_default().push(def);
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
        if tdef.is_unsafe {
            p.gx.trait_unsafe.insert(trait_def, true);
        }
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
                if at_default.is_some() {
                    // Associated type defaults are unstable in
                    // rustc (E0658); rule zero rejects them.
                    errs.push(not_yet("L0621", at.span, "associated type defaults"));
                }
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
        // Associated consts: resolve and store the type for impl
        // validation. The values ride the const evaluator when a
        // use needs them.
        let const_parts: Vec<(Sym, ast::TyId, bool)> = {
            let ast::ItemKind::Trait(tdef) = &p.ast.items[item_i].kind else { unreachable!() };
            tdef.consts.iter().map(|ac| (ac.name, ac.ty, ac.default.is_some())).collect()
        };
        for (ac_name, ty, has_default) in const_parts {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            match resolve_scoped(p.ast, p.interner, p.known, &cx, &mut p.tys, ty, &scope) {
                Ok(t) => {
                    if let Some(assoc) = p.gx.index.trait_record(trait_def).and_then(|r| r.assoc_by_name(ac_name)) {
                        p.gx.trait_assoc_consts.insert(assoc, (t, has_default));
                    }
                }
                Err(d) => errs.push(d),
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
                build_generics_shifted(p.ast, p.interner, p.known, &cx, &mut p.tys, &fdef.generics, &fdef.where_clause, shift, &scope, errs)
            };
            let mut combined = generics.clone();
            combined.params.extend(own_generics.params.iter().cloned());
            combined.predicates.extend(own_generics.predicates.iter().copied());
            let mut mscope = scope.clone();
            mscope.type_params.extend(own_scope.type_params.iter().copied());
            mscope.const_params.extend(own_scope.const_params.iter().copied());
            mscope.param_tys.extend(own_scope.param_tys.iter().copied());
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
    // Associated consts: presence is required the same way (a
    // trait default covers a missing one), and a written const
    // must have the trait's type for it. Their values are
    // const-evaluated at use sites.
    for ac in &imp.consts {
        let Some(assoc) = rec.assoc_by_name(ac.name) else {
            errs.push(Diag::new(
                "L0102",
                ac.name_span,
                format!("trait has no associated const named `{}`", p.name(ac.name)),
                "Check the spelling against the trait definition.",
            ));
            continue;
        };
        if let Some(&(want, _)) = p.gx.trait_assoc_consts.get(&assoc) {
            let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
            match resolve_scoped(p.ast, p.interner, p.known, &cx, &mut p.tys, ac.ty, scope) {
                Ok(got) => {
                    let args: Vec<GenericArg> = p.tys.args(tr.args).to_vec();
                    let want = subst(&mut p.tys, want, &args);
                    if got != want {
                        errs.push(Diag::new(
                            "L0110",
                            ac.name_span,
                            format!("associated const `{}` has a different type than the trait declares", p.name(ac.name)),
                            "Match the type in the trait definition.",
                        ));
                    }
                }
                Err(diag) => errs.push(diag),
            }
        }
    }
    for &(assoc, cname, is_type) in &rec.assoc_items {
        if is_type || imp.consts.iter().any(|ac| ac.name == cname) {
            continue;
        }
        // Lang traits store no const types here; only user-trait
        // consts (recorded above) can be required.
        if p.gx.trait_assoc_consts.get(&assoc).is_some_and(|&(_, d)| !d) {
            errs.push(Diag::new(
                "L0110",
                imp.span,
                format!("the impl is missing the associated const `{}`", p.name(cname)),
                "Add the const to the impl.",
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
    check_impl_rules(p, imp, &impl_generics, self_pat, tr, errs);
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
        validate_method_sig(p, &tmpl, local, tr, impl_parent_n, &assoc_tys, imp.span, errs);
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

/// True when const parameter `idx` occurs in a type (in an
/// array length or a const argument).
fn ty_uses_const_param(tys: &impl TyIntern, t: Ty, idx: u32) -> bool {
    let in_const = |c: ConstId| matches!(tys.const_kind(c), ConstKind::Param(p) if p == idx);
    let in_args = |a: ArgsId| {
        tys.args(a).iter().any(|g| match g {
            GenericArg::Ty(e) => ty_uses_const_param(tys, *e, idx),
            GenericArg::Const(c) => in_const(*c),
            GenericArg::Lifetime(_) => false,
        })
    };
    match tys.kind(t) {
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) => ty_uses_const_param(tys, e, idx),
        TyKind::Array(e, n) => in_const(n) || ty_uses_const_param(tys, e, idx),
        TyKind::Tuple(ts) => tys.tys_of(ts).iter().any(|&e| ty_uses_const_param(tys, e, idx)),
        TyKind::Adt(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) | TyKind::Projection(_, a) => in_args(a),
        _ => false,
    }
}

/// The header rules of one trait impl that are not about its
/// items: `Sized` cannot be implemented, `unsafe` must match
/// between trait and impl, a `Drop` impl must cover the Adt as
/// written with no extra bounds, and every impl parameter must
/// be constrained by the trait ref (Self or a trait input).
fn check_impl_rules(p: &mut Program, imp: &ast::ImplDef, generics: &Generics, self_pat: Ty, tr: TraitRef, errs: &mut Vec<Diag>) {
    let lang = p.gx.lang;
    if tr.def == lang.sized {
        errs.push(Diag::new(
            "L0110",
            imp.span,
            "the `Sized` trait cannot be implemented in user code",
            "Remove the impl; sizedness is automatic.",
        ));
    }
    let trait_unsafe = p.gx.trait_unsafe.get(&tr.def).copied().unwrap_or(false) || tr.def == lang.send || tr.def == lang.sync;
    if trait_unsafe && !imp.is_unsafe {
        errs.push(Diag::new(
            "L0110",
            imp.span,
            "this trait is unsafe, so its impl must be `unsafe impl`",
            "Write `unsafe impl`, after checking the trait's contract holds.",
        ));
    } else if !trait_unsafe && imp.is_unsafe {
        errs.push(Diag::new(
            "L0110",
            imp.span,
            "this trait is not unsafe, so its impl cannot be `unsafe impl`",
            "Remove `unsafe` from the impl.",
        ));
    }
    // Every parameter must be constrained by the header: it
    // occurs in the trait ref, or it is the value of an
    // associated type binding in the trait ref or a where
    // clause (`Item = U`). Occurring only in an associated
    // type definition, or only bounded in a where clause, does
    // not constrain it (rustc E0207).
    let mut ref_tys: Vec<Ty> = p.tys.args(tr.args).iter().filter_map(|g| g.as_ty()).collect();
    ref_tys.extend(p.tys.bindings(tr.bindings).iter().filter_map(|(_, g)| g.as_ty()));
    for pred in &generics.predicates {
        match pred {
            Predicate::AssocEq(b) => ref_tys.push(b.value.ty),
            Predicate::Trait(b) => ref_tys.extend(p.tys.bindings(b.value.bindings).iter().filter_map(|(_, g)| g.as_ty())),
            _ => {}
        }
    }
    for (i, param) in generics.params.iter().enumerate() {
        let used = match param.kind {
            ParamKind::Type => ref_tys.iter().any(|&t| ty_uses_param(&p.tys, t, i as u32)),
            ParamKind::Const(_) => ref_tys.iter().any(|&t| ty_uses_const_param(&p.tys, t, i as u32)),
            ParamKind::Lifetime => continue,
        };
        if !used {
            errs.push(Diag::new(
                "L0110",
                param.span,
                format!(
                    "the {} parameter `{}` is not used in the impl header",
                    if matches!(param.kind, ParamKind::Const(_)) { "const" } else { "type" },
                    p.name(param.name)
                ),
                "Use it in the Self type or a trait input, or remove it.",
            ));
        }
    }
    if tr.def == lang.drop {
        check_drop_impl(p, imp, generics, self_pat, errs);
    }
}

/// The `Drop` header rules: the Self type must be the Adt
/// applied to its own parameters in order (no `Drop for
/// G<u8>`), and the impl may not require more bounds than the
/// Adt itself declares (rustc E0366 and E0367).
fn check_drop_impl(p: &Program, imp: &ast::ImplDef, generics: &Generics, self_pat: Ty, errs: &mut Vec<Diag>) {
    let TyKind::Adt(def, args) = p.tys.kind(self_pat) else {
        errs.push(Diag::new("L0110", imp.span, "`Drop` can only be implemented for a struct or enum", "Implement `Drop` on the type itself."));
        return;
    };
    let Some(adt_idx) = p.gx.adt_info.iter().position(|&(d, _)| d == def) else { return };
    let n_params = p.gx.adt_generics[adt_idx].params.len();
    let written: Vec<GenericArg> = p.tys.args(args).to_vec();
    let in_order = written.len() == n_params
        && written.iter().enumerate().all(|(i, g)| match g {
            GenericArg::Ty(t) => matches!(p.tys.kind(*t), TyKind::Param(pid) if pid.0 as usize == i),
            GenericArg::Const(c) => matches!(p.tys.const_kind(*c), ConstKind::Param(cp) if cp as usize == i),
            GenericArg::Lifetime(_) => true,
        });
    if !in_order {
        errs.push(Diag::new(
            "L0110",
            imp.span,
            "`Drop` must be implemented for the type with its own parameters, not one instance of it",
            "Write `impl<T> Drop for Type<T>` with the type's own parameter list.",
        ));
        return;
    }
    let adt_preds: Vec<TraitRef> = p.gx.adt_generics[adt_idx]
        .predicates
        .iter()
        .filter_map(|p2| match p2 {
            Predicate::Trait(b) => Some(b.value),
            _ => None,
        })
        .collect();
    for pred in &generics.predicates {
        let Predicate::Trait(b) = pred else { continue };
        if b.value.def == p.gx.lang.sized {
            continue;
        }
        if !adt_preds.contains(&b.value) {
            errs.push(Diag::new(
                "L0110",
                imp.span,
                "a `Drop` impl cannot require bounds the type does not declare",
                "Move the bound to the type definition, or remove it from the impl.",
            ));
            return;
        }
    }
}

/// Rewrites projections of this impl's associated types to the
/// impl's bindings (in impl parameter space). Used when the
/// solver cannot normalize them because the Self type is still
/// a parameter.
fn rewrite_impl_projections(p: &mut Program, t: Ty, assoc_tys: &[(DefId, Ty)]) -> Ty {
    match p.tys.kind(t) {
        TyKind::Projection(assoc, _) => match assoc_tys.iter().find(|(d, _)| *d == assoc.0) {
            Some((_, bound)) => rewrite_impl_projections(p, *bound, assoc_tys),
            None => t,
        },
        TyKind::Ref(r, m, e) => {
            let e = rewrite_impl_projections(p, e, assoc_tys);
            p.tys.intern(TyKind::Ref(r, m, e))
        }
        TyKind::Adt(d, a) => {
            let raw: Vec<GenericArg> = p.tys.args(a).to_vec();
            let out: Vec<GenericArg> = raw
                .iter()
                .map(|&g| match g {
                    GenericArg::Ty(e) => GenericArg::Ty(rewrite_impl_projections(p, e, assoc_tys)),
                    other => other,
                })
                .collect();
            let a = p.tys.intern_args(&out);
            p.tys.intern(TyKind::Adt(d, a))
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = p.tys.tys_of(ts).to_vec();
            let out: Vec<Ty> = elems.iter().map(|&e| rewrite_impl_projections(p, e, assoc_tys)).collect();
            let ts = p.tys.intern_tys(&out);
            p.tys.intern(TyKind::Tuple(ts))
        }
        TyKind::Slice(e) => {
            let e = rewrite_impl_projections(p, e, assoc_tys);
            p.tys.intern(TyKind::Slice(e))
        }
        TyKind::Array(e, n) => {
            let e = rewrite_impl_projections(p, e, assoc_tys);
            p.tys.intern(TyKind::Array(e, n))
        }
        _ => t,
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
    assoc_tys: &[(DefId, Ty)],
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
    let want_params: Vec<Ty> = tmpl
        .params
        .iter()
        .map(|&t| {
            let t = subst(&mut p.tys, t, &subst_args);
            rewrite_impl_projections(p, t, assoc_tys)
        })
        .collect();
    let want_ret = {
        let t = subst(&mut p.tys, tmpl.ret, &subst_args);
        rewrite_impl_projections(p, t, assoc_tys)
    };
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
    // Closures: one Fn/FnMut/FnOnce (plus Copy/Clone) record per
    // closure template. The Self pattern is the closure type over
    // the template's parameters; the Fn input is the tuple of the
    // signature parameters and Output is the return parameter.
    // Only non-capturing closures exist in this slice, and those
    // always implement all three Fn traits.
    let closures: Vec<(DefId, LocalDefId)> = p.gx.closure_by_def.iter().map(|(&d, &l)| (d, l)).collect();
    for (def, local) in closures {
        let Some(Some(tmpl)) = p.gx.fn_templates.get(local.0 as usize).cloned() else { continue };
        let mut lt = 0u32;
        let pat_args: Vec<GenericArg> = tmpl
            .generics
            .params
            .iter()
            .enumerate()
            .map(|(i, pd)| match pd.kind {
                ParamKind::Type => GenericArg::Ty(p.tys.intern(TyKind::Param(ParamId(i as u32)))),
                ParamKind::Lifetime => {
                    let a = GenericArg::Lifetime(Region::Param(lt));
                    lt += 1;
                    a
                }
                ParamKind::Const(_) => GenericArg::Const(p.tys.intern_const(ConstKind::Param(i as u32))),
            })
            .collect();
        let args_id = p.tys.intern_args(&pat_args);
        let self_pat = p.tys.intern(TyKind::Closure(def, args_id));
        // The signature pattern is the template's own FnInfo:
        // annotated types are fixed there, unwritten ones are
        // the signature parameters.
        let (inputs, output) = {
            let info = p.fn_info(local);
            (info.params.clone(), info.ret)
        };
        let ts = p.tys.intern_tys(&inputs);
        let tuple = p.tys.intern(TyKind::Tuple(ts));
        let generics = Generics { parent: None, params: tmpl.generics.params.clone(), predicates: Vec::new() };
        for tr in [lang.fn_, lang.fn_mut, lang.fn_once] {
            let assoc: Vec<(DefId, Ty)> = lang.output_of(tr).map(|o| vec![(o, output)]).unwrap_or_default();
            insert_synthetic(p, &mut ordinal, tr, self_pat, &[tuple], generics.clone(), assoc, Synthetic::Lang, false, span);
        }
        for tr in [lang.copy, lang.clone] {
            insert_synthetic(p, &mut ordinal, tr, self_pat, &[], generics.clone(), Vec::new(), Synthetic::Lang, false, span);
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
        // Operator traits on scalars, for associated-type
        // normalization (`<i64 as Add>::Output`): the operations
        // themselves stay on the builtin scalar path.
        for (tr, two) in [
            (lang.add, true),
            (lang.sub, true),
            (lang.mul, true),
            (lang.div, true),
            (lang.rem, true),
            (lang.bit_and, true),
            (lang.bit_or, true),
            (lang.bit_xor, true),
            (lang.shl, true),
            (lang.shr, true),
            (lang.neg, false),
            (lang.not, false),
        ] {
            if let Some(out) = lang.output_of(tr) {
                let rest: &[Ty] = if two { &[t] } else { &[] };
                insert_synthetic(p, &mut ordinal, tr, t, rest, g0.clone(), vec![(out, t)], Synthetic::Lang, false, span);
            }
        }
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

/// An owned snapshot of a type from any store (see `lift_ty`).
/// A body overlay borrows the global store, so a type cannot be
/// lifted by walking it while interning into the globals; the
/// snapshot breaks that borrow.
enum OwnedTy {
    Leaf(TyKind),
    Ref(Region, Mut, Box<OwnedTy>),
    RawPtr(Mut, Box<OwnedTy>),
    Slice(Box<OwnedTy>),
    Array(Box<OwnedTy>, ConstKind),
    Tuple(Vec<OwnedTy>),
    Adt(DefId, Vec<OwnedArg>),
    FnDef(DefId, Vec<OwnedArg>),
    Closure(DefId, Vec<OwnedArg>),
    Opaque(DefId, Vec<OwnedArg>),
    Projection(AssocId, Vec<OwnedArg>),
    FnPtr(Binder<FnSig>, Vec<OwnedTy>, Box<OwnedTy>),
    Dyn(Binder<Vec<OwnedArg>>, Vec<(u32, Vec<OwnedArg>)>, AutoTraits, Region),
}

enum OwnedArg {
    Ty(OwnedTy),
    Lifetime(Region),
    Const(ConstKind),
}

/// Copies one body type out of its store, or None when it still
/// holds an inference variable or the error type (a variable the
/// zonk could not resolve): such a type names no instance, and the
/// body that made it has an error report of its own.
fn snapshot_ty(src: &dyn TyIntern, t: Ty) -> Option<OwnedTy> {
    Some(match src.kind(t) {
        TyKind::Infer(_) | TyKind::Error => return None,
        TyKind::Ref(r, m, e) => OwnedTy::Ref(r, m, Box::new(snapshot_ty(src, e)?)),
        TyKind::RawPtr(m, e) => OwnedTy::RawPtr(m, Box::new(snapshot_ty(src, e)?)),
        TyKind::Slice(e) => OwnedTy::Slice(Box::new(snapshot_ty(src, e)?)),
        TyKind::Array(e, n) => match src.const_kind(n) {
            ConstKind::Infer(_) => return None,
            k => OwnedTy::Array(Box::new(snapshot_ty(src, e)?), k),
        },
        TyKind::Tuple(ts) => {
            let mut out = Vec::new();
            for e in src.tys_of(ts).to_vec() {
                out.push(snapshot_ty(src, e)?);
            }
            OwnedTy::Tuple(out)
        }
        TyKind::Adt(d, a) => OwnedTy::Adt(d, snapshot_args(src, a)?),
        TyKind::FnDef(d, a) => OwnedTy::FnDef(d, snapshot_args(src, a)?),
        TyKind::Closure(d, a) => OwnedTy::Closure(d, snapshot_args(src, a)?),
        TyKind::Opaque(d, a) => OwnedTy::Opaque(d, snapshot_args(src, a)?),
        TyKind::Projection(d, a) => OwnedTy::Projection(d, snapshot_args(src, a)?),
        TyKind::FnPtr(sig) => {
            let b = src.sig(sig);
            let mut inputs = Vec::new();
            for e in src.tys_of(b.value.inputs).to_vec() {
                inputs.push(snapshot_ty(src, e)?);
            }
            OwnedTy::FnPtr(b, inputs, Box::new(snapshot_ty(src, b.value.output)?))
        }
        TyKind::Dyn(b, r) => {
            let bounds = src.dyn_bounds(b).clone();
            let principal: Binder<Vec<OwnedArg>> = match bounds.principal {
                Some(pr) => Binder { count: pr.count, value: snapshot_args(src, pr.value.args)? },
                None => Binder { count: 0, value: Vec::new() },
            };
            let mut supers = Vec::new();
            for sup in bounds.supertraits.iter() {
                supers.push((sup.count, snapshot_args(src, sup.value.args)?));
            }
            OwnedTy::Dyn(principal, supers, bounds.auto, r)
        }
        kind => OwnedTy::Leaf(kind),
    })
}

fn snapshot_args(src: &dyn TyIntern, a: ArgsId) -> Option<Vec<OwnedArg>> {
    let mut out = Vec::new();
    for g in src.args(a).to_vec() {
        out.push(match g {
            GenericArg::Ty(e) => OwnedArg::Ty(snapshot_ty(src, e)?),
            GenericArg::Const(c) => match src.const_kind(c) {
                ConstKind::Infer(_) => return None,
                k => OwnedArg::Const(k),
            },
            GenericArg::Lifetime(r) => OwnedArg::Lifetime(r),
        });
    }
    Some(out)
}

fn build_owned_ty(p: &mut Program, t: &OwnedTy) -> Ty {
    match t {
        OwnedTy::Leaf(kind) => p.tys.intern(*kind),
        OwnedTy::Ref(r, m, e) => {
            let e = build_owned_ty(p, e);
            p.tys.intern(TyKind::Ref(*r, *m, e))
        }
        OwnedTy::RawPtr(m, e) => {
            let e = build_owned_ty(p, e);
            p.tys.intern(TyKind::RawPtr(*m, e))
        }
        OwnedTy::Slice(e) => {
            let e = build_owned_ty(p, e);
            p.tys.intern(TyKind::Slice(e))
        }
        OwnedTy::Array(e, k) => {
            let e = build_owned_ty(p, e);
            let n = p.tys.intern_const(*k);
            p.tys.intern(TyKind::Array(e, n))
        }
        OwnedTy::Tuple(elems) => {
            let out: Vec<Ty> = elems.iter().map(|e| build_owned_ty(p, e)).collect();
            let ts = p.tys.intern_tys(&out);
            p.tys.intern(TyKind::Tuple(ts))
        }
        OwnedTy::Adt(d, a) => {
            let a = build_owned_args(p, a);
            p.tys.intern(TyKind::Adt(*d, a))
        }
        OwnedTy::FnDef(d, a) => {
            let a = build_owned_args(p, a);
            p.tys.intern(TyKind::FnDef(*d, a))
        }
        OwnedTy::Closure(d, a) => {
            let a = build_owned_args(p, a);
            p.tys.intern(TyKind::Closure(*d, a))
        }
        OwnedTy::Opaque(d, a) => {
            let a = build_owned_args(p, a);
            p.tys.intern(TyKind::Opaque(*d, a))
        }
        OwnedTy::Projection(d, a) => {
            let a = build_owned_args(p, a);
            p.tys.intern(TyKind::Projection(*d, a))
        }
        OwnedTy::FnPtr(b, inputs, output) => {
            let out: Vec<Ty> = inputs.iter().map(|e| build_owned_ty(p, e)).collect();
            let inputs_id = p.tys.intern_tys(&out);
            let output = build_owned_ty(p, output);
            let sig = p.tys.intern_sig(Binder { count: b.count, value: FnSig { inputs: inputs_id, output, ..b.value } });
            p.tys.intern(TyKind::FnPtr(sig))
        }
        OwnedTy::Dyn(principal, supers, auto, r) => {
            // Dyn bounds from another store lose their bindings
            // here (only args are snapshotted); dyn types in
            // instance args are outside this wave's mono subset,
            // and the principal trait identity is not recoverable
            // from args alone, so this arm is unreachable in
            // practice and answers the error type.
            let _ = (principal, supers, auto, r);
            ERROR
        }
    }
}

fn build_owned_args(p: &mut Program, args: &[OwnedArg]) -> ArgsId {
    let out: Vec<GenericArg> = args
        .iter()
        .map(|a| match a {
            OwnedArg::Ty(e) => GenericArg::Ty(build_owned_ty(p, e)),
            OwnedArg::Lifetime(r) => GenericArg::Lifetime(*r),
            OwnedArg::Const(k) => GenericArg::Const(p.tys.intern_const(*k)),
        })
        .collect();
    p.tys.intern_args(&out)
}

/// Lifts one type from a body-local store into the program's
/// global store (the owned type store lift of ARCH 2.1, in its
/// structural form). None when the type still contains an
/// inference variable (the request that named it is not
/// concrete yet).
// Used by ensure_adt_instances_in below; both are kept for the
// cross-store mono wiring that lands after this increment.
#[allow(dead_code)]
pub fn lift_ty(p: &mut Program, src: &dyn TyIntern, t: Ty) -> Option<Ty> {
    let owned = snapshot_ty(src, t)?;
    Some(build_owned_ty(p, &owned))
}

/// Finds the global type structurally equal to a body-local type.
fn find_global_ty(p: &Program, src: &dyn TyIntern, t: Ty) -> Option<Ty> {
    let g = &p.tys;
    Some(match src.kind(t) {
        TyKind::Ref(r, m, e) => g.get(TyKind::Ref(r, m, find_global_ty(p, src, e)?))?,
        TyKind::RawPtr(m, e) => g.get(TyKind::RawPtr(m, find_global_ty(p, src, e)?))?,
        TyKind::Slice(e) => g.get(TyKind::Slice(find_global_ty(p, src, e)?))?,
        TyKind::Array(e, n) => {
            let n = match src.const_kind(n) {
                ConstKind::Infer(_) => return None,
                k => g.consts_get(k)?,
            };
            g.get(TyKind::Array(find_global_ty(p, src, e)?, n))?
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = src.tys_of(ts).to_vec();
            let mut out = Vec::new();
            for e in elems {
                out.push(find_global_ty(p, src, e)?);
            }
            let ts = g.get_tys(&out)?;
            g.get(TyKind::Tuple(ts))?
        }
        TyKind::Adt(d, a) => {
            let raw: Vec<GenericArg> = src.args(a).to_vec();
            let mut out: Vec<GenericArg> = Vec::new();
            for gg in raw {
                out.push(match gg {
                    GenericArg::Ty(e) => GenericArg::Ty(find_global_ty(p, src, e)?),
                    GenericArg::Const(c) => match src.const_kind(c) {
                        ConstKind::Infer(_) => return None,
                        k => GenericArg::Const(g.consts_get(k)?),
                    },
                    other => other,
                });
            }
            let aid = g.get_args(&out)?;
            g.get(TyKind::Adt(d, aid))?
        }
        TyKind::Projection(d, a) => {
            let raw: Vec<GenericArg> = src.args(a).to_vec();
            let mut out: Vec<GenericArg> = Vec::new();
            for gg in raw {
                out.push(match gg {
                    GenericArg::Ty(e) => GenericArg::Ty(find_global_ty(p, src, e)?),
                    other => other,
                });
            }
            let aid = g.get_args(&out)?;
            g.get(TyKind::Projection(d, aid))?
        }
        kind => g.get(kind)?,
    })
}

/// The mono instance for one template and body-local args, as
/// lowering needs it. Compares candidate instance args (global)
/// against the lifted body args structurally.
pub fn instance_for(p: &Program, src: &dyn TyIntern, template: LocalDefId, args: &[GenericArg]) -> Option<LocalDefId> {
    let template_def = p.def_id(template);
    // Lift each arg by structural find; tuple args fall back to a
    // direct comparison against every instance of this template.
    let mut lifted: Vec<GenericArg> = Vec::new();
    for &g in args {
        match g {
            GenericArg::Ty(e) => lifted.push(GenericArg::Ty(find_global_ty(p, src, e)?)),
            other => lifted.push(other),
        }
    }
    for ((def, aid), local) in &p.gx.instance_by_key {
        if *def == template_def && p.tys.args(*aid) == lifted.as_slice() {
            return Some(*local);
        }
    }
    None
}

/// One opaque abstract type: a fresh unit Adt standing for one
/// type parameter in a template check. Its derives come from the
/// parameter's bounds, so the structural derive queries answer
/// for it exactly what the bounds promise.
fn opaque_adt(p: &mut Program, key: (DefId, u32), bounds: &[DefId], memo: &mut FxMap<(DefId, u32), AdtId>, ordinal: &mut u32) -> Ty {
    if let Some(&a) = memo.get(&key) {
        return p.tys.adt_ty(a);
    }
    let lang = p.gx.lang;
    let derives = crate::check::collect::Derives {
        debug: bounds.contains(&lang.debug),
        clone: bounds.contains(&lang.clone) || bounds.contains(&lang.copy),
        copy: bounds.contains(&lang.copy),
        partial_eq: bounds.contains(&lang.partial_eq) || bounds.contains(&lang.eq),
        eq: bounds.contains(&lang.eq),
        hash: bounds.contains(&lang.hash),
    };
    let id = AdtId(p.adts.len() as u32);
    let def = DefId {
        krate: p.krate,
        hash: crate::def::item_hash(p.stable_crate, &["<abstract>"], crate::def::DefKind::Adt, &format!("Opaque{}", *ordinal), 0),
    };
    *ordinal += 1;
    let name = p.interner.intern("Opaque");
    p.adts.push(crate::check::collect::AdtDef {
        name,
        is_enum: false,
        repr: crate::ty::layout::Repr::default(),
        variants: vec![crate::check::collect::Variant {
            name,
            shape: crate::check::collect::VariantShape::Unit,
            fields: Vec::new(),
            disc: 0,
        }],
        derives,
        span: Span::default(),
    });
    p.tys.register_adt(def, id);
    p.defs.insert_adt(
        def,
        id,
        crate::ty::defs::DefData::skeleton(crate::ty::defs::DefKind::Struct, None, name, crate::ty::defs::Vis::Priv, Span::default()),
    );
    p.gx.adt_info.push((def, 0));
    p.gx.adt_generics.push(Generics::default());
    p.gx.adt_envs.push(Vec::new());
    p.gx.adt_scopes.push(Scope::default());
    p.gx.adt_instance_of.push(None);
    memo.insert(key, id);
    p.tys.adt_ty(id)
}

/// The bounds on one parameter of a template, as trait defs.
fn param_bound_traits(env: &[Predicate], tys: &impl TyIntern, idx: u32) -> Vec<DefId> {
    let mut out = Vec::new();
    for pred in env {
        if let Predicate::Trait(b) = pred
            && tys.args(b.value.args)[0].as_ty().is_some_and(|t| matches!(tys.kind(t), TyKind::Param(p) if p.0 == idx))
        {
            out.push(b.value.def);
        }
    }
    out
}

/// A stub fn for one trait method on abstract types: the trait
/// method template substituted with the bound's trait ref,
/// projections replaced by the synthetic impl's assoc bindings
/// (or fresh opaques). Stubs carry signatures only; abstract
/// checks call them but never check or generate their bodies.
fn abstract_stub(
    p: &mut Program,
    method_def: DefId,
    trait_args: &[GenericArg],
    assoc_tys: &[(DefId, Ty)],
    memo: &mut FxMap<(DefId, ArgsId), LocalDefId>,
) -> LocalDefId {
    let args_id = p.tys.intern_args(trait_args);
    if let Some(&existing) = memo.get(&(method_def, args_id)) {
        return existing;
    }
    let tmpl = match p.gx.trait_methods.get(&method_def).cloned() {
        Some(t) => t,
        None => return lang_stub(p, method_def, trait_args, assoc_tys, memo, args_id),
    };
    // Substitute trait params, then renumber the method's own
    // params down to 0-based for the stub's own generics.
    let trait_n = trait_args.len();
    let mut full: Vec<GenericArg> = trait_args.to_vec();
    let own_n = tmpl.generics.params.len().saturating_sub(trait_n);
    for j in 0..own_n {
        let t = p.tys.intern(TyKind::Param(ParamId((trait_n + j) as u32)));
        full.push(GenericArg::Ty(t));
    }
    let subst_all = |p: &mut Program, t: Ty| -> Ty {
        let t = subst(&mut p.tys, t, &full);
        let t = rewrite_impl_projections(p, t, assoc_tys);
        // Renumber own params: Param(trait_n + j) -> Param(j).
        let remap: Vec<GenericArg> = (0..(trait_n + own_n) as u32)
            .map(|i| {
                let ni = if (i as usize) >= trait_n { i - trait_n as u32 } else { i };
                GenericArg::Ty(p.tys.intern(TyKind::Param(ParamId(ni))))
            })
            .collect();
        subst(&mut p.tys, t, &remap)
    };
    let params: Vec<Ty> = tmpl.params.iter().map(|&t| subst_all(p, t)).collect();
    let ret = subst_all(p, tmpl.ret);
    let own_generics =
        Generics { parent: None, params: tmpl.generics.params[trait_n.min(tmpl.generics.params.len())..].to_vec(), predicates: Vec::new() };
    let id = LocalDefId(p.fns.len() as u32);
    let def_id = DefId {
        krate: p.krate,
        hash: crate::def::item_hash(p.stable_crate, &["<abstract>"], crate::def::DefKind::Method, &format!("stub#{}", id.0), 0),
    };
    p.fn_defs.push(def_id);
    p.def_by_hash.entry(def_id.hash).or_insert(id);
    p.fns.push(crate::check::collect::FnInfo {
        name: tmpl.name,
        def: tmpl.def,
        owner: None,
        self_kind: tmpl.self_kind,
        params,
        ret,
        ret_borrows_from: tmpl.ret_borrows_from,
        is_const: tmpl.def.qual.is_const,
    });
    let is_template = !own_generics.params.is_empty();
    p.gx.fn_templates.push(if is_template { Some(FnTemplate { generics: own_generics, env: Vec::new() }) } else { None });
    p.gx.fn_scopes.push(FnScope::default());
    p.gx.fn_class.push(FnClass::Stub);
    memo.insert((method_def, args_id), id);
    id
}

/// A stub for one lang trait method (lang traits have no method
/// templates; the few signatures abstract checks call are built
/// here from the trait ref). Signatures use projections for the
/// assoc types, rewritten through the synthetic impl's bindings.
fn lang_stub(
    p: &mut Program,
    method_def: DefId,
    trait_args: &[GenericArg],
    assoc_tys: &[(DefId, Ty)],
    memo: &mut FxMap<(DefId, ArgsId), LocalDefId>,
    args_id: ArgsId,
) -> LocalDefId {
    let lang = p.gx.lang;
    let self_ty = trait_args[0].as_ty().unwrap_or(ERROR);
    let trait_def = p.gx.index.trait_of_method(method_def).unwrap_or(DefId::PLACEHOLDER);
    let proj = |p: &mut Program, assoc: DefId, args: &[GenericArg]| -> Ty {
        let a = p.tys.intern_args(args);
        let t = p.tys.intern(TyKind::Projection(AssocId(assoc), a));
        rewrite_impl_projections(p, t, assoc_tys)
    };
    let ref_of = |p: &mut Program, mutable: bool, t: Ty| p.tys.mk_ref(mutable, t);
    let (self_kind, params, ret): (ast::SelfKind, Vec<Ty>, Ty) = if trait_def == lang.iterator {
        let item = proj(p, lang.assoc_item, trait_args);
        let opt = p.tys.mk_option(item);
        (ast::SelfKind::RefMut, vec![ref_of(p, true, self_ty)], opt)
    } else if trait_def == lang.into_iterator {
        let into = proj(p, lang.assoc_into_iter, trait_args);
        (ast::SelfKind::Value, vec![self_ty], into)
    } else if trait_def == lang.clone {
        (ast::SelfKind::Ref, vec![ref_of(p, false, self_ty)], self_ty)
    } else if trait_def == lang.deref {
        let target = proj(p, lang.assoc_target, trait_args);
        let r = ref_of(p, false, target);
        (ast::SelfKind::Ref, vec![ref_of(p, false, self_ty)], r)
    } else if trait_def == lang.deref_mut {
        let target = proj(p, lang.assoc_target, trait_args);
        let r = ref_of(p, true, target);
        (ast::SelfKind::RefMut, vec![ref_of(p, true, self_ty)], r)
    } else if trait_def == lang.from {
        let input = trait_args.get(1).and_then(|g| g.as_ty()).unwrap_or(ERROR);
        (ast::SelfKind::Value, vec![input], self_ty)
    } else if trait_def == lang.default {
        (ast::SelfKind::Value, Vec::new(), self_ty)
    } else if trait_def == lang.drop {
        (ast::SelfKind::RefMut, vec![ref_of(p, true, self_ty)], UNIT)
    } else if lang.output_of(trait_def).is_some() {
        // Binary and unary operators and the Fn family: the
        // receiver form follows the std signatures closely
        // enough for abstract checking (by value for operators).
        let out = proj(p, lang.output_of(trait_def).unwrap(), trait_args);
        let rhs = trait_args.get(1).and_then(|g| g.as_ty()).unwrap_or(self_ty);
        (ast::SelfKind::Value, vec![self_ty, rhs], out)
    } else {
        (ast::SelfKind::Ref, vec![ref_of(p, false, self_ty)], UNIT)
    };
    // The stub's FnInfo needs an AST def; lang methods have none,
    // so point it at any existing one: stubs are never checked,
    // only their signatures are read. Use the first fn's def.
    let any_def = p.fns.first().map(|f| f.def).expect("a program with abstract checks has fns");
    let name =
        p.gx.index
            .trait_record(trait_def)
            .and_then(|r| r.methods.iter().find(|(d, _)| *d == method_def).map(|(_, n)| *n))
            .unwrap_or(Sym(0));
    let id = LocalDefId(p.fns.len() as u32);
    let def_id = DefId {
        krate: p.krate,
        hash: crate::def::item_hash(p.stable_crate, &["<abstract>"], crate::def::DefKind::Method, &format!("langstub#{}", id.0), 0),
    };
    p.fn_defs.push(def_id);
    p.def_by_hash.entry(def_id.hash).or_insert(id);
    p.fns.push(crate::check::collect::FnInfo {
        name,
        def: any_def,
        is_const: false,
        owner: None,
        self_kind: if trait_def == lang.from || trait_def == lang.default { None } else { Some(self_kind) },
        params,
        ret,
        ret_borrows_from: None,
    });
    p.gx.fn_templates.push(None);
    p.gx.fn_scopes.push(FnScope::default());
    p.gx.fn_class.push(FnClass::Stub);
    memo.insert((method_def, args_id), id);
    id
}

/// Synthetic impls that make one template's bounds true for its
/// abstract instance: for every env trait predicate (substituted
/// with the abstract args) that selection cannot already prove,
/// insert an impl record whose methods are stubs.
fn abstract_synthetic_impls(
    p: &mut Program,
    env: &[Predicate],
    subst_args: &[GenericArg],
    stub_memo: &mut FxMap<(DefId, ArgsId), LocalDefId>,
    ordinal: &mut u32,
) {
    use crate::traits::index::{ImplRecord, Synthetic, pattern_head};
    let lang = p.gx.lang;
    let mut done: Vec<TraitRef> = Vec::new();
    for &pred in env {
        let Predicate::Trait(b) = pred else { continue };
        if b.count != 0 {
            continue;
        }
        let tr = crate::traits::index::subst_trait_ref_pub(&mut p.tys, b.value, subst_args);
        if tr.def == lang.sized || lang.is_auto(tr.def) {
            continue;
        }
        if done.contains(&tr) {
            continue;
        }
        done.push(tr);
        // Already made true by an earlier abstract synthetic?
        // (A real impl header matching is not enough: its where
        // clauses may not hold for the opaque types, which is
        // exactly what the synthetic replaces.)
        if p.gx.index.impls_of_trait(tr.def).iter().any(|&id| {
            let r = p.gx.index.get(id);
            r.synthetic == crate::traits::index::Synthetic::Abstract && r.trait_ref == tr
        }) {
            continue;
        }
        let Some(rec) = p.gx.index.trait_record(tr.def).cloned() else { continue };
        // Assoc bindings: equalities in the env, else the
        // trait ref's own bindings, else a fresh opaque.
        let mut assoc_tys: Vec<(DefId, Ty)> = Vec::new();
        for &(assoc, _n, is_type) in &rec.assoc_items {
            if !is_type {
                continue;
            }
            let bound = p.tys.bindings(tr.bindings).iter().find(|(d, _)| *d == assoc).and_then(|(_, g)| g.as_ty()).or_else(|| {
                env.iter().find_map(|ep| match ep {
                    Predicate::AssocEq(eq) if eq.value.assoc == assoc => Some(subst(&mut p.tys, eq.value.ty, subst_args)),
                    _ => None,
                })
            });
            let bound = match bound {
                Some(t) => t,
                None => {
                    let mut memo: FxMap<(DefId, u32), AdtId> = FxMap::default();
                    opaque_adt(p, (assoc, *ordinal), &[], &mut memo, ordinal)
                }
            };
            assoc_tys.push((assoc, bound));
        }
        let trait_args: Vec<GenericArg> = p.tys.args(tr.args).to_vec();
        let mut items: Vec<DefId> = Vec::new();
        for (method_def, _mname) in &rec.methods {
            let stub = abstract_stub(p, *method_def, &trait_args, &assoc_tys, stub_memo);
            items.push(p.def_id(stub));
        }
        let self_pat = trait_args[0].as_ty().unwrap_or(ERROR);
        let Some((head, blanket)) = pattern_head(&p.tys, self_pat, &[]) else { continue };
        let def = synthetic_impl_def(p, *ordinal);
        *ordinal += 1;
        let assoc_tys2 = assoc_tys.clone();
        p.gx.index.insert_impl(ImplRecord {
            def,
            trait_def: tr.def,
            trait_ref: tr,
            generics: Generics::default(),
            assoc_tys,
            assoc_consts: Vec::new(),
            items,
            synthetic: Synthetic::Abstract,
            local: true,
            span: Span::default(),
            head,
            blanket,
        });
        // Associated bounds of this trait (`type It: Iter`) must
        // also hold for the bindings just chosen, or calls
        // through them in the abstract body find no impl.
        let bound_preds: Vec<Predicate> = rec
            .generics
            .predicates
            .iter()
            .map(|&pred| {
                let args: Vec<GenericArg> = p.tys.args(tr.args).to_vec();
                let sub = crate::traits::index::subst_predicate(&mut p.tys, pred, &args);
                match sub {
                    Predicate::Trait(b) => {
                        let self_ty = b.value.args;
                        let raw: Vec<GenericArg> = p.tys.args(self_ty).to_vec();
                        let rewritten: Vec<GenericArg> = raw
                            .iter()
                            .map(|&g| match g {
                                GenericArg::Ty(t) => GenericArg::Ty(rewrite_impl_projections(p, t, &assoc_tys2)),
                                other => other,
                            })
                            .collect();
                        let args2 = p.tys.intern_args(&rewritten);
                        Predicate::Trait(Binder { count: b.count, value: TraitRef { args: args2, ..b.value } })
                    }
                    other => other,
                }
            })
            .collect();
        abstract_synthetic_impls(p, &bound_preds, subst_args, stub_memo, ordinal);
    }
}

/// The abstract check of every template (ARCH 4.1's soundness
/// argument, in this pipeline's form): instantiate each generic
/// Adt and fn once with fresh opaque types standing for its
/// parameters, make its bounds true with synthetic impls, and
/// check the bodies. An error here is a real template error
/// rustc also reports, because the opaque types have exactly
/// the operations the bounds promise and no others. Concrete
/// instances are then sound to check on their own.
fn abstract_check(p: &mut Program) -> Vec<Diag> {
    let mut errs: Vec<Diag> = Vec::new();
    let mut opaque_memo: FxMap<(DefId, u32), AdtId> = FxMap::default();
    let mut stub_memo: FxMap<(DefId, ArgsId), LocalDefId> = FxMap::default();
    let mut ordinal = 1_000_000u32;
    // Abstract Adt instances first (their fields are already
    // resolved; this makes the types other templates name).
    let n_adts = p.gx.adt_info.len();
    for a in 0..n_adts {
        let (def, n_params) = p.gx.adt_info[a];
        if n_params == 0 {
            continue;
        }
        let env = p.gx.adt_envs[a].clone();
        let mut args: Vec<GenericArg> = Vec::new();
        for (i, param) in p.gx.adt_generics[a].params.clone().iter().enumerate() {
            match param.kind {
                ParamKind::Type => {
                    let bounds = param_bound_traits(&env, &p.tys, i as u32);
                    args.push(GenericArg::Ty(opaque_adt(p, (def, i as u32), &bounds, &mut opaque_memo, &mut ordinal)));
                }
                ParamKind::Lifetime => args.push(GenericArg::Lifetime(Region::Erased)),
                ParamKind::Const(ct) => {
                    let c = match p.tys.kind(ct) {
                        TyKind::Bool => p.tys.intern_const(ConstKind::Bool(false)),
                        TyKind::Char => p.tys.intern_const(ConstKind::Char('\0')),
                        _ => p.tys.intern_const(ConstKind::Int(1)),
                    };
                    args.push(GenericArg::Const(c));
                }
            }
        }
        abstract_synthetic_impls(p, &env, &args, &mut stub_memo, &mut ordinal);
        adt_instance(p, AdtId(a as u32), &args);
    }
    // Abstract fn instances, then check them to a fixpoint like
    // the concrete loop, but collecting real errors. Closure
    // templates get no abstract instance: a closure signature
    // is inferred, not universally quantified, so arbitrary
    // opaques would be wrong types for the body. The enclosing
    // abstract body checks the closure body in place instead
    // (see `closure_expr`), which is where its errors report.
    let templates: Vec<LocalDefId> = (0..p.fns.len() as u32)
        .map(LocalDefId)
        .filter(|&f| p.gx.fn_templates.get(f.0 as usize).is_some_and(|t| t.is_some()) && !p.gx.closure_fns.contains_key(&f))
        .collect();
    let mut queue: Vec<LocalDefId> = Vec::new();
    for t in templates {
        let tmpl = p.gx.fn_templates[t.0 as usize].clone().unwrap();
        let tdef = p.def_id(t);
        let mut args: Vec<GenericArg> = Vec::new();
        for (i, param) in tmpl.generics.params.iter().enumerate() {
            match param.kind {
                ParamKind::Type => {
                    let bounds = param_bound_traits(&tmpl.env, &p.tys, i as u32);
                    args.push(GenericArg::Ty(opaque_adt(p, (tdef, i as u32), &bounds, &mut opaque_memo, &mut ordinal)));
                }
                ParamKind::Lifetime => args.push(GenericArg::Lifetime(Region::Erased)),
                ParamKind::Const(ct) => {
                    let c = match p.tys.kind(ct) {
                        TyKind::Bool => p.tys.intern_const(ConstKind::Bool(false)),
                        TyKind::Char => p.tys.intern_const(ConstKind::Char('\0')),
                        _ => p.tys.intern_const(ConstKind::Int(1)),
                    };
                    args.push(GenericArg::Const(c));
                }
            }
        }
        abstract_synthetic_impls(p, &tmpl.env, &args, &mut stub_memo, &mut ordinal);
        // A trait method body may call the trait's own methods
        // on Self: make the trait itself true for the abstract
        // Self type the same way.
        if p.gx.trait_methods.contains_key(&tdef)
            && let Some(trait_def) = p.gx.index.trait_of_method(tdef)
        {
            let trait_n = p.gx.index.trait_record(trait_def).map_or(0, |r| r.generics.params.len());
            let tr_args: Vec<GenericArg> = args.iter().take(trait_n).copied().collect();
            let tr_args_id = p.tys.intern_args(&tr_args);
            let self_pred = Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args: tr_args_id, bindings: EMPTY_BINDINGS }));
            abstract_synthetic_impls(p, &[self_pred], &args, &mut stub_memo, &mut ordinal);
        }
        // The abstract instance's env keeps only equalities and
        // structural facts; trait bounds are the synthetic
        // impls' job now.
        let inst = fn_instance(p, t, &args, FnClass::Abstract);
        p.gx.mono_counts.0 += 1;
        queue.push(inst);
    }
    let mut rounds = 0usize;
    while !queue.is_empty() {
        rounds += 1;
        if rounds > 512 {
            break;
        }
        let mut next_queue: Vec<LocalDefId> = Vec::new();
        for fid in std::mem::take(&mut queue) {
            let (checked, mut body_errs) = {
                let (c, e) = crate::check::check_fn(p, fid);
                // Snapshot the requests out of the checked body.
                let reqs: Vec<(LocalDefId, Vec<OwnedArg>)> = c
                    .inst_requests
                    .iter()
                    .filter_map(|(t, raw)| {
                        let mut owned = Vec::new();
                        for g in raw {
                            match g {
                                GenericArg::Ty(e) => owned.push(OwnedArg::Ty(snapshot_ty(&c.tys, *e)?)),
                                GenericArg::Const(k) => match c.tys.const_kind(*k) {
                                    ConstKind::Infer(_) => return None,
                                    kk => owned.push(OwnedArg::Const(kk)),
                                },
                                GenericArg::Lifetime(r) => owned.push(OwnedArg::Lifetime(*r)),
                            }
                        }
                        Some((*t, owned))
                    })
                    .collect();
                // Borrow checking runs on abstract bodies too:
                // a move of a non-Copy opaque is exactly the
                // template error this pass exists to catch.
                let mut e = e;
                if e.is_empty() {
                    let body = crate::lower::lower(p, fid, c);
                    e.extend(crate::borrowck::borrowck(p, &body));
                }
                (reqs, e)
            };
            errs.append(&mut body_errs);
            for (template, owned_args) in checked {
                // Closure instances are concrete-only (see the
                // template list above); the body was already
                // checked in place.
                if p.gx.closure_fns.contains_key(&template) {
                    continue;
                }
                let mut lifted: Vec<GenericArg> = Vec::new();
                for a in &owned_args {
                    lifted.push(match a {
                        OwnedArg::Ty(e) => {
                            let gt = build_owned_ty(p, e);
                            GenericArg::Ty(normalize_global(p, gt))
                        }
                        OwnedArg::Const(k) => GenericArg::Const(p.tys.intern_const(*k)),
                        OwnedArg::Lifetime(r) => GenericArg::Lifetime(*r),
                    });
                }
                let template_def = p.def_id(template);
                let args_id = p.tys.intern_args(&lifted);
                if p.gx.abstract_by_key.contains_key(&(template_def, args_id)) {
                    continue;
                }
                let inst = fn_instance(p, template, &lifted, FnClass::Abstract);
                p.gx.mono_counts.0 += 1;
                next_queue.push(inst);
            }
        }
        queue = next_queue;
    }
    errs
}

/// Normalizes one global type through the solver, lifting the
/// result back into the global store when normalization rewrote
/// it in the solver's overlay.
fn normalize_global(p: &mut Program, t: Ty) -> Ty {
    if !p.tys.flags(t).contains_projection() {
        return t;
    }
    let owned = {
        let mut cx = crate::traits::solve::PureCx::new(&p.tys);
        let mut solver = Solver::new();
        let out = crate::traits::solve::normalize(&mut solver, &mut cx, &p.gx.index, &[], t);
        snapshot_ty(&cx.tys, out)
    };
    match owned {
        Some(owned) => build_owned_ty(p, &owned),
        None => t,
    }
}

/// Substitutes and normalizes a list of signature types.
fn subst_norm_all(p: &mut Program, tys_in: &[Ty], args: &[GenericArg]) -> Vec<Ty> {
    let substed: Vec<Ty> = tys_in.iter().map(|&t| subst(&mut p.tys, t, args)).collect();
    substed.into_iter().map(|t| normalize_global(p, t)).collect()
}

/// Creates (or finds) the Adt instance for one application.
fn adt_instance(p: &mut Program, template: AdtId, args: &[GenericArg]) -> AdtId {
    let (def, _) = p.gx.adt_info[template.0 as usize];
    let args_id = p.tys.intern_args(args);
    if let Some(inst) = p.tys.local_adt_instance(def, args_id) {
        return inst;
    }
    let src_variants: Vec<(Sym, crate::check::collect::VariantShape, i128, Vec<(Sym, Ty)>)> =
        p.adt(template).variants.iter().map(|v| (v.name, v.shape, v.disc, v.fields.iter().map(|f| (f.name, f.ty)).collect())).collect();
    let mut variants: Vec<crate::check::collect::Variant> = Vec::with_capacity(src_variants.len());
    for (vname, shape, disc, fields) in src_variants {
        let mut out_fields = Vec::with_capacity(fields.len());
        for (name, ty) in fields {
            let ty = subst(&mut p.tys, ty, args);
            let ty = normalize_global(p, ty);
            out_fields.push(crate::check::collect::Field { name, ty });
        }
        variants.push(crate::check::collect::Variant { name: vname, shape, fields: out_fields, disc });
    }
    let id = AdtId(p.adts.len() as u32);
    let (name, is_enum, derives, span) = {
        let src = p.adt(template);
        (src.name, src.is_enum, src.derives, src.span)
    };
    p.adts.push(crate::check::collect::AdtDef { name, is_enum, variants, derives, span, repr: p.adt(template).repr });
    p.tys.register_adt_instance(def, args_id, id);
    p.defs.insert_adt_instance(def, id);
    p.gx.adt_info.push((def, args.len()));
    p.gx.adt_generics.push(Generics::default());
    p.gx.adt_envs.push(Vec::new());
    let full = p.tys.full_adt_ty(id).unwrap();
    p.gx.adt_scopes.push(Scope { self_ty: Some(full), ..Scope::default() });
    p.gx.adt_instance_of.push(Some((def, args_id)));
    p.gx.mono_counts.1 += 1;
    id
}

/// The owner Adt instance of one instantiated method, from its
/// substituted receiver parameter type.
fn instance_owner(p: &mut Program, params: &[Ty], self_kind: Option<ast::SelfKind>) -> Option<AdtId> {
    if self_kind.is_none() {
        return None;
    }
    let mut t = *params.first()?;
    // Peel reference forms and smart-pointer-shaped typed
    // receivers down to the Adt application.
    for _ in 0..4 {
        match p.tys.kind(t) {
            TyKind::Ref(_, _, inner) => t = inner,
            TyKind::Adt(def, args) => {
                if let Some(template) = p.defs.local_adt(def) {
                    let args_vec: Vec<GenericArg> = p.tys.args(args).to_vec();
                    if args_vec.is_empty() {
                        return Some(template);
                    }
                    return Some(adt_instance(p, template, &args_vec));
                }
                // A smart-pointer Adt (Box/Rc when they exist):
                // look through one type argument.
                match p.tys.args(args).first().and_then(|g| g.as_ty()) {
                    Some(inner) => t = inner,
                    None => return None,
                }
            }
            _ => return None,
        }
    }
    None
}

/// Creates (or finds) one fn instance. `class` is Instance for
/// concrete code, Abstract for template checks.
fn fn_instance(p: &mut Program, template: LocalDefId, args: &[GenericArg], class: FnClass) -> LocalDefId {
    let template_def = p.def_id(template);
    let args_id = p.tys.intern_args(args);
    if class == FnClass::Instance
        && let Some(&existing) = p.gx.instance_by_key.get(&(template_def, args_id))
    {
        return existing;
    }
    if class == FnClass::Abstract
        && let Some(&existing) = p.gx.abstract_by_key.get(&(template_def, args_id))
    {
        return existing;
    }
    let (def, name, self_kind) = {
        let f = p.fn_info(template);
        (f.def, f.name, f.self_kind)
    };
    let raw_params: Vec<Ty> = p.fn_info(template).params.clone();
    let raw_ret = p.fn_info(template).ret;
    let ret_borrows_from = p.fn_info(template).ret_borrows_from;
    let params = subst_norm_all(p, &raw_params, args);
    let raw_ret = subst(&mut p.tys, raw_ret, args);
    let ret = normalize_global(p, raw_ret);
    let owner = instance_owner(p, &params, self_kind);
    // Instance identity: template disk identity plus the args
    // fingerprint (the InstanceKeyHash of section 4.2).
    let key = crate::driver::graph::InstanceKey { def: template_def, args: args_id };
    let kh = p.instance_key_hash(&key);
    // The instance def lives under an "<instance>" module with
    // the key hash in its name, so it can never collide with a
    // user def's path hash in the slot registry.
    let def_id = DefId {
        krate: p.krate,
        hash: crate::def::item_hash(p.stable_crate, &["<instance>"], crate::def::DefKind::Fn, &format!("{}#{}", p.name(name), kh.0), 0),
    };
    let id = LocalDefId(p.fns.len() as u32);
    p.fn_defs.push(def_id);
    p.def_by_hash.entry(def_id.hash).or_insert(id);
    let mut data = crate::ty::defs::DefData::skeleton(
        if owner.is_some() { crate::ty::defs::DefKind::Method } else { crate::ty::defs::DefKind::Fn },
        None,
        name,
        crate::ty::defs::Vis::Priv,
        def.name_span,
    );
    data.sig = crate::ty::defs::SigData::Fn { params: params.clone(), ret };
    p.defs.insert(def_id, data);
    p.fns.push(crate::check::collect::FnInfo { name, def, owner, self_kind, params, ret, ret_borrows_from, is_const: def.qual.is_const });
    p.gx.fn_templates.push(None);
    // The body scope of an instance: no parameters, the concrete
    // Self type, and the template's assoc sources substituted.
    let scope = {
        let mut sc = Scope::default();
        sc.self_ty = owner.map(|a| p.tys.adt_ty(a));
        if let Some(ts) = p.gx.fn_scopes.get(template.0 as usize) {
            for src in &ts.scope.assoc_srcs {
                let self_ty = subst(&mut p.tys, src.self_ty, args);
                let sargs = crate::traits::index::subst_args_pub(&mut p.tys, src.args, args);
                sc.assoc_srcs.push(AssocSrc { self_ty, trait_def: src.trait_def, args: sargs, assocs: src.assocs.clone() });
            }
            for (name, t) in &ts.scope.param_tys {
                let t2 = subst(&mut p.tys, *t, args);
                sc.param_tys.push((*name, t2));
            }
        }
        sc
    };
    p.gx.fn_scopes.push(FnScope { env: Vec::new(), scope });
    p.gx.fn_class.push(class);
    if let Some(cf) = p.gx.closure_fns.get(&template).copied() {
        p.gx.closure_fns.insert(id, cf);
    }
    p.gx.instances.insert(id, InstanceInfo { template_def, template_local: Some(template), args: args_id });
    if class == FnClass::Abstract {
        p.gx.abstract_by_key.insert((template_def, args_id), id);
    }
    if class == FnClass::Instance {
        p.gx.instance_by_key.insert((template_def, args_id), id);
        p.gx.mono_counts.1 += 1;
        // Inherent instances join the compat method table.
        if let Some(owner) = owner
            && p.gx.inherent_methods.values().any(|ts| ts.contains(&template))
        {
            let cands = p.methods.entry((owner, name)).or_default();
            if !cands.contains(&id) {
                cands.push(id);
            }
        }
    }
    id
}

/// Walks one checked type for generic Adt applications mono has
/// not made yet, creating them (their own fields may name more).
// Not wired yet; see the note on lift_ty above.
#[allow(dead_code)]
fn ensure_adt_instances_in(p: &mut Program, src: &dyn TyIntern, t: Ty, depth: u32) {
    if depth > 32 {
        return;
    }
    match src.kind(t) {
        TyKind::Adt(def, a) => {
            let raw: Vec<GenericArg> = src.args(a).to_vec();
            for g in &raw {
                if let Some(e) = g.as_ty() {
                    ensure_adt_instances_in(p, src, e, depth + 1);
                }
            }
            if !raw.is_empty()
                && let Some(template) = p.defs.local_adt(def)
                && !p.gx.adt_generics[template.0 as usize].params.is_empty()
            {
                let mut lifted: Vec<GenericArg> = Vec::new();
                let mut ok = true;
                for g in &raw {
                    match g {
                        GenericArg::Ty(e) => match lift_ty(p, src, *e) {
                            Some(gt) => lifted.push(GenericArg::Ty(gt)),
                            None => {
                                ok = false;
                                break;
                            }
                        },
                        GenericArg::Const(c) => match src.const_kind(*c) {
                            ConstKind::Infer(_) => {
                                ok = false;
                                break;
                            }
                            k => lifted.push(GenericArg::Const(p.tys.intern_const(k))),
                        },
                        other => lifted.push(*other),
                    }
                }
                if ok {
                    adt_instance(p, template, &lifted);
                }
            }
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => {
            ensure_adt_instances_in(p, src, e, depth + 1)
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = src.tys_of(ts).to_vec();
            for e in elems {
                ensure_adt_instances_in(p, src, e, depth + 1);
            }
        }
        TyKind::Projection(_, a) | TyKind::FnDef(_, a) | TyKind::Closure(_, a) | TyKind::Opaque(_, a) => {
            let raw: Vec<GenericArg> = src.args(a).to_vec();
            for g in &raw {
                if let Some(e) = g.as_ty() {
                    ensure_adt_instances_in(p, src, e, depth + 1);
                }
            }
        }
        _ => {}
    }
}

/// Finds the Drop method instance for one concrete Adt instance,
/// creating it when a `Drop` impl applies. Records it for cgen.
fn ensure_drop_method(p: &mut Program, adt: AdtId, queue: &mut Vec<LocalDefId>) {
    if p.gx.drop_methods.contains_key(&adt) {
        return;
    }
    let Some(self_ty) = p.tys.full_adt_ty(adt) else { return };
    let args_id = p.tys.intern_args(&[GenericArg::Ty(self_ty)]);
    let tr = TraitRef { def: p.gx.lang.drop, args: args_id, bindings: EMPTY_BINDINGS };
    let sel = {
        let mut cx = crate::traits::solve::PureCx::new(&p.tys);
        let mut solver = Solver::new();
        solver.select(&mut cx, &p.gx.index, &[], tr)
    };
    let Selection::Impl { id, args: impl_args, .. } = sel else { return };
    let record = p.gx.index.get(id).clone();
    let Some(local) = record.items.iter().copied().find_map(|d| p.local_def(d.hash).filter(|&l| p.name(p.fn_info(l).name) == "drop"))
    else {
        return;
    };
    let drop_fn = if p.gx.fn_templates.get(local.0 as usize).is_some_and(|t| t.is_some()) {
        let raw: Vec<GenericArg> = impl_args;
        let before = p.fns.len();
        let inst = fn_instance(p, local, &raw, FnClass::Instance);
        if inst.0 as usize >= before {
            queue.push(inst);
        }
        inst
    } else {
        local
    };
    p.gx.drop_methods.insert(adt, drop_fn);
}

/// Materializes every reachable instance (section 4.1's mono
/// half for wave A): check plain fns for requests, create the
/// instances they name, check those, to a fixpoint. Discovery
/// check errors are discarded; the driver's own check reports
/// them against the finished tables. Returns mono's own errors
/// (instantiation depth and count caps, section 4.2).
pub fn materialize(p: &mut Program) -> Vec<Diag> {
    if !p.gx.has_generics {
        return Vec::new();
    }
    // Templates check once abstractly first; a template error
    // rejects the program before any instance is made.
    let abstract_errs = abstract_check(p);
    if !abstract_errs.is_empty() {
        return abstract_errs;
    }
    let mut errs: Vec<Diag> = Vec::new();
    // Adt instances named by plain signatures and fields first.
    for a in 0..p.gx.adt_info.len() {
        let fields: Vec<Ty> = p.adts[a].variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
        for t in fields {
            ensure_global_adt_instances(p, t, 0);
        }
    }
    let mut queue: Vec<LocalDefId> =
        (0..p.fns.len() as u32).map(LocalDefId).filter(|&f| p.gx.fn_class.get(f.0 as usize) == Some(&FnClass::Plain)).collect();
    let mut depths: FxMap<LocalDefId, usize> = FxMap::default();
    let mut rounds = 0usize;
    while !queue.is_empty() {
        rounds += 1;
        if rounds > 4096 || p.fns.len() > 200_000 {
            errs.push(Diag::new(
                "L0611",
                Span::default(),
                "too many monomorphized instances",
                "Reduce the generic instantiations in this program.",
            ));
            break;
        }
        let mut next_queue: Vec<LocalDefId> = Vec::new();
        for fid in std::mem::take(&mut queue) {
            let depth = depths.get(&fid).copied().unwrap_or(0);
            // Snapshot everything the instance requests name,
            // then drop the checked body: it borrows the program
            // this loop is about to extend.
            let (adt_tys_owned, requests_owned) = {
                let (checked, _discarded) = crate::check::check_fn(p, fid);
                let mut adt_tys: Vec<OwnedTy> = Vec::new();
                for t in checked.expr_ty.iter().copied().chain(checked.locals.iter().map(|l| l.ty)) {
                    if let Some(o) = snapshot_ty(&checked.tys, t) {
                        adt_tys.push(o);
                    }
                }
                let mut reqs: Vec<(LocalDefId, Vec<OwnedArg>)> = Vec::new();
                for (template, raw_args) in &checked.inst_requests {
                    let mut owned: Vec<OwnedArg> = Vec::new();
                    let mut ok = true;
                    for g in raw_args {
                        match g {
                            GenericArg::Ty(e) => match snapshot_ty(&checked.tys, *e) {
                                Some(o) => owned.push(OwnedArg::Ty(o)),
                                None => {
                                    ok = false;
                                    break;
                                }
                            },
                            GenericArg::Const(c) => match checked.tys.const_kind(*c) {
                                ConstKind::Infer(_) => {
                                    ok = false;
                                    break;
                                }
                                k => owned.push(OwnedArg::Const(k)),
                            },
                            GenericArg::Lifetime(r) => owned.push(OwnedArg::Lifetime(*r)),
                        }
                    }
                    if ok {
                        reqs.push((*template, owned));
                    }
                }
                (adt_tys, reqs)
            };
            for owned in &adt_tys_owned {
                let gt = build_owned_ty(p, owned);
                ensure_global_adt_instances(p, gt, 0);
            }
            for (template, owned_args) in requests_owned {
                if depth + 1 > crate::mono::MAX_INSTANCE_DEPTH {
                    errs.push(Diag::new(
                        "L0611",
                        p.fn_info(template).def.name_span,
                        "instantiation depth limit reached",
                        "Reduce the recursive generic instantiation.",
                    ));
                    continue;
                }
                let mut lifted: Vec<GenericArg> = Vec::with_capacity(owned_args.len());
                for a in &owned_args {
                    lifted.push(match a {
                        OwnedArg::Ty(e) => {
                            let gt = build_owned_ty(p, e);
                            GenericArg::Ty(normalize_global(p, gt))
                        }
                        OwnedArg::Const(k) => GenericArg::Const(p.tys.intern_const(*k)),
                        OwnedArg::Lifetime(r) => GenericArg::Lifetime(*r),
                    });
                }
                let template_def = p.def_id(template);
                let args_id = p.tys.intern_args(&lifted);
                if p.gx.instance_by_key.contains_key(&(template_def, args_id)) {
                    continue;
                }
                let inst = fn_instance(p, template, &lifted, FnClass::Instance);
                depths.insert(inst, depth + 1);
                next_queue.push(inst);
            }
            // Drop glue for Adt instances this round made.
            let adt_ids: Vec<AdtId> = (0..p.adts.len() as u32).map(AdtId).collect();
            for a in adt_ids {
                ensure_drop_method(p, a, &mut next_queue);
            }
        }
        queue = next_queue;
    }
    errs
}

/// `ensure_adt_instances_in` for types already in the global
/// store (signatures and fields at collect time).
fn ensure_global_adt_instances(p: &mut Program, t: Ty, depth: u32) {
    if depth > 32 {
        return;
    }
    match p.tys.kind(t) {
        TyKind::Adt(def, a) => {
            let raw: Vec<GenericArg> = p.tys.args(a).to_vec();
            for g in &raw {
                if let Some(e) = g.as_ty() {
                    ensure_global_adt_instances(p, e, depth + 1);
                }
            }
            if !raw.is_empty()
                && let Some(template) = p.defs.local_adt(def)
                && !p.gx.adt_generics[template.0 as usize].params.is_empty()
            {
                adt_instance(p, template, &raw);
            }
        }
        TyKind::Ref(_, _, e) | TyKind::RawPtr(_, e) | TyKind::Slice(e) | TyKind::Array(e, _) => {
            ensure_global_adt_instances(p, e, depth + 1)
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = p.tys.tys_of(ts).to_vec();
            for e in elems {
                ensure_global_adt_instances(p, e, depth + 1);
            }
        }
        _ => {}
    }
}

/// Appends trait default method bodies as template fns. Runs
/// after collect's fn pass: `Program::fns` must keep the AST fns
/// first, in AST order, because the driver maps slots by that
/// order (section 1.7). Mono materializes these templates per
/// impl instance on demand.
pub fn append_trait_default_templates(p: &mut Program) {
    let defaults: Vec<(DefId, TraitMethodTemplate)> =
        p.gx.trait_methods.iter().filter(|(_, t)| t.def.body.is_some()).map(|(&d, t)| (d, t.clone())).collect();
    for (method_def, tmpl) in defaults {
        let local = LocalDefId(p.fns.len() as u32);
        p.fn_defs.push(method_def);
        p.def_by_hash.entry(method_def.hash).or_insert(local);
        let trait_def = p.gx.index.trait_of_assoc(method_def);
        let mut data = crate::ty::defs::DefData::skeleton(
            crate::ty::defs::DefKind::Method,
            trait_def,
            tmpl.name,
            crate::ty::defs::Vis::Priv,
            tmpl.def.name_span,
        );
        data.generics = tmpl.generics.clone();
        data.sig = crate::ty::defs::SigData::Fn { params: tmpl.params.clone(), ret: tmpl.ret };
        p.defs.insert(method_def, data);
        p.fns.push(crate::check::collect::FnInfo {
            name: tmpl.name,
            def: tmpl.def,
            owner: None,
            self_kind: tmpl.self_kind,
            params: tmpl.params.clone(),
            ret: tmpl.ret,
            ret_borrows_from: tmpl.ret_borrows_from,
            is_const: tmpl.def.qual.is_const,
        });
        p.gx.fn_templates.push(Some(FnTemplate { generics: tmpl.generics.clone(), env: tmpl.env.clone() }));
        p.gx.fn_scopes.push(FnScope { env: tmpl.env.clone(), scope: tmpl.scope.clone() });
        p.gx.fn_class.push(FnClass::Template);
    }
}

/// Appends one template fn per closure expression in every
/// collected fn body. A closure template's generics are its
/// enclosing fn's generics (the immediately enclosing closure
/// for a nested one) plus one type parameter per UNWRITTEN
/// signature type (closure parameters first, then the return
/// type); written types resolve in the enclosing scope and
/// are fixed parts of the template signature. Body checking
/// instantiates the signature parameters from the body and
/// Fn obligations, so mono materializes closure instances
/// exactly like fn instances. Only non-capturing closures
/// are supported; capture use is rejected during body checking.
pub fn collect_closures(p: &mut Program, errs: &mut Vec<Diag>) {
    let sig_name = p.interner.intern("<closure>");
    let hosts: Vec<LocalDefId> = (0..p.fns.len() as u32)
        .map(LocalDefId)
        .filter(|&f| matches!(p.gx.fn_class.get(f.0 as usize), Some(FnClass::Plain | FnClass::Template) | None))
        .collect();
    for host in hosts {
        let (lo, hi) = p.fn_info(host).def.exprs;
        let mut found: Vec<ast::ExprId> = Vec::new();
        for raw in lo..hi {
            let e = ast::ExprId(raw);
            if matches!(p.ast.expr(e), ast::Expr::Closure { .. }) {
                found.push(e);
            }
        }
        if found.is_empty() {
            continue;
        }
        p.gx.has_generics = true;
        // Token order, outer before inner at equal starts.
        found.sort_by(|&a, &b| {
            let (sa, sb) = (p.ast.expr_span(a), p.ast.expr_span(b));
            (sa.lo, std::cmp::Reverse(sa.hi), std::cmp::Reverse(a.0)).cmp(&(sb.lo, std::cmp::Reverse(sb.hi), std::cmp::Reverse(b.0)))
        });
        let contains = |outer: Span, inner: Span| outer.lo <= inner.lo && inner.hi <= outer.hi;
        // (span, local id) of enclosing closures, innermost last.
        let mut stack: Vec<(Span, LocalDefId)> = Vec::new();
        // Ordinal among the closures of one enclosing body.
        let mut ordinals: FxMap<LocalDefId, u32> = FxMap::default();
        for e in found {
            let span = p.ast.expr_span(e);
            while stack.last().is_some_and(|(s, _)| !contains(*s, span)) {
                stack.pop();
            }
            let parent = stack.last().map_or(host, |&(_, l)| l);
            let ordinal = {
                let o = ordinals.entry(parent).or_insert(0);
                let v = *o;
                *o += 1;
                v
            };
            let (mut generics, env, scope) = match p.gx.fn_templates.get(parent.0 as usize).cloned().flatten() {
                Some(t) => (t.generics, t.env, p.gx.fn_scopes[parent.0 as usize].scope.clone()),
                None => (Generics::default(), p.gx.fn_scopes[parent.0 as usize].env.clone(), p.gx.fn_scopes[parent.0 as usize].scope.clone()),
            };
            generics.parent = None;
            let n_parent = generics.params.len();
            let (ctys, cret) = match p.ast.expr(e) {
                ast::Expr::Closure { params: cparams, ret: cret, .. } => (cparams.iter().map(|c| c.ty).collect::<Vec<_>>(), *cret),
                _ => unreachable!(),
            };
            // Written signature types are fixed template types
            // resolved in the enclosing scope; unwritten ones
            // become signature parameters, in written order.
            let written = |p: &mut Program, t: ast::TyId, scope: &Scope, errs: &mut Vec<Diag>| {
                let cx = p.gx.resolve_cx(&p.type_names, &p.aliases);
                resolve_scoped(p.ast, p.interner, p.known, &cx, &mut p.tys, t, scope).unwrap_or_else(|d| {
                    errs.push(d);
                    ERROR
                })
            };
            let mut next_param = n_parent as u32;
            let mut mk = |p: &mut Program, generics: &mut Generics, t: Option<ast::TyId>, scope: &Scope, errs: &mut Vec<Diag>| match t {
                Some(t) => written(p, t, scope, errs),
                None => {
                    let ty = p.tys.intern(TyKind::Param(ParamId(next_param)));
                    next_param += 1;
                    generics.params.push(ParamDef { name: sig_name, kind: ParamKind::Type, span });
                    ty
                }
            };
            let mut params: Vec<Ty> = Vec::new();
            for ct in ctys {
                params.push(mk(p, &mut generics, ct, &scope.clone(), errs));
            }
            let ret = mk(p, &mut generics, cret, &scope.clone(), errs);
            let parent_def = p.def_id(parent);
            let name = p.fn_info(parent).name;
            let def = p.fn_info(host).def;
            let def_id = DefId {
                krate: p.krate,
                hash: crate::def::item_hash(
                    p.stable_crate,
                    &["<closure>"],
                    crate::def::DefKind::Fn,
                    &format!("{}#{ordinal}", parent_def.hash.0),
                    0,
                ),
            };
            let local = LocalDefId(p.fns.len() as u32);
            p.fn_defs.push(def_id);
            p.def_by_hash.entry(def_id.hash).or_insert(local);
            let mut data = crate::ty::defs::DefData::skeleton(crate::ty::defs::DefKind::Fn, None, name, crate::ty::defs::Vis::Priv, span);
            data.generics = generics.clone();
            data.sig = crate::ty::defs::SigData::Fn { params: params.clone(), ret };
            p.defs.insert(def_id, data);
            p.fns.push(crate::check::collect::FnInfo {
                name,
                def,
                owner: None,
                self_kind: None,
                params,
                ret,
                ret_borrows_from: None,
                is_const: false,
            });
            p.gx.fn_templates.push(Some(FnTemplate { generics, env: env.clone() }));
            p.gx.fn_scopes.push(FnScope { env, scope });
            p.gx.fn_class.push(FnClass::Template);
            p.gx.closure_fns.insert(local, ClosureFn { expr: e });
            p.gx.closure_by_expr.insert(e, local);
            p.gx.closure_by_def.insert(def_id, local);
            stack.push((span, local));
        }
    }
}

/// Proves one trait goal in pattern space (collect time): the
/// param env speaks first, then impls, with a confirmed impl's
/// own clauses proved the same way. `Sized` and the auto traits
/// hold by construction here (sizedness is checked where types
/// are used). A goal the solver can only defer counts as not
/// proved: at collect the bound must be in the env or in an impl.
fn prove_trait_ref(
    index: &crate::traits::ImplIndex,
    lang: &LangTraits,
    solver: &mut crate::traits::solve::Solver,
    cx: &mut crate::traits::solve::PureCx,
    env: &[Predicate],
    tr: TraitRef,
    depth: u32,
) -> bool {
    use crate::traits::solve::Selection;
    if depth > 24 {
        return false;
    }
    if tr.def == lang.sized || lang.is_auto(tr.def) {
        return true;
    }
    match solver.select(cx, index, env, tr) {
        Selection::Impl { nested, .. } => nested.iter().all(|pred| match pred {
            Predicate::Trait(b) if b.count == 0 => prove_trait_ref(index, lang, solver, cx, env, b.value, depth + 1),
            _ => true,
        }),
        Selection::ParamEvidence(_) => true,
        _ => false,
    }
}

/// One trait goal with a fresh solver (collect-time proves are
/// independent of each other).
fn prove_goal(p: &Program, env: &[Predicate], tr: TraitRef) -> bool {
    let mut cx = crate::traits::solve::PureCx::new(&p.tys);
    let mut solver = crate::traits::solve::Solver::new();
    prove_trait_ref(&p.gx.index, &p.gx.lang, &mut solver, &mut cx, env, tr, 0)
}

/// The obligations one written impl owes its trait: the trait's
/// own predicates (supertraits, bounds on the trait's
/// parameters, and bounds on its associated types) with the
/// impl's trait ref substituted in and its associated types
/// rewritten to the impl's bindings. Runs at finish, when the
/// whole impl set exists (rustc E0277's class).
fn check_impl_obligations(p: &mut Program, errs: &mut Vec<Diag>) {
    use crate::traits::index::{Synthetic, subst_predicate};
    let records: Vec<crate::traits::index::ImplRecord> =
        p.gx.index.all_impls().filter(|(_, r)| r.synthetic == Synthetic::None && r.local).map(|(_, r)| r.clone()).collect();
    for rec in records {
        let Some(trec) = p.gx.index.trait_record(rec.trait_def).cloned() else { continue };
        if trec.generics.predicates.is_empty() {
            continue;
        }
        let subst_args: Vec<GenericArg> = p.tys.args(rec.trait_ref.args).to_vec();
        let mut goals: Vec<TraitRef> = Vec::new();
        for &pred in &trec.generics.predicates {
            let Predicate::Trait(b) = subst_predicate(&mut p.tys, pred, &subst_args) else { continue };
            if b.count != 0 {
                continue;
            }
            let old_args: Vec<GenericArg> = p.tys.args(b.value.args).to_vec();
            let new_args: Vec<GenericArg> = old_args
                .iter()
                .map(|&g| match g {
                    GenericArg::Ty(t) => GenericArg::Ty(rewrite_impl_projections(p, t, &rec.assoc_tys)),
                    other => other,
                })
                .collect();
            let args = p.tys.intern_args(&new_args);
            goals.push(TraitRef { def: b.value.def, args, bindings: b.value.bindings });
        }
        if goals.is_empty() {
            continue;
        }
        let env = elaborate_env(&mut p.tys, &p.gx.index, &rec.generics.predicates);
        for goal in goals {
            if !prove_goal(p, &env, goal) {
                let gname = p.gx.index.trait_record(goal.def).map_or("?", |r| p.name(r.name));
                let tname = p.name(trec.name);
                errs.push(Diag::new(
                    "L0612",
                    rec.span,
                    format!("this impl of `{tname}` does not satisfy the `{gname}` bound the trait requires"),
                    format!("Add the `{gname}` impl or bound, or change the impl's types so the bound holds."),
                ));
            }
        }
    }
}

/// Supertrait cycles among user traits (rustc E0391): an edge
/// runs from a trait to each trait its own bounds name on
/// `Self`. Every trait on a cycle is reported once.
fn check_supertrait_cycles(p: &Program, errs: &mut Vec<Diag>) {
    let mut edges: FxMap<DefId, Vec<DefId>> = FxMap::default();
    for &def in p.gx.trait_names.values() {
        let Some(rec) = p.gx.index.trait_record(def) else { continue };
        let mut outs = Vec::new();
        for pred in &rec.generics.predicates {
            let Predicate::Trait(b) = pred else { continue };
            if b.count != 0 {
                continue;
            }
            let self_is_param0 = p
                .tys
                .args(b.value.args)
                .first()
                .and_then(|g| g.as_ty())
                .is_some_and(|t| matches!(p.tys.kind(t), TyKind::Param(pid) if pid.0 == 0));
            if self_is_param0 && p.gx.trait_names.values().any(|&d| d == b.value.def) {
                outs.push(b.value.def);
            }
        }
        edges.insert(def, outs);
    }
    // A trait is on a cycle when it can reach itself.
    for start in edges.keys().copied().collect::<Vec<_>>() {
        let mut seen: Vec<DefId> = Vec::new();
        let mut stack: Vec<DefId> = edges.get(&start).cloned().unwrap_or_default();
        let mut cyclic = false;
        while let Some(cur) = stack.pop() {
            if cur == start {
                cyclic = true;
                break;
            }
            if seen.contains(&cur) {
                continue;
            }
            seen.push(cur);
            if let Some(next) = edges.get(&cur) {
                stack.extend(next.iter().copied());
            }
        }
        if cyclic {
            let rec = p.gx.index.trait_record(start);
            errs.push(Diag::new(
                "L0110",
                rec.map_or(Span::default(), |r| r.span),
                format!("the supertraits of `{}` form a cycle", rec.map_or("?", |r| p.name(r.name))),
                "Remove one of the bounds so the trait graph has no cycle.",
            ));
        }
    }
}

/// A manual `Copy` impl needs every field to be `Copy` (rustc
/// E0204), and no type may be both `Copy` and `Drop` (E0184).
fn check_copy_impls(p: &mut Program, errs: &mut Vec<Diag>) {
    use crate::traits::index::Synthetic;
    let lang = p.gx.lang;
    let records: Vec<crate::traits::index::ImplRecord> = p.gx.index.all_impls().map(|(_, r)| r.clone()).collect();
    let mut copy_adts: Vec<DefId> = Vec::new();
    for rec in &records {
        if rec.trait_def == lang.copy
            && let TyKind::Adt(d, _) = p.tys.kind(rec.self_ty(&p.tys))
        {
            copy_adts.push(d);
        }
    }
    for rec in &records {
        if rec.trait_def == lang.drop
            && rec.synthetic == Synthetic::None
            && let TyKind::Adt(d, _) = p.tys.kind(rec.self_ty(&p.tys))
            && copy_adts.contains(&d)
        {
            errs.push(Diag::new(
                "L0110",
                rec.span,
                "a type cannot implement both `Copy` and `Drop`",
                "Remove the `Copy` impl or the `Drop` impl.",
            ));
        }
        if rec.trait_def != lang.copy || rec.synthetic != Synthetic::None {
            continue;
        }
        let self_ty = rec.self_ty(&p.tys);
        let TyKind::Adt(def, args) = p.tys.kind(self_ty) else { continue };
        let Some(idx) = p.gx.adt_info.iter().position(|&(d, _)| d == def) else { continue };
        let field_tys: Vec<Ty> = p.adt(AdtId(idx as u32)).variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect();
        let self_args: Vec<GenericArg> = p.tys.args(args).to_vec();
        let field_tys: Vec<Ty> = field_tys.iter().map(|&t| subst(&mut p.tys, t, &self_args)).collect();
        let env = elaborate_env(&mut p.tys, &p.gx.index, &rec.generics.predicates);
        for ft in field_tys {
            let fargs = p.tys.intern_args(&[GenericArg::Ty(ft)]);
            let goal = TraitRef { def: lang.copy, args: fargs, bindings: EMPTY_BINDINGS };
            if !prove_goal(p, &env, goal) {
                errs.push(Diag::new(
                    "L0110",
                    rec.span,
                    "this type cannot be `Copy` because one of its fields is not `Copy`",
                    "Remove the `Copy` impl, or change the field to a `Copy` type.",
                ));
                break;
            }
        }
    }
}

/// `#[derive(Eq)]` requires `PartialEq` and `Eq` fields;
/// `#[derive(Hash)]` requires `Hash` fields (rustc E0277 for
/// the generated impls). The derived impl bounds each type
/// parameter by the derived trait, as rustc writes it.
fn check_derive_bounds(p: &mut Program, errs: &mut Vec<Diag>) {
    let lang = p.gx.lang;
    let n = p.gx.adt_info.len();
    for idx in 0..n {
        let adt_id = AdtId(idx as u32);
        let (def, _) = p.gx.adt_info[idx];
        let (derives, span, field_tys) = {
            let a = p.adt(adt_id);
            (a.derives, a.span, a.variants.iter().flat_map(|v| v.fields.iter().map(|f| f.ty)).collect::<Vec<Ty>>())
        };
        if !derives.eq && !derives.hash {
            continue;
        }
        let base_env = elaborate_env(&mut p.tys, &p.gx.index, &p.gx.adt_generics[idx].predicates.clone());
        for (wanted, trait_def, dname) in [(derives.eq, lang.eq, "Eq"), (derives.hash, lang.hash, "Hash")] {
            if !wanted {
                continue;
            }
            if dname == "Eq" {
                let has_pe = derives.partial_eq
                    || p.gx.index.impls_of_trait(lang.partial_eq).iter().any(|&id| {
                        matches!(p.tys.kind(p.gx.index.get(id).self_ty(&p.tys)), TyKind::Adt(d, _) if d == def)
                    });
                if !has_pe {
                    errs.push(Diag::new(
                        "L0110",
                        span,
                        "deriving `Eq` requires `PartialEq`",
                        "Add `PartialEq` to the derive list, or implement it by hand.",
                    ));
                    continue;
                }
            }
            // The derive's own parameter bounds join the env.
            let mut env = base_env.clone();
            for (i, param) in p.gx.adt_generics[idx].params.iter().enumerate() {
                if param.kind != ParamKind::Type {
                    continue;
                }
                let t = p.tys.intern(TyKind::Param(ParamId(i as u32)));
                let args = p.tys.intern_args(&[GenericArg::Ty(t)]);
                env.push(Predicate::Trait(Binder::plain(TraitRef { def: trait_def, args, bindings: EMPTY_BINDINGS })));
            }
            let env = elaborate_env(&mut p.tys, &p.gx.index, &env);
            for &ft in &field_tys {
                let fargs = p.tys.intern_args(&[GenericArg::Ty(ft)]);
                let goal = TraitRef { def: trait_def, args: fargs, bindings: EMPTY_BINDINGS };
                if !prove_goal(p, &env, goal) {
                    errs.push(Diag::new(
                        "L0110",
                        span,
                        format!("deriving `{dname}` requires every field to implement `{dname}`"),
                        "Change the field type, or implement the trait by hand.",
                    ));
                    break;
                }
            }
        }
    }
}

/// The last collect step before mono: synthetic impls, then
/// coherence over the whole index (section 2.6).
pub fn finish_collect(p: &mut Program, errs: &mut Vec<Diag>) {
    append_trait_default_templates(p);
    collect_closures(p, errs);
    add_synthetic_impls(p);
    check_supertrait_cycles(p, errs);
    check_impl_obligations(p, errs);
    check_copy_impls(p, errs);
    check_derive_bounds(p, errs);
    let is_local = |d: DefId| d.krate == p.krate;
    let lang = p.gx.lang;
    let by_construction = [lang.sized, lang.send, lang.sync, lang.unpin];
    // No fundamental Adts exist yet (`Box` and `Pin` are not
    // supported types); the reference wrappers are structural.
    let pairs = p.gx.index.coherence_overlaps(&mut p.tys, &[], &by_construction, &is_local);
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
    // Inherent overlap (rustc E0592): two inherent methods of one
    // Adt with one name whose Self patterns can both apply.
    let mut inherent_dups: Vec<LocalDefId> = Vec::new();
    for cands in p.gx.inherent_methods.clone().values() {
        for (i, &a) in cands.iter().enumerate() {
            for &b in &cands[i + 1..] {
                let (Some((pat_a, gen_a)), Some((pat_b, gen_b))) =
                    (p.gx.inherent_self_pats.get(&a).cloned(), p.gx.inherent_self_pats.get(&b).cloned())
                else {
                    continue;
                };
                if p.gx.index.inherent_pair_overlaps(&mut p.tys, pat_a, &gen_a, pat_b, &gen_b, &[], &by_construction, &is_local) {
                    inherent_dups.push(b);
                }
            }
        }
    }
    inherent_dups.sort_by_key(|f| f.0);
    inherent_dups.dedup();
    for f in inherent_dups {
        let info = p.fn_info(f);
        errs.push(Diag::new(
            "L0106",
            info.def.name_span,
            format!("`{}` is defined more than once", p.name(info.name)),
            "Rename one of the definitions, or narrow one impl's Self type so they cannot both apply.",
        ));
    }
    // Mono runs last: it checks bodies against the finished
    // tables and appends every reachable instance.
    if errs.is_empty() {
        errs.extend(materialize(p));
    }
}
