// Syntax tree. Nodes live in flat arenas and refer to each other by u32 index, not by pointer.
//
// AST v2 (docs/ARCH.md section 9.2, S3b): this file freezes node shapes for all
// syntax of milestones 4 to 7. Existing variants keep their order; new variants are
// appended at the end of each enum and must never be renumbered. The parser still
// rejects most new forms with a stable code (see docs/errors/REGISTRY.md); each
// form's parser lands later with its feature owner, starting with W-CORELANG.
// Until then, code outside the parser never sees the new nodes in a program that
// passes parsing, but every later package codes against these shapes.
use crate::diag::Span;
use crate::intern::Sym;
use crate::lexer::{Delim, IntSuffix, TokenTree};

macro_rules! ids {
    ($($name:ident),*) => {$(
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name(pub u32);
    )*};
}
ids!(ExprId, PatId, TyId, BlockId);

#[derive(Default)]
pub struct Ast {
    pub items: Vec<Item>,
    /// Items written inside function bodies, in order of appearance. A body item
    /// statement (`Stmt::Item`) holds an index into this list. These are never
    /// top-level items: collect must not treat them as module items.
    pub stmt_items: Vec<Item>,
    pub exprs: Vec<Expr>,
    pub expr_spans: Vec<Span>,
    pub pats: Vec<Pat>,
    pub pat_spans: Vec<Span>,
    pub tys: Vec<TyExpr>,
    pub ty_spans: Vec<Span>,
    pub blocks: Vec<Block>,
    pub strings: Vec<String>,
}

impl Ast {
    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.exprs[id.0 as usize]
    }
    pub fn expr_span(&self, id: ExprId) -> Span {
        self.expr_spans[id.0 as usize]
    }
    pub fn pat(&self, id: PatId) -> &Pat {
        &self.pats[id.0 as usize]
    }
    pub fn pat_span(&self, id: PatId) -> Span {
        self.pat_spans[id.0 as usize]
    }
    pub fn ty(&self, id: TyId) -> &TyExpr {
        &self.tys[id.0 as usize]
    }
    pub fn ty_span(&self, id: TyId) -> Span {
        self.ty_spans[id.0 as usize]
    }
    pub fn block(&self, id: BlockId) -> &Block {
        &self.blocks[id.0 as usize]
    }
}

pub struct Item {
    pub vis: Vis,
    pub attrs: Vec<Attr>,
    pub kind: ItemKind,
    pub span: Span,
}

pub enum ItemKind {
    Fn(FnDef),
    Struct(StructDef),
    Enum(EnumDef),
    Impl(ImplDef),
    /// A `use` declaration. Until module resolution lands the tree is recorded
    /// but has no effect, exactly as the old payload-free `Use` behaved.
    Use(UseDef),
    // ---- AST v2 items: shapes only for now; the parser rejects each form. ----
    Mod(ModDef),
    Trait(TraitDef),
    Type(TypeAliasDef),
    Const(ConstDef),
    Static(StaticDef),
    MacroRules(MacroRulesDef),
    ExternCrate(ExternCrateDef),
    ExternBlock(ExternBlockDef),
    Union(UnionDef),
    /// A macro call in item position: `make!(...)` or `make! { ... }`.
    MacroCall(MacroCall),
}

/// Visibility as written: private, `pub`, or `pub(path)` where the path is
/// `crate`, `super`, or follows `in`. Not checked yet; recorded for resolve.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum Vis {
    #[default]
    Private,
    Public,
    Restricted {
        path: Vec<PathSeg>,
        span: Span,
    },
}

/// A lifetime as written, without the leading `'`: `'a`, `'static`, or `'_`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Lifetime {
    pub name: Sym,
    pub span: Span,
}

/// A loop or block label as written (`'outer`). Same token as a lifetime; the
/// syntactic position tells them apart.
pub type Label = Lifetime;

/// Whether an attribute is outer (`#[..]`, on the next item) or inner (`#![..]`,
/// on the enclosing item).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AttrStyle {
    Outer,
    Inner,
}

/// The part of an attribute after its path: nothing, `= value`, or a token list.
#[derive(Clone, Debug)]
pub enum AttrInput {
    None,
    /// `#[path = "file.rs"]`: the value expression (in practice a literal).
    Eq(ExprId),
    /// `#[cfg(target_os = "linux")]`, `#[derive(Debug)]`, `#[repr(C)]`: the
    /// delimiter and the raw token trees inside. Each attribute's owner parses
    /// its own grammar from the trees (cfg in resolve, derive in collect).
    List(Delim, Vec<TokenTree>),
}

/// One attribute. `derives` on struct and enum defs stay as the fast path for
/// today's derive handling; `attrs` is the general record later stages read
/// (cfg stripping, `#[path]`, `#[repr]`, test markers, and so on).
#[derive(Clone, Debug)]
pub struct Attr {
    pub style: AttrStyle,
    pub path: Vec<PathSeg>,
    pub input: AttrInput,
    pub span: Span,
}

/// Generic parameters as written: `<` params `>`. Empty when an item has none.
#[derive(Clone, Debug, Default)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub span: Span,
}

/// One generic parameter: a lifetime, a type, or a const, each with its
/// written bounds and default.
#[derive(Clone, Debug)]
pub enum GenericParam {
    Lifetime { lt: Lifetime, bounds: Vec<Lifetime>, attrs: Vec<Attr> },
    Type { name: Sym, span: Span, bounds: Vec<TraitBound>, default: Option<TyId>, attrs: Vec<Attr> },
    Const { name: Sym, span: Span, ty: TyId, default: Option<ExprId>, attrs: Vec<Attr> },
}

/// A `where` clause as written. Empty when an item has none.
#[derive(Clone, Debug, Default)]
pub struct WhereClause {
    pub preds: Vec<WherePred>,
    pub span: Span,
}

/// One `where` predicate. `binder` is a leading `for<'a, ..>` on a type
/// predicate (empty when absent).
#[derive(Clone, Debug)]
pub enum WherePred {
    Type { binder: Vec<Lifetime>, ty: TyId, bounds: Vec<TraitBound> },
    Lifetime { lt: Lifetime, bounds: Vec<Lifetime> },
}

/// One bound in a bound list (`T: A + B + 'a`): a trait bound (optionally
/// higher-ranked and optionally `?`-relaxed) or a lifetime bound.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraitBound {
    Trait { binder: Vec<Lifetime>, trait_ref: TraitRefExpr, maybe: bool },
    Lifetime(Lifetime),
}

/// A trait reference as written in a bound or an impl header: a path whose
/// last segment may use parenthesized sugar (`Fn(A) -> B`) or angle bindings
/// (`Iterator<Item = u8>`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TraitRefExpr {
    pub path: Vec<PathSeg>,
}

/// Qualifiers on a function: `const`, `async`, `unsafe`, and `extern "abi"`.
/// `abi` is an index into the AST string table.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct FnQual {
    pub is_const: bool,
    pub is_async: bool,
    pub is_unsafe: bool,
    pub abi: Option<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SelfKind {
    Value,
    Ref,
    RefMut,
    /// A typed receiver: `self: Box<Self>` and kin (docs/ARCH.md section 2.9).
    /// The written type is in `SelfParam::ty`.
    Typed,
}

pub struct SelfParam {
    pub kind: SelfKind,
    pub mutable: bool,
    /// The lifetime on a reference receiver (`&'a self`), when written.
    pub lifetime: Option<Lifetime>,
    /// The written receiver type for `SelfKind::Typed` (`self: Rc<Self>`).
    pub ty: Option<TyId>,
    pub attrs: Vec<Attr>,
    pub span: Span,
}

pub struct Param {
    /// The binding name for a plain `name: Ty` parameter. When `pat` is set it
    /// holds the pattern instead and `name` and `mutable` are not used.
    pub name: Sym,
    pub mutable: bool,
    pub pat: Option<PatId>,
    pub ty: TyId,
    pub attrs: Vec<Attr>,
    pub span: Span,
}

pub struct FnDef {
    pub name: Sym,
    pub name_span: Span,
    /// True for `#[test]` functions. Used by `lust test`; ignored by normal builds.
    pub is_test: bool,
    /// Visibility and attributes as written. A top-level fn repeats its item's
    /// visibility here so impl and trait methods carry their own the same way.
    pub vis: Vis,
    pub attrs: Vec<Attr>,
    pub qual: FnQual,
    pub generics: Generics,
    pub self_param: Option<SelfParam>,
    pub params: Vec<Param>,
    /// True for a trailing `...` variadic marker (extern fns only).
    pub variadic: bool,
    pub ret: Option<TyId>,
    pub where_clause: WhereClause,
    /// The body block, or None for a declaration without a body (a trait
    /// method signature or a foreign fn). Every fn the parser accepts today
    /// has a body.
    pub body: Option<BlockId>,
    /// Expressions and patterns of this function are contiguous: `exprs.0..exprs.1`.
    pub exprs: (u32, u32),
    pub pats: (u32, u32),
}

pub struct FieldDef {
    pub name: Sym,
    pub vis: Vis,
    pub attrs: Vec<Attr>,
    pub ty: TyId,
    pub span: Span,
}

pub struct StructDef {
    pub name: Sym,
    pub name_span: Span,
    pub generics: Generics,
    /// Unit, tuple, or named fields, in the same shape as enum variants.
    /// For tuple fields, `FieldDef::name` is meaningless and must not be read.
    pub fields: VariantFields,
    pub where_clause: WhereClause,
    pub derives: Vec<(Sym, Span)>,
}

pub enum VariantFields {
    Unit,
    Tuple(Vec<FieldDef>),
    Struct(Vec<FieldDef>),
}

pub struct VariantDef {
    pub name: Sym,
    pub attrs: Vec<Attr>,
    pub fields: VariantFields,
    /// An explicit discriminant (`A = 3`), when written.
    pub discriminant: Option<ExprId>,
    pub span: Span,
}

pub struct EnumDef {
    pub name: Sym,
    pub name_span: Span,
    pub generics: Generics,
    pub variants: Vec<VariantDef>,
    pub where_clause: WhereClause,
    pub derives: Vec<(Sym, Span)>,
}

pub struct ImplDef {
    pub generics: Generics,
    pub is_unsafe: bool,
    /// True for a negative impl (`impl !Send for T`).
    pub is_negative: bool,
    /// The trait being implemented, or None for an inherent impl.
    pub trait_ref: Option<TraitRefExpr>,
    pub self_ty: TyId,
    pub where_clause: WhereClause,
    pub fns: Vec<FnDef>,
    pub consts: Vec<AssocConstDef>,
    pub types: Vec<AssocTypeDef>,
    pub span: Span,
}

/// A `use` declaration: one tree (`use a::{b, c as d, self};`, `use a::*;`).
pub struct UseDef {
    pub tree: UseTree,
    pub span: Span,
}

/// One use tree node. `prefix` is the path written before this node: for
/// `a::b::{c, d}` the group node has prefix `a::b` and each child has an
/// empty prefix and one name. A node's own name, when it has one, is the
/// last prefix segment.
#[derive(Clone, Debug)]
pub struct UseTree {
    /// True when the tree was written with a leading `::` (`use ::a::b;`).
    pub leading_colon: bool,
    pub prefix: Vec<PathSeg>,
    pub kind: UseKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum UseKind {
    /// Imports the prefix's last segment, renamed with `as` when present.
    /// `self` in a group is a prefix segment naming the module itself.
    Simple {
        rename: Option<Sym>,
    },
    Glob,
    Group(Vec<UseTree>),
}

/// A `mod` item. `body` is Some for an inline module (`mod m { .. }`) and
/// None for a file module (`mod m;`); a `#[path]` attribute sits in the
/// item's attrs.
pub struct ModDef {
    pub name: Sym,
    pub name_span: Span,
    pub body: Option<Vec<Item>>,
    pub span: Span,
}

/// A trait definition. Method signatures are `FnDef`s with no body;
/// a method with a default body has one.
pub struct TraitDef {
    pub name: Sym,
    pub name_span: Span,
    pub is_unsafe: bool,
    pub is_auto: bool,
    pub generics: Generics,
    pub bounds: Vec<TraitBound>,
    pub where_clause: WhereClause,
    pub fns: Vec<FnDef>,
    pub consts: Vec<AssocConstDef>,
    pub types: Vec<AssocTypeDef>,
    pub span: Span,
}

/// An associated const in a trait or an impl. `default` is the value in an
/// impl, and in a trait when a default is written.
pub struct AssocConstDef {
    pub name: Sym,
    pub name_span: Span,
    pub vis: Vis,
    pub attrs: Vec<Attr>,
    pub ty: TyId,
    pub default: Option<ExprId>,
    pub span: Span,
}

/// An associated type in a trait or an impl. In an impl, `default` is the
/// assigned type (`type Item = u8;`); in a trait it is the written default.
/// Its own generics (a GAT) are recorded here and rejected by the trait owner.
pub struct AssocTypeDef {
    pub name: Sym,
    pub name_span: Span,
    pub vis: Vis,
    pub attrs: Vec<Attr>,
    pub generics: Generics,
    pub bounds: Vec<TraitBound>,
    pub where_clause: WhereClause,
    pub default: Option<TyId>,
    pub span: Span,
}

/// A `type` alias item: `type Name<..> = Target;`.
pub struct TypeAliasDef {
    pub name: Sym,
    pub name_span: Span,
    pub generics: Generics,
    pub where_clause: WhereClause,
    pub ty: TyId,
    pub span: Span,
}

/// A `const` item. `name` is None for an unnamed const (`const _: () = ..;`).
/// `value` is None only where Rust allows a declaration without one.
pub struct ConstDef {
    pub name: Option<Sym>,
    pub name_span: Span,
    pub ty: TyId,
    pub value: Option<ExprId>,
    pub span: Span,
}

/// A `static` item. `value` is None only in an extern block.
pub struct StaticDef {
    pub name: Sym,
    pub name_span: Span,
    pub mutable: bool,
    pub ty: TyId,
    pub value: Option<ExprId>,
    pub span: Span,
}

/// A `macro_rules!` definition. The rules stay as raw token trees: matching
/// and transcription belong to the macro owner (docs/ARCH.md section 6).
pub struct MacroRulesDef {
    pub name: Sym,
    pub name_span: Span,
    pub delim: Delim,
    pub tokens: Vec<TokenTree>,
    pub span: Span,
}

/// A macro call as raw token trees, in whichever syntactic position it was
/// written. Built-in macros keep their parsed `Expr::Macro` form; this shape
/// is for user macros the expander will own.
#[derive(Clone, Debug)]
pub struct MacroCall {
    pub path: Vec<PathSeg>,
    pub delim: Delim,
    pub tokens: Vec<TokenTree>,
    pub span: Span,
}

/// An `extern crate` item, with an `as` rename when written.
pub struct ExternCrateDef {
    pub name: Sym,
    pub name_span: Span,
    pub rename: Option<Sym>,
    pub span: Span,
}

/// An `extern "abi" { .. }` block of foreign declarations.
pub struct ExternBlockDef {
    /// The ABI string as an index into the AST string table, when written.
    pub abi: Option<u32>,
    pub is_unsafe: bool,
    pub items: Vec<ForeignItem>,
    pub span: Span,
}

/// One declaration inside an extern block.
pub enum ForeignItem {
    Fn(FnDef),
    Static(StaticDef),
    /// An opaque foreign type: `type Opaque;`.
    Type {
        name: Sym,
        name_span: Span,
        vis: Vis,
        attrs: Vec<Attr>,
        generics: Generics,
        where_clause: WhereClause,
        span: Span,
    },
    MacroCall(MacroCall),
}

/// A `union` definition: named fields, like a struct.
pub struct UnionDef {
    pub name: Sym,
    pub name_span: Span,
    pub generics: Generics,
    pub fields: Vec<FieldDef>,
    pub where_clause: WhereClause,
    pub derives: Vec<(Sym, Span)>,
    pub span: Span,
}

/// Generic arguments on one path segment, as written.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum GenericArgs {
    #[default]
    None,
    /// Angle arguments: `<T, 'a, 3, Item = u8>`, in written order.
    Angle(Vec<GenericArg>),
    /// Parenthesized sugar on a trait path: `Fn(A, B) -> C`.
    Parenthesized { inputs: Vec<TyId>, output: Option<TyId> },
}

/// One generic argument. A const argument is an expression: a literal, a
/// path to a const param or item, or a braced const block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GenericArg {
    Type(TyId),
    Lifetime(Lifetime),
    Const(ExprId),
    /// An associated binding: `Item = u8`, `Item: Clone`, or `Output = C`.
    Binding {
        name: Sym,
        span: Span,
        kind: BindingKind,
    },
}

/// The right side of an associated binding in generic arguments.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindingKind {
    EqTy(TyId),
    EqConst(ExprId),
    Constraint(Vec<TraitBound>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathSeg {
    pub name: Sym,
    pub args: GenericArgs,
}

impl PathSeg {
    /// A segment with no generic arguments.
    pub fn plain(name: Sym) -> PathSeg {
        PathSeg { name, args: GenericArgs::None }
    }
    /// The type arguments among the angle arguments, in written order.
    /// Lifetime, const, and binding arguments are skipped; callers that must
    /// reject those instead of skipping check `args` themselves.
    pub fn type_args(&self) -> Vec<TyId> {
        match &self.args {
            GenericArgs::Angle(args) => args
                .iter()
                .filter_map(|a| match a {
                    GenericArg::Type(t) => Some(*t),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        }
    }
    /// True when the segment carries any written generic argument.
    pub fn has_args(&self) -> bool {
        !matches!(self.args, GenericArgs::None)
    }
}

pub enum TyExpr {
    Path(Vec<PathSeg>),
    Ref {
        lifetime: Option<Lifetime>,
        mutable: bool,
        inner: TyId,
    },
    Unit,
    // ---- AST v2 types: shapes only for now; the parser rejects each form. ----
    /// A tuple type with one or more elements. The empty tuple stays `Unit`.
    Tuple(Vec<TyId>),
    /// `[T; N]`: the element type and the length expression.
    Array {
        inner: TyId,
        len: ExprId,
    },
    /// `[T]`.
    Slice(TyId),
    /// A raw pointer: `*const T` when `mutable` is false, `*mut T` when true.
    Ptr {
        mutable: bool,
        inner: TyId,
    },
    /// A function pointer type, with a leading `for<'a, ..>` binder when written.
    FnPtr {
        binder: Vec<Lifetime>,
        qual: FnQual,
        inputs: Vec<FtyParam>,
        variadic: bool,
        ret: Option<TyId>,
    },
    /// `dyn Bounds + 'a`: trait bounds plus a written lifetime bound.
    Dyn {
        binder: Vec<Lifetime>,
        bounds: Vec<TraitBound>,
        lifetime: Option<Lifetime>,
    },
    /// `impl Bounds` in argument, return, or associated position.
    ImplTrait {
        bounds: Vec<TraitBound>,
    },
    /// A qualified path: `<SelfTy as Trait>::Segs`.
    QPath {
        self_ty: TyId,
        trait_path: Vec<PathSeg>,
        segs: Vec<PathSeg>,
    },
    /// The never type `!`.
    Never,
    /// A parenthesized type `(T)`.
    Paren(TyId),
    /// The inferred type `_`.
    Infer,
    /// A macro call in type position.
    MacroCall(MacroCall),
}

/// One parameter of a function pointer type. The name (`fn(x: i64)`) is
/// optional and has no meaning beyond the signature text.
#[derive(Clone, Debug)]
pub struct FtyParam {
    pub name: Option<Sym>,
    pub ty: TyId,
    pub attrs: Vec<Attr>,
    pub span: Span,
}

pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Option<ExprId>,
    pub span: Span,
}

pub enum Stmt {
    /// A `let` statement. `els` is the block of a `let .. else { .. }` form.
    Let {
        pat: PatId,
        ty: Option<TyId>,
        init: Option<ExprId>,
        els: Option<BlockId>,
        attrs: Vec<Attr>,
        span: Span,
    },
    Expr {
        expr: ExprId,
        semi: bool,
    },
    /// An item inside a function body: an index into `Ast::stmt_items`.
    Item(u32),
    /// A macro call in statement position (`m!(..);`). `semi` records whether
    /// a `;` followed a `()` or `[]` call, which changes its type to unit.
    Macro {
        call: MacroCall,
        semi: bool,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
}

impl BinOp {
    pub fn is_cmp(self) -> bool {
        matches!(self, BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge)
    }
    pub fn symbol(self) -> &'static str {
        use BinOp::*;
        match self {
            Add => "+",
            Sub => "-",
            Mul => "*",
            Div => "/",
            Rem => "%",
            BitAnd => "&",
            BitOr => "|",
            BitXor => "^",
            Shl => "<<",
            Shr => ">>",
            Eq => "==",
            Ne => "!=",
            Lt => "<",
            Le => "<=",
            Gt => ">",
            Ge => ">=",
            And => "&&",
            Or => "||",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MacroKind {
    Println,
    Print,
    Eprintln,
    Eprint,
    Format,
    Panic,
    Vec,
    Assert,
    AssertEq,
    AssertNe,
    Todo,
    Unreachable,
}

/// A parsed format string. `Arg` holds an index into the macro's argument list.
#[derive(Clone, Debug)]
pub enum FmtPiece {
    Lit(String),
    Arg { index: usize, debug: bool },
}

pub struct Arm {
    pub attrs: Vec<Attr>,
    pub pat: PatId,
    pub guard: Option<ExprId>,
    pub body: ExprId,
}

/// One closure parameter: a pattern and an optional written type.
pub struct ClosureParam {
    pub pat: PatId,
    pub ty: Option<TyId>,
    pub attrs: Vec<Attr>,
    pub span: Span,
}

pub enum Expr {
    Int(u64, Option<IntSuffix>),
    Bool(bool),
    Str(u32),
    Char(char),
    Unit,
    Path(Vec<PathSeg>),
    SelfValue,
    Block(BlockId),
    If {
        cond: ExprId,
        then: BlockId,
        els: Option<ExprId>,
    },
    While {
        label: Option<Label>,
        cond: ExprId,
        body: BlockId,
    },
    Loop {
        label: Option<Label>,
        body: BlockId,
    },
    For {
        label: Option<Label>,
        pat: PatId,
        iter: ExprId,
        body: BlockId,
    },
    Match {
        scrut: ExprId,
        arms: Vec<Arm>,
    },
    Call {
        callee: ExprId,
        args: Vec<ExprId>,
    },
    /// A method call. `generic_args` is the turbofish (`recv.m::<T>(..)`),
    /// with lifetime, const, and binding arguments in written order.
    MethodCall {
        recv: ExprId,
        name: Sym,
        name_span: Span,
        generic_args: Vec<GenericArg>,
        args: Vec<ExprId>,
    },
    Field {
        base: ExprId,
        name: Sym,
    },
    Index {
        base: ExprId,
        index: ExprId,
    },
    Binary {
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    Unary {
        op: UnOp,
        expr: ExprId,
    },
    Cast {
        expr: ExprId,
        ty: TyId,
    },
    /// A borrow. `raw` marks `&raw const` and `&raw mut`, where `mutable`
    /// says which of the two was written.
    Ref {
        mutable: bool,
        raw: bool,
        expr: ExprId,
    },
    Deref(ExprId),
    Assign {
        lhs: ExprId,
        rhs: ExprId,
    },
    AssignOp {
        op: BinOp,
        lhs: ExprId,
        rhs: ExprId,
    },
    /// A struct literal. `update` is the base in `S { a: 1, ..base }`.
    StructLit {
        path: Vec<PathSeg>,
        fields: Vec<(Sym, Span, ExprId)>,
        update: Option<ExprId>,
    },
    Range {
        lo: Option<ExprId>,
        hi: Option<ExprId>,
        inclusive: bool,
    },
    Break {
        label: Option<Label>,
        value: Option<ExprId>,
    },
    Continue(Option<Label>),
    Return(Option<ExprId>),
    Macro {
        kind: MacroKind,
        args: Vec<ExprId>,
        fmt: Vec<FmtPiece>,
        repeat: bool,
    },
    // ---- AST v2 expressions: shapes only for now; the parser rejects each form. ----
    /// A float literal: an index into the AST string table holding its text.
    Float(u32),
    /// A tuple expression with one or more elements. `()` stays `Unit`.
    Tuple(Vec<ExprId>),
    /// An array literal `[a, b, c]`.
    Array(Vec<ExprId>),
    /// An array repeat literal `[value; len]`.
    ArrayRepeat {
        value: ExprId,
        len: ExprId,
    },
    /// A closure: `move |params| -> Ret body`, with `async` when written.
    /// The body is an expression (a block body is `Expr::Block`).
    Closure {
        is_move: bool,
        is_async: bool,
        params: Vec<ClosureParam>,
        ret: Option<TyId>,
        body: ExprId,
    },
    /// The `?` operator.
    Try(ExprId),
    /// An `.await` postfix.
    Await(ExprId),
    /// An `async` block: `async move { .. }`.
    AsyncBlock {
        is_move: bool,
        body: BlockId,
    },
    /// An `unsafe { .. }` block.
    UnsafeBlock(BlockId),
    /// A labeled block: `'a: { .. }`.
    LabeledBlock {
        label: Label,
        body: BlockId,
    },
    /// A `let` in an `if` or `while` condition, including let chains joined
    /// by `&&`. Only valid as (part of) a condition.
    Let {
        pat: PatId,
        scrut: ExprId,
    },
    /// A tuple field access: `value.0`.
    TupleField {
        base: ExprId,
        index: u32,
    },
    /// A qualified path: `<SelfTy as Trait>::Segs`.
    QPath {
        self_ty: TyId,
        trait_path: Vec<PathSeg>,
        segs: Vec<PathSeg>,
    },
    /// An inline const block: `const { .. }`.
    ConstBlock(BlockId),
    /// The inferred expression `_` (const generic arguments and the like).
    Underscore,
    /// A user macro call in expression position, as raw token trees.
    MacroCall(MacroCall),
}

pub enum Pat {
    Wild,
    Binding {
        name: Sym,
        mutable: bool,
        by_ref: bool,
    },
    Lit(ExprId),
    /// A path pattern: a unit variant such as `Kind::C`.
    Path(Vec<PathSeg>),
    TupleStruct {
        path: Vec<PathSeg>,
        elems: Vec<PatId>,
    },
    Struct {
        path: Vec<PathSeg>,
        fields: Vec<(Sym, PatId)>,
        rest: bool,
    },
    Or(Vec<PatId>),
    /// A range pattern. `lo` is None for `..hi` and `..=hi`; `hi` is None
    /// for `lo..`; `inclusive` marks `..=`.
    Range {
        lo: Option<ExprId>,
        hi: Option<ExprId>,
        inclusive: bool,
    },
    // ---- AST v2 patterns: shapes only for now; the parser rejects each form. ----
    /// A tuple pattern: `(a, b, ..)`. A `..` element is `Pat::Rest`.
    Tuple(Vec<PatId>),
    /// A slice pattern: `[first, rest @ .., last]`. `middle`, when present,
    /// is the pattern bound to the middle slice (a binding or `_`).
    Slice {
        prefix: Vec<PatId>,
        middle: Option<PatId>,
        suffix: Vec<PatId>,
    },
    /// A reference pattern: `&pat` or `&mut pat`.
    Ref {
        mutable: bool,
        inner: PatId,
    },
    /// An `@` binding: `name @ pat`, with `ref` and `mut` as written.
    At {
        name: Sym,
        mutable: bool,
        by_ref: bool,
        inner: PatId,
    },
    /// A rest pattern `..` inside a tuple, tuple-struct, or slice pattern.
    Rest,
    /// A parenthesized pattern `(pat)`.
    Paren(PatId),
    /// A qualified path pattern: `<SelfTy as Trait>::CONST`.
    QPath {
        self_ty: TyId,
        trait_path: Vec<PathSeg>,
        segs: Vec<PathSeg>,
    },
    /// A macro call in pattern position, as raw token trees.
    MacroCall(MacroCall),
}

/// Index offsets for merging one chunk's arenas after another's.
#[derive(Clone, Copy)]
struct Shift {
    e: u32,
    p: u32,
    t: u32,
    b: u32,
    s: u32,
    /// Offset of this chunk's body items in the merged `stmt_items`.
    si: u32,
}

impl Shift {
    fn e(&self, x: ExprId) -> ExprId {
        ExprId(x.0 + self.e)
    }
    fn p(&self, x: PatId) -> PatId {
        PatId(x.0 + self.p)
    }
    fn t(&self, x: TyId) -> TyId {
        TyId(x.0 + self.t)
    }
    fn b(&self, x: BlockId) -> BlockId {
        BlockId(x.0 + self.b)
    }
    fn es(&self, xs: &mut [ExprId]) {
        xs.iter_mut().for_each(|x| *x = self.e(*x));
    }
    fn ts(&self, xs: &mut [TyId]) {
        xs.iter_mut().for_each(|x| *x = self.t(*x));
    }
    fn ps(&self, xs: &mut [PatId]) {
        xs.iter_mut().for_each(|x| *x = self.p(*x));
    }
    fn str_id(&self, x: &mut u32) {
        *x += self.s;
    }
    fn trees(&self, trees: &mut [TokenTree]) {
        for tree in trees {
            match tree {
                TokenTree::Token(tok) => match &mut tok.tok {
                    crate::lexer::Tok::Str(i) | crate::lexer::Tok::Float(i) => *i += self.s,
                    _ => {}
                },
                TokenTree::Delim(_, inner, _) => self.trees(inner),
            }
        }
    }
    fn generic_arg(&self, a: &mut GenericArg) {
        match a {
            GenericArg::Type(t) => *t = self.t(*t),
            GenericArg::Lifetime(_) => {}
            GenericArg::Const(e) => *e = self.e(*e),
            GenericArg::Binding { kind, .. } => match kind {
                BindingKind::EqTy(t) => *t = self.t(*t),
                BindingKind::EqConst(e) => *e = self.e(*e),
                BindingKind::Constraint(bounds) => self.bounds(bounds),
            },
        }
    }
    fn args(&self, args: &mut GenericArgs) {
        match args {
            GenericArgs::None => {}
            GenericArgs::Angle(args) => {
                for a in args {
                    self.generic_arg(a);
                }
            }
            GenericArgs::Parenthesized { inputs, output } => {
                self.ts(inputs);
                *output = output.map(|t| self.t(t));
            }
        }
    }
    fn path(&self, segs: &mut [PathSeg]) {
        segs.iter_mut().for_each(|s| self.args(&mut s.args));
    }
    fn vis(&self, v: &mut Vis) {
        if let Vis::Restricted { path, .. } = v {
            self.path(path);
        }
    }
    fn attrs(&self, attrs: &mut [Attr]) {
        for a in attrs {
            self.path(&mut a.path);
            match &mut a.input {
                AttrInput::None => {}
                AttrInput::Eq(e) => *e = self.e(*e),
                AttrInput::List(_, trees) => self.trees(trees),
            }
        }
    }
    fn bounds(&self, bounds: &mut [TraitBound]) {
        for b in bounds {
            if let TraitBound::Trait { trait_ref, .. } = b {
                self.path(&mut trait_ref.path);
            }
        }
    }
    fn generics(&self, g: &mut Generics) {
        for p in &mut g.params {
            match p {
                GenericParam::Lifetime { attrs, .. } => self.attrs(attrs),
                GenericParam::Type { bounds, default, attrs, .. } => {
                    self.bounds(bounds);
                    *default = default.map(|t| self.t(t));
                    self.attrs(attrs);
                }
                GenericParam::Const { ty, default, attrs, .. } => {
                    *ty = self.t(*ty);
                    *default = default.map(|e| self.e(e));
                    self.attrs(attrs);
                }
            }
        }
    }
    fn where_clause(&self, w: &mut WhereClause) {
        for p in &mut w.preds {
            match p {
                WherePred::Type { ty, bounds, .. } => {
                    *ty = self.t(*ty);
                    self.bounds(bounds);
                }
                WherePred::Lifetime { .. } => {}
            }
        }
    }
    fn macro_call(&self, m: &mut MacroCall) {
        self.path(&mut m.path);
        self.trees(&mut m.tokens);
    }
    fn use_tree(&self, t: &mut UseTree) {
        self.path(&mut t.prefix);
        if let UseKind::Group(trees) = &mut t.kind {
            trees.iter_mut().for_each(|c| self.use_tree(c));
        }
    }
    fn assoc_consts(&self, cs: &mut [AssocConstDef]) {
        for c in cs {
            self.vis(&mut c.vis);
            self.attrs(&mut c.attrs);
            c.ty = self.t(c.ty);
            c.default = c.default.map(|e| self.e(e));
        }
    }
    fn assoc_types(&self, ts: &mut [AssocTypeDef]) {
        for t in ts {
            self.vis(&mut t.vis);
            self.attrs(&mut t.attrs);
            self.generics(&mut t.generics);
            self.bounds(&mut t.bounds);
            self.where_clause(&mut t.where_clause);
            t.default = t.default.map(|x| self.t(x));
        }
    }
    fn fn_def(&self, f: &mut FnDef) {
        self.vis(&mut f.vis);
        self.attrs(&mut f.attrs);
        if let Some(a) = &mut f.qual.abi {
            self.str_id(a);
        }
        self.generics(&mut f.generics);
        if let Some(sp) = &mut f.self_param {
            sp.ty = sp.ty.map(|t| self.t(t));
            self.attrs(&mut sp.attrs);
        }
        f.params.iter_mut().for_each(|p| {
            p.ty = self.t(p.ty);
            p.pat = p.pat.map(|x| self.p(x));
            self.attrs(&mut p.attrs);
        });
        f.ret = f.ret.map(|t| self.t(t));
        self.where_clause(&mut f.where_clause);
        f.body = f.body.map(|b| self.b(b));
        f.exprs = (f.exprs.0 + self.e, f.exprs.1 + self.e);
        f.pats = (f.pats.0 + self.p, f.pats.1 + self.p);
    }
    fn fields(&self, fs: &mut [FieldDef]) {
        fs.iter_mut().for_each(|f| {
            f.ty = self.t(f.ty);
            self.vis(&mut f.vis);
            self.attrs(&mut f.attrs);
        });
    }
    fn variant_fields(&self, vf: &mut VariantFields) {
        match vf {
            VariantFields::Unit => {}
            VariantFields::Tuple(fs) | VariantFields::Struct(fs) => self.fields(fs),
        }
    }
    fn item(&self, item: &mut Item) {
        self.vis(&mut item.vis);
        self.attrs(&mut item.attrs);
        match &mut item.kind {
            ItemKind::Fn(f) => self.fn_def(f),
            ItemKind::Struct(s) => {
                self.generics(&mut s.generics);
                self.variant_fields(&mut s.fields);
                self.where_clause(&mut s.where_clause);
            }
            ItemKind::Enum(e) => {
                self.generics(&mut e.generics);
                self.where_clause(&mut e.where_clause);
                for v in &mut e.variants {
                    self.attrs(&mut v.attrs);
                    self.variant_fields(&mut v.fields);
                    v.discriminant = v.discriminant.map(|x| self.e(x));
                }
            }
            ItemKind::Impl(imp) => {
                self.generics(&mut imp.generics);
                if let Some(tr) = &mut imp.trait_ref {
                    self.path(&mut tr.path);
                }
                imp.self_ty = self.t(imp.self_ty);
                self.where_clause(&mut imp.where_clause);
                imp.fns.iter_mut().for_each(|f| self.fn_def(f));
                self.assoc_consts(&mut imp.consts);
                self.assoc_types(&mut imp.types);
            }
            ItemKind::Use(u) => self.use_tree(&mut u.tree),
            ItemKind::Mod(m) => {
                if let Some(items) = &mut m.body {
                    items.iter_mut().for_each(|i| self.item(i));
                }
            }
            ItemKind::Trait(tr) => {
                self.generics(&mut tr.generics);
                self.bounds(&mut tr.bounds);
                self.where_clause(&mut tr.where_clause);
                tr.fns.iter_mut().for_each(|f| self.fn_def(f));
                self.assoc_consts(&mut tr.consts);
                self.assoc_types(&mut tr.types);
            }
            ItemKind::Type(a) => {
                self.generics(&mut a.generics);
                self.where_clause(&mut a.where_clause);
                a.ty = self.t(a.ty);
            }
            ItemKind::Const(c) => {
                c.ty = self.t(c.ty);
                c.value = c.value.map(|e| self.e(e));
            }
            ItemKind::Static(s) => {
                s.ty = self.t(s.ty);
                s.value = s.value.map(|e| self.e(e));
            }
            ItemKind::MacroRules(m) => self.trees(&mut m.tokens),
            ItemKind::ExternCrate(_) => {}
            ItemKind::ExternBlock(b) => {
                if let Some(a) = &mut b.abi {
                    self.str_id(a);
                }
                for fi in &mut b.items {
                    match fi {
                        ForeignItem::Fn(f) => self.fn_def(f),
                        ForeignItem::Static(s) => {
                            s.ty = self.t(s.ty);
                            s.value = s.value.map(|e| self.e(e));
                        }
                        ForeignItem::Type { vis, attrs, generics, where_clause, .. } => {
                            self.vis(vis);
                            self.attrs(attrs);
                            self.generics(generics);
                            self.where_clause(where_clause);
                        }
                        ForeignItem::MacroCall(m) => self.macro_call(m),
                    }
                }
            }
            ItemKind::Union(u) => {
                self.generics(&mut u.generics);
                self.fields(&mut u.fields);
                self.where_clause(&mut u.where_clause);
            }
            ItemKind::MacroCall(m) => self.macro_call(m),
        }
    }
}

impl Ast {
    /// Merges chunk ASTs in order. Index shifting runs in parallel, one chunk per thread.
    pub fn concat(mut chunks: Vec<Ast>) -> Ast {
        let mut sh = Shift { e: 0, p: 0, t: 0, b: 0, s: 0, si: 0 };
        let mut shifts = Vec::with_capacity(chunks.len());
        for c in &chunks {
            shifts.push(sh);
            sh = Shift {
                e: sh.e + c.exprs.len() as u32,
                p: sh.p + c.pats.len() as u32,
                t: sh.t + c.tys.len() as u32,
                b: sh.b + c.blocks.len() as u32,
                s: sh.s + c.strings.len() as u32,
                si: sh.si + c.stmt_items.len() as u32,
            };
        }
        std::thread::scope(|scope| {
            for (c, &s) in chunks.iter_mut().zip(&shifts).skip(1) {
                scope.spawn(move || c.shift(s));
            }
        });
        let mut out = Ast {
            items: Vec::with_capacity(chunks.iter().map(|c| c.items.len()).sum()),
            stmt_items: Vec::with_capacity(sh.si as usize),
            exprs: Vec::with_capacity(sh.e as usize),
            expr_spans: Vec::with_capacity(sh.e as usize),
            pats: Vec::with_capacity(sh.p as usize),
            pat_spans: Vec::with_capacity(sh.p as usize),
            tys: Vec::with_capacity(sh.t as usize),
            ty_spans: Vec::with_capacity(sh.t as usize),
            blocks: Vec::with_capacity(sh.b as usize),
            strings: Vec::with_capacity(sh.s as usize),
        };
        for mut c in chunks {
            out.items.append(&mut c.items);
            out.stmt_items.append(&mut c.stmt_items);
            out.exprs.append(&mut c.exprs);
            out.expr_spans.append(&mut c.expr_spans);
            out.pats.append(&mut c.pats);
            out.pat_spans.append(&mut c.pat_spans);
            out.tys.append(&mut c.tys);
            out.ty_spans.append(&mut c.ty_spans);
            out.blocks.append(&mut c.blocks);
            out.strings.append(&mut c.strings);
        }
        out
    }

    /// Moves another chunk's nodes into this AST (shifting their indexes) and returns its items,
    /// for the caller to place. Nodes are only ever appended, so existing items stay valid.
    pub fn append_chunk(&mut self, mut o: Ast) -> Vec<Item> {
        let sh = Shift {
            e: self.exprs.len() as u32,
            p: self.pats.len() as u32,
            t: self.tys.len() as u32,
            b: self.blocks.len() as u32,
            s: self.strings.len() as u32,
            si: self.stmt_items.len() as u32,
        };
        o.shift(sh);
        self.stmt_items.append(&mut o.stmt_items);
        self.exprs.append(&mut o.exprs);
        self.expr_spans.append(&mut o.expr_spans);
        self.pats.append(&mut o.pats);
        self.pat_spans.append(&mut o.pat_spans);
        self.tys.append(&mut o.tys);
        self.ty_spans.append(&mut o.ty_spans);
        self.blocks.append(&mut o.blocks);
        self.strings.append(&mut o.strings);
        o.items
    }

    /// Adds `sh` to every index stored in this chunk's nodes.
    fn shift(&mut self, sh: Shift) {
        let o = self;
        for item in o.items.iter_mut().chain(o.stmt_items.iter_mut()) {
            sh.item(item);
        }
        for e in &mut o.exprs {
            match e {
                Expr::Int(..) | Expr::Bool(_) | Expr::Char(_) | Expr::Unit | Expr::SelfValue | Expr::Continue(_) | Expr::Underscore => {}
                Expr::Str(i) | Expr::Float(i) => *i += sh.s,
                Expr::Path(segs) => sh.path(segs),
                Expr::Block(b)
                | Expr::Loop { body: b, .. }
                | Expr::UnsafeBlock(b)
                | Expr::LabeledBlock { body: b, .. }
                | Expr::AsyncBlock { body: b, .. }
                | Expr::ConstBlock(b) => *b = sh.b(*b),
                Expr::If { cond, then, els } => {
                    *cond = sh.e(*cond);
                    *then = sh.b(*then);
                    *els = els.map(|x| sh.e(x));
                }
                Expr::While { cond, body, .. } => {
                    *cond = sh.e(*cond);
                    *body = sh.b(*body);
                }
                Expr::For { pat, iter, body, .. } => {
                    *pat = sh.p(*pat);
                    *iter = sh.e(*iter);
                    *body = sh.b(*body);
                }
                Expr::Match { scrut, arms } => {
                    *scrut = sh.e(*scrut);
                    for a in arms {
                        sh.attrs(&mut a.attrs);
                        a.pat = sh.p(a.pat);
                        a.guard = a.guard.map(|g| sh.e(g));
                        a.body = sh.e(a.body);
                    }
                }
                Expr::Call { callee, args } => {
                    *callee = sh.e(*callee);
                    sh.es(args);
                }
                Expr::MethodCall { recv, generic_args, args, .. } => {
                    *recv = sh.e(*recv);
                    generic_args.iter_mut().for_each(|a| sh.generic_arg(a));
                    sh.es(args);
                }
                Expr::Field { base, .. } | Expr::TupleField { base, .. } => *base = sh.e(*base),
                Expr::Index { base, index } => {
                    *base = sh.e(*base);
                    *index = sh.e(*index);
                }
                Expr::Binary { lhs, rhs, .. } | Expr::Assign { lhs, rhs } | Expr::AssignOp { lhs, rhs, .. } => {
                    *lhs = sh.e(*lhs);
                    *rhs = sh.e(*rhs);
                }
                Expr::Unary { expr, .. } | Expr::Ref { expr, .. } | Expr::Deref(expr) | Expr::Try(expr) | Expr::Await(expr) => {
                    *expr = sh.e(*expr)
                }
                Expr::Cast { expr, ty } => {
                    *expr = sh.e(*expr);
                    *ty = sh.t(*ty);
                }
                Expr::StructLit { path, fields, update } => {
                    sh.path(path);
                    fields.iter_mut().for_each(|f| f.2 = sh.e(f.2));
                    *update = update.map(|x| sh.e(x));
                }
                Expr::Range { lo, hi, .. } => {
                    *lo = lo.map(|x| sh.e(x));
                    *hi = hi.map(|x| sh.e(x));
                }
                Expr::Break { value, .. } => *value = value.map(|x| sh.e(x)),
                Expr::Return(v) => *v = v.map(|x| sh.e(x)),
                Expr::Macro { args, .. } => sh.es(args),
                Expr::Tuple(elems) | Expr::Array(elems) => sh.es(elems),
                Expr::ArrayRepeat { value, len } => {
                    *value = sh.e(*value);
                    *len = sh.e(*len);
                }
                Expr::Closure { params, ret, body, .. } => {
                    for p in params {
                        p.pat = sh.p(p.pat);
                        p.ty = p.ty.map(|t| sh.t(t));
                        sh.attrs(&mut p.attrs);
                    }
                    *ret = ret.map(|t| sh.t(t));
                    *body = sh.e(*body);
                }
                Expr::Let { pat, scrut } => {
                    *pat = sh.p(*pat);
                    *scrut = sh.e(*scrut);
                }
                Expr::QPath { self_ty, trait_path, segs } => {
                    *self_ty = sh.t(*self_ty);
                    sh.path(trait_path);
                    sh.path(segs);
                }
                Expr::MacroCall(m) => sh.macro_call(m),
            }
        }
        for p in &mut o.pats {
            match p {
                Pat::Wild | Pat::Binding { .. } | Pat::Rest => {}
                Pat::Lit(e) => *e = sh.e(*e),
                Pat::Range { lo, hi, .. } => {
                    *lo = lo.map(|x| sh.e(x));
                    *hi = hi.map(|x| sh.e(x));
                }
                Pat::Path(segs) => sh.path(segs),
                Pat::TupleStruct { path, elems } => {
                    sh.path(path);
                    sh.ps(elems);
                }
                Pat::Struct { path, fields, .. } => {
                    sh.path(path);
                    fields.iter_mut().for_each(|f| f.1 = sh.p(f.1));
                }
                Pat::Or(alts) | Pat::Tuple(alts) => sh.ps(alts),
                Pat::Slice { prefix, middle, suffix } => {
                    sh.ps(prefix);
                    *middle = middle.map(|x| sh.p(x));
                    sh.ps(suffix);
                }
                Pat::Ref { inner, .. } | Pat::Paren(inner) => *inner = sh.p(*inner),
                Pat::At { inner, .. } => *inner = sh.p(*inner),
                Pat::QPath { self_ty, trait_path, segs } => {
                    *self_ty = sh.t(*self_ty);
                    sh.path(trait_path);
                    sh.path(segs);
                }
                Pat::MacroCall(m) => sh.macro_call(m),
            }
        }
        for t in &mut o.tys {
            match t {
                TyExpr::Path(segs) => sh.path(segs),
                TyExpr::Ref { inner, .. } | TyExpr::Slice(inner) | TyExpr::Ptr { inner, .. } | TyExpr::Paren(inner) => {
                    *inner = sh.t(*inner)
                }
                TyExpr::Unit | TyExpr::Never | TyExpr::Infer => {}
                TyExpr::Tuple(ts) => sh.ts(ts),
                TyExpr::Array { inner, len } => {
                    *inner = sh.t(*inner);
                    *len = sh.e(*len);
                }
                TyExpr::FnPtr { qual, inputs, ret, .. } => {
                    if let Some(a) = &mut qual.abi {
                        sh.str_id(a);
                    }
                    for p in inputs {
                        p.ty = sh.t(p.ty);
                        sh.attrs(&mut p.attrs);
                    }
                    *ret = ret.map(|x| sh.t(x));
                }
                TyExpr::Dyn { bounds, .. } => sh.bounds(bounds),
                TyExpr::ImplTrait { bounds } => sh.bounds(bounds),
                TyExpr::QPath { self_ty, trait_path, segs } => {
                    *self_ty = sh.t(*self_ty);
                    sh.path(trait_path);
                    sh.path(segs);
                }
                TyExpr::MacroCall(m) => sh.macro_call(m),
            }
        }
        for b in &mut o.blocks {
            b.tail = b.tail.map(|x| sh.e(x));
            for st in &mut b.stmts {
                match st {
                    Stmt::Let { pat, ty, init, els, attrs, .. } => {
                        *pat = sh.p(*pat);
                        *ty = ty.map(|t| sh.t(t));
                        *init = init.map(|x| sh.e(x));
                        *els = els.map(|x| sh.b(x));
                        sh.attrs(attrs);
                    }
                    Stmt::Expr { expr, .. } => *expr = sh.e(*expr),
                    Stmt::Item(i) => *i += sh.si,
                    Stmt::Macro { call, .. } => sh.macro_call(call),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Merging two chunks shifts indexes inside AST v2 nodes the parser does
    /// not build yet (tuple types, closures, qualified paths, generic args),
    /// not only inside the nodes of the current subset.
    #[test]
    fn concat_shifts_v2_nodes() {
        let span = Span::default();
        let mut a = Ast::default();
        a.tys.push(TyExpr::Unit);
        a.ty_spans.push(span);
        a.exprs.push(Expr::Unit);
        a.expr_spans.push(span);
        a.strings.push("a".into());

        let mut b = Ast::default();
        // b-local ids: ty 0 = path type, ty 1 = tuple of it; expr 0 = tuple of unit.
        b.tys.push(TyExpr::Path(vec![PathSeg {
            name: Sym(7),
            args: GenericArgs::Angle(vec![
                GenericArg::Type(TyId(1)),
                GenericArg::Const(ExprId(0)),
                GenericArg::Binding { name: Sym(8), span, kind: BindingKind::EqTy(TyId(1)) },
            ]),
        }]));
        b.tys.push(TyExpr::Tuple(vec![TyId(0)]));
        b.ty_spans = vec![span, span];
        b.exprs.push(Expr::Tuple(vec![ExprId(0)]));
        b.exprs.push(Expr::Closure { is_move: true, is_async: false, params: Vec::new(), ret: Some(TyId(1)), body: ExprId(0) });
        b.expr_spans = vec![span, span];
        b.strings.push("b".into());

        let out = Ast::concat(vec![a, b]);
        // After chunk a (1 ty, 1 expr), b's ty 1 is out ty 2 and expr 0 is out expr 1.
        match &out.tys[1] {
            TyExpr::Path(segs) => match &segs[0].args {
                GenericArgs::Angle(args) => {
                    assert!(matches!(args[0], GenericArg::Type(TyId(2))));
                    assert!(matches!(args[1], GenericArg::Const(ExprId(1))));
                    assert!(matches!(&args[2], GenericArg::Binding { kind: BindingKind::EqTy(TyId(2)), .. }));
                }
                other => panic!("want angle args, got {other:?}"),
            },
            _ => panic!("want path type"),
        }
        assert!(matches!(&out.tys[2], TyExpr::Tuple(ts) if ts == &vec![TyId(1)]));
        assert!(matches!(&out.exprs[1], Expr::Tuple(es) if es == &vec![ExprId(1)]));
        assert!(matches!(&out.exprs[2], Expr::Closure { ret: Some(TyId(2)), body: ExprId(1), .. }));
    }
}
