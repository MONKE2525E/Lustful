// Syntax tree. Nodes live in flat arenas and refer to each other by u32 index, not by pointer.
use crate::diag::Span;
use crate::intern::Sym;
use crate::lexer::IntSuffix;

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
    pub kind: ItemKind,
}

pub enum ItemKind {
    Fn(FnDef),
    Struct(StructDef),
    Enum(EnumDef),
    Impl(ImplDef),
    Use,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SelfKind {
    Value,
    Ref,
    RefMut,
}

pub struct SelfParam {
    pub kind: SelfKind,
    pub mutable: bool,
    pub span: Span,
}

pub struct Param {
    pub name: Sym,
    pub mutable: bool,
    pub ty: TyId,
    pub span: Span,
}

pub struct FnDef {
    pub name: Sym,
    pub name_span: Span,
    /// True for `#[test]` functions. Used by `lust test`; ignored by normal builds.
    pub is_test: bool,
    pub self_param: Option<SelfParam>,
    pub params: Vec<Param>,
    pub ret: Option<TyId>,
    pub body: BlockId,
    /// Expressions and patterns of this function are contiguous: `exprs.0..exprs.1`.
    pub exprs: (u32, u32),
    pub pats: (u32, u32),
}

pub struct FieldDef {
    pub name: Sym,
    pub ty: TyId,
    pub span: Span,
}

pub struct StructDef {
    pub name: Sym,
    pub name_span: Span,
    pub fields: Vec<FieldDef>,
    pub derives: Vec<(Sym, Span)>,
}

pub enum VariantFields {
    Unit,
    Tuple(Vec<TyId>),
    Struct(Vec<FieldDef>),
}

pub struct VariantDef {
    pub name: Sym,
    pub fields: VariantFields,
    pub span: Span,
}

pub struct EnumDef {
    pub name: Sym,
    pub name_span: Span,
    pub variants: Vec<VariantDef>,
    pub derives: Vec<(Sym, Span)>,
}

pub struct ImplDef {
    pub self_ty: TyId,
    pub fns: Vec<FnDef>,
}

#[derive(Clone, Debug)]
pub struct PathSeg {
    pub name: Sym,
    pub generics: Vec<TyId>,
}

pub enum TyExpr {
    Path(Vec<PathSeg>),
    Ref { mutable: bool, inner: TyId },
    Unit,
}

pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Option<ExprId>,
    pub span: Span,
}

pub enum Stmt {
    Let { pat: PatId, ty: Option<TyId>, init: Option<ExprId>, span: Span },
    Expr { expr: ExprId, semi: bool },
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
    pub pat: PatId,
    pub guard: Option<ExprId>,
    pub body: ExprId,
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
    If { cond: ExprId, then: BlockId, els: Option<ExprId> },
    While { cond: ExprId, body: BlockId },
    Loop { body: BlockId },
    For { pat: PatId, iter: ExprId, body: BlockId },
    Match { scrut: ExprId, arms: Vec<Arm> },
    Call { callee: ExprId, args: Vec<ExprId> },
    MethodCall { recv: ExprId, name: Sym, name_span: Span, generics: Vec<TyId>, args: Vec<ExprId> },
    Field { base: ExprId, name: Sym },
    Index { base: ExprId, index: ExprId },
    Binary { op: BinOp, lhs: ExprId, rhs: ExprId },
    Unary { op: UnOp, expr: ExprId },
    Cast { expr: ExprId, ty: TyId },
    Ref { mutable: bool, expr: ExprId },
    Deref(ExprId),
    Assign { lhs: ExprId, rhs: ExprId },
    AssignOp { op: BinOp, lhs: ExprId, rhs: ExprId },
    StructLit { path: Vec<PathSeg>, fields: Vec<(Sym, Span, ExprId)> },
    Range { lo: Option<ExprId>, hi: Option<ExprId>, inclusive: bool },
    Break(Option<ExprId>),
    Continue,
    Return(Option<ExprId>),
    Macro { kind: MacroKind, args: Vec<ExprId>, fmt: Vec<FmtPiece>, repeat: bool },
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
    Range {
        lo: ExprId,
        hi: ExprId,
    },
}

/// Index offsets for merging one chunk's arenas after another's.
#[derive(Clone, Copy)]
struct Shift {
    e: u32,
    p: u32,
    t: u32,
    b: u32,
    s: u32,
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
    fn path(&self, segs: &mut [PathSeg]) {
        segs.iter_mut().for_each(|s| self.ts(&mut s.generics));
    }
    fn fn_def(&self, f: &mut FnDef) {
        f.params.iter_mut().for_each(|p| p.ty = self.t(p.ty));
        f.ret = f.ret.map(|t| self.t(t));
        f.body = self.b(f.body);
        f.exprs = (f.exprs.0 + self.e, f.exprs.1 + self.e);
        f.pats = (f.pats.0 + self.p, f.pats.1 + self.p);
    }
    fn fields(&self, fs: &mut [FieldDef]) {
        fs.iter_mut().for_each(|f| f.ty = self.t(f.ty));
    }
}

impl Ast {
    /// Merges chunk ASTs in order. Index shifting runs in parallel, one chunk per thread.
    pub fn concat(mut chunks: Vec<Ast>) -> Ast {
        let mut sh = Shift { e: 0, p: 0, t: 0, b: 0, s: 0 };
        let mut shifts = Vec::with_capacity(chunks.len());
        for c in &chunks {
            shifts.push(sh);
            sh = Shift {
                e: sh.e + c.exprs.len() as u32,
                p: sh.p + c.pats.len() as u32,
                t: sh.t + c.tys.len() as u32,
                b: sh.b + c.blocks.len() as u32,
                s: sh.s + c.strings.len() as u32,
            };
        }
        std::thread::scope(|scope| {
            for (c, &s) in chunks.iter_mut().zip(&shifts).skip(1) {
                scope.spawn(move || c.shift(s));
            }
        });
        let mut out = Ast {
            items: Vec::with_capacity(chunks.iter().map(|c| c.items.len()).sum()),
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
        };
        o.shift(sh);
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
        for item in &mut o.items {
            match &mut item.kind {
                ItemKind::Fn(f) => sh.fn_def(f),
                ItemKind::Struct(s) => sh.fields(&mut s.fields),
                ItemKind::Enum(e) => e.variants.iter_mut().for_each(|v| match &mut v.fields {
                    VariantFields::Unit => {}
                    VariantFields::Tuple(ts) => sh.ts(ts),
                    VariantFields::Struct(fs) => sh.fields(fs),
                }),
                ItemKind::Impl(imp) => {
                    imp.self_ty = sh.t(imp.self_ty);
                    imp.fns.iter_mut().for_each(|f| sh.fn_def(f));
                }
                ItemKind::Use => {}
            }
        }
        for e in &mut o.exprs {
            match e {
                Expr::Int(..) | Expr::Bool(_) | Expr::Char(_) | Expr::Unit | Expr::SelfValue | Expr::Continue => {}
                Expr::Str(i) => *i += sh.s,
                Expr::Path(segs) => sh.path(segs),
                Expr::Block(b) | Expr::Loop { body: b } => *b = sh.b(*b),
                Expr::If { cond, then, els } => {
                    *cond = sh.e(*cond);
                    *then = sh.b(*then);
                    *els = els.map(|x| sh.e(x));
                }
                Expr::While { cond, body } => {
                    *cond = sh.e(*cond);
                    *body = sh.b(*body);
                }
                Expr::For { pat, iter, body } => {
                    *pat = sh.p(*pat);
                    *iter = sh.e(*iter);
                    *body = sh.b(*body);
                }
                Expr::Match { scrut, arms } => {
                    *scrut = sh.e(*scrut);
                    for a in arms {
                        a.pat = sh.p(a.pat);
                        a.guard = a.guard.map(|g| sh.e(g));
                        a.body = sh.e(a.body);
                    }
                }
                Expr::Call { callee, args } => {
                    *callee = sh.e(*callee);
                    sh.es(args);
                }
                Expr::MethodCall { recv, generics, args, .. } => {
                    *recv = sh.e(*recv);
                    sh.ts(generics);
                    sh.es(args);
                }
                Expr::Field { base, .. } => *base = sh.e(*base),
                Expr::Index { base, index } => {
                    *base = sh.e(*base);
                    *index = sh.e(*index);
                }
                Expr::Binary { lhs, rhs, .. } | Expr::Assign { lhs, rhs } | Expr::AssignOp { lhs, rhs, .. } => {
                    *lhs = sh.e(*lhs);
                    *rhs = sh.e(*rhs);
                }
                Expr::Unary { expr, .. } | Expr::Ref { expr, .. } | Expr::Deref(expr) => *expr = sh.e(*expr),
                Expr::Cast { expr, ty } => {
                    *expr = sh.e(*expr);
                    *ty = sh.t(*ty);
                }
                Expr::StructLit { path, fields } => {
                    sh.path(path);
                    fields.iter_mut().for_each(|f| f.2 = sh.e(f.2));
                }
                Expr::Range { lo, hi, .. } => {
                    *lo = lo.map(|x| sh.e(x));
                    *hi = hi.map(|x| sh.e(x));
                }
                Expr::Break(v) | Expr::Return(v) => *v = v.map(|x| sh.e(x)),
                Expr::Macro { args, .. } => sh.es(args),
            }
        }
        for p in &mut o.pats {
            match p {
                Pat::Wild | Pat::Binding { .. } => {}
                Pat::Lit(e) => *e = sh.e(*e),
                Pat::Range { lo, hi } => {
                    *lo = sh.e(*lo);
                    *hi = sh.e(*hi);
                }
                Pat::Path(segs) => sh.path(segs),
                Pat::TupleStruct { path, elems } => {
                    sh.path(path);
                    elems.iter_mut().for_each(|x| *x = sh.p(*x));
                }
                Pat::Struct { path, fields, .. } => {
                    sh.path(path);
                    fields.iter_mut().for_each(|f| f.1 = sh.p(f.1));
                }
                Pat::Or(alts) => alts.iter_mut().for_each(|x| *x = sh.p(*x)),
            }
        }
        for t in &mut o.tys {
            match t {
                TyExpr::Path(segs) => sh.path(segs),
                TyExpr::Ref { inner, .. } => *inner = sh.t(*inner),
                TyExpr::Unit => {}
            }
        }
        for b in &mut o.blocks {
            b.tail = b.tail.map(|x| sh.e(x));
            for st in &mut b.stmts {
                match st {
                    Stmt::Let { pat, ty, init, .. } => {
                        *pat = sh.p(*pat);
                        *ty = ty.map(|t| sh.t(t));
                        *init = init.map(|x| sh.e(x));
                    }
                    Stmt::Expr { expr, .. } => *expr = sh.e(*expr),
                }
            }
        }
    }
}
