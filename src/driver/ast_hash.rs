// Structural AST scan for the resolver path: per-item hashes (everything
// except fn bodies) and per-fn body hashes plus body identifier sets, in
// the same shapes `scan::scan` produces from tokens for the single-file
// path. The worklist's merged Ast is post-expansion, post-cfg-strip, and
// path-rewritten, so hashing it covers macro-definition edits and cfg
// strip effects that a source-text body hash cannot see. Spans are never
// hashed (positions do not change meaning, and an edit above a body must
// not rehash it); string-table indices hash by content, because indices
// shift when other files change. Matches are exhaustive with no wildcard
// arm: a new Ast variant fails to compile here instead of silently
// hashing as "unchanged", which would be a false-reuse bug.
use crate::ast::*;
use crate::intern::{FxHasher, Sym};
use crate::lexer::{Tok, TokenTree};
use crate::scan;
use std::hash::{Hash, Hasher};

/// One scan of a merged crate Ast: item scans parallel to `ast.items`,
/// and per-fn (body hash, body idents) in fn-location order (top-level
/// fns and impl methods in item order, as `collect` numbers them).
pub struct AstScans {
    pub items: Vec<scan::ItemScan>,
    pub bodies: Vec<(u64, Vec<Sym>)>,
}

/// One item's scan and its fns' body scans.
fn scan_item(ast: &Ast, item: &Item) -> (scan::ItemScan, Vec<(u64, Vec<Sym>)>) {
    let mut w = Walker { ast, idents: None };
    let mut h = FxHasher::default();
    w.item(&mut h, item, false);
    let fn_name = match &item.kind {
        ItemKind::Fn(f) => Some(f.name),
        _ => None,
    };
    let scan = scan::ItemScan { hash: h.finish(), fn_name };
    let bodies: Vec<(u64, Vec<Sym>)> = match &item.kind {
        ItemKind::Fn(f) => vec![body_scan(ast, f)],
        ItemKind::Impl(imp) => imp.fns.iter().map(|f| body_scan(ast, f)).collect(),
        _ => Vec::new(),
    };
    (scan, bodies)
}

fn assemble(ast: &Ast, per_item: Vec<(scan::ItemScan, Vec<(u64, Vec<Sym>)>)>) -> AstScans {
    let mut items = Vec::with_capacity(per_item.len());
    let mut bodies = Vec::new();
    for (scan, bs) in per_item {
        items.push(scan);
        bodies.extend(bs);
    }
    // Nested fns follow the top-level fns, in stmt item order (collect's order).
    for item in &ast.stmt_items {
        if let ItemKind::Fn(f) = &item.kind {
            bodies.push(body_scan(ast, f));
        }
    }
    AstScans { items, bodies }
}

/// Scans one merged Ast. Item and body hashing are read-only walks,
/// so they run in parallel across items (one pass produces each
/// item's scan and its fns' body scans). See the module docs.
pub(crate) fn scan_ast(ast: &Ast) -> AstScans {
    assemble(ast, super::compile::par_map(&ast.items, |item| scan_item(ast, item)))
}

/// Scans one per-file Ast chunk serially. The worklist scans each
/// flattened chunk on its own (in parallel across files) and caches
/// the result per file; chunk scans concatenate to the merged scan
/// because string indices hash by content and spans never hash.
pub(crate) fn scan_ast_seq(ast: &Ast) -> AstScans {
    assemble(ast, ast.items.iter().map(|item| scan_item(ast, item)).collect())
}

/// The hash of one fn's head: name, qualifiers, generics, self and
/// parameter bindings (names, patterns, types), return type, and
/// where clause. The driver stores it per slot: a body is checked
/// against its own head, so a head change always rechecks the fn
/// itself, even when its body hash and caller-visible `Sig`
/// fingerprint (which excludes parameter names) both stand.
pub(crate) fn fn_head_hash(ast: &Ast, f: &FnDef) -> u64 {
    let mut w = Walker { ast, idents: None };
    let mut h = FxHasher::default();
    "ast-fn-head-v1".hash(&mut h);
    w.fn_head(&mut h, f, false);
    h.finish()
}

/// The body hash and sorted identifier set of one fn.
fn body_scan(ast: &Ast, f: &FnDef) -> (u64, Vec<Sym>) {
    let mut idents = Vec::new();
    let mut w = Walker { ast, idents: Some(&mut idents) };
    let mut h = FxHasher::default();
    "ast-body-v1".hash(&mut h);
    match f.body {
        Some(b) => w.block(&mut h, b),
        None => 0u8.hash(&mut h),
    }
    let hash = h.finish();
    let mut idents = idents;
    idents.sort_unstable();
    idents.dedup();
    (hash, idents)
}

struct Walker<'a> {
    ast: &'a Ast,
    /// When set (body scans), every hashed identifier is also recorded.
    idents: Option<&'a mut Vec<Sym>>,
}

impl Walker<'_> {
    fn sym(&mut self, h: &mut FxHasher, s: Sym) {
        s.hash(h);
        if let Some(v) = &mut self.idents {
            v.push(s);
        }
    }

    fn string_at(&mut self, h: &mut FxHasher, i: u32) {
        self.ast.strings.get(i as usize).map_or("", String::as_str).hash(h);
    }

    fn lifetime(&mut self, h: &mut FxHasher, lt: &Lifetime) {
        self.sym(h, lt.name);
    }

    fn vis(&mut self, h: &mut FxHasher, v: &Vis) {
        match v {
            Vis::Private => 0u8.hash(h),
            Vis::Public => 1u8.hash(h),
            Vis::Restricted { path, .. } => {
                2u8.hash(h);
                self.path(h, path);
            }
        }
    }

    fn trees(&mut self, h: &mut FxHasher, trees: &[TokenTree]) {
        (trees.len() as u64).hash(h);
        for t in trees {
            match t {
                TokenTree::Token(tok) => {
                    0u8.hash(h);
                    std::mem::discriminant(&tok.tok).hash(h);
                    match &tok.tok {
                        Tok::Ident(s) | Tok::Reserved(s) | Tok::Lifetime(s) => self.sym(h, *s),
                        Tok::Int(v, suf) => {
                            v.hash(h);
                            suf.map(|s| s as u8).hash(h);
                        }
                        Tok::Char(c) => c.hash(h),
                        t => {
                            if let Some(i) = t.string_index() {
                                self.string_at(h, i);
                            }
                        }
                    }
                }
                TokenTree::Delim(d, inner, _) => {
                    1u8.hash(h);
                    std::mem::discriminant(d).hash(h);
                    self.trees(h, inner);
                }
            }
        }
    }

    fn attrs(&mut self, h: &mut FxHasher, attrs: &[Attr]) {
        (attrs.len() as u64).hash(h);
        for a in attrs {
            match a.style {
                AttrStyle::Outer => 0u8.hash(h),
                AttrStyle::Inner => 1u8.hash(h),
            }
            self.path(h, &a.path);
            match &a.input {
                AttrInput::None => 0u8.hash(h),
                AttrInput::Eq(e) => {
                    1u8.hash(h);
                    self.expr(h, *e);
                }
                AttrInput::List(d, trees) => {
                    2u8.hash(h);
                    std::mem::discriminant(d).hash(h);
                    self.trees(h, trees);
                }
            }
        }
    }

    fn path(&mut self, h: &mut FxHasher, segs: &[PathSeg]) {
        (segs.len() as u64).hash(h);
        for s in segs {
            self.sym(h, s.name);
            self.generic_args(h, &s.args);
        }
    }

    fn generic_args(&mut self, h: &mut FxHasher, args: &GenericArgs) {
        match args {
            GenericArgs::None => 0u8.hash(h),
            GenericArgs::Angle(args) => {
                1u8.hash(h);
                (args.len() as u64).hash(h);
                for a in args {
                    self.generic_arg(h, a);
                }
            }
            GenericArgs::Parenthesized { inputs, output } => {
                2u8.hash(h);
                for t in inputs {
                    self.ty(h, *t);
                }
                match output {
                    Some(t) => self.ty(h, *t),
                    None => 0u8.hash(h),
                }
            }
        }
    }

    fn generic_arg(&mut self, h: &mut FxHasher, a: &GenericArg) {
        match a {
            GenericArg::Type(t) => {
                0u8.hash(h);
                self.ty(h, *t);
            }
            GenericArg::Lifetime(lt) => {
                1u8.hash(h);
                self.lifetime(h, lt);
            }
            GenericArg::Const(e) => {
                2u8.hash(h);
                self.expr(h, *e);
            }
            GenericArg::Binding { name, kind, .. } => {
                3u8.hash(h);
                self.sym(h, *name);
                match kind {
                    BindingKind::EqTy(t) => {
                        0u8.hash(h);
                        self.ty(h, *t);
                    }
                    BindingKind::EqConst(e) => {
                        1u8.hash(h);
                        self.expr(h, *e);
                    }
                    BindingKind::Constraint(bounds) => {
                        2u8.hash(h);
                        self.bounds(h, bounds);
                    }
                }
            }
        }
    }

    fn bounds(&mut self, h: &mut FxHasher, bounds: &[TraitBound]) {
        (bounds.len() as u64).hash(h);
        for b in bounds {
            match b {
                TraitBound::Trait { binder, trait_ref, maybe } => {
                    0u8.hash(h);
                    for lt in binder {
                        self.lifetime(h, lt);
                    }
                    self.path(h, &trait_ref.path);
                    maybe.hash(h);
                }
                TraitBound::Lifetime(lt) => {
                    1u8.hash(h);
                    self.lifetime(h, lt);
                }
            }
        }
    }

    fn generics(&mut self, h: &mut FxHasher, g: &Generics) {
        (g.params.len() as u64).hash(h);
        for p in &g.params {
            match p {
                GenericParam::Lifetime { lt, bounds, attrs } => {
                    0u8.hash(h);
                    self.lifetime(h, lt);
                    for b in bounds {
                        self.lifetime(h, b);
                    }
                    self.attrs(h, attrs);
                }
                GenericParam::Type { name, bounds, default, attrs, .. } => {
                    1u8.hash(h);
                    self.sym(h, *name);
                    self.bounds(h, bounds);
                    match default {
                        Some(t) => self.ty(h, *t),
                        None => 0u8.hash(h),
                    }
                    self.attrs(h, attrs);
                }
                GenericParam::Const { name, ty, default, attrs, .. } => {
                    2u8.hash(h);
                    self.sym(h, *name);
                    self.ty(h, *ty);
                    match default {
                        Some(e) => self.expr(h, *e),
                        None => 0u8.hash(h),
                    }
                    self.attrs(h, attrs);
                }
            }
        }
    }

    fn where_clause(&mut self, h: &mut FxHasher, w: &WhereClause) {
        (w.preds.len() as u64).hash(h);
        for p in &w.preds {
            match p {
                WherePred::Type { binder, ty, bounds } => {
                    0u8.hash(h);
                    for lt in binder {
                        self.lifetime(h, lt);
                    }
                    self.ty(h, *ty);
                    self.bounds(h, bounds);
                }
                WherePred::Lifetime { lt, bounds } => {
                    1u8.hash(h);
                    self.lifetime(h, lt);
                    for b in bounds {
                        self.lifetime(h, b);
                    }
                }
            }
        }
    }

    fn qual(&mut self, h: &mut FxHasher, q: &FnQual) {
        (q.is_const, q.is_async, q.is_unsafe).hash(h);
        match q.abi {
            Some(i) => self.string_at(h, i),
            None => 0u8.hash(h),
        }
    }

    fn ty(&mut self, h: &mut FxHasher, t: TyId) {
        match self.ast.ty(t) {
            TyExpr::Path(segs) => {
                0u8.hash(h);
                self.path(h, segs);
            }
            TyExpr::Ref { lifetime, mutable, inner } => {
                1u8.hash(h);
                match lifetime {
                    Some(lt) => self.lifetime(h, lt),
                    None => 0u8.hash(h),
                }
                mutable.hash(h);
                self.ty(h, *inner);
            }
            TyExpr::Unit => 2u8.hash(h),
            TyExpr::Tuple(ts) => {
                3u8.hash(h);
                (ts.len() as u64).hash(h);
                for t in ts {
                    self.ty(h, *t);
                }
            }
            TyExpr::Array { inner, len } => {
                4u8.hash(h);
                self.ty(h, *inner);
                self.expr(h, *len);
            }
            TyExpr::Slice(inner) => {
                5u8.hash(h);
                self.ty(h, *inner);
            }
            TyExpr::Ptr { mutable, inner } => {
                (6u8, mutable).hash(h);
                self.ty(h, *inner);
            }
            TyExpr::FnPtr { binder, qual, inputs, variadic, ret } => {
                7u8.hash(h);
                for lt in binder {
                    self.lifetime(h, lt);
                }
                self.qual(h, qual);
                (inputs.len() as u64).hash(h);
                for p in inputs {
                    match p.name {
                        Some(n) => self.sym(h, n),
                        None => 0u8.hash(h),
                    }
                    self.attrs(h, &p.attrs);
                    self.ty(h, p.ty);
                }
                variadic.hash(h);
                match ret {
                    Some(t) => self.ty(h, *t),
                    None => 0u8.hash(h),
                }
            }
            TyExpr::Dyn { binder, bounds, lifetime } => {
                8u8.hash(h);
                for lt in binder {
                    self.lifetime(h, lt);
                }
                self.bounds(h, bounds);
                match lifetime {
                    Some(lt) => self.lifetime(h, lt),
                    None => 0u8.hash(h),
                }
            }
            TyExpr::ImplTrait { bounds } => {
                9u8.hash(h);
                self.bounds(h, bounds);
            }
            TyExpr::QPath { self_ty, trait_path, segs } => {
                10u8.hash(h);
                self.ty(h, *self_ty);
                self.path(h, trait_path);
                self.path(h, segs);
            }
            TyExpr::Never => 11u8.hash(h),
            TyExpr::Paren(inner) => {
                12u8.hash(h);
                self.ty(h, *inner);
            }
            TyExpr::Infer => 13u8.hash(h),
            TyExpr::MacroCall(c) => {
                14u8.hash(h);
                self.macro_call(h, c);
            }
        }
    }

    fn macro_call(&mut self, h: &mut FxHasher, c: &MacroCall) {
        self.path(h, &c.path);
        std::mem::discriminant(&c.delim).hash(h);
        self.trees(h, &c.tokens);
    }

    fn block(&mut self, h: &mut FxHasher, b: BlockId) {
        let block = self.ast.block(b);
        self.attrs(h, &block.inner_attrs);
        (block.stmts.len() as u64).hash(h);
        for s in &block.stmts {
            self.stmt(h, s);
        }
        self.attrs(h, &block.tail_attrs);
        match block.tail {
            Some(e) => self.expr(h, e),
            None => 0u8.hash(h),
        }
    }

    fn stmt(&mut self, h: &mut FxHasher, s: &Stmt) {
        match s {
            Stmt::Let { pat, ty, init, els, attrs, .. } => {
                0u8.hash(h);
                self.pat(h, *pat);
                match ty {
                    Some(t) => self.ty(h, *t),
                    None => 0u8.hash(h),
                }
                match init {
                    Some(e) => self.expr(h, *e),
                    None => 0u8.hash(h),
                }
                match els {
                    Some(b) => self.block(h, *b),
                    None => 0u8.hash(h),
                }
                self.attrs(h, attrs);
            }
            Stmt::Expr { expr, semi, attrs } => {
                (1u8, semi).hash(h);
                self.expr(h, *expr);
                self.attrs(h, attrs);
            }
            Stmt::Item(i) => {
                2u8.hash(h);
                // A body-local item is part of this body's meaning:
                // hash it whole, fn bodies included.
                let item = &self.ast.stmt_items[*i as usize];
                self.item(h, item, true);
            }
            Stmt::Macro { call, semi } => {
                (3u8, semi).hash(h);
                self.macro_call(h, call);
            }
        }
    }

    fn label(&mut self, h: &mut FxHasher, l: &Option<Label>) {
        match l {
            Some(l) => self.lifetime(h, l),
            None => 0u8.hash(h),
        }
    }

    fn expr(&mut self, h: &mut FxHasher, e: ExprId) {
        match self.ast.expr(e) {
            Expr::Int(v, suf) => {
                0u8.hash(h);
                v.hash(h);
                suf.map(|s| s as u8).hash(h);
            }
            Expr::Bool(b) => (1u8, b).hash(h),
            Expr::Str(i) => {
                2u8.hash(h);
                self.string_at(h, *i);
            }
            Expr::Char(c) => (3u8, c).hash(h),
            Expr::Unit => 4u8.hash(h),
            Expr::Path(segs) => {
                5u8.hash(h);
                self.path(h, segs);
            }
            Expr::SelfValue => 6u8.hash(h),
            Expr::Block(b) => {
                7u8.hash(h);
                self.block(h, *b);
            }
            Expr::If { cond, then, els } => {
                8u8.hash(h);
                self.expr(h, *cond);
                self.block(h, *then);
                match els {
                    Some(e) => self.expr(h, *e),
                    None => 0u8.hash(h),
                }
            }
            Expr::While { label, cond, body } => {
                9u8.hash(h);
                self.label(h, label);
                self.expr(h, *cond);
                self.block(h, *body);
            }
            Expr::Loop { label, body } => {
                10u8.hash(h);
                self.label(h, label);
                self.block(h, *body);
            }
            Expr::For { label, pat, iter, body } => {
                11u8.hash(h);
                self.label(h, label);
                self.pat(h, *pat);
                self.expr(h, *iter);
                self.block(h, *body);
            }
            Expr::Match { scrut, arms } => {
                12u8.hash(h);
                self.expr(h, *scrut);
                (arms.len() as u64).hash(h);
                for a in arms {
                    self.attrs(h, &a.attrs);
                    self.pat(h, a.pat);
                    match a.guard {
                        Some(g) => self.expr(h, g),
                        None => 0u8.hash(h),
                    }
                    self.expr(h, a.body);
                }
            }
            Expr::Call { callee, args } => {
                13u8.hash(h);
                self.expr(h, *callee);
                (args.len() as u64).hash(h);
                for a in args {
                    self.expr(h, *a);
                }
            }
            Expr::MethodCall { recv, name, generic_args, args, .. } => {
                14u8.hash(h);
                self.expr(h, *recv);
                self.sym(h, *name);
                (generic_args.len() as u64).hash(h);
                for a in generic_args {
                    self.generic_arg(h, a);
                }
                (args.len() as u64).hash(h);
                for a in args {
                    self.expr(h, *a);
                }
            }
            Expr::Field { base, name } => {
                15u8.hash(h);
                self.expr(h, *base);
                self.sym(h, *name);
            }
            Expr::Index { base, index } => {
                16u8.hash(h);
                self.expr(h, *base);
                self.expr(h, *index);
            }
            Expr::Binary { op, lhs, rhs } => {
                17u8.hash(h);
                std::mem::discriminant(op).hash(h);
                self.expr(h, *lhs);
                self.expr(h, *rhs);
            }
            Expr::Unary { op, expr } => {
                18u8.hash(h);
                std::mem::discriminant(op).hash(h);
                self.expr(h, *expr);
            }
            Expr::Cast { expr, ty } => {
                19u8.hash(h);
                self.expr(h, *expr);
                self.ty(h, *ty);
            }
            Expr::Ref { mutable, raw, expr } => {
                (20u8, mutable, raw).hash(h);
                self.expr(h, *expr);
            }
            Expr::Deref(e) => {
                21u8.hash(h);
                self.expr(h, *e);
            }
            Expr::Assign { lhs, rhs } => {
                22u8.hash(h);
                self.expr(h, *lhs);
                self.expr(h, *rhs);
            }
            Expr::AssignOp { op, lhs, rhs } => {
                23u8.hash(h);
                std::mem::discriminant(op).hash(h);
                self.expr(h, *lhs);
                self.expr(h, *rhs);
            }
            Expr::StructLit { path, fields, update } => {
                24u8.hash(h);
                self.path(h, path);
                (fields.len() as u64).hash(h);
                for (name, _, e) in fields {
                    self.sym(h, *name);
                    self.expr(h, *e);
                }
                match update {
                    Some(e) => self.expr(h, *e),
                    None => 0u8.hash(h),
                }
            }
            Expr::Range { lo, hi, inclusive } => {
                (25u8, inclusive).hash(h);
                match lo {
                    Some(e) => self.expr(h, *e),
                    None => 0u8.hash(h),
                }
                match hi {
                    Some(e) => self.expr(h, *e),
                    None => 0u8.hash(h),
                }
            }
            Expr::Break { label, value } => {
                26u8.hash(h);
                self.label(h, label);
                match value {
                    Some(e) => self.expr(h, *e),
                    None => 0u8.hash(h),
                }
            }
            Expr::Continue(label) => {
                27u8.hash(h);
                self.label(h, label);
            }
            Expr::Return(v) => {
                28u8.hash(h);
                match v {
                    Some(e) => self.expr(h, *e),
                    None => 0u8.hash(h),
                }
            }
            Expr::Macro { kind, args, fmt, repeat } => {
                (29u8, repeat).hash(h);
                std::mem::discriminant(kind).hash(h);
                (args.len() as u64).hash(h);
                for a in args {
                    self.expr(h, *a);
                }
                (fmt.len() as u64).hash(h);
                for f in fmt {
                    match f {
                        FmtPiece::Lit(s) => {
                            0u8.hash(h);
                            s.hash(h);
                        }
                        FmtPiece::Arg { index, debug, spec } => {
                            (1u8, *index as u64, debug).hash(h);
                            (spec.kind as u8, spec.fill, spec.align, spec.plus, spec.alt, spec.zero, spec.width, spec.precision).hash(h);
                        }
                    }
                }
            }
            Expr::Float(i) => {
                30u8.hash(h);
                self.string_at(h, *i);
            }
            Expr::Tuple(es) => {
                31u8.hash(h);
                (es.len() as u64).hash(h);
                for e in es {
                    self.expr(h, *e);
                }
            }
            Expr::Array(es) => {
                32u8.hash(h);
                (es.len() as u64).hash(h);
                for e in es {
                    self.expr(h, *e);
                }
            }
            Expr::ArrayRepeat { value, len } => {
                33u8.hash(h);
                self.expr(h, *value);
                self.expr(h, *len);
            }
            Expr::Closure { is_move, is_async, params, ret, body } => {
                (34u8, is_move, is_async).hash(h);
                (params.len() as u64).hash(h);
                for p in params {
                    self.pat(h, p.pat);
                    match p.ty {
                        Some(t) => self.ty(h, t),
                        None => 0u8.hash(h),
                    }
                    self.attrs(h, &p.attrs);
                }
                match ret {
                    Some(t) => self.ty(h, *t),
                    None => 0u8.hash(h),
                }
                self.expr(h, *body);
            }
            Expr::Try(e) => {
                35u8.hash(h);
                self.expr(h, *e);
            }
            Expr::Await(e) => {
                36u8.hash(h);
                self.expr(h, *e);
            }
            Expr::AsyncBlock { is_move, body } => {
                (37u8, is_move).hash(h);
                self.block(h, *body);
            }
            Expr::UnsafeBlock(b) => {
                38u8.hash(h);
                self.block(h, *b);
            }
            Expr::LabeledBlock { label, body } => {
                39u8.hash(h);
                self.lifetime(h, label);
                self.block(h, *body);
            }
            Expr::Let { pat, scrut } => {
                40u8.hash(h);
                self.pat(h, *pat);
                self.expr(h, *scrut);
            }
            Expr::TupleField { base, index } => {
                (41u8, index).hash(h);
                self.expr(h, *base);
            }
            Expr::QPath { self_ty, trait_path, segs } => {
                42u8.hash(h);
                self.ty(h, *self_ty);
                self.path(h, trait_path);
                self.path(h, segs);
            }
            Expr::ConstBlock(b) => {
                43u8.hash(h);
                self.block(h, *b);
            }
            Expr::Underscore => 44u8.hash(h),
            Expr::MacroCall(c) => {
                45u8.hash(h);
                self.macro_call(h, c);
            }
            Expr::OffsetOf { ty, fields } => {
                46u8.hash(h);
                self.ty(h, *ty);
                (fields.len() as u64).hash(h);
                for f in fields {
                    match f {
                        crate::ast::OffsetField::Name(s) => {
                            0u8.hash(h);
                            self.sym(h, *s);
                        }
                        crate::ast::OffsetField::Index(i) => {
                            1u8.hash(h);
                            i.hash(h);
                        }
                    }
                }
            }
        }
    }

    fn pat(&mut self, h: &mut FxHasher, p: PatId) {
        match self.ast.pat(p) {
            Pat::Wild => 0u8.hash(h),
            Pat::Binding { name, mutable, by_ref } => {
                (1u8, mutable, by_ref).hash(h);
                self.sym(h, *name);
            }
            Pat::Lit(e) => {
                2u8.hash(h);
                self.expr(h, *e);
            }
            Pat::Path(segs) => {
                3u8.hash(h);
                self.path(h, segs);
            }
            Pat::TupleStruct { path, elems } => {
                4u8.hash(h);
                self.path(h, path);
                (elems.len() as u64).hash(h);
                for e in elems {
                    self.pat(h, *e);
                }
            }
            Pat::Struct { path, fields, rest } => {
                (5u8, rest).hash(h);
                self.path(h, path);
                (fields.len() as u64).hash(h);
                for (name, sub) in fields {
                    self.sym(h, *name);
                    self.pat(h, *sub);
                }
            }
            Pat::Or(elems) => {
                6u8.hash(h);
                (elems.len() as u64).hash(h);
                for e in elems {
                    self.pat(h, *e);
                }
            }
            Pat::Range { lo, hi, inclusive } => {
                (7u8, inclusive).hash(h);
                match lo {
                    Some(e) => self.expr(h, *e),
                    None => 0u8.hash(h),
                }
                match hi {
                    Some(e) => self.expr(h, *e),
                    None => 0u8.hash(h),
                }
            }
            Pat::Tuple(elems) => {
                8u8.hash(h);
                (elems.len() as u64).hash(h);
                for e in elems {
                    self.pat(h, *e);
                }
            }
            Pat::Slice { prefix, middle, suffix } => {
                9u8.hash(h);
                (prefix.len() as u64).hash(h);
                for e in prefix {
                    self.pat(h, *e);
                }
                match middle {
                    Some(m) => self.pat(h, *m),
                    None => 0u8.hash(h),
                }
                (suffix.len() as u64).hash(h);
                for e in suffix {
                    self.pat(h, *e);
                }
            }
            Pat::Ref { mutable, inner } => {
                (10u8, mutable).hash(h);
                self.pat(h, *inner);
            }
            Pat::At { name, mutable, by_ref, inner } => {
                (11u8, mutable, by_ref).hash(h);
                self.sym(h, *name);
                self.pat(h, *inner);
            }
            Pat::Rest => 12u8.hash(h),
            Pat::Paren(inner) => {
                13u8.hash(h);
                self.pat(h, *inner);
            }
            Pat::QPath { self_ty, trait_path, segs } => {
                14u8.hash(h);
                self.ty(h, *self_ty);
                self.path(h, trait_path);
                self.path(h, segs);
            }
            Pat::MacroCall(c) => {
                15u8.hash(h);
                self.macro_call(h, c);
            }
        }
    }
}

impl Walker<'_> {
    /// A fn's signature side: everything but the body block, unless
    /// `with_body` (trait default bodies and body-local items are
    /// environment, not separately numbered fns).
    fn fn_head(&mut self, h: &mut FxHasher, f: &FnDef, with_body: bool) {
        self.sym(h, f.name);
        f.is_test.hash(h);
        self.vis(h, &f.vis);
        self.attrs(h, &f.attrs);
        self.qual(h, &f.qual);
        self.generics(h, &f.generics);
        match &f.self_param {
            Some(sp) => {
                1u8.hash(h);
                match sp.kind {
                    SelfKind::Value => 0u8.hash(h),
                    SelfKind::Ref => 1u8.hash(h),
                    SelfKind::RefMut => 2u8.hash(h),
                    SelfKind::Typed => 3u8.hash(h),
                }
                sp.mutable.hash(h);
                match &sp.lifetime {
                    Some(lt) => self.lifetime(h, lt),
                    None => 0u8.hash(h),
                }
                match sp.ty {
                    Some(t) => self.ty(h, t),
                    None => 0u8.hash(h),
                }
                self.attrs(h, &sp.attrs);
            }
            None => 0u8.hash(h),
        }
        (f.params.len() as u64).hash(h);
        for p in &f.params {
            self.sym(h, p.name);
            p.mutable.hash(h);
            match p.pat {
                Some(pat) => self.pat(h, pat),
                None => 0u8.hash(h),
            }
            self.ty(h, p.ty);
            self.attrs(h, &p.attrs);
        }
        f.variadic.hash(h);
        match f.ret {
            Some(t) => self.ty(h, t),
            None => 0u8.hash(h),
        }
        self.where_clause(h, &f.where_clause);
        if with_body {
            match f.body {
                Some(b) => self.block(h, b),
                None => 0u8.hash(h),
            }
        }
    }

    fn fields(&mut self, h: &mut FxHasher, fields: &VariantFields) {
        let (tag, fs): (u8, &[FieldDef]) = match fields {
            VariantFields::Unit => (0, &[]),
            VariantFields::Tuple(fs) => (1, fs),
            VariantFields::Struct(fs) => (2, fs),
        };
        tag.hash(h);
        (fs.len() as u64).hash(h);
        for fd in fs {
            self.sym(h, fd.name);
            self.vis(h, &fd.vis);
            self.attrs(h, &fd.attrs);
            self.ty(h, fd.ty);
        }
    }

    fn assoc_consts(&mut self, h: &mut FxHasher, consts: &[AssocConstDef]) {
        (consts.len() as u64).hash(h);
        for c in consts {
            self.sym(h, c.name);
            self.vis(h, &c.vis);
            self.attrs(h, &c.attrs);
            self.ty(h, c.ty);
            match c.default {
                Some(e) => self.expr(h, e),
                None => 0u8.hash(h),
            }
        }
    }

    fn assoc_types(&mut self, h: &mut FxHasher, types: &[AssocTypeDef]) {
        (types.len() as u64).hash(h);
        for t in types {
            self.sym(h, t.name);
            self.vis(h, &t.vis);
            self.attrs(h, &t.attrs);
            self.generics(h, &t.generics);
            self.bounds(h, &t.bounds);
            self.where_clause(h, &t.where_clause);
            match t.default {
                Some(ty) => self.ty(h, ty),
                None => 0u8.hash(h),
            }
        }
    }

    fn use_tree(&mut self, h: &mut FxHasher, t: &UseTree) {
        t.leading_colon.hash(h);
        self.path(h, &t.prefix);
        match &t.kind {
            UseKind::Simple { rename } => {
                0u8.hash(h);
                match rename {
                    Some(r) => self.sym(h, *r),
                    None => 0u8.hash(h),
                }
            }
            UseKind::Glob => 1u8.hash(h),
            UseKind::Group(children) => {
                2u8.hash(h);
                (children.len() as u64).hash(h);
                for c in children {
                    self.use_tree(h, c);
                }
            }
        }
    }

    /// One item's environment hash contribution. `with_bodies` includes
    /// fn body blocks (body-local items only; top-level fn bodies are
    /// hashed per fn by `body_scan`).
    fn item(&mut self, h: &mut FxHasher, item: &Item, with_bodies: bool) {
        self.vis(h, &item.vis);
        self.attrs(h, &item.attrs);
        match &item.kind {
            ItemKind::Fn(f) => {
                0u8.hash(h);
                self.fn_head(h, f, with_bodies);
            }
            ItemKind::Struct(s) => {
                1u8.hash(h);
                self.sym(h, s.name);
                self.generics(h, &s.generics);
                self.fields(h, &s.fields);
                self.where_clause(h, &s.where_clause);
                (s.derives.len() as u64).hash(h);
                for (d, _) in &s.derives {
                    self.sym(h, *d);
                }
            }
            ItemKind::Enum(e) => {
                2u8.hash(h);
                self.sym(h, e.name);
                self.generics(h, &e.generics);
                (e.variants.len() as u64).hash(h);
                for v in &e.variants {
                    self.sym(h, v.name);
                    self.attrs(h, &v.attrs);
                    self.fields(h, &v.fields);
                    match v.discriminant {
                        Some(x) => self.expr(h, x),
                        None => 0u8.hash(h),
                    }
                }
                self.where_clause(h, &e.where_clause);
                (e.derives.len() as u64).hash(h);
                for (d, _) in &e.derives {
                    self.sym(h, *d);
                }
            }
            ItemKind::Impl(imp) => {
                3u8.hash(h);
                self.attrs(h, &imp.inner_attrs);
                self.generics(h, &imp.generics);
                (imp.is_unsafe, imp.is_negative).hash(h);
                match &imp.trait_ref {
                    Some(tr) => self.path(h, &tr.path),
                    None => 0u8.hash(h),
                }
                self.ty(h, imp.self_ty);
                self.where_clause(h, &imp.where_clause);
                (imp.fns.len() as u64).hash(h);
                for f in &imp.fns {
                    self.fn_head(h, f, with_bodies);
                }
                self.assoc_consts(h, &imp.consts);
                self.assoc_types(h, &imp.types);
            }
            ItemKind::Use(u) => {
                4u8.hash(h);
                self.use_tree(h, &u.tree);
            }
            ItemKind::Mod(m) => {
                5u8.hash(h);
                self.attrs(h, &m.inner_attrs);
                self.sym(h, m.name);
                match &m.body {
                    Some(items) => {
                        (items.len() as u64).hash(h);
                        for it in items {
                            self.item(h, it, with_bodies);
                        }
                    }
                    None => 0u8.hash(h),
                }
            }
            ItemKind::Trait(t) => {
                6u8.hash(h);
                self.attrs(h, &t.inner_attrs);
                self.sym(h, t.name);
                (t.is_unsafe, t.is_auto).hash(h);
                self.generics(h, &t.generics);
                self.bounds(h, &t.bounds);
                self.where_clause(h, &t.where_clause);
                (t.fns.len() as u64).hash(h);
                for f in &t.fns {
                    // Trait default bodies are environment: they are
                    // not separately numbered fns.
                    self.fn_head(h, f, true);
                }
                self.assoc_consts(h, &t.consts);
                self.assoc_types(h, &t.types);
            }
            ItemKind::Type(a) => {
                7u8.hash(h);
                self.sym(h, a.name);
                self.generics(h, &a.generics);
                self.where_clause(h, &a.where_clause);
                self.ty(h, a.ty);
            }
            ItemKind::Const(c) => {
                8u8.hash(h);
                match c.name {
                    Some(n) => self.sym(h, n),
                    None => 0u8.hash(h),
                }
                self.ty(h, c.ty);
                match c.value {
                    Some(e) => self.expr(h, e),
                    None => 0u8.hash(h),
                }
            }
            ItemKind::Static(s) => {
                (9u8, s.mutable).hash(h);
                self.sym(h, s.name);
                self.ty(h, s.ty);
                match s.value {
                    Some(e) => self.expr(h, e),
                    None => 0u8.hash(h),
                }
            }
            ItemKind::MacroRules(m) => {
                10u8.hash(h);
                self.sym(h, m.name);
                std::mem::discriminant(&m.delim).hash(h);
                self.trees(h, &m.tokens);
            }
            ItemKind::ExternCrate(e) => {
                11u8.hash(h);
                self.sym(h, e.name);
                match e.rename {
                    Some(r) => self.sym(h, r),
                    None => 0u8.hash(h),
                }
            }
            ItemKind::ExternBlock(b) => {
                (12u8, b.is_unsafe).hash(h);
                match b.abi {
                    Some(i) => self.string_at(h, i),
                    None => 0u8.hash(h),
                }
                (b.items.len() as u64).hash(h);
                for it in &b.items {
                    match it {
                        ForeignItem::Fn(f) => {
                            0u8.hash(h);
                            self.fn_head(h, f, with_bodies);
                        }
                        ForeignItem::Static(s) => {
                            (1u8, s.mutable).hash(h);
                            self.sym(h, s.name);
                            self.ty(h, s.ty);
                            match s.value {
                                Some(e) => self.expr(h, e),
                                None => 0u8.hash(h),
                            }
                        }
                        ForeignItem::Type { name, vis, attrs, generics, where_clause, .. } => {
                            2u8.hash(h);
                            self.sym(h, *name);
                            self.vis(h, vis);
                            self.attrs(h, attrs);
                            self.generics(h, generics);
                            self.where_clause(h, where_clause);
                        }
                        ForeignItem::MacroCall(c) => {
                            3u8.hash(h);
                            self.macro_call(h, c);
                        }
                    }
                }
            }
            ItemKind::Union(u) => {
                13u8.hash(h);
                self.sym(h, u.name);
                self.generics(h, &u.generics);
                (u.fields.len() as u64).hash(h);
                for fd in &u.fields {
                    self.sym(h, fd.name);
                    self.vis(h, &fd.vis);
                    self.attrs(h, &fd.attrs);
                    self.ty(h, fd.ty);
                }
                self.where_clause(h, &u.where_clause);
                (u.derives.len() as u64).hash(h);
                for (d, _) in &u.derives {
                    self.sym(h, *d);
                }
            }
            ItemKind::MacroCall(c) => {
                14u8.hash(h);
                self.macro_call(h, c);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::FileId;
    use crate::intern::{Interner, Known};
    use crate::{lexer, parser};

    fn scan_src(src: &str) -> AstScans {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let lexed = lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        scan_ast(&ast)
    }

    /// Per-chunk serial scans concatenate to the merged Ast scan:
    /// the worklist caches one scan per file chunk and joins them.
    #[test]
    fn chunk_scans_join_to_merged_scan() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let parse = |src: &str, file: u32| {
            let lexed = lexer::lex(src, FileId(file), 0, &interner).unwrap();
            parser::parse(&lexed, &interner, &known).unwrap()
        };
        let a = parse("struct A { x: i64 }\nfn fa(a: i64) -> i64 { a + 1 }\n", 0);
        let b = parse("fn fb() -> &'static str { \"hi\" }\nfn main() { println!(\"{}\", fa(2)); }\n", 1);
        let (sa, sb) = (scan_ast_seq(&a), scan_ast_seq(&b));
        let merged = scan_ast(&Ast::concat(vec![a, b]));
        let joined_items: Vec<u64> = sa.items.iter().chain(&sb.items).map(|i| i.hash).collect();
        assert_eq!(joined_items, merged.items.iter().map(|i| i.hash).collect::<Vec<_>>());
        let joined_bodies: Vec<u64> = sa.bodies.iter().chain(&sb.bodies).map(|b| b.0).collect();
        assert_eq!(joined_bodies, merged.bodies.iter().map(|b| b.0).collect::<Vec<_>>());
        let joined_idents: Vec<&Vec<Sym>> = sa.bodies.iter().chain(&sb.bodies).map(|b| &b.1).collect();
        assert_eq!(joined_idents, merged.bodies.iter().map(|b| &b.1).collect::<Vec<_>>());
    }

    const BASE: &str = "\
struct Foo { x: i64 }
impl Foo { fn get(&self) -> i64 { self.x } }
fn helper(a: i64) -> i64 { a + 1 }
fn main() { let f = Foo { x: helper(1) }; println!(\"{}\", f.get()); }
";

    /// A body-only edit changes exactly that body's hash; every item
    /// hash and every other body hash stays.
    #[test]
    fn body_edit_changes_only_that_body() {
        let a = scan_src(BASE);
        let b = scan_src(&BASE.replace("a + 1", "a + 2"));
        assert_eq!(a.items.iter().map(|i| i.hash).collect::<Vec<_>>(), b.items.iter().map(|i| i.hash).collect::<Vec<_>>());
        let changed: Vec<usize> = (0..a.bodies.len()).filter(|&i| a.bodies[i].0 != b.bodies[i].0).collect();
        assert_eq!(changed, vec![1], "only helper (fn order: get, helper, main)");
    }

    /// A signature edit changes the item hash, not the body hash.
    #[test]
    fn signature_edit_changes_item_not_body() {
        let a = scan_src(BASE);
        let b = scan_src(&BASE.replace("fn helper(a: i64)", "fn helper(a: i64, extra: i64)"));
        assert_ne!(a.items[2].hash, b.items[2].hash);
        assert_eq!(a.bodies[1].0, b.bodies[1].0);
    }

    /// Moves and blank lines hash the same: positions are not content.
    #[test]
    fn line_shifts_do_not_rehash() {
        let a = scan_src(BASE);
        let b = scan_src(&format!("\n\n{BASE}"));
        assert_eq!(a.items.iter().map(|i| i.hash).collect::<Vec<_>>(), b.items.iter().map(|i| i.hash).collect::<Vec<_>>());
        assert_eq!(a.bodies.iter().map(|b| b.0).collect::<Vec<_>>(), b.bodies.iter().map(|b| b.0).collect::<Vec<_>>());
    }

    /// A type edit (field added) changes the type item's hash only.
    #[test]
    fn type_edit_changes_type_item() {
        let a = scan_src(BASE);
        let b = scan_src(&BASE.replace("struct Foo { x: i64 }", "struct Foo { x: i64, y: i64 }"));
        assert_ne!(a.items[0].hash, b.items[0].hash);
        assert_eq!(a.items[2].hash, b.items[2].hash);
        assert_eq!(a.bodies.iter().map(|b| b.0).collect::<Vec<_>>(), b.bodies.iter().map(|b| b.0).collect::<Vec<_>>());
    }
}
