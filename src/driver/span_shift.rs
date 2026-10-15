// Moves every span of a merged Ast for one text edit in one file (the
// daemon's body patch, driver/patch.rs). The edit replaced old bytes
// `a..b` of `file` with text `d` bytes longer (or shorter): a span edge
// at or after `b` moves by `d`, an edge before it stays. Spans inside the
// replaced bytes belong to the body the patch replaces; they are left
// as they are and no reachable node keeps them.
//
// The walk visits every `Span` the Ast holds: the three span arenas,
// spans inside expression, pattern, and type payloads, blocks and
// statements, items and their parts, attributes, and token trees. A
// test parses one text twice, the second time with bytes inserted, and
// compares the two Asts after the shift (`shift_matches_reparse`), so a
// span field the walk misses fails it.
use crate::ast::*;
use crate::diag::{CtxtId, FileId, Span};
use crate::intern::FxMap;
use crate::lexer::TokenTree;
use std::ops::Range;

/// One text edit: old bytes `a..b` of `file` now take `b - a + d` bytes.
#[derive(Clone, Copy)]
pub struct Edit {
    pub file: FileId,
    pub a: u32,
    pub b: u32,
    pub d: i64,
}

impl Edit {
    /// The span after the edit (see the module docs). A span whose
    /// expansion context names a moved call site or definition gets a
    /// fresh context (`diag::reshift_ctxt`); `ctxts` memoizes them.
    pub fn span(&self, s: Span, ctxts: &mut FxMap<u32, CtxtId>) -> Span {
        let mut s = s;
        if s.ctxt != CtxtId::ROOT {
            s.ctxt = crate::diag::reshift_ctxt(s.ctxt, &|x| self.plain(x), ctxts);
        }
        self.plain(s)
    }

    /// `span` without the context step.
    pub fn plain(&self, mut s: Span) -> Span {
        if s.file == self.file {
            if s.lo >= self.b {
                s.lo = (s.lo as i64 + self.d) as u32;
            }
            if s.hi > self.b {
                s.hi = (s.hi as i64 + self.d) as u32;
            }
        }
        s
    }
}

/// Where one file's nodes sit in a merged Ast: index ranges per arena
/// and item list. The worklist concatenates one chunk per file, so each
/// file starts as one range per list; each body patch appends one more.
#[derive(Clone, Default)]
pub struct FileRanges {
    pub exprs: Vec<Range<usize>>,
    pub pats: Vec<Range<usize>>,
    pub tys: Vec<Range<usize>>,
    pub blocks: Vec<Range<usize>>,
    pub items: Vec<Range<usize>>,
    pub stmt_items: Vec<Range<usize>>,
}

/// Per file of `n_files`, the smallest index range of each list that
/// holds every node whose own span names the file. A node's inner spans
/// name its own file unless a macro or an include moved tokens across
/// files; the caller only walks by these ranges when neither can.
pub fn ranges_by_file(ast: &Ast, n_files: usize) -> Vec<FileRanges> {
    fn spread(spans: impl Iterator<Item = Span>, n: usize) -> Vec<Vec<Range<usize>>> {
        let mut out: Vec<Option<Range<usize>>> = vec![None; n];
        for (i, s) in spans.enumerate() {
            if let Some(r) = out.get_mut(s.file.0 as usize) {
                *r = Some(r.as_ref().map_or(i..i + 1, |r| r.start..i + 1));
            }
        }
        out.into_iter().map(|r| r.into_iter().collect()).collect()
    }
    let exprs = spread(ast.expr_spans.iter().copied(), n_files);
    let pats = spread(ast.pat_spans.iter().copied(), n_files);
    let tys = spread(ast.ty_spans.iter().copied(), n_files);
    let blocks = spread(ast.blocks.iter().map(|b| b.span), n_files);
    let items = spread(ast.items.iter().map(|i| i.span), n_files);
    let stmt_items = spread(ast.stmt_items.iter().map(|i| i.span), n_files);
    (0..n_files)
        .map(|k| FileRanges {
            exprs: exprs[k].clone(),
            pats: pats[k].clone(),
            tys: tys[k].clone(),
            blocks: blocks[k].clone(),
            items: items[k].clone(),
            stmt_items: stmt_items[k].clone(),
        })
        .collect()
}

/// Applies `edit` to every span of `ast`, or, with `ranges`, to the
/// spans of the nodes in those ranges (see `ranges_by_file`). Returns
/// the number of spans visited (the patch's work counter).
pub fn shift_ast(ast: &mut Ast, edit: Edit, ranges: Option<&FileRanges>) -> usize {
    let mut w = Walk { edit, ctxts: FxMap::default(), visited: 0 };
    let Ast { inner_attrs, items, stmt_items, exprs, expr_spans, pats, pat_spans, tys, ty_spans, blocks, .. } = ast;
    let all = |n: usize| vec![0..n];
    let pick = |n: usize, f: fn(&FileRanges) -> &Vec<Range<usize>>| ranges.map_or_else(|| all(n), |r| f(r).clone());
    for r in pick(exprs.len(), |r| &r.exprs) {
        for i in r {
            w.sp(&mut expr_spans[i]);
            w.expr(&mut exprs[i]);
        }
    }
    for r in pick(pats.len(), |r| &r.pats) {
        for i in r {
            w.sp(&mut pat_spans[i]);
            w.pat(&mut pats[i]);
        }
    }
    for r in pick(tys.len(), |r| &r.tys) {
        for i in r {
            w.sp(&mut ty_spans[i]);
            w.ty(&mut tys[i]);
        }
    }
    for r in pick(blocks.len(), |r| &r.blocks) {
        blocks[r].iter_mut().for_each(|b| w.block(b));
    }
    // Inner attributes of every file's chunk merge into one short list.
    w.attrs(inner_attrs);
    for r in pick(items.len(), |r| &r.items) {
        items[r].iter_mut().for_each(|it| w.item(it));
    }
    for r in pick(stmt_items.len(), |r| &r.stmt_items) {
        stmt_items[r].iter_mut().for_each(|it| w.item(it));
    }
    w.visited
}

/// Blanks the nodes whose own span lies inside bytes `lo..hi` of
/// `file` (a replaced fn body, before the shift): expressions become
/// `()`, patterns `_`, types `_`, blocks empty. Nothing reaches them any
/// more, but passes that scan whole arenas would still see their kinds.
pub fn blank_nodes(ast: &mut Ast, file: FileId, (lo, hi): (u32, u32), ranges: Option<&FileRanges>) {
    let inside = |s: &Span| s.file == file && lo <= s.lo && s.hi <= hi;
    let all = |n: usize| vec![0..n];
    let pick = |n: usize, f: fn(&FileRanges) -> &Vec<Range<usize>>| ranges.map_or_else(|| all(n), |r| f(r).clone());
    for i in pick(ast.exprs.len(), |r| &r.exprs).into_iter().flatten() {
        if inside(&ast.expr_spans[i]) {
            ast.exprs[i] = Expr::Unit;
        }
    }
    for i in pick(ast.pats.len(), |r| &r.pats).into_iter().flatten() {
        if inside(&ast.pat_spans[i]) {
            ast.pats[i] = Pat::Wild;
        }
    }
    for i in pick(ast.tys.len(), |r| &r.tys).into_iter().flatten() {
        if inside(&ast.ty_spans[i]) {
            ast.tys[i] = TyExpr::Infer;
        }
    }
    for i in pick(ast.blocks.len(), |r| &r.blocks).into_iter().flatten() {
        let b = &mut ast.blocks[i];
        if inside(&b.span) {
            *b = Block { inner_attrs: Vec::new(), stmts: Vec::new(), tail: None, tail_attrs: Vec::new(), span: b.span };
        }
    }
}

struct Walk {
    edit: Edit,
    ctxts: FxMap<u32, CtxtId>,
    visited: usize,
}

impl Walk {
    fn sp(&mut self, s: &mut Span) {
        self.visited += 1;
        *s = self.edit.span(*s, &mut self.ctxts);
    }
    fn lt(&mut self, l: &mut Lifetime) {
        self.sp(&mut l.span);
    }
    fn lts(&mut self, ls: &mut [Lifetime]) {
        ls.iter_mut().for_each(|l| self.lt(l));
    }
    fn trees(&mut self, trees: &mut [TokenTree]) {
        for t in trees {
            match t {
                TokenTree::Token(tok) => self.sp(&mut tok.span),
                TokenTree::Delim(_, inner, span) => {
                    self.sp(span);
                    self.trees(inner);
                }
            }
        }
    }
    fn args(&mut self, args: &mut GenericArgs) {
        if let GenericArgs::Angle(args) = args {
            for a in args {
                match a {
                    GenericArg::Lifetime(l) => self.lt(l),
                    GenericArg::Binding { span, kind, .. } => {
                        self.sp(span);
                        if let BindingKind::Constraint(bounds) = kind {
                            self.bounds(bounds);
                        }
                    }
                    GenericArg::Type(_) | GenericArg::Const(_) => {}
                }
            }
        }
    }
    fn path(&mut self, segs: &mut [PathSeg]) {
        segs.iter_mut().for_each(|s| self.args(&mut s.args));
    }
    fn vis(&mut self, v: &mut Vis) {
        if let Vis::Restricted { path, span } = v {
            self.path(path);
            self.sp(span);
        }
    }
    fn attrs(&mut self, attrs: &mut [Attr]) {
        for a in attrs {
            self.path(&mut a.path);
            if let AttrInput::List(_, trees) = &mut a.input {
                self.trees(trees);
            }
            self.sp(&mut a.span);
        }
    }
    fn bounds(&mut self, bounds: &mut [TraitBound]) {
        for b in bounds {
            match b {
                TraitBound::Trait { binder, trait_ref, .. } => {
                    self.lts(binder);
                    self.path(&mut trait_ref.path);
                }
                TraitBound::Lifetime(l) => self.lt(l),
            }
        }
    }
    fn generics(&mut self, g: &mut Generics) {
        for p in &mut g.params {
            match p {
                GenericParam::Lifetime { lt, bounds, attrs } => {
                    self.lt(lt);
                    self.lts(bounds);
                    self.attrs(attrs);
                }
                GenericParam::Type { span, bounds, attrs, .. } => {
                    self.sp(span);
                    self.bounds(bounds);
                    self.attrs(attrs);
                }
                GenericParam::Const { span, attrs, .. } => {
                    self.sp(span);
                    self.attrs(attrs);
                }
            }
        }
        self.sp(&mut g.span);
    }
    fn where_clause(&mut self, w: &mut WhereClause) {
        for p in &mut w.preds {
            match p {
                WherePred::Type { binder, bounds, .. } => {
                    self.lts(binder);
                    self.bounds(bounds);
                }
                WherePred::Lifetime { lt, bounds } => {
                    self.lt(lt);
                    self.lts(bounds);
                }
            }
        }
        self.sp(&mut w.span);
    }
    fn macro_call(&mut self, m: &mut MacroCall) {
        self.path(&mut m.path);
        self.trees(&mut m.tokens);
        self.sp(&mut m.span);
    }
    fn use_tree(&mut self, t: &mut UseTree) {
        self.path(&mut t.prefix);
        if let UseKind::Group(trees) = &mut t.kind {
            trees.iter_mut().for_each(|c| self.use_tree(c));
        }
        self.sp(&mut t.span);
    }
    fn fn_def(&mut self, f: &mut FnDef) {
        self.sp(&mut f.name_span);
        self.vis(&mut f.vis);
        self.attrs(&mut f.attrs);
        self.generics(&mut f.generics);
        if let Some(sp) = &mut f.self_param {
            if let Some(l) = &mut sp.lifetime {
                self.lt(l);
            }
            self.attrs(&mut sp.attrs);
            self.sp(&mut sp.span);
        }
        for p in &mut f.params {
            self.attrs(&mut p.attrs);
            self.sp(&mut p.span);
        }
        self.where_clause(&mut f.where_clause);
    }
    fn fields(&mut self, fs: &mut [FieldDef]) {
        for f in fs {
            self.vis(&mut f.vis);
            self.attrs(&mut f.attrs);
            self.sp(&mut f.span);
        }
    }
    fn variant_fields(&mut self, vf: &mut VariantFields) {
        if let VariantFields::Tuple(fs) | VariantFields::Struct(fs) = vf {
            self.fields(fs);
        }
    }
    fn derives(&mut self, ds: &mut [(crate::intern::Sym, Span)]) {
        ds.iter_mut().for_each(|(_, s)| self.sp(s));
    }
    fn assoc_consts(&mut self, cs: &mut [AssocConstDef]) {
        for c in cs {
            self.sp(&mut c.name_span);
            self.vis(&mut c.vis);
            self.attrs(&mut c.attrs);
            self.sp(&mut c.span);
        }
    }
    fn assoc_types(&mut self, ts: &mut [AssocTypeDef]) {
        for t in ts {
            self.sp(&mut t.name_span);
            self.vis(&mut t.vis);
            self.attrs(&mut t.attrs);
            self.generics(&mut t.generics);
            self.bounds(&mut t.bounds);
            self.where_clause(&mut t.where_clause);
            self.sp(&mut t.span);
        }
    }
    fn item(&mut self, item: &mut Item) {
        self.vis(&mut item.vis);
        self.attrs(&mut item.attrs);
        self.sp(&mut item.span);
        match &mut item.kind {
            ItemKind::Fn(f) => self.fn_def(f),
            ItemKind::Struct(s) => {
                self.sp(&mut s.name_span);
                self.generics(&mut s.generics);
                self.variant_fields(&mut s.fields);
                self.where_clause(&mut s.where_clause);
                self.derives(&mut s.derives);
            }
            ItemKind::Enum(e) => {
                self.sp(&mut e.name_span);
                self.generics(&mut e.generics);
                for v in &mut e.variants {
                    self.attrs(&mut v.attrs);
                    self.variant_fields(&mut v.fields);
                    self.sp(&mut v.span);
                }
                self.where_clause(&mut e.where_clause);
                self.derives(&mut e.derives);
            }
            ItemKind::Impl(imp) => {
                self.attrs(&mut imp.inner_attrs);
                self.generics(&mut imp.generics);
                if let Some(tr) = &mut imp.trait_ref {
                    self.path(&mut tr.path);
                }
                self.where_clause(&mut imp.where_clause);
                imp.fns.iter_mut().for_each(|f| self.fn_def(f));
                self.assoc_consts(&mut imp.consts);
                self.assoc_types(&mut imp.types);
                self.sp(&mut imp.span);
            }
            ItemKind::Use(u) => {
                self.use_tree(&mut u.tree);
                self.sp(&mut u.span);
            }
            ItemKind::Mod(m) => {
                self.sp(&mut m.name_span);
                self.attrs(&mut m.inner_attrs);
                if let Some(items) = &mut m.body {
                    items.iter_mut().for_each(|i| self.item(i));
                }
                self.sp(&mut m.span);
            }
            ItemKind::Trait(tr) => {
                self.attrs(&mut tr.inner_attrs);
                self.sp(&mut tr.name_span);
                self.generics(&mut tr.generics);
                self.bounds(&mut tr.bounds);
                self.where_clause(&mut tr.where_clause);
                tr.fns.iter_mut().for_each(|f| self.fn_def(f));
                self.assoc_consts(&mut tr.consts);
                self.assoc_types(&mut tr.types);
                self.sp(&mut tr.span);
            }
            ItemKind::Type(a) => {
                self.sp(&mut a.name_span);
                self.generics(&mut a.generics);
                self.where_clause(&mut a.where_clause);
                self.sp(&mut a.span);
            }
            ItemKind::Const(c) => {
                self.sp(&mut c.name_span);
                self.sp(&mut c.span);
            }
            ItemKind::Static(s) => {
                self.sp(&mut s.name_span);
                self.sp(&mut s.span);
            }
            ItemKind::MacroRules(m) => {
                self.sp(&mut m.name_span);
                self.trees(&mut m.tokens);
                self.sp(&mut m.span);
            }
            ItemKind::ExternCrate(x) => {
                self.sp(&mut x.name_span);
                self.sp(&mut x.span);
            }
            ItemKind::ExternBlock(b) => {
                for fi in &mut b.items {
                    match fi {
                        ForeignItem::Fn(f) => self.fn_def(f),
                        ForeignItem::Static(s) => {
                            self.sp(&mut s.name_span);
                            self.sp(&mut s.span);
                        }
                        ForeignItem::Type { name_span, vis, attrs, generics, where_clause, span, .. } => {
                            self.sp(name_span);
                            self.vis(vis);
                            self.attrs(attrs);
                            self.generics(generics);
                            self.where_clause(where_clause);
                            self.sp(span);
                        }
                        ForeignItem::MacroCall(m) => self.macro_call(m),
                    }
                }
                self.sp(&mut b.span);
            }
            ItemKind::Union(u) => {
                self.sp(&mut u.name_span);
                self.generics(&mut u.generics);
                self.fields(&mut u.fields);
                self.where_clause(&mut u.where_clause);
                self.derives(&mut u.derives);
                self.sp(&mut u.span);
            }
            ItemKind::MacroCall(m) => self.macro_call(m),
        }
    }
    fn label(&mut self, l: &mut Option<Label>) {
        if let Some(l) = l {
            self.lt(l);
        }
    }
    fn expr(&mut self, e: &mut Expr) {
        match e {
            Expr::Path(segs) => self.path(segs),
            Expr::While { label, .. } | Expr::Loop { label, .. } | Expr::For { label, .. } | Expr::Break { label, .. } => self.label(label),
            Expr::Continue(label) => self.label(label),
            Expr::LabeledBlock { label, .. } => self.lt(label),
            Expr::Match { arms, .. } => arms.iter_mut().for_each(|a| self.attrs(&mut a.attrs)),
            Expr::MethodCall { name_span, generic_args, .. } => {
                self.sp(name_span);
                let mut args = GenericArgs::Angle(std::mem::take(generic_args));
                self.args(&mut args);
                if let GenericArgs::Angle(a) = args {
                    *generic_args = a;
                }
            }
            Expr::StructLit { path, fields, .. } => {
                self.path(path);
                fields.iter_mut().for_each(|(_, s, _)| self.sp(s));
            }
            Expr::Closure { params, .. } => {
                for p in params {
                    self.attrs(&mut p.attrs);
                    self.sp(&mut p.span);
                }
            }
            Expr::QPath { trait_path, segs, .. } => {
                self.path(trait_path);
                self.path(segs);
            }
            Expr::MacroCall(m) => self.macro_call(m),
            Expr::Int(..)
            | Expr::Bool(_)
            | Expr::Str(_)
            | Expr::Char(_)
            | Expr::Unit
            | Expr::SelfValue
            | Expr::Block(_)
            | Expr::If { .. }
            | Expr::Call { .. }
            | Expr::Field { .. }
            | Expr::Index { .. }
            | Expr::Binary { .. }
            | Expr::Unary { .. }
            | Expr::Cast { .. }
            | Expr::Ref { .. }
            | Expr::Deref(_)
            | Expr::Assign { .. }
            | Expr::AssignOp { .. }
            | Expr::Range { .. }
            | Expr::Return(_)
            | Expr::Macro { .. }
            | Expr::Float(_)
            | Expr::Tuple(_)
            | Expr::Array(_)
            | Expr::ArrayRepeat { .. }
            | Expr::Try(_)
            | Expr::Await(_)
            | Expr::AsyncBlock { .. }
            | Expr::UnsafeBlock(_)
            | Expr::Let { .. }
            | Expr::TupleField { .. }
            | Expr::ConstBlock(_)
            | Expr::Underscore
            | Expr::OffsetOf { .. }
            | Expr::ByteStr(_) => {}
        }
    }
    fn pat(&mut self, p: &mut Pat) {
        match p {
            Pat::Path(path) | Pat::TupleStruct { path, .. } | Pat::Struct { path, .. } => self.path(path),
            Pat::QPath { trait_path, segs, .. } => {
                self.path(trait_path);
                self.path(segs);
            }
            Pat::MacroCall(m) => self.macro_call(m),
            Pat::Wild
            | Pat::Binding { .. }
            | Pat::Lit(_)
            | Pat::Or(_)
            | Pat::Range { .. }
            | Pat::Tuple(_)
            | Pat::Slice { .. }
            | Pat::Ref { .. }
            | Pat::At { .. }
            | Pat::Rest
            | Pat::Paren(_) => {}
        }
    }
    fn ty(&mut self, t: &mut TyExpr) {
        match t {
            TyExpr::Path(path) => self.path(path),
            TyExpr::Ref { lifetime, .. } => {
                if let Some(l) = lifetime {
                    self.lt(l);
                }
            }
            TyExpr::FnPtr { binder, inputs, .. } => {
                self.lts(binder);
                for p in inputs {
                    self.attrs(&mut p.attrs);
                    self.sp(&mut p.span);
                }
            }
            TyExpr::Dyn { binder, bounds, lifetime } => {
                self.lts(binder);
                self.bounds(bounds);
                if let Some(l) = lifetime {
                    self.lt(l);
                }
            }
            TyExpr::ImplTrait { bounds } => self.bounds(bounds),
            TyExpr::QPath { trait_path, segs, .. } => {
                self.path(trait_path);
                self.path(segs);
            }
            TyExpr::MacroCall(m) => self.macro_call(m),
            TyExpr::Unit
            | TyExpr::Tuple(_)
            | TyExpr::Array { .. }
            | TyExpr::Slice(_)
            | TyExpr::Ptr { .. }
            | TyExpr::Never
            | TyExpr::Paren(_)
            | TyExpr::Infer => {}
        }
    }
    fn block(&mut self, b: &mut Block) {
        self.attrs(&mut b.inner_attrs);
        for st in &mut b.stmts {
            match st {
                Stmt::Let { attrs, span, .. } => {
                    self.attrs(attrs);
                    self.sp(span);
                }
                Stmt::Expr { attrs, .. } => self.attrs(attrs),
                Stmt::Item(_) => {}
                Stmt::Macro { call, .. } => self.macro_call(call),
            }
        }
        self.attrs(&mut b.tail_attrs);
        self.sp(&mut b.span);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::{Interner, Known};

    /// A program with most node kinds that carry spans of their own.
    const SRC: &str = r#"#![allow(dead_code)]
use std::collections::HashMap;
use std::fmt::{self, Display as Disp};
mod inner {
    pub(crate) fn deep<'a, T: Clone + 'a>(x: &'a T) -> T where T: Copy { *x }
}
#[derive(Debug, Clone)]
pub struct Point<T> { pub x: T, #[allow(unused)] y: T }
struct Unit;
struct Tup(pub i32, u8);
#[repr(u8)]
enum Kind { A = 1, B(i32), C { v: u64 } }
trait Shape: Clone where Self: Sized {
    type Out: Copy;
    const SIDES: u32 = 4;
    fn area(&self) -> f64;
    fn twice(&self) -> f64 { self.area() * 2.0 }
}
impl<T: Copy> Point<T> {
    const ORIGIN: i32 = 0;
    fn get(&self) -> T { self.x }
}
impl fmt::Display for Unit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "unit") }
}
type Map = HashMap<String, Vec<i32>>;
const LIMIT: usize = 10;
static mut COUNT: i32 = 0;
macro_rules! twice { ($e:expr) => { $e * 2 }; }
fn first(xs: &[i32], f: fn(i32) -> i32, d: &dyn Fn(i32) -> bool) -> impl Iterator<Item = i32> + '_ {
    let mut total = 0;
    'outer: for (i, x) in xs.iter().enumerate() {
        while total < 100 { total += f(*x); if d(total) { break 'outer; } }
        let p = Point { x: i, y: i };
        match p {
            Point { x: 0, .. } => continue,
            #[allow(unused)]
            Point { x, y } if x > y => total -= 1,
            _ => {}
        }
    }
    let c = |a: i32, b| -> i32 { a + b };
    let v: Vec<u8> = Vec::<u8>::with_capacity(LIMIT);
    let q = <Point<i32> as Clone>::clone(&Point { x: 1, y: 2 });
    let r = 'blk: { if total > 3 { break 'blk 1; } 2 };
    println!("{} {} {}", c(1, 2), v.len(), q.x + r);
    let k = Kind::C { v: 3 };
    if let Kind::C { v } = k { total += v as i32; }
    xs.iter().map(move |x| x + total)
}
fn main() {
    let xs = [1, 2, 3];
    let _ = first(&xs, |x| x, &|x| x > 2).count();
    let _ = twice!(3);
    let _: Map = HashMap::new();
}
"#;

    fn parse(src: &str, interner: &Interner, known: &Known) -> Ast {
        let l = crate::lexer::lex(src, FileId(0), 0, interner).unwrap();
        let ctx = crate::expand::ExpandCtx::for_file(interner, known, std::path::Path::new("t.rs"), src, false);
        let l = crate::expand::expand_lexed(l, &ctx).unwrap_or_else(|d| panic!("{}", d.message));
        crate::parser::parse(&l, interner, known).unwrap_or_else(|d| panic!("{}", d.message))
    }

    /// Every list of the Ast, with expansion context ids blanked: each
    /// expansion registers fresh ids, so two parses never share them.
    /// `call_sites` compares what the ids stand for.
    fn dump(ast: &Ast) -> String {
        let text = format!(
            "{:?}\n{:?}\n{:?}\n{:?}\n{:?}\n{:?}\n{:?}\n{:?}\n{:?}\n{:?}",
            ast.inner_attrs,
            ast.items,
            ast.stmt_items,
            ast.exprs,
            ast.expr_spans,
            ast.pats,
            ast.pat_spans,
            ast.tys,
            ast.ty_spans,
            ast.blocks
        );
        let mut out = String::with_capacity(text.len());
        let mut rest = text.as_str();
        while let Some(i) = rest.find("CtxtId(") {
            out.push_str(&rest[..i + 7]);
            rest = &rest[i + 7..];
            rest = &rest[rest.find(')').unwrap()..];
        }
        out.push_str(rest);
        out
    }

    /// The call site of every expression span (through its expansion
    /// chain), which a moved context must carry along.
    fn call_sites(ast: &Ast) -> Vec<Span> {
        ast.expr_spans.iter().map(|&s| crate::diag::call_site_span(s)).collect()
    }

    /// Shifting a parse for a whitespace edit gives exactly the parse of
    /// the edited text, spans included: a span field the walk misses
    /// keeps its old offset and shows in the dump. Inserts and deletes,
    /// at the top of the file and inside a body, whole-Ast and by ranges.
    #[test]
    fn shift_matches_reparse() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let body = SRC.find("let mut total").unwrap();
        let cases: Vec<(usize, usize, &str)> = vec![
            (body, body, "   \n\n  "),
            (body - 4, body, ""),
            (SRC.find("struct Unit").unwrap(), SRC.find("struct Unit").unwrap(), "\n\n"),
        ];
        for (a, b, ins) in cases {
            let edited = format!("{}{}{}", &SRC[..a], ins, &SRC[b..]);
            let want = dump(&parse(&edited, &interner, &known));
            let edit = Edit { file: FileId(0), a: a as u32, b: b as u32, d: ins.len() as i64 - (b - a) as i64 };
            let mut whole = parse(SRC, &interner, &known);
            assert_ne!(dump(&whole), want, "the edit moves some span");
            shift_ast(&mut whole, edit, None);
            assert_eq!(dump(&whole), want, "whole-Ast shift for edit at {a}..{b}");
            assert_eq!(call_sites(&whole), call_sites(&parse(&edited, &interner, &known)), "call sites for edit at {a}..{b}");
            let mut ranged = parse(SRC, &interner, &known);
            let ranges = ranges_by_file(&ranged, 1);
            shift_ast(&mut ranged, edit, Some(&ranges[0]));
            assert_eq!(dump(&ranged), want, "ranged shift for edit at {a}..{b}");
        }
    }
}
