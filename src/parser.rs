// Recursive-descent parser with precedence climbing for binary operators.
// Rust syntax that lust rejects on purpose (lifetimes, user macros) gets its own error code here.
use crate::ast::*;
use crate::diag::{Diag, Span, unsupported};
use crate::intern::{Interner, Known, Sym};
use crate::lexer::{Lexed, Tok, Token};

type PResult<T> = Result<T, Diag>;

pub struct Parser<'a> {
    toks: &'a [Token],
    pos: usize,
    ast: Ast,
    interner: &'a Interner,
    known: &'a Known,
    /// Added to string-literal token indexes: where this token list's strings start in the AST.
    str_base: u32,
    /// Current nesting depth, capped so pathological input cannot overflow the stack.
    depth: u32,
}

/// The deepest nesting lust parses (parentheses, prefix operators, blocks, types,
/// patterns, and operator or method chains). Real code stays far below this.
const MAX_DEPTH: u32 = 2000;

/// Parses a whole file (or chunk) into an `Ast`. Stops at the first error.
pub fn parse(lexed: &Lexed, interner: &Interner, known: &Known) -> PResult<Ast> {
    let mut p = Parser { toks: &lexed.tokens, pos: 0, ast: Ast::default(), interner, known, str_base: 0, depth: 0 };
    p.ast.strings = lexed.strings.clone();
    while p.peek() != Tok::Eof {
        let before = p.pos;
        let item = p.item()?;
        if let Some(item) = item {
            p.ast.items.push(item);
        }
        // No parse loop may spin in place on bad input: each round must consume a token.
        if p.pos == before {
            return Err(syntax(p.span(), format!("expected an item, found {:?}", p.peek())));
        }
    }
    Ok(p.ast)
}

/// A parsed function body: its block, and its expression and pattern ranges.
pub type ParsedBody = (BlockId, (u32, u32), (u32, u32));

/// Parses one function body (`tokens` runs from its `{` to its `}`) and appends it to `ast`.
/// Returns the body block and the new expression and pattern ranges for the function.
pub fn parse_body(tokens: &[Token], strings: &[String], ast: &mut Ast, interner: &Interner, known: &Known) -> PResult<ParsedBody> {
    let mut toks = tokens.to_vec();
    let end = tokens.last().map_or(Span::default(), |t| t.span);
    toks.push(Token { tok: Tok::Eof, span: Span::new(end.end, end.end) });
    let str_base = ast.strings.len() as u32;
    ast.strings.extend_from_slice(strings);
    let mut p = Parser { toks: &toks, pos: 0, ast: std::mem::take(ast), interner, known, str_base, depth: 0 };
    let (e0, p0) = (p.ast.exprs.len() as u32, p.ast.pats.len() as u32);
    let body = p.block();
    let ranges = ((e0, p.ast.exprs.len() as u32), (p0, p.ast.pats.len() as u32));
    *ast = p.ast;
    Ok((body?, ranges.0, ranges.1))
}

fn syntax(span: Span, msg: impl Into<String>) -> Diag {
    Diag::new("L0001", span, msg, "Fix the syntax. Lust uses Rust syntax.")
}

fn lifetime_error(span: Span) -> Diag {
    Diag::new(
        "L0203",
        span,
        "lifetime names are not supported",
        "Remove the lifetime. Lust uses Rust's elision rules only. If elision is ambiguous, return an owned value or an index.",
    )
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Tok {
        self.toks[self.pos].tok
    }
    fn peek_at(&self, n: usize) -> Tok {
        self.toks.get(self.pos + n).map_or(Tok::Eof, |t| t.tok)
    }
    fn span(&self) -> Span {
        self.toks[self.pos].span
    }
    fn prev_span(&self) -> Span {
        self.toks[self.pos.saturating_sub(1)].span
    }
    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos];
        if t.tok != Tok::Eof {
            self.pos += 1;
        }
        t
    }
    fn eat(&mut self, t: Tok) -> bool {
        if self.peek() == t {
            self.bump();
            true
        } else {
            false
        }
    }
    fn expect(&mut self, t: Tok, what: &str) -> PResult<Span> {
        if self.peek() == t { Ok(self.bump().span) } else { Err(syntax(self.span(), format!("expected {what}, found {:?}", self.peek()))) }
    }
    fn ident(&mut self) -> PResult<(Sym, Span)> {
        match self.peek() {
            Tok::Ident(s) => Ok((s, self.bump().span)),
            Tok::SelfUpper => Ok((self.known.self_type, self.bump().span)),
            Tok::Reserved(_) => Err(self.reserved_error(self.span())),
            Tok::Lifetime => Err(lifetime_error(self.span())),
            t => Err(syntax(self.span(), format!("expected identifier, found {t:?}"))),
        }
    }
    /// The error for a reserved keyword (`gen`, `try`, ...) used where an identifier belongs.
    fn reserved_error(&self, span: Span) -> Diag {
        let Tok::Reserved(s) = self.toks[self.pos.min(self.toks.len() - 1)].tok else {
            return syntax(span, "expected identifier");
        };
        let name = self.interner.get(s);
        Diag::new(
            "L0001",
            span,
            format!("expected identifier, found reserved keyword `{name}`"),
            format!("Rename it, or write `r#{name}` to use it as an identifier."),
        )
    }

    /// True if the next two tokens are `>` `>` with no space, which means a right shift.
    fn at_shr(&self) -> bool {
        self.peek() == Tok::Gt && self.peek_at(1) == Tok::Gt && self.toks[self.pos].span.end == self.toks[self.pos + 1].span.start
    }
    /// True at a `>>=`: lexed as `>` followed by `>=`, touching.
    fn at_shr_assign(&self) -> bool {
        self.peek() == Tok::Gt && self.peek_at(1) == Tok::Ge && self.toks[self.pos].span.end == self.toks[self.pos + 1].span.start
    }

    /// Runs `f` one nesting level deeper, or errors past `MAX_DEPTH`.
    fn nest<T>(&mut self, f: impl FnOnce(&mut Self) -> PResult<T>) -> PResult<T> {
        if self.depth >= MAX_DEPTH {
            return Err(Diag::new(
                "L9001",
                self.span(),
                format!("nesting deeper than {MAX_DEPTH} levels is not supported"),
                "Split the expression into smaller pieces with `let`.",
            ));
        }
        self.depth += 1;
        let r = f(self);
        self.depth -= 1;
        r
    }
    fn push_expr(&mut self, e: Expr, span: Span) -> ExprId {
        self.ast.exprs.push(e);
        self.ast.expr_spans.push(span);
        ExprId(self.ast.exprs.len() as u32 - 1)
    }
    fn push_pat(&mut self, p: Pat, span: Span) -> PatId {
        self.ast.pats.push(p);
        self.ast.pat_spans.push(span);
        PatId(self.ast.pats.len() as u32 - 1)
    }
    fn push_ty(&mut self, t: TyExpr, span: Span) -> TyId {
        self.ast.tys.push(t);
        self.ast.ty_spans.push(span);
        TyId(self.ast.tys.len() as u32 - 1)
    }
    fn push_block(&mut self, b: Block) -> BlockId {
        self.ast.blocks.push(b);
        BlockId(self.ast.blocks.len() as u32 - 1)
    }

    // ---------- Items ----------

    /// Parses outer attributes. Returns the derive list and whether `#[test]` was present.
    /// Lint attributes are accepted and ignored.
    fn attributes(&mut self) -> PResult<(Vec<(Sym, Span)>, bool)> {
        let mut derives = Vec::new();
        let mut is_test = false;
        while self.peek() == Tok::Pound {
            let start = self.bump().span;
            let inner = self.eat(Tok::Bang);
            self.expect(Tok::LBracket, "`[`")?;
            let (name, name_span) = self.ident()?;
            let k = self.known;
            match name {
                _ if name == k.derive && !inner => {
                    self.expect(Tok::LParen, "`(`")?;
                    while self.peek() != Tok::RParen {
                        derives.push(self.ident()?);
                        if !self.eat(Tok::Comma) {
                            break;
                        }
                    }
                    self.expect(Tok::RParen, "`)`")?;
                }
                _ if name == k.test && !inner => is_test = true,
                _ if name == k.allow || name == k.warn || name == k.deny => {
                    // Lint attributes have no effect in lust. Skip the argument list.
                    self.expect(Tok::LParen, "`(`")?;
                    let mut depth = 1;
                    while depth > 0 {
                        match self.bump().tok {
                            Tok::LParen => depth += 1,
                            Tok::RParen => depth -= 1,
                            Tok::Eof => return Err(syntax(start, "unterminated attribute")),
                            _ => {}
                        }
                    }
                }
                _ => {
                    return Err(Diag::new(
                        "L0402",
                        name_span,
                        format!("unsupported attribute `{}`", self.interner.get(name)),
                        "Lust supports #[derive(...)], #[test], and lint attributes such as #[allow(...)].",
                    ));
                }
            }
            self.expect(Tok::RBracket, "`]`")?;
        }
        Ok((derives, is_test))
    }

    fn item(&mut self) -> PResult<Option<Item>> {
        let (derives, is_test) = self.attributes()?;
        let start = self.span();
        self.eat(Tok::Pub);
        if self.peek() == Tok::LParen {
            // pub(crate) and similar. `bump` does not move past `Eof`, so stop there.
            while self.bump().tok != Tok::RParen {
                if self.peek() == Tok::Eof {
                    return Err(syntax(self.span(), "expected `)` in visibility, found end of file"));
                }
            }
        }
        let kind = match self.peek() {
            Tok::Fn => {
                let mut def = self.fn_def()?;
                def.is_test = is_test;
                ItemKind::Fn(def)
            }
            Tok::Struct => ItemKind::Struct(self.struct_def(derives)?),
            Tok::Enum => ItemKind::Enum(self.enum_def(derives)?),
            Tok::Impl => ItemKind::Impl(self.impl_def()?),
            Tok::Use => {
                self.bump();
                while self.peek() != Tok::Semi && self.peek() != Tok::Eof {
                    self.bump();
                }
                self.expect(Tok::Semi, "`;`")?;
                ItemKind::Use
            }
            Tok::Eof if derives.is_empty() => return Ok(None),
            Tok::Trait => return Err(unsupported(start, "trait definitions")),
            Tok::Mod => return Err(unsupported(start, "modules")),
            Tok::Const | Tok::Static => return Err(unsupported(start, "const and static items")),
            Tok::Type => return Err(unsupported(start, "type aliases")),
            Tok::Unsafe => return Err(Diag::new("L0404", start, "`unsafe` is not supported", "Remove the unsafe code.")),
            Tok::Async => return Err(Diag::new("L0405", start, "`async` is not supported", "Use std::thread and channels.")),
            Tok::Ident(_) if self.peek_at(1) == Tok::Bang => return Err(macro_error(start)),
            Tok::Reserved(_) => return Err(self.reserved_error(start)),
            t => return Err(syntax(start, format!("expected an item, found {t:?}"))),
        };
        Ok(Some(Item { kind }))
    }

    fn no_generics(&mut self, what: &str) -> PResult<()> {
        if self.peek() == Tok::Lt {
            if self.peek_at(1) == Tok::Lifetime {
                return Err(lifetime_error(self.toks[self.pos + 1].span));
            }
            return Err(unsupported(self.span(), &format!("generic {what}")));
        }
        Ok(())
    }

    fn fn_def(&mut self) -> PResult<FnDef> {
        self.expect(Tok::Fn, "`fn`")?;
        let (name, name_span) = self.ident()?;
        self.no_generics("functions")?;
        self.expect(Tok::LParen, "`(`")?;
        let mut self_param = None;
        let mut params = Vec::new();
        // `self`, `mut self`, `&self`, `&mut self`.
        let s = self.span();
        let self_form = match (self.peek(), self.peek_at(1), self.peek_at(2)) {
            (Tok::SelfLower, _, _) => Some((SelfKind::Value, false, 1)),
            (Tok::Mut, Tok::SelfLower, _) => Some((SelfKind::Value, true, 2)),
            (Tok::Amp, Tok::SelfLower, _) => Some((SelfKind::Ref, false, 2)),
            (Tok::Amp, Tok::Mut, Tok::SelfLower) => Some((SelfKind::RefMut, false, 3)),
            (Tok::Amp, Tok::Lifetime, _) => return Err(lifetime_error(self.toks[self.pos + 1].span)),
            _ => None,
        };
        if let Some((kind, mutable, n)) = self_form {
            for _ in 0..n {
                self.bump();
            }
            self_param = Some(SelfParam { kind, mutable, span: s.to(self.prev_span()) });
            if self.peek() == Tok::Colon {
                return Err(unsupported(self.span(), "typed `self` parameters"));
            }
            if !self.eat(Tok::Comma) && self.peek() != Tok::RParen {
                return Err(syntax(self.span(), "expected `,` or `)`"));
            }
        }
        while self.peek() != Tok::RParen {
            let start = self.span();
            let mutable = self.eat(Tok::Mut);
            let (pname, _) = match self.peek() {
                Tok::Ident(_) => self.ident()?,
                Tok::Reserved(_) => return Err(self.reserved_error(self.span())),
                _ => return Err(unsupported(start, "patterns in parameters")),
            };
            self.expect(Tok::Colon, "`:`")?;
            let ty = self.ty()?;
            params.push(Param { name: pname, mutable, ty, span: start.to(self.prev_span()) });
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RParen, "`)`")?;
        let ret = if self.eat(Tok::Arrow) { Some(self.ty()?) } else { None };
        if self.peek() == Tok::Where {
            return Err(unsupported(self.span(), "where clauses"));
        }
        let (e0, p0) = (self.ast.exprs.len() as u32, self.ast.pats.len() as u32);
        let body = self.block()?;
        let exprs = (e0, self.ast.exprs.len() as u32);
        let pats = (p0, self.ast.pats.len() as u32);
        Ok(FnDef { name, name_span, is_test: false, self_param, params, ret, body, exprs, pats })
    }

    fn fields(&mut self) -> PResult<Vec<FieldDef>> {
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while self.peek() != Tok::RBrace {
            self.eat(Tok::Pub);
            let (name, span) = self.ident()?;
            self.expect(Tok::Colon, "`:`")?;
            let ty = self.ty()?;
            fields.push(FieldDef { name, ty, span });
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(fields)
    }

    fn struct_def(&mut self, derives: Vec<(Sym, Span)>) -> PResult<StructDef> {
        self.expect(Tok::Struct, "`struct`")?;
        let (name, name_span) = self.ident()?;
        self.no_generics("structs")?;
        let fields = match self.peek() {
            Tok::Semi => {
                self.bump();
                Vec::new()
            }
            Tok::LParen => return Err(unsupported(self.span(), "tuple structs")),
            _ => self.fields()?,
        };
        Ok(StructDef { name, name_span, fields, derives })
    }

    fn enum_def(&mut self, derives: Vec<(Sym, Span)>) -> PResult<EnumDef> {
        self.expect(Tok::Enum, "`enum`")?;
        let (name, name_span) = self.ident()?;
        self.no_generics("enums")?;
        self.expect(Tok::LBrace, "`{`")?;
        let mut variants = Vec::new();
        while self.peek() != Tok::RBrace {
            let (vname, span) = self.ident()?;
            let fields = match self.peek() {
                Tok::LParen => {
                    self.bump();
                    let mut tys = Vec::new();
                    while self.peek() != Tok::RParen {
                        tys.push(self.ty()?);
                        if !self.eat(Tok::Comma) {
                            break;
                        }
                    }
                    self.expect(Tok::RParen, "`)`")?;
                    VariantFields::Tuple(tys)
                }
                Tok::LBrace => VariantFields::Struct(self.fields()?),
                Tok::Eq => return Err(unsupported(self.span(), "explicit enum discriminants")),
                _ => VariantFields::Unit,
            };
            variants.push(VariantDef { name: vname, fields, span });
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(EnumDef { name, name_span, variants, derives })
    }

    fn impl_def(&mut self) -> PResult<ImplDef> {
        self.expect(Tok::Impl, "`impl`")?;
        self.no_generics("impls")?;
        let self_ty = self.ty()?;
        if self.peek() == Tok::For {
            return Err(unsupported(self.span(), "trait impls"));
        }
        self.expect(Tok::LBrace, "`{`")?;
        let mut fns = Vec::new();
        while self.peek() != Tok::RBrace {
            let (_, is_test) = self.attributes()?;
            self.eat(Tok::Pub);
            if self.peek() != Tok::Fn {
                return Err(unsupported(self.span(), "associated consts and types"));
            }
            let mut def = self.fn_def()?;
            def.is_test = is_test;
            fns.push(def);
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(ImplDef { self_ty, fns })
    }

    // ---------- Types ----------

    fn ty(&mut self) -> PResult<TyId> {
        self.nest(|p| p.ty_inner())
    }

    fn ty_inner(&mut self) -> PResult<TyId> {
        let start = self.span();
        match self.peek() {
            Tok::Amp | Tok::AndAnd => {
                let double = self.bump().tok == Tok::AndAnd;
                if self.peek() == Tok::Lifetime {
                    return Err(lifetime_error(self.span()));
                }
                let mutable = self.eat(Tok::Mut);
                let inner = self.ty()?;
                let span = start.to(self.prev_span());
                let mut t = self.push_ty(TyExpr::Ref { mutable, inner }, span);
                if double {
                    t = self.push_ty(TyExpr::Ref { mutable: false, inner: t }, span);
                }
                Ok(t)
            }
            Tok::LParen => {
                self.bump();
                if self.eat(Tok::RParen) {
                    return Ok(self.push_ty(TyExpr::Unit, start.to(self.prev_span())));
                }
                Err(unsupported(start, "tuple types"))
            }
            Tok::LBracket => Err(unsupported(start, "array and slice types")),
            Tok::Impl | Tok::Dyn => Err(unsupported(start, "`impl Trait` and `dyn Trait` types")),
            Tok::Fn => Err(unsupported(start, "function pointer types")),
            _ => {
                let path = self.path(true)?;
                Ok(self.push_ty(TyExpr::Path(path), start.to(self.prev_span())))
            }
        }
    }

    /// Parses `a::b::<T>::c`. In type position (`in_type`), generics need no `::`.
    fn path(&mut self, in_type: bool) -> PResult<Vec<PathSeg>> {
        let mut segs = Vec::new();
        loop {
            let (name, _) = self.ident()?;
            let mut generics = Vec::new();
            let turbofish = self.peek() == Tok::PathSep && self.peek_at(1) == Tok::Lt;
            if (in_type && self.peek() == Tok::Lt) || turbofish {
                if turbofish {
                    self.bump();
                }
                self.bump();
                while self.peek() != Tok::Gt {
                    if self.peek() == Tok::Lifetime {
                        return Err(lifetime_error(self.span()));
                    }
                    generics.push(self.ty()?);
                    if !self.eat(Tok::Comma) {
                        break;
                    }
                }
                self.expect(Tok::Gt, "`>`")?;
            }
            segs.push(PathSeg { name, generics });
            if self.peek() == Tok::PathSep && matches!(self.peek_at(1), Tok::Ident(_) | Tok::SelfUpper) {
                self.bump();
            } else {
                break;
            }
        }
        Ok(segs)
    }

    // ---------- Blocks and statements ----------

    fn block(&mut self) -> PResult<BlockId> {
        self.nest(|p| p.block_inner())
    }

    fn block_inner(&mut self) -> PResult<BlockId> {
        let start = self.expect(Tok::LBrace, "`{`")?;
        let mut stmts = Vec::new();
        let mut tail = None;
        while self.peek() != Tok::RBrace {
            if self.peek() == Tok::Eof {
                return Err(syntax(self.span(), "expected `}`, found end of file"));
            }
            if self.eat(Tok::Semi) {
                continue;
            }
            if matches!(self.peek(), Tok::Fn | Tok::Struct | Tok::Enum | Tok::Impl | Tok::Use | Tok::Pound) {
                return Err(unsupported(self.span(), "items inside function bodies"));
            }
            if self.peek() == Tok::Let {
                let s = self.bump().span;
                let pat = self.pattern()?;
                let ty = if self.eat(Tok::Colon) { Some(self.ty()?) } else { None };
                let init = if self.eat(Tok::Eq) { Some(self.expr()?) } else { None };
                if self.peek() == Tok::Else {
                    return Err(unsupported(self.span(), "let-else"));
                }
                self.expect(Tok::Semi, "`;`")?;
                stmts.push(Stmt::Let { pat, ty, init, span: s.to(self.prev_span()) });
                continue;
            }
            let block_like = matches!(self.peek(), Tok::If | Tok::Match | Tok::While | Tok::Loop | Tok::For | Tok::LBrace);
            let expr = if block_like {
                let e = self.block_like_expr()?;
                // Allow method calls on a block-like expression, as rustc does.
                if self.peek() == Tok::Dot || self.peek() == Tok::Question {
                    let e = self.postfix(e)?;
                    self.binary_rest(e, 0, false)?
                } else {
                    e
                }
            } else {
                self.expr()?
            };
            if self.eat(Tok::Semi) {
                stmts.push(Stmt::Expr { expr, semi: true });
            } else if self.peek() == Tok::RBrace {
                tail = Some(expr);
            } else if block_like {
                stmts.push(Stmt::Expr { expr, semi: false });
            } else {
                return Err(syntax(self.span(), format!("expected `;` or `}}`, found {:?}", self.peek())));
            }
        }
        let end = self.expect(Tok::RBrace, "`}`")?;
        Ok(self.push_block(Block { stmts, tail, span: start.to(end) }))
    }

    // ---------- Patterns ----------

    fn pattern(&mut self) -> PResult<PatId> {
        self.nest(|p| p.pattern_inner())
    }

    fn pattern_inner(&mut self) -> PResult<PatId> {
        let start = self.span();
        self.eat(Tok::Pipe);
        let first = self.pattern_one()?;
        if self.peek() != Tok::Pipe {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat(Tok::Pipe) {
            alts.push(self.pattern_one()?);
        }
        Ok(self.push_pat(Pat::Or(alts), start.to(self.prev_span())))
    }

    fn pattern_one(&mut self) -> PResult<PatId> {
        let start = self.span();
        let pat = match self.peek() {
            Tok::Underscore => {
                self.bump();
                Pat::Wild
            }
            Tok::Ref | Tok::Mut => {
                let by_ref = self.eat(Tok::Ref);
                let mutable = self.eat(Tok::Mut);
                let (name, _) = self.ident()?;
                Pat::Binding { name, mutable, by_ref }
            }
            Tok::Int(..) | Tok::Minus | Tok::Str(_) | Tok::Char(_) | Tok::True | Tok::False => {
                let lo = self.literal_expr()?;
                if self.eat(Tok::DotDotEq) {
                    let hi = self.literal_expr()?;
                    Pat::Range { lo, hi }
                } else {
                    Pat::Lit(lo)
                }
            }
            Tok::Ident(_) | Tok::SelfUpper => {
                let path = self.path(false)?;
                match self.peek() {
                    Tok::LParen => {
                        self.bump();
                        let mut elems = Vec::new();
                        while self.peek() != Tok::RParen {
                            if self.peek() == Tok::DotDot {
                                return Err(unsupported(self.span(), "`..` in tuple patterns"));
                            }
                            elems.push(self.pattern()?);
                            if !self.eat(Tok::Comma) {
                                break;
                            }
                        }
                        self.expect(Tok::RParen, "`)`")?;
                        Pat::TupleStruct { path, elems }
                    }
                    Tok::LBrace => {
                        self.bump();
                        let mut fields = Vec::new();
                        let mut rest = false;
                        while self.peek() != Tok::RBrace {
                            if self.eat(Tok::DotDot) {
                                rest = true;
                                break;
                            }
                            let fstart = self.span();
                            let by_ref = self.eat(Tok::Ref);
                            let mutable = self.eat(Tok::Mut);
                            let (fname, fspan) = self.ident()?;
                            let p = if !by_ref && !mutable && self.eat(Tok::Colon) {
                                self.pattern()?
                            } else {
                                self.push_pat(Pat::Binding { name: fname, mutable, by_ref }, fstart.to(fspan))
                            };
                            fields.push((fname, p));
                            if !self.eat(Tok::Comma) {
                                break;
                            }
                        }
                        self.expect(Tok::RBrace, "`}`")?;
                        Pat::Struct { path, fields, rest }
                    }
                    _ if path.len() == 1 => {
                        // A lone identifier is a binding. Unit variants need a path such as `Kind::C`.
                        Pat::Binding { name: path[0].name, mutable: false, by_ref: false }
                    }
                    _ => Pat::Path(path),
                }
            }
            Tok::LParen => return Err(unsupported(start, "tuple patterns")),
            Tok::LBracket => return Err(unsupported(start, "slice patterns")),
            Tok::Amp => return Err(unsupported(start, "reference patterns")),
            Tok::Reserved(_) => return Err(self.reserved_error(start)),
            t => return Err(syntax(start, format!("expected a pattern, found {t:?}"))),
        };
        Ok(self.push_pat(pat, start.to(self.prev_span())))
    }

    fn literal_expr(&mut self) -> PResult<ExprId> {
        let start = self.span();
        let neg = self.eat(Tok::Minus);
        let e = match self.bump().tok {
            Tok::Int(v, s) => Expr::Int(v, s),
            Tok::Str(i) if !neg => Expr::Str(i + self.str_base),
            Tok::Char(c) if !neg => Expr::Char(c),
            Tok::True if !neg => Expr::Bool(true),
            Tok::False if !neg => Expr::Bool(false),
            t => return Err(syntax(start, format!("expected a literal, found {t:?}"))),
        };
        let span = start.to(self.prev_span());
        let id = self.push_expr(e, span);
        Ok(if neg { self.push_expr(Expr::Unary { op: UnOp::Neg, expr: id }, span) } else { id })
    }

    // ---------- Expressions ----------

    pub fn expr(&mut self) -> PResult<ExprId> {
        self.expr_ctx(false)
    }

    /// `no_struct` is set in `if`, `while`, `match`, and `for` heads, where `{` starts the body.
    fn expr_ctx(&mut self, no_struct: bool) -> PResult<ExprId> {
        let start = self.span();
        if matches!(self.peek(), Tok::Pipe | Tok::OrOr | Tok::Move) {
            return Err(unsupported(start, "closures"));
        }
        // Assignment is right-associative and lowest.
        let lhs = self.range_expr(no_struct)?;
        // `>>=` arrives as two tokens (`>` then `>=`), since `>>` is never lexed as one.
        let (op, consume) = if self.at_shr_assign() {
            (Some(BinOp::Shr), 2)
        } else {
            (
                match self.peek() {
                    Tok::Eq => None,
                    Tok::PlusEq => Some(BinOp::Add),
                    Tok::MinusEq => Some(BinOp::Sub),
                    Tok::StarEq => Some(BinOp::Mul),
                    Tok::SlashEq => Some(BinOp::Div),
                    Tok::PercentEq => Some(BinOp::Rem),
                    Tok::AmpEq => Some(BinOp::BitAnd),
                    Tok::PipeEq => Some(BinOp::BitOr),
                    Tok::CaretEq => Some(BinOp::BitXor),
                    Tok::ShlEq => Some(BinOp::Shl),
                    _ => return Ok(lhs),
                },
                1,
            )
        };
        for _ in 0..consume {
            self.bump();
        }
        let rhs = self.expr_ctx(no_struct)?;
        let span = start.to(self.prev_span());
        Ok(match op {
            None => self.push_expr(Expr::Assign { lhs, rhs }, span),
            Some(op) => self.push_expr(Expr::AssignOp { op, lhs, rhs }, span),
        })
    }

    fn range_expr(&mut self, no_struct: bool) -> PResult<ExprId> {
        let start = self.span();
        let lo = if matches!(self.peek(), Tok::DotDot | Tok::DotDotEq) { None } else { Some(self.binary(0, no_struct)?) };
        let inclusive = match self.peek() {
            Tok::DotDot => false,
            Tok::DotDotEq => true,
            _ => return Ok(lo.unwrap()),
        };
        self.bump();
        let ends = matches!(self.peek(), Tok::RParen | Tok::RBracket | Tok::RBrace | Tok::Comma | Tok::Semi | Tok::Eof)
            || (no_struct && self.peek() == Tok::LBrace);
        let hi = if ends { None } else { Some(self.binary(0, no_struct)?) };
        Ok(self.push_expr(Expr::Range { lo, hi, inclusive }, start.to(self.prev_span())))
    }

    fn binop(&self) -> Option<(BinOp, u8, usize)> {
        // (operator, precedence, token count). Higher binds tighter.
        Some(match self.peek() {
            Tok::OrOr => (BinOp::Or, 1, 1),
            Tok::AndAnd => (BinOp::And, 2, 1),
            Tok::EqEq => (BinOp::Eq, 3, 1),
            Tok::Ne => (BinOp::Ne, 3, 1),
            Tok::Lt => (BinOp::Lt, 3, 1),
            Tok::Le => (BinOp::Le, 3, 1),
            // `>>=` is a compound assignment, not a shift: leave it for `expr_ctx`.
            Tok::Gt if self.at_shr_assign() => return None,
            Tok::Gt if self.at_shr() => (BinOp::Shr, 7, 2),
            Tok::Gt => (BinOp::Gt, 3, 1),
            Tok::Ge => (BinOp::Ge, 3, 1),
            Tok::Pipe => (BinOp::BitOr, 4, 1),
            Tok::Caret => (BinOp::BitXor, 5, 1),
            Tok::Amp => (BinOp::BitAnd, 6, 1),
            Tok::Shl => (BinOp::Shl, 7, 1),
            Tok::Plus => (BinOp::Add, 8, 1),
            Tok::Minus => (BinOp::Sub, 8, 1),
            Tok::Star => (BinOp::Mul, 9, 1),
            Tok::Slash => (BinOp::Div, 9, 1),
            Tok::Percent => (BinOp::Rem, 9, 1),
            _ => return None,
        })
    }

    fn binary(&mut self, min_prec: u8, no_struct: bool) -> PResult<ExprId> {
        let lhs = self.unary(no_struct)?;
        self.binary_rest(lhs, min_prec, no_struct)
    }

    fn binary_rest(&mut self, mut lhs: ExprId, min_prec: u8, no_struct: bool) -> PResult<ExprId> {
        // A long flat chain (`a + a + ...`) makes a deep tree without any recursion
        // here, so count the operators to keep later passes off the stack limit.
        let mut chain = 0u32;
        while let Some((op, prec, n)) = self.binop() {
            chain += 1;
            if chain > MAX_DEPTH {
                return Err(Diag::new(
                    "L9001",
                    self.span(),
                    format!("operator chains longer than {MAX_DEPTH} are not supported"),
                    "Split the expression into smaller pieces with `let`.",
                ));
            }
            if prec <= min_prec {
                break;
            }
            for _ in 0..n {
                self.bump();
            }
            let rhs = self.binary(prec, no_struct)?;
            let span = self.ast.expr_span(lhs).to(self.prev_span());
            if op.is_cmp()
                && let Some((op2, prec2, _)) = self.binop()
                && prec2 == prec
                && op2.is_cmp()
            {
                return Err(syntax(self.span(), "comparison operators cannot be chained; add parentheses"));
            }
            lhs = self.push_expr(Expr::Binary { op, lhs, rhs }, span);
        }
        // `as` binds tighter than every binary operator; handled in `unary` postfix.
        Ok(lhs)
    }

    /// A prefix expression followed by any `as` casts. Prefix operators bind tighter than `as`.
    fn unary(&mut self, no_struct: bool) -> PResult<ExprId> {
        let e = self.prefix(no_struct)?;
        self.cast_rest(e)
    }

    fn prefix(&mut self, no_struct: bool) -> PResult<ExprId> {
        self.nest(|p| p.prefix_inner(no_struct))
    }

    fn prefix_inner(&mut self, no_struct: bool) -> PResult<ExprId> {
        let start = self.span();
        let e = match self.peek() {
            Tok::Minus => {
                self.bump();
                let inner = self.prefix(no_struct)?;
                Expr::Unary { op: UnOp::Neg, expr: inner }
            }
            Tok::Bang => {
                self.bump();
                let inner = self.prefix(no_struct)?;
                Expr::Unary { op: UnOp::Not, expr: inner }
            }
            Tok::Star => {
                self.bump();
                Expr::Deref(self.prefix(no_struct)?)
            }
            Tok::Amp | Tok::AndAnd => {
                let double = self.bump().tok == Tok::AndAnd;
                let mutable = self.eat(Tok::Mut);
                let inner = self.prefix(no_struct)?;
                let span = start.to(self.prev_span());
                let mut id = self.push_expr(Expr::Ref { mutable, expr: inner }, span);
                if double {
                    id = self.push_expr(Expr::Ref { mutable: false, expr: id }, span);
                }
                return Ok(id);
            }
            _ => {
                let e = self.primary(no_struct)?;
                return self.postfix(e);
            }
        };
        Ok(self.push_expr(e, start.to(self.prev_span())))
    }

    fn cast_rest(&mut self, mut e: ExprId) -> PResult<ExprId> {
        while self.peek() == Tok::As {
            self.bump();
            let ty = self.ty()?;
            let span = self.ast.expr_span(e).to(self.prev_span());
            e = self.push_expr(Expr::Cast { expr: e, ty }, span);
        }
        Ok(e)
    }

    fn postfix(&mut self, mut e: ExprId) -> PResult<ExprId> {
        // Like `binary_rest`, a long postfix chain makes a deep tree iteratively.
        let mut chain = 0u32;
        loop {
            chain += 1;
            if chain > MAX_DEPTH {
                return Err(Diag::new(
                    "L9001",
                    self.span(),
                    format!("method and field chains longer than {MAX_DEPTH} are not supported"),
                    "Split the expression into smaller pieces with `let`.",
                ));
            }
            let start = self.ast.expr_span(e);
            match self.peek() {
                Tok::LParen => {
                    let args = self.call_args()?;
                    e = self.push_expr(Expr::Call { callee: e, args }, start.to(self.prev_span()));
                }
                Tok::Dot => {
                    self.bump();
                    if let Tok::Int(..) = self.peek() {
                        return Err(unsupported(self.span(), "tuple fields"));
                    }
                    let (name, name_span) = self.ident()?;
                    let mut generics = Vec::new();
                    if self.peek() == Tok::PathSep && self.peek_at(1) == Tok::Lt {
                        self.bump();
                        self.bump();
                        while self.peek() != Tok::Gt {
                            generics.push(self.ty()?);
                            if !self.eat(Tok::Comma) {
                                break;
                            }
                        }
                        self.expect(Tok::Gt, "`>`")?;
                    }
                    if self.peek() == Tok::LParen {
                        let args = self.call_args()?;
                        e = self.push_expr(Expr::MethodCall { recv: e, name, name_span, generics, args }, start.to(self.prev_span()));
                    } else {
                        e = self.push_expr(Expr::Field { base: e, name }, start.to(self.prev_span()));
                    }
                }
                Tok::LBracket => {
                    self.bump();
                    let index = self.expr()?;
                    self.expect(Tok::RBracket, "`]`")?;
                    e = self.push_expr(Expr::Index { base: e, index }, start.to(self.prev_span()));
                }
                Tok::Question => return Err(unsupported(self.span(), "the `?` operator")),
                _ => return Ok(e),
            }
        }
    }

    fn call_args(&mut self) -> PResult<Vec<ExprId>> {
        self.expect(Tok::LParen, "`(`")?;
        let mut args = Vec::new();
        while self.peek() != Tok::RParen {
            args.push(self.expr()?);
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RParen, "`)`")?;
        Ok(args)
    }

    fn block_like_expr(&mut self) -> PResult<ExprId> {
        let start = self.span();
        let e = match self.peek() {
            Tok::LBrace => Expr::Block(self.block()?),
            Tok::If => return self.if_expr(),
            Tok::While => {
                self.bump();
                if self.eat(Tok::Let) {
                    return self.while_let(start);
                }
                let cond = self.expr_ctx(true)?;
                let body = self.block()?;
                Expr::While { cond, body }
            }
            Tok::Loop => {
                self.bump();
                Expr::Loop { body: self.block()? }
            }
            Tok::For => {
                self.bump();
                let pat = self.pattern()?;
                self.expect(Tok::In, "`in`")?;
                let iter = self.expr_ctx(true)?;
                let body = self.block()?;
                Expr::For { pat, iter, body }
            }
            Tok::Match => {
                self.bump();
                let scrut = self.expr_ctx(true)?;
                self.expect(Tok::LBrace, "`{`")?;
                let mut arms = Vec::new();
                while self.peek() != Tok::RBrace {
                    let pat = self.pattern()?;
                    let guard = if self.eat(Tok::If) { Some(self.expr()?) } else { None };
                    self.expect(Tok::FatArrow, "`=>`")?;
                    let block_body = self.peek() == Tok::LBrace;
                    let body = if block_body { self.block_like_expr()? } else { self.expr()? };
                    arms.push(Arm { pat, guard, body });
                    if !self.eat(Tok::Comma) && !block_body && self.peek() != Tok::RBrace {
                        return Err(syntax(self.span(), "expected `,` after match arm"));
                    }
                }
                self.expect(Tok::RBrace, "`}`")?;
                Expr::Match { scrut, arms }
            }
            _ => unreachable!(),
        };
        Ok(self.push_expr(e, start.to(self.prev_span())))
    }

    fn if_expr(&mut self) -> PResult<ExprId> {
        let start = self.expect(Tok::If, "`if`")?;
        if self.eat(Tok::Let) {
            return self.if_let(start);
        }
        let cond = self.expr_ctx(true)?;
        let then = self.block()?;
        let els = if self.eat(Tok::Else) {
            if self.peek() == Tok::If {
                Some(self.if_expr()?)
            } else {
                let s = self.span();
                let b = self.block()?;
                Some(self.push_expr(Expr::Block(b), s.to(self.prev_span())))
            }
        } else {
            None
        };
        Ok(self.push_expr(Expr::If { cond, then, els }, start.to(self.prev_span())))
    }

    /// `if let P = e { a } else { b }` becomes `match e { P => { a } _ => { b } }`.
    fn if_let(&mut self, start: Span) -> PResult<ExprId> {
        let pat = self.pattern()?;
        self.expect(Tok::Eq, "`=`")?;
        let scrut = self.expr_ctx(true)?;
        let then = self.block()?;
        let then_span = self.ast.block(then).span;
        let then_e = self.push_expr(Expr::Block(then), then_span);
        let els = if self.eat(Tok::Else) {
            if self.peek() == Tok::If {
                self.if_expr()?
            } else {
                let s = self.span();
                let b = self.block()?;
                self.push_expr(Expr::Block(b), s.to(self.prev_span()))
            }
        } else {
            self.push_expr(Expr::Unit, then_span)
        };
        let span = start.to(self.prev_span());
        let wild = self.push_pat(Pat::Wild, span);
        let arms = vec![Arm { pat, guard: None, body: then_e }, Arm { pat: wild, guard: None, body: els }];
        Ok(self.push_expr(Expr::Match { scrut, arms }, span))
    }

    /// `while let P = e { body }` becomes `loop { match e { P => { body } _ => break } }`.
    fn while_let(&mut self, start: Span) -> PResult<ExprId> {
        let pat = self.pattern()?;
        self.expect(Tok::Eq, "`=`")?;
        let scrut = self.expr_ctx(true)?;
        let body = self.block()?;
        let span = start.to(self.prev_span());
        let body_e = self.push_expr(Expr::Block(body), span);
        let brk = self.push_expr(Expr::Break(None), span);
        let wild = self.push_pat(Pat::Wild, span);
        let arms = vec![Arm { pat, guard: None, body: body_e }, Arm { pat: wild, guard: None, body: brk }];
        let m = self.push_expr(Expr::Match { scrut, arms }, span);
        let block = self.push_block(Block { stmts: vec![Stmt::Expr { expr: m, semi: true }], tail: None, span });
        Ok(self.push_expr(Expr::Loop { body: block }, span))
    }

    fn primary(&mut self, no_struct: bool) -> PResult<ExprId> {
        let start = self.span();
        let e = match self.peek() {
            Tok::Int(v, s) => {
                self.bump();
                Expr::Int(v, s)
            }
            Tok::Float => return Err(unsupported(start, "floating point numbers")),
            Tok::Str(i) => {
                self.bump();
                Expr::Str(i + self.str_base)
            }
            Tok::Char(c) => {
                self.bump();
                Expr::Char(c)
            }
            Tok::True => {
                self.bump();
                Expr::Bool(true)
            }
            Tok::False => {
                self.bump();
                Expr::Bool(false)
            }
            Tok::SelfLower => {
                self.bump();
                Expr::SelfValue
            }
            Tok::LParen => {
                self.bump();
                if self.eat(Tok::RParen) {
                    Expr::Unit
                } else {
                    let inner = self.expr()?;
                    if self.peek() == Tok::Comma {
                        return Err(unsupported(self.span(), "tuples"));
                    }
                    self.expect(Tok::RParen, "`)`")?;
                    return Ok(inner);
                }
            }
            Tok::LBracket => return Err(unsupported(start, "array literals")),
            Tok::If | Tok::Match | Tok::While | Tok::Loop | Tok::For | Tok::LBrace => return self.block_like_expr(),
            Tok::Break => {
                self.bump();
                if matches!(self.peek(), Tok::Lifetime) {
                    return Err(unsupported(self.span(), "loop labels"));
                }
                let val = if self.can_start_expr() { Some(self.expr()?) } else { None };
                Expr::Break(val)
            }
            Tok::Continue => {
                self.bump();
                Expr::Continue
            }
            Tok::Return => {
                self.bump();
                let val = if self.can_start_expr() { Some(self.expr()?) } else { None };
                Expr::Return(val)
            }
            Tok::Lifetime => return Err(unsupported(start, "loop labels")),
            Tok::Pipe | Tok::OrOr | Tok::Move => return Err(unsupported(start, "closures")),
            Tok::Unsafe => return Err(Diag::new("L0404", start, "`unsafe` is not supported", "Remove the unsafe code.")),
            Tok::Ident(_) | Tok::SelfUpper => {
                if self.peek_at(1) == Tok::Bang {
                    return self.macro_call();
                }
                let path = self.path(false)?;
                if self.peek() == Tok::LBrace && !no_struct {
                    return self.struct_lit(path, start);
                }
                Expr::Path(path)
            }
            Tok::Reserved(_) => return Err(self.reserved_error(start)),
            t => return Err(syntax(start, format!("expected an expression, found {t:?}"))),
        };
        Ok(self.push_expr(e, start.to(self.prev_span())))
    }

    fn can_start_expr(&self) -> bool {
        !matches!(self.peek(), Tok::Semi | Tok::RBrace | Tok::RParen | Tok::Comma | Tok::RBracket | Tok::Eof)
    }

    fn struct_lit(&mut self, path: Vec<PathSeg>, start: Span) -> PResult<ExprId> {
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while self.peek() != Tok::RBrace {
            if self.peek() == Tok::DotDot {
                return Err(unsupported(self.span(), "struct update syntax"));
            }
            let (name, span) = self.ident()?;
            let value = if self.eat(Tok::Colon) {
                self.expr()?
            } else {
                let seg = PathSeg { name, generics: Vec::new() };
                self.push_expr(Expr::Path(vec![seg]), span)
            };
            fields.push((name, span, value));
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(self.push_expr(Expr::StructLit { path, fields }, start.to(self.prev_span())))
    }

    fn macro_call(&mut self) -> PResult<ExprId> {
        let start = self.span();
        let (name, _) = self.ident()?;
        self.bump(); // `!`
        let k = self.known;
        let table = [
            (k.println, MacroKind::Println),
            (k.print, MacroKind::Print),
            (k.eprintln, MacroKind::Eprintln),
            (k.eprint, MacroKind::Eprint),
            (k.format, MacroKind::Format),
            (k.panic, MacroKind::Panic),
            (k.vec, MacroKind::Vec),
            (k.assert, MacroKind::Assert),
            (k.assert_eq, MacroKind::AssertEq),
            (k.assert_ne, MacroKind::AssertNe),
            (k.todo, MacroKind::Todo),
            (k.unreachable, MacroKind::Unreachable),
        ];
        let Some(&(_, kind)) = table.iter().find(|(s, _)| *s == name) else {
            return Err(macro_error(start));
        };
        let close = match self.bump().tok {
            Tok::LParen => Tok::RParen,
            Tok::LBracket => Tok::RBracket,
            Tok::LBrace => Tok::RBrace,
            _ => return Err(syntax(start, "expected `(` after macro name")),
        };
        let mut args = Vec::new();
        let mut fmt = Vec::new();
        let mut repeat = false;
        // Leading non-format arguments.
        let fixed = match kind {
            MacroKind::Assert => 1,
            MacroKind::AssertEq | MacroKind::AssertNe => 2,
            _ => 0,
        };
        if kind == MacroKind::Vec {
            while self.peek() != close {
                args.push(self.expr()?);
                if self.eat(Tok::Semi) {
                    args.push(self.expr()?);
                    repeat = true;
                    break;
                }
                if !self.eat(Tok::Comma) {
                    break;
                }
            }
        } else {
            for _ in 0..fixed {
                args.push(self.expr()?);
                if !self.eat(Tok::Comma) {
                    break;
                }
            }
            if args.len() < fixed {
                return Err(syntax(self.span(), "too few arguments for this macro"));
            }
            // `print!`, `eprint!`, and `format!` need a format string; `println!` and kin do not.
            let needs_str = matches!(kind, MacroKind::Print | MacroKind::Eprint | MacroKind::Format);
            if needs_str && !matches!(self.peek(), Tok::Str(_)) {
                return Err(syntax(self.span(), "expected a format string literal"));
            }
            if let Tok::Str(si) = self.peek() {
                let lit_span = self.bump().span;
                let mut extra = Vec::new();
                while self.eat(Tok::Comma) {
                    if self.peek() == close {
                        break;
                    }
                    if matches!(self.peek(), Tok::Ident(_)) && self.peek_at(1) == Tok::Eq {
                        return Err(unsupported(self.span(), "named format arguments"));
                    }
                    extra.push(self.expr()?);
                }
                let s = self.ast.strings[(si + self.str_base) as usize].clone();
                let base = args.len();
                fmt = self.format_string(&s, lit_span, base, &mut extra)?;
                args.extend(extra);
            } else if self.peek() != close {
                return Err(syntax(self.span(), "expected a format string literal"));
            }
        }
        self.expect(close, "closing delimiter")?;
        Ok(self.push_expr(Expr::Macro { kind, args, fmt, repeat }, start.to(self.prev_span())))
    }

    /// Splits a format string into pieces. `{name}` captures become extra path arguments.
    fn format_string(&mut self, s: &str, span: Span, base: usize, extra: &mut Vec<ExprId>) -> PResult<Vec<FmtPiece>> {
        let mut pieces = Vec::new();
        let mut lit = String::new();
        let mut next = 0usize;
        let mut chars = s.chars().peekable();
        let explicit = extra.len();
        let mut used = vec![false; explicit];
        while let Some(c) = chars.next() {
            if c == '{' && chars.peek() == Some(&'{') {
                chars.next();
                lit.push('{');
            } else if c == '}' && chars.peek() == Some(&'}') {
                chars.next();
                lit.push('}');
            } else if c == '{' {
                let mut spec = String::new();
                loop {
                    match chars.next() {
                        Some('}') => break,
                        Some(ch) => spec.push(ch),
                        None => return Err(syntax(span, "unterminated `{` in format string")),
                    }
                }
                let (name, fmt) = spec.split_once(':').unwrap_or((spec.as_str(), ""));
                let debug = match fmt {
                    "" => false,
                    "?" => true,
                    _ => return Err(unsupported(span, &format!("format spec `{{:{fmt}}}`"))),
                };
                let index = if name.is_empty() {
                    next += 1;
                    next - 1
                } else if let Ok(n) = name.parse::<usize>() {
                    n
                } else {
                    let sym = self.interner.intern(name);
                    let seg = PathSeg { name: sym, generics: Vec::new() };
                    let e = self.push_expr(Expr::Path(vec![seg]), span);
                    extra.push(e);
                    used.push(true);
                    extra.len() - 1
                };
                if index >= extra.len() {
                    return Err(syntax(span, "format string refers to a missing argument"));
                }
                used[index] = true;
                if !lit.is_empty() {
                    pieces.push(FmtPiece::Lit(std::mem::take(&mut lit)));
                }
                pieces.push(FmtPiece::Arg { index: base + index, debug });
            } else if c == '}' {
                return Err(syntax(span, "unmatched `}` in format string"));
            } else {
                lit.push(c);
            }
        }
        if used.iter().any(|u| !u) {
            return Err(syntax(span, "format argument never used"));
        }
        if !lit.is_empty() {
            pieces.push(FmtPiece::Lit(lit));
        }
        Ok(pieces)
    }
}

fn macro_error(span: Span) -> Diag {
    Diag::new(
        "L0401",
        span,
        "user macros are not supported",
        "Write a function. Lust has built-in println!, print!, eprintln!, format!, vec!, panic!, assert!, assert_eq!, assert_ne!, todo!, and unreachable!.",
    )
}
