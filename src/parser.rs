// Recursive-descent parser with precedence climbing for binary operators.
// Rust syntax that lust rejects on purpose gets its own stable error code here:
// lifetimes and user macros keep their original codes (L0203, L0401), `unsafe`
// and `async` keep theirs (L0404, L0405), and each AST v2 form whose parser
// lands later rejects with the Appendix A code for its area (docs/ARCH.md S3b).
use crate::ast::*;
use crate::diag::{Diag, Span, not_yet};
use crate::intern::{Interner, Known, Sym};
use crate::lexer::{Delim, Lexed, Tok, Token, TokenTree};

// Stable Appendix A codes for AST v2 forms the parser recognizes but does not
// build yet. Each code's registry row and explain page name its area.
#[allow(dead_code)] // Module forms parse now; the resolver rejects the rest.
const C_MOD: &str = "L0505"; // modules, imports, and module paths
const C_ATTR: &str = "L0522"; // cfg and known-but-unhandled attributes
const C_TY: &str = "L0602"; // type forms and type aliases
const C_TRAIT: &str = "L0614"; // traits, generics, and where clauses
const C_ASSOC: &str = "L0621"; // associated items and qualified paths
const C_CONST: &str = "L0632"; // const and static items, const generics
const C_LIT: &str = "L0641"; // float and byte literals, other std-surface syntax
#[allow(dead_code)] // Typed receivers parse now; collect rejects them until method resolution lands.
const C_METHOD: &str = "L0721"; // method and receiver forms
const C_EXTERN: &str = "L0810"; // extern blocks and foreign items
const C_CORE: &str = "L0820"; // core expression, pattern, and statement forms

fn unsafe_error(span: Span) -> Diag {
    Diag::new("L0404", span, "`unsafe` is not supported", "Remove the unsafe code.")
}

fn async_error(span: Span) -> Diag {
    Diag::new("L0405", span, "`async` is not supported", "Use std::thread and channels.")
}

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
    /// The first form (by span) that parses into AST v2 shapes but
    /// later stages do not support yet: the parser builds the shape
    /// and records the reject it used to emit on sight, so the
    /// error a user sees is still the first one in the file.
    /// `parse` returns it after the parse, or in place of a later
    /// hard error.
    deferred: Option<Diag>,
    /// True while parsing an `if` or `while` condition, where `let` may
    /// appear as a chain element.
    let_ok: bool,
}

/// The deepest nesting lust parses (parentheses, prefix operators, blocks, types,
/// patterns, and operator or method chains). Real code stays far below this.
const MAX_DEPTH: u32 = 2000;

/// Parses a whole file (or chunk) into an `Ast`. Stops at the first error.
pub fn parse(lexed: &Lexed, interner: &Interner, known: &Known) -> PResult<Ast> {
    let mut p =
        Parser { toks: &lexed.tokens, pos: 0, ast: Ast::default(), interner, known, str_base: 0, depth: 0, deferred: None, let_ok: false };
    p.ast.strings = lexed.strings.clone();
    while p.peek() != Tok::Eof {
        let before = p.pos;
        let item = match p.item() {
            Ok(item) => item,
            Err(hard) => return Err(p.earlier(hard)),
        };
        if let Some(item) = item {
            p.ast.items.push(item);
        }
        // No parse loop may spin in place on bad input: each round must consume a token.
        if p.pos == before {
            return Err(p.earlier(syntax(p.span(), format!("expected an item, found {}", tok_name(p.peek())))));
        }
    }
    if let Some(d) = p.deferred.take() {
        return Err(d);
    }
    Ok(p.ast)
}

/// A parsed function body: its block, and its expression and pattern ranges.
pub type ParsedBody = (BlockId, (u32, u32), (u32, u32));

/// What one run of attributes in front of an item or part of an item yielded:
/// the derive list and `#[test]` flag today's stages read, plus the recorded
/// attributes later stages will read.
#[derive(Default)]
struct ParsedAttrs {
    derives: Vec<(Sym, Span)>,
    is_test: bool,
    attrs: Vec<Attr>,
}

/// Attributes the resolver reads (docs/ARCH.md section 1.6): parsed and
/// recorded like `derive`, then honored by cfg stripping and module
/// loading. `cfg!` the macro is a separate form and stays with W-MACRO.
const RESOLVE_ATTRS: &[&str] = &["cfg", "cfg_attr", "path", "macro_use", "macro_export", "no_implicit_prelude"];

/// Rust attribute names lust knows by name but does not handle yet
/// (docs/ARCH.md section 1.6 lists what each later package must honor).
/// These reject with L0522; any other name rejects with L0402.
const KNOWN_ATTRS: &[&str] = &[
    "repr",
    "inline",
    "cold",
    "must_use",
    "track_caller",
    "non_exhaustive",
    "deprecated",
    "doc",
    "bench",
    "ignore",
    "should_panic",
    "global_allocator",
    "default",
    "target_feature",
    "link_section",
    "export_name",
    "link",
    "no_mangle",
    "no_link",
    "crate_type",
    "crate_name",
    "recursion_limit",
    "type_length_limit",
    "feature",
    "forbid",
];

/// Parses one function body (`tokens` runs from its `{` to its `}`) and appends it to `ast`.
/// Returns the body block and the new expression and pattern ranges for the function.
pub fn parse_body(tokens: &[Token], strings: &[String], ast: &mut Ast, interner: &Interner, known: &Known) -> PResult<ParsedBody> {
    let mut toks = tokens.to_vec();
    let end = tokens.last().map_or(Span::default(), |t| t.span);
    toks.push(Token { tok: Tok::Eof, span: Span { lo: end.hi, ..end } });
    let str_base = ast.strings.len() as u32;
    ast.strings.extend_from_slice(strings);
    let mut p =
        Parser { toks: &toks, pos: 0, ast: std::mem::take(ast), interner, known, str_base, depth: 0, deferred: None, let_ok: false };
    let (e0, p0) = (p.ast.exprs.len() as u32, p.ast.pats.len() as u32);
    let body = p.block();
    let ranges = ((e0, p.ast.exprs.len() as u32), (p0, p.ast.pats.len() as u32));
    let deferred = p.deferred.take();
    *ast = p.ast;
    let body = match (body, deferred) {
        (Err(hard), Some(d)) if d.span.lo <= hard.span.lo => return Err(d),
        (Ok(_), Some(d)) => return Err(d),
        (body, _) => body?,
    };
    Ok((body, ranges.0, ranges.1))
}

/// Fragment probes for macro matching (src/expand, ARCH 6.2): each returns
/// true when `toks` parses as exactly one fragment of the named kind with
/// this parser. `toks` has no final `Eof`; one is added. String-literal
/// tokens in `toks` index into `strings`, as in a `Lexed`.
fn probe_with(toks: &[Token], strings: &[String], interner: &Interner, known: &Known, f: impl FnOnce(&mut Parser) -> bool) -> bool {
    let mut v: Vec<Token> = toks.to_vec();
    let end = toks.last().map_or(Span::default(), |t| t.span);
    v.push(Token { tok: Tok::Eof, span: Span { lo: end.hi, ..end } });
    let mut ast = Ast::default();
    ast.strings = strings.to_vec();
    let mut p = Parser { toks: &v, pos: 0, ast, interner, known, str_base: 0, depth: 0, deferred: None, let_ok: false };
    f(&mut p)
}

/// True when `toks` is exactly one expression.
pub fn probe_expr(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> bool {
    probe_with(toks, strings, interner, known, |p| p.expr().is_ok() && p.peek() == Tok::Eof)
}

/// True when `toks` is exactly one type.
pub fn probe_ty(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> bool {
    probe_with(toks, strings, interner, known, |p| p.ty().is_ok() && p.peek() == Tok::Eof)
}

/// True when `toks` is exactly one pattern.
pub fn probe_pat(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> bool {
    probe_with(toks, strings, interner, known, |p| p.pattern().is_ok() && p.peek() == Tok::Eof)
}

/// True when `toks` (braces included) is exactly one block.
pub fn probe_block(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> bool {
    probe_with(toks, strings, interner, known, |p| p.block().is_ok() && p.peek() == Tok::Eof)
}

/// True when `toks` is exactly one statement: wrapped in a block it parses
/// as one statement (an expression statement without `;` becomes the block
/// tail, which still counts as the one statement rustc's `stmt` fragment
/// accepts). A trailing `;` in `toks` is the caller's to include or not.
pub fn probe_stmt(toks: &[Token], strings: &[String], interner: &Interner, known: &Known) -> bool {
    let span = toks.first().map_or(Span::default(), |t| t.span);
    let mut wrapped = Vec::with_capacity(toks.len() + 2);
    wrapped.push(Token { tok: Tok::LBrace, span });
    wrapped.extend_from_slice(toks);
    wrapped.push(Token { tok: Tok::RBrace, span });
    probe_with(&wrapped, strings, interner, known, |p| match p.block() {
        Ok(b) if p.peek() == Tok::Eof => {
            let block = p.ast.block(b);
            block.stmts.len() + usize::from(block.tail.is_some()) == 1
        }
        _ => false,
    })
}

/// Converts a flat token slice into nested token trees. Unbalanced input
/// nests on a best-effort basis; attribute contents are stored, not checked.
fn token_trees(toks: &[Token]) -> Vec<TokenTree> {
    fn delim_of(t: Tok) -> Option<Delim> {
        match t {
            Tok::LParen => Some(Delim::Paren),
            Tok::LBracket => Some(Delim::Bracket),
            Tok::LBrace => Some(Delim::Brace),
            _ => None,
        }
    }
    fn closes(open: Delim, t: Tok) -> bool {
        matches!((open, t), (Delim::Paren, Tok::RParen) | (Delim::Bracket, Tok::RBracket) | (Delim::Brace, Tok::RBrace))
    }
    fn build(toks: &[Token], pos: &mut usize, close: Option<Delim>, depth: u32) -> Vec<TokenTree> {
        let mut out = Vec::new();
        while let Some(t) = toks.get(*pos) {
            if close.is_some_and(|d| closes(d, t.tok)) {
                *pos += 1;
                break;
            }
            *pos += 1;
            if let Some(d) = delim_of(t.tok).filter(|_| depth < MAX_DEPTH) {
                let inner = build(toks, pos, Some(d), depth + 1);
                out.push(TokenTree::Delim(d, inner, t.span));
            } else {
                out.push(TokenTree::Token(*t));
            }
        }
        out
    }
    let mut pos = 0;
    build(toks, &mut pos, None, 0)
}

fn syntax(span: Span, msg: impl Into<String>) -> Diag {
    Diag::new("L0001", span, msg, "Fix the syntax. Lust uses Rust syntax.")
}

/// A token's name for error messages. Never shows the payload, so internal ids (interned
/// symbol numbers, string indexes) cannot leak into diagnostics.
fn tok_name(t: Tok) -> &'static str {
    use Tok::*;
    match t {
        Ident(_) => "identifier",
        Reserved(_) => "reserved keyword",
        Int(..) => "integer literal",
        Float(_) => "float literal",
        Str(_) => "string literal",
        DocStr(_) => "doc comment string",
        ByteStr => "byte string literal",
        ByteChar => "byte char literal",
        Char(_) => "char literal",
        Lifetime(_) => "lifetime",
        As => "`as`",
        Break => "`break`",
        Const => "`const`",
        Continue => "`continue`",
        Else => "`else`",
        Enum => "`enum`",
        False => "`false`",
        Fn => "`fn`",
        For => "`for`",
        If => "`if`",
        Impl => "`impl`",
        In => "`in`",
        Let => "`let`",
        Loop => "`loop`",
        Match => "`match`",
        Mod => "`mod`",
        Mut => "`mut`",
        Pub => "`pub`",
        Ref => "`ref`",
        Return => "`return`",
        SelfLower => "`self`",
        SelfUpper => "`Self`",
        Static => "`static`",
        Struct => "`struct`",
        Trait => "`trait`",
        True => "`true`",
        Type => "`type`",
        Unsafe => "`unsafe`",
        Use => "`use`",
        Where => "`where`",
        While => "`while`",
        Async => "`async`",
        Dyn => "`dyn`",
        Move => "`move`",
        Crate => "`crate`",
        Super => "`super`",
        Extern => "`extern`",
        Await => "`await`",
        LParen => "`(`",
        RParen => "`)`",
        LBrace => "`{`",
        RBrace => "`}`",
        LBracket => "`[`",
        RBracket => "`]`",
        Comma => "`,`",
        Semi => "`;`",
        Colon => "`:`",
        PathSep => "`::`",
        Dot => "`.`",
        DotDot => "`..`",
        DotDotEq => "`..=`",
        Ellipsis => "`...`",
        Arrow => "`->`",
        FatArrow => "`=>`",
        Eq => "`=`",
        EqEq => "`==`",
        Ne => "`!=`",
        Lt => "`<`",
        Le => "`<=`",
        Gt => "`>`",
        Ge => "`>=`",
        Plus => "`+`",
        Minus => "`-`",
        Star => "`*`",
        Slash => "`/`",
        Percent => "`%`",
        PlusEq => "`+=`",
        MinusEq => "`-=`",
        StarEq => "`*=`",
        SlashEq => "`/=`",
        PercentEq => "`%=`",
        AmpEq => "`&=`",
        PipeEq => "`|=`",
        CaretEq => "`^=`",
        ShlEq => "`<<=`",
        Amp => "`&`",
        AndAnd => "`&&`",
        Pipe => "`|`",
        OrOr => "`||`",
        Caret => "`^`",
        Bang => "`!`",
        Pound => "`#`",
        Question => "`?`",
        Underscore => "`_`",
        Shl => "`<<`",
        Dollar => "`$`",
        At => "`@`",
        Eof => "end of file",
    }
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
        if self.peek() == t {
            Ok(self.bump().span)
        } else {
            Err(syntax(self.span(), format!("expected {what}, found {}", tok_name(self.peek()))))
        }
    }
    fn ident(&mut self) -> PResult<(Sym, Span)> {
        match self.peek() {
            Tok::Ident(s) => Ok((s, self.bump().span)),
            Tok::SelfUpper => Ok((self.known.self_type, self.bump().span)),
            Tok::Reserved(_) => Err(self.reserved_error(self.span())),
            Tok::Lifetime(_) => Err(lifetime_error(self.span())),
            t => Err(syntax(self.span(), format!("expected identifier, found {}", tok_name(t)))),
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

    /// The rejection for an AST v2 form that starts at the current token.
    fn reject(&self, code: &'static str, what: &str) -> Diag {
        not_yet(code, self.span(), what)
    }

    /// Records the reject for a form the parser builds but later
    /// stages do not support yet, keeping the earliest by span.
    /// See the `deferred` field. No form defers today (generic and
    /// trait forms reach collect since W-TRAITS-CORE); the slot
    /// stays for the next AST form that parses before it checks.
    #[allow(dead_code)]
    fn defer(&mut self, d: Diag) {
        if self.deferred.as_ref().is_none_or(|old| d.span.lo < old.span.lo) {
            self.deferred = Some(d);
        }
    }

    /// The earlier of the deferred reject and a hard parse error.
    fn earlier(&mut self, hard: Diag) -> Diag {
        match self.deferred.take() {
            Some(d) if d.span.lo <= hard.span.lo => d,
            _ => hard,
        }
    }

    /// True when the current token is the identifier `name` (for weak keywords
    /// such as `union`, `macro_rules`, and `raw`).
    fn at_ident(&self, name: &str) -> bool {
        matches!(self.peek(), Tok::Ident(s) if self.interner.get(s) == name)
    }

    /// True at a macro call head: a path of one or more segments ending in `!`
    /// (for example `a::b!(..)`). Bounded: stops at the first other token.
    fn at_path_macro_call(&self) -> bool {
        let mut j = self.pos;
        loop {
            match self.toks.get(j).map(|t| t.tok) {
                Some(Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower) => j += 1,
                _ => return false,
            }
            match self.toks.get(j).map(|t| t.tok) {
                Some(Tok::Bang) => return true,
                Some(Tok::PathSep) => j += 1,
                _ => return false,
            }
        }
    }

    /// Parses visibility: `pub`, `pub(crate)`, `pub(super)`, or `pub(in path)`.
    /// Tolerant inside the parentheses, as the old skip-to-`)` code was: name
    /// tokens become the restricted path and other tokens are skipped.
    fn vis(&mut self) -> PResult<Vis> {
        if !self.eat(Tok::Pub) {
            return Ok(Vis::Private);
        }
        if self.peek() != Tok::LParen {
            return Ok(Vis::Public);
        }
        let start = self.bump().span;
        let mut path = Vec::new();
        while self.peek() != Tok::RParen {
            if self.peek() == Tok::Eof {
                return Err(syntax(self.span(), "expected `)` in visibility, found end of file"));
            }
            match self.bump().tok {
                Tok::Ident(s) | Tok::Reserved(s) => path.push(PathSeg::plain(s)),
                Tok::Crate => path.push(PathSeg::plain(self.interner.intern("crate"))),
                Tok::Super => path.push(PathSeg::plain(self.interner.intern("super"))),
                Tok::SelfLower => path.push(PathSeg::plain(self.known.self_value)),
                Tok::SelfUpper => path.push(PathSeg::plain(self.known.self_type)),
                _ => {}
            }
        }
        let end = self.bump().span;
        Ok(Vis::Restricted { path, span: start.to(end) })
    }

    /// True when the token after the current one starts where the current one ends, in
    /// the same file: the two were lexed as one punctuator with no space between them.
    fn next_touches(&self) -> bool {
        let a = self.toks[self.pos].span;
        let b = self.toks[self.pos + 1].span;
        a.file == b.file && a.hi == b.lo
    }
    /// True if the next two tokens are `>` `>` with no space, which means a right shift.
    fn at_shr(&self) -> bool {
        self.peek() == Tok::Gt && self.peek_at(1) == Tok::Gt && self.next_touches()
    }
    /// True at a `>>=`: lexed as `>` followed by `>=`, touching.
    fn at_shr_assign(&self) -> bool {
        self.peek() == Tok::Gt && self.peek_at(1) == Tok::Ge && self.next_touches()
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

    /// Parses attributes (outer, or inner at the start of a file or block).
    /// Returns the derive list, whether `#[test]` was present, and the recorded
    /// attributes. Lint attributes and known tool attributes (`rustfmt::`,
    /// `clippy::`) are accepted and ignored, as before. A known Rust attribute
    /// lust does not handle yet (cfg, repr, path, inline, and kin) rejects with
    /// L0522; a name lust does not know at all rejects with L0402.
    fn attributes(&mut self) -> PResult<ParsedAttrs> {
        self.attributes_at(true)
    }

    /// Attributes on a part of an item (a field, parameter, variant, arm, or
    /// statement). `derive` and `test` are not valid there (rustc rejects
    /// them), so they get the unsupported-attribute error, not a free pass.
    fn part_attributes(&mut self) -> PResult<ParsedAttrs> {
        self.attributes_at(false)
    }

    fn attributes_at(&mut self, item_level: bool) -> PResult<ParsedAttrs> {
        let mut out = ParsedAttrs::default();
        while self.peek() == Tok::Pound {
            let start = self.bump().span;
            let inner = self.eat(Tok::Bang);
            self.expect(Tok::LBracket, "`[`")?;
            // Find the matching `]` first, so nested brackets inside the
            // attribute cannot confuse the per-attribute handling below.
            let body_start = self.pos;
            let mut depth = 1usize;
            let mut body_end = None;
            for j in body_start..self.toks.len() {
                match self.toks[j].tok {
                    Tok::LBracket => depth += 1,
                    Tok::RBracket => {
                        depth -= 1;
                        if depth == 0 {
                            body_end = Some(j);
                            break;
                        }
                    }
                    Tok::Eof => break,
                    _ => {}
                }
            }
            let Some(body_end) = body_end else {
                return Err(syntax(start, "unterminated attribute"));
            };
            let body: Vec<Token> = self.toks[body_start..body_end].to_vec();
            self.pos = body_end + 1;
            // The attribute path: name segments joined by `::` at the start.
            let mut path: Vec<PathSeg> = Vec::new();
            let mut bi = 0usize;
            while let Some(t) = body.get(bi) {
                match t.tok {
                    Tok::Ident(s) => {
                        path.push(PathSeg::plain(s));
                        bi += 1;
                        if body.get(bi).map(|t| t.tok) == Some(Tok::PathSep) {
                            bi += 1;
                        } else {
                            break;
                        }
                    }
                    _ => break,
                }
            }
            let Some(first) = path.first().map(|s| s.name) else {
                return Err(syntax(start, "expected an attribute name"));
            };
            let name_span = body.first().map_or(start, |t| t.span);
            let name_text = self.interner.get(first).to_string();
            let input = if body.get(bi).map(|t| t.tok) == Some(Tok::LParen) {
                // The usual form: `#[name(..)]`. The list is what is inside.
                let mut d = 0usize;
                let mut end = body.len();
                for (j, t) in body.iter().enumerate().skip(bi) {
                    match t.tok {
                        Tok::LParen => d += 1,
                        Tok::RParen => {
                            d -= 1;
                            if d == 0 {
                                end = j;
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                AttrInput::List(Delim::Paren, token_trees(&body[bi + 1..end]))
            } else if bi < body.len() {
                AttrInput::List(Delim::Bracket, token_trees(&body[bi..]))
            } else {
                AttrInput::None
            };
            let attr = Attr {
                style: if inner { AttrStyle::Inner } else { AttrStyle::Outer },
                path: path.clone(),
                input,
                span: start.to(name_span),
            };
            let k = self.known;
            if path.len() > 1 {
                // Tool attributes under a known tool namespace are ignored.
                if name_text == "rustfmt" || name_text == "clippy" {
                    out.attrs.push(attr);
                    continue;
                }
                return Err(Diag::new(
                    "L0402",
                    name_span,
                    format!("unsupported attribute `{name_text}`"),
                    "Lust supports #[derive(...)], #[test], and lint attributes such as #[allow(...)].",
                ));
            }
            if !item_level && (first == k.derive || first == k.test) {
                return Err(Diag::new(
                    "L0402",
                    name_span,
                    format!("unsupported attribute `{name_text}`"),
                    "Lust supports #[derive(...)] on structs and enums, #[test] on functions, and lint attributes such as #[allow(...)].",
                ));
            }
            match first {
                _ if first == k.derive && !inner => {
                    // The derive names are the identifiers inside the `(..)`.
                    if body.get(bi).map(|t| t.tok) != Some(Tok::LParen) {
                        return Err(syntax(name_span, "expected `(` after `derive`"));
                    }
                    for t in &body[bi + 1..] {
                        match t.tok {
                            Tok::Ident(s) => out.derives.push((s, t.span)),
                            Tok::Comma | Tok::PathSep => {}
                            Tok::RParen => break,
                            _ => return Err(syntax(t.span, "expected a trait name in `derive`")),
                        }
                    }
                }
                _ if first == k.test && !inner => out.is_test = true,
                // Doc comments lex to this attribute; it carries no code.
                _ if name_text == "doc" => {}
                _ if name_text == "repr" => {}
                _ if first == k.allow || first == k.warn || first == k.deny => {}
                _ if RESOLVE_ATTRS.contains(&name_text.as_str()) => {}
                _ if KNOWN_ATTRS.contains(&name_text.as_str()) => {
                    return Err(Diag::new(
                        C_ATTR,
                        name_span,
                        format!("the `#[{name_text}]` attribute is not supported yet"),
                        "Remove the attribute, or rewrite this part with the supported subset (see README).",
                    ));
                }
                _ => {
                    return Err(Diag::new(
                        "L0402",
                        name_span,
                        format!("unsupported attribute `{name_text}`"),
                        "Lust supports #[derive(...)], #[test], and lint attributes such as #[allow(...)].",
                    ));
                }
            }
            out.attrs.push(attr);
        }
        Ok(out)
    }

    fn item(&mut self) -> PResult<Option<Item>> {
        let start = self.span();
        let parsed = self.attributes()?;
        let derives = parsed.derives.clone();
        let vis = self.vis()?;
        // A `const` item (`const NAME: Ty = ...;`), told apart from a
        // `const fn` qualifier by the name and colon after it.
        if self.peek() == Tok::Const && matches!(self.peek_at(1), Tok::Ident(_) | Tok::Underscore) && self.peek_at(2) == Tok::Colon {
            let kind = ItemKind::Const(self.const_def()?);
            return Ok(Some(Item { vis, attrs: parsed.attrs, kind, span: start.to(self.prev_span()) }));
        }
        // Function and impl qualifiers, in any written order: `const`,
        // `async`, `unsafe`, and `extern "abi"`. A lone `const` with no `fn`
        // after it is a const item, handled in the match below.
        let mut qual = FnQual::default();
        loop {
            match self.peek() {
                Tok::Const if !qual.is_const => {
                    self.bump();
                    qual.is_const = true;
                }
                Tok::Async if !qual.is_async => {
                    self.bump();
                    qual.is_async = true;
                }
                Tok::Unsafe if !qual.is_unsafe => {
                    self.bump();
                    qual.is_unsafe = true;
                }
                Tok::Extern if qual.abi.is_none() => {
                    self.bump();
                    if let Tok::Str(i) = self.peek() {
                        self.bump();
                        qual.abi = Some(i + self.str_base);
                    } else {
                        // `extern { .. }`, `extern crate`, or `extern fn`: put the
                        // marker in with no ABI string, told apart by what follows.
                        qual.abi = Some(u32::MAX);
                        break;
                    }
                }
                _ => break,
            }
        }
        let has_qual = qual.is_const || qual.is_async || qual.is_unsafe || qual.abi.is_some();
        let kind = match self.peek() {
            Tok::Fn if has_qual && !(qual.is_const && !qual.is_async && !qual.is_unsafe && qual.abi.is_none()) => {
                return Err(if qual.is_async {
                    async_error(start)
                } else if qual.is_unsafe {
                    unsafe_error(start)
                } else {
                    not_yet(C_EXTERN, start, "extern functions")
                });
            }
            Tok::Fn => {
                let mut def = self.fn_def()?;
                def.is_test = parsed.is_test;
                def.vis = vis.clone();
                def.attrs = parsed.attrs.clone();
                def.qual = qual;
                ItemKind::Fn(def)
            }
            Tok::Struct if !has_qual => ItemKind::Struct(self.struct_def(derives)?),
            Tok::Enum if !has_qual => ItemKind::Enum(self.enum_def(derives)?),
            Tok::Impl if qual.is_unsafe && !qual.is_const && !qual.is_async && qual.abi.is_none() => ItemKind::Impl(self.impl_def(true)?),
            Tok::Impl if !has_qual => ItemKind::Impl(self.impl_def(false)?),
            Tok::Use if !has_qual => ItemKind::Use(self.use_def()?),
            Tok::Eof if derives.is_empty() && !has_qual => return Ok(None),
            Tok::Trait if !qual.is_const && !qual.is_async && qual.abi.is_none() => {
                let mut def = self.trait_def()?;
                def.is_unsafe = qual.is_unsafe;
                ItemKind::Trait(def)
            }
            Tok::Mod if !has_qual => ItemKind::Mod(self.mod_def()?),
            Tok::Static if !has_qual => ItemKind::Static(self.static_def()?),
            Tok::Type if !has_qual => ItemKind::Type(self.type_alias_def()?),
            // `extern { .. }` and `extern crate ..;`: the qualifier loop ate `extern`.
            Tok::LBrace if qual.abi.is_some() => return Err(not_yet(C_EXTERN, start, "extern blocks")),
            Tok::Crate if qual.abi.is_some() => ItemKind::ExternCrate(self.extern_crate_def()?),
            _ if qual.is_const => return Err(not_yet(C_CONST, start, "const and static items")),
            _ if qual.is_async => return Err(async_error(start)),
            _ if qual.is_unsafe => return Err(unsafe_error(start)),
            Tok::Ident(_) if self.at_ident("union") && matches!(self.peek_at(1), Tok::Ident(_)) => {
                return Err(not_yet(C_TY, start, "unions"));
            }
            Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super if self.at_path_macro_call() => {
                return Err(macro_error(start));
            }
            Tok::Reserved(_) => return Err(self.reserved_error(start)),
            t => return Err(syntax(start, format!("expected an item, found {}", tok_name(t)))),
        };
        Ok(Some(Item { vis, attrs: parsed.attrs, kind, span: start.to(self.prev_span()) }))
    }

    /// Parses a `use` declaration into a tree. If the tree parse fails, falls
    /// back to the old behavior (skip to the `;`, record an empty group) so
    /// every program that parsed before still parses.
    fn use_def(&mut self) -> PResult<UseDef> {
        let start = self.expect(Tok::Use, "`use`")?;
        let saved = self.pos;
        let tree = match self.use_tree() {
            Ok(tree) if self.eat(Tok::Semi) => tree,
            _ => {
                self.pos = saved;
                while self.peek() != Tok::Semi && self.peek() != Tok::Eof {
                    self.bump();
                }
                self.expect(Tok::Semi, "`;`")?;
                UseTree { leading_colon: false, prefix: Vec::new(), kind: UseKind::Group(Vec::new()), span: start }
            }
        };
        Ok(UseDef { tree, span: start.to(self.prev_span()) })
    }

    /// One use tree: a prefix path, then a name, a `*`, or a `{..}` group.
    fn use_tree(&mut self) -> PResult<UseTree> {
        let start = self.span();
        let leading_colon = self.eat(Tok::PathSep);
        if self.eat(Tok::LBrace) {
            return Ok(UseTree {
                leading_colon,
                prefix: Vec::new(),
                kind: UseKind::Group(self.use_group()?),
                span: start.to(self.prev_span()),
            });
        }
        if self.eat(Tok::Star) {
            return Ok(UseTree { leading_colon, prefix: Vec::new(), kind: UseKind::Glob, span: start.to(self.prev_span()) });
        }
        let mut prefix = Vec::new();
        loop {
            let name = match self.peek() {
                Tok::Ident(_) | Tok::SelfUpper => self.ident()?.0,
                Tok::SelfLower => {
                    self.bump();
                    self.known.self_value
                }
                Tok::Crate => {
                    self.bump();
                    self.interner.intern("crate")
                }
                Tok::Super => {
                    self.bump();
                    self.interner.intern("super")
                }
                t => return Err(syntax(self.span(), format!("expected a name in `use`, found {}", tok_name(t)))),
            };
            prefix.push(PathSeg::plain(name));
            if !self.eat(Tok::PathSep) {
                break;
            }
            if self.eat(Tok::Star) {
                return Ok(UseTree { leading_colon, prefix, kind: UseKind::Glob, span: start.to(self.prev_span()) });
            }
            if self.eat(Tok::LBrace) {
                return Ok(UseTree { leading_colon, prefix, kind: UseKind::Group(self.use_group()?), span: start.to(self.prev_span()) });
            }
        }
        let rename = if self.eat(Tok::As) {
            Some(match self.peek() {
                Tok::Underscore => {
                    self.bump();
                    self.interner.intern("_")
                }
                _ => self.ident()?.0,
            })
        } else {
            None
        };
        Ok(UseTree { leading_colon, prefix, kind: UseKind::Simple { rename }, span: start.to(self.prev_span()) })
    }

    /// A `mod` item: `mod name;` (a file module; the resolver finds the
    /// file) or `mod name { ... }` (inline items parsed in place).
    fn mod_def(&mut self) -> PResult<ModDef> {
        let start = self.expect(Tok::Mod, "`mod`")?;
        let (name, name_span) = self.ident()?;
        if self.eat(Tok::Semi) {
            return Ok(ModDef { name, name_span, body: None, span: start.to(self.prev_span()) });
        }
        self.expect(Tok::LBrace, "`{` or `;`")?;
        let mut items = Vec::new();
        while self.peek() != Tok::RBrace {
            if self.peek() == Tok::Eof {
                return Err(syntax(self.span(), "expected `}`, found end of file"));
            }
            let before = self.pos;
            if let Some(item) = self.nest(|p| p.item())? {
                items.push(item);
            }
            if self.pos == before {
                return Err(syntax(self.span(), format!("expected an item, found {}", tok_name(self.peek()))));
            }
        }
        self.bump();
        Ok(ModDef { name, name_span, body: Some(items), span: start.to(self.prev_span()) })
    }

    /// A `const` item: `const NAME: Ty = value;` (`_` for an unnamed const).
    fn const_def(&mut self) -> PResult<ConstDef> {
        let start = self.expect(Tok::Const, "`const`")?;
        let (name, name_span) = if self.peek() == Tok::Underscore {
            (None, self.bump().span)
        } else {
            let (n, s) = self.ident()?;
            (Some(n), s)
        };
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.ty()?;
        let value = if self.eat(Tok::Eq) { Some(self.expr()?) } else { None };
        self.expect(Tok::Semi, "`;`")?;
        Ok(ConstDef { name, name_span, ty, value, span: start.to(self.prev_span()) })
    }

    /// A `static` item: `static [mut] NAME: Ty = value;`.
    fn static_def(&mut self) -> PResult<StaticDef> {
        let start = self.expect(Tok::Static, "`static`")?;
        let mutable = self.eat(Tok::Mut);
        let (name, name_span) = self.ident()?;
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.ty()?;
        let value = if self.eat(Tok::Eq) { Some(self.expr()?) } else { None };
        self.expect(Tok::Semi, "`;`")?;
        Ok(StaticDef { name, name_span, mutable, ty, value, span: start.to(self.prev_span()) })
    }

    /// A `type` alias: `type Name = Target;`. Generic aliases reject with
    /// the generics code, like generic structs today.
    fn type_alias_def(&mut self) -> PResult<TypeAliasDef> {
        let start = self.expect(Tok::Type, "`type`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(false)?;
        // For an alias the where clause follows the target type.
        self.expect(Tok::Eq, "`=`")?;
        let ty = self.ty()?;
        let where_clause = self.where_clause()?;
        self.expect(Tok::Semi, "`;`")?;
        Ok(TypeAliasDef { name, name_span, generics, where_clause, ty, span: start.to(self.prev_span()) })
    }

    /// An `extern crate` item, after the qualifier loop ate `extern`:
    /// `crate name;` or `crate name as rename;` (`crate self as name;`
    /// for the crate itself).
    fn extern_crate_def(&mut self) -> PResult<ExternCrateDef> {
        let start = self.expect(Tok::Crate, "`crate`")?;
        let (name, name_span) = if self.peek() == Tok::SelfLower {
            let s = self.bump().span;
            (self.known.self_value, s)
        } else {
            self.ident()?
        };
        let rename = if self.eat(Tok::As) {
            Some(if self.peek() == Tok::Underscore {
                self.bump();
                self.interner.intern("_")
            } else {
                self.ident()?.0
            })
        } else {
            None
        };
        self.expect(Tok::Semi, "`;`")?;
        Ok(ExternCrateDef { name, name_span, rename, span: start.to(self.prev_span()) })
    }

    /// The children of a use group, after its `{`.
    fn use_group(&mut self) -> PResult<Vec<UseTree>> {
        let mut out = Vec::new();
        while self.peek() != Tok::RBrace {
            out.push(self.nest(|p| p.use_tree())?);
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(out)
    }

    /// One written lifetime ('a, 'static, '_) at the current token.
    fn lifetime_here(&mut self) -> PResult<Lifetime> {
        match self.peek() {
            Tok::Lifetime(name) => Ok(Lifetime { name, span: self.bump().span }),
            t => Err(syntax(self.span(), format!("expected a lifetime, found {}", tok_name(t)))),
        }
    }

    /// Generic parameters as written: `<..>`, or empty when absent.
    /// Additive parser work for W-CORELANG (the AST owner) on behalf
    /// of W-TRAITS-CORE: the shapes are the frozen AST v2 ones.
    /// Lifetime
    /// parameters keep the old L0203 reject where `allow_lifetimes`
    /// is false (fns, structs, enums); impls and traits record them.
    fn generics(&mut self, allow_lifetimes: bool) -> PResult<Generics> {
        let start = self.span();
        if !self.eat(Tok::Lt) {
            return Ok(Generics { params: Vec::new(), span: start });
        }
        let mut params = Vec::new();
        loop {
            if self.eat(Tok::Gt) {
                break;
            }
            let pattrs = self.part_attributes()?;
            match self.peek() {
                Tok::Lifetime(_) => {
                    if !allow_lifetimes {
                        return Err(lifetime_error(self.span()));
                    }
                    let lt = self.lifetime_here()?;
                    let mut bounds = Vec::new();
                    if self.eat(Tok::Colon) {
                        loop {
                            bounds.push(self.lifetime_here()?);
                            if !self.eat(Tok::Plus) {
                                break;
                            }
                            if !matches!(self.peek(), Tok::Lifetime(_)) {
                                break;
                            }
                        }
                    }
                    params.push(GenericParam::Lifetime { lt, bounds, attrs: pattrs.attrs });
                }
                Tok::Const => {
                    self.bump();
                    let (name, span) = self.ident()?;
                    self.expect(Tok::Colon, "`:`")?;
                    let ty = self.ty()?;
                    let default = if self.eat(Tok::Eq) { Some(self.const_arg_expr()?) } else { None };
                    params.push(GenericParam::Const { name, span, ty, default, attrs: pattrs.attrs });
                }
                Tok::Ident(_) => {
                    let (name, span) = self.ident()?;
                    let bounds = if self.eat(Tok::Colon) { self.bounds()? } else { Vec::new() };
                    let default = if self.eat(Tok::Eq) { Some(self.ty()?) } else { None };
                    params.push(GenericParam::Type { name, span, bounds, default, attrs: pattrs.attrs });
                }
                t => return Err(syntax(self.span(), format!("expected a generic parameter, found {}", tok_name(t)))),
            }
            if !self.eat(Tok::Comma) {
                self.expect(Tok::Gt, "`>`")?;
                break;
            }
        }
        Ok(Generics { params, span: start.to(self.prev_span()) })
    }

    /// A `for<'a, ..>` binder in a bound, or empty when absent.
    fn opt_binder(&mut self) -> PResult<Vec<Lifetime>> {
        if self.peek() != Tok::For {
            return Ok(Vec::new());
        }
        self.bump();
        self.expect(Tok::Lt, "`<`")?;
        let mut out = Vec::new();
        loop {
            if self.eat(Tok::Gt) {
                break;
            }
            out.push(self.lifetime_here()?);
            if !self.eat(Tok::Comma) {
                self.expect(Tok::Gt, "`>`")?;
                break;
            }
        }
        Ok(out)
    }

    /// A trait path as written in a bound or impl header, with
    /// parenthesized sugar (`Fn(A) -> B`) attached to its last
    /// segment when present.
    fn trait_path(&mut self) -> PResult<Vec<PathSeg>> {
        let mut path = self.path(true)?;
        if self.peek() == Tok::LParen {
            self.bump();
            let mut inputs = Vec::new();
            while self.peek() != Tok::RParen {
                inputs.push(self.ty()?);
                if !self.eat(Tok::Comma) {
                    break;
                }
            }
            self.expect(Tok::RParen, "`)`")?;
            let output = if self.eat(Tok::Arrow) { Some(self.ty()?) } else { None };
            if let Some(last) = path.last_mut() {
                last.args = GenericArgs::Parenthesized { inputs, output };
            }
        }
        Ok(path)
    }

    /// One bound: a trait bound (optionally `for<..>`-bound and
    /// `?`-relaxed) or a lifetime bound.
    fn trait_bound(&mut self) -> PResult<TraitBound> {
        let binder = self.opt_binder()?;
        let maybe = self.eat(Tok::Question);
        if matches!(self.peek(), Tok::Lifetime(_)) && binder.is_empty() && !maybe {
            return Ok(TraitBound::Lifetime(self.lifetime_here()?));
        }
        // The legacy `~const` and `async` bound modifiers are not
        // in the subset; plain paths and `?Trait` are.
        let path = self.trait_path()?;
        Ok(TraitBound::Trait { binder, trait_ref: TraitRefExpr { path }, maybe })
    }

    /// A `+`-separated bound list, at least one bound. A trailing
    /// `+` before the list's terminator ends the list.
    fn bounds(&mut self) -> PResult<Vec<TraitBound>> {
        let mut out = Vec::new();
        loop {
            out.push(self.trait_bound()?);
            if !self.eat(Tok::Plus) {
                break;
            }
            if matches!(self.peek(), Tok::Comma | Tok::Gt | Tok::LBrace | Tok::Semi | Tok::RParen | Tok::Eq) {
                break;
            }
        }
        Ok(out)
    }

    /// A `where` clause as written, or empty when absent.
    fn where_clause(&mut self) -> PResult<WhereClause> {
        let start = self.span();
        if !self.eat(Tok::Where) {
            return Ok(WhereClause { preds: Vec::new(), span: start });
        }
        let mut preds = Vec::new();
        loop {
            if matches!(self.peek(), Tok::LBrace | Tok::Semi) {
                break;
            }
            if matches!(self.peek(), Tok::Lifetime(_)) {
                let lt = self.lifetime_here()?;
                self.expect(Tok::Colon, "`:`")?;
                let mut bounds = Vec::new();
                loop {
                    bounds.push(self.lifetime_here()?);
                    if !self.eat(Tok::Plus) {
                        break;
                    }
                    if !matches!(self.peek(), Tok::Lifetime(_)) {
                        break;
                    }
                }
                preds.push(WherePred::Lifetime { lt, bounds });
            } else {
                let binder = self.opt_binder()?;
                let ty = self.ty()?;
                self.expect(Tok::Colon, "`:`")?;
                let bounds = self.bounds()?;
                preds.push(WherePred::Type { binder, ty, bounds });
            }
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        Ok(WhereClause { preds, span: start.to(self.prev_span()) })
    }

    fn fn_def(&mut self) -> PResult<FnDef> {
        self.fn_def_inner(false)
    }

    /// A fn definition. With `sig_only`, a trailing `;` instead of a
    /// body is a bodyless declaration (a trait method signature).
    fn fn_def_inner(&mut self, sig_only: bool) -> PResult<FnDef> {
        self.expect(Tok::Fn, "`fn`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(false)?;
        self.expect(Tok::LParen, "`(`")?;
        let mut self_param = None;
        let mut params = Vec::new();
        // `self`, `mut self`, `&self`, `&mut self`, the same with a
        // written lifetime, and typed receivers (`self: Rc<Self>`).
        let s = self.span();
        let typed_self = (self.peek() == Tok::SelfLower && self.peek_at(1) == Tok::Colon)
            || (self.peek() == Tok::Mut && self.peek_at(1) == Tok::SelfLower && self.peek_at(2) == Tok::Colon);
        if typed_self {
            let mutable = self.eat(Tok::Mut);
            self.bump(); // `self`
            self.bump(); // `:`
            let ty = self.ty()?;
            self_param = Some(SelfParam {
                kind: SelfKind::Typed,
                mutable,
                lifetime: None,
                ty: Some(ty),
                attrs: Vec::new(),
                span: s.to(self.prev_span()),
            });
            if !self.eat(Tok::Comma) && self.peek() != Tok::RParen {
                return Err(syntax(self.span(), "expected `,` or `)`"));
            }
        }
        let self_form = if typed_self {
            None
        } else {
            match (self.peek(), self.peek_at(1), self.peek_at(2), self.peek_at(3)) {
                (Tok::SelfLower, _, _, _) => Some((SelfKind::Value, false, 1, None)),
                (Tok::Mut, Tok::SelfLower, _, _) => Some((SelfKind::Value, true, 2, None)),
                (Tok::Amp, Tok::SelfLower, _, _) => Some((SelfKind::Ref, false, 2, None)),
                (Tok::Amp, Tok::Mut, Tok::SelfLower, _) => Some((SelfKind::RefMut, false, 3, None)),
                (Tok::Amp, Tok::Lifetime(lt), Tok::SelfLower, _) => {
                    Some((SelfKind::Ref, false, 3, Some(Lifetime { name: lt, span: self.toks[self.pos + 1].span })))
                }
                (Tok::Amp, Tok::Lifetime(lt), Tok::Mut, Tok::SelfLower) => {
                    Some((SelfKind::RefMut, false, 4, Some(Lifetime { name: lt, span: self.toks[self.pos + 1].span })))
                }
                _ => None,
            }
        };
        if let Some((kind, mutable, n, lifetime)) = self_form {
            if let Some(_lt) = lifetime {}
            for _ in 0..n {
                self.bump();
            }
            self_param = Some(SelfParam { kind, mutable, lifetime, ty: None, attrs: Vec::new(), span: s.to(self.prev_span()) });
            if !self.eat(Tok::Comma) && self.peek() != Tok::RParen {
                return Err(syntax(self.span(), "expected `,` or `)`"));
            }
        }
        while self.peek() != Tok::RParen {
            let pattrs = self.part_attributes()?;
            let start = self.span();
            if self.peek() == Tok::DotDot {
                return Err(self.reject(C_CORE, "variadic parameters"));
            }
            let mutable = self.eat(Tok::Mut);
            let (pname, pspan) = match self.peek() {
                Tok::Ident(_) => self.ident()?,
                Tok::Reserved(_) => return Err(self.reserved_error(self.span())),
                _ => return Err(not_yet(C_CORE, start, "patterns in parameters")),
            };
            self.expect(Tok::Colon, "`:`")?;
            let ty = self.ty()?;
            // The span starts at the name, not at `mut`: hygiene reads the
            // name token's context as the binding's context (ARCH 6.3).
            params.push(Param { name: pname, mutable, pat: None, ty, attrs: pattrs.attrs, span: pspan.to(self.prev_span()) });
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RParen, "`)`")?;
        let ret = if self.eat(Tok::Arrow) { Some(self.ty()?) } else { None };
        let where_clause = self.where_clause()?;
        let (e0, p0) = (self.ast.exprs.len() as u32, self.ast.pats.len() as u32);
        let body = if sig_only && self.eat(Tok::Semi) { None } else { Some(self.block()?) };
        let exprs = (e0, self.ast.exprs.len() as u32);
        let pats = (p0, self.ast.pats.len() as u32);
        Ok(FnDef {
            name,
            name_span,
            is_test: false,
            vis: Vis::Private,
            attrs: Vec::new(),
            qual: FnQual::default(),
            generics,
            self_param,
            params,
            variadic: false,
            ret,
            where_clause,
            body,
            exprs,
            pats,
        })
    }

    fn fields(&mut self) -> PResult<Vec<FieldDef>> {
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        while self.peek() != Tok::RBrace {
            let fattrs = self.part_attributes()?;
            let vis = self.vis()?;
            let (name, span) = self.ident()?;
            self.expect(Tok::Colon, "`:`")?;
            let ty = self.ty()?;
            fields.push(FieldDef { name, vis, attrs: fattrs.attrs, ty, span });
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(fields)
    }

    /// Tuple variant fields after the `(`: types with optional attributes.
    /// `FieldDef::name` is unused for these (see `StructDef::fields`).
    fn tuple_fields(&mut self) -> PResult<Vec<FieldDef>> {
        let mut fields = Vec::new();
        while self.peek() != Tok::RParen {
            let fattrs = self.part_attributes()?;
            let _vis = self.vis()?;
            let span = self.span();
            let ty = self.ty()?;
            fields.push(FieldDef { name: Sym(0), vis: _vis, attrs: fattrs.attrs, ty, span });
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RParen, "`)`")?;
        Ok(fields)
    }

    fn struct_def(&mut self, derives: Vec<(Sym, Span)>) -> PResult<StructDef> {
        self.expect(Tok::Struct, "`struct`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(false)?;
        // The where clause sits before the fields (named struct)
        // or before the `;` (unit struct). Tuple structs put it
        // after the fields; they still reject below.
        let where_clause = self.where_clause()?;
        let fields = match self.peek() {
            Tok::Semi => {
                self.bump();
                VariantFields::Unit
            }
            Tok::LParen => {
                self.bump();
                let fs = self.tuple_fields()?;
                self.expect(Tok::Semi, "`;`")?;
                VariantFields::Tuple(fs)
            }
            _ => VariantFields::Struct(self.fields()?),
        };
        Ok(StructDef { name, name_span, generics, fields, where_clause, derives })
    }

    fn enum_def(&mut self, derives: Vec<(Sym, Span)>) -> PResult<EnumDef> {
        self.expect(Tok::Enum, "`enum`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(false)?;
        let where_clause = self.where_clause()?;
        self.expect(Tok::LBrace, "`{`")?;
        let mut variants = Vec::new();
        while self.peek() != Tok::RBrace {
            let vattrs = self.part_attributes()?;
            let (vname, span) = self.ident()?;
            let fields = match self.peek() {
                Tok::LParen => {
                    self.bump();
                    VariantFields::Tuple(self.tuple_fields()?)
                }
                Tok::LBrace => VariantFields::Struct(self.fields()?),
                _ => VariantFields::Unit,
            };
            let discriminant = if self.eat(Tok::Eq) { Some(self.expr()?) } else { None };
            variants.push(VariantDef { name: vname, attrs: vattrs.attrs, fields, discriminant, span });
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(EnumDef { name, name_span, generics, variants, where_clause, derives })
    }

    /// One associated type in a trait or an impl:
    /// `type Name<..>: Bounds = Default;` (parts optional by context;
    /// collect checks which parts each context requires).
    fn assoc_type(&mut self) -> PResult<AssocTypeDef> {
        let start = self.expect(Tok::Type, "`type`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(true)?;
        let bounds = if self.eat(Tok::Colon) { self.bounds()? } else { Vec::new() };
        let where_clause = self.where_clause()?;
        let default = if self.eat(Tok::Eq) { Some(self.ty()?) } else { None };
        self.expect(Tok::Semi, "`;`")?;
        Ok(AssocTypeDef {
            name,
            name_span,
            vis: Vis::Private,
            attrs: Vec::new(),
            generics,
            bounds,
            where_clause,
            default,
            span: start.to(self.prev_span()),
        })
    }

    /// One associated const in a trait or an impl:
    /// `const NAME: Ty = value;` (the value is optional in a trait).
    fn assoc_const(&mut self) -> PResult<AssocConstDef> {
        let start = self.expect(Tok::Const, "`const`")?;
        let (name, name_span) = self.ident()?;
        self.expect(Tok::Colon, "`:`")?;
        let ty = self.ty()?;
        let default = if self.eat(Tok::Eq) { Some(self.expr()?) } else { None };
        self.expect(Tok::Semi, "`;`")?;
        Ok(AssocConstDef { name, name_span, vis: Vis::Private, attrs: Vec::new(), ty, default, span: start.to(self.prev_span()) })
    }

    /// A trait definition: supertrait bounds, a where clause, and
    /// method signatures (with optional default bodies), associated
    /// types, and associated consts.
    fn trait_def(&mut self) -> PResult<TraitDef> {
        let start = self.expect(Tok::Trait, "`trait`")?;
        let (name, name_span) = self.ident()?;
        let generics = self.generics(true)?;
        let bounds = if self.eat(Tok::Colon) { self.bounds()? } else { Vec::new() };
        let where_clause = self.where_clause()?;
        self.expect(Tok::LBrace, "`{`")?;
        let mut fns = Vec::new();
        let mut consts = Vec::new();
        let mut types = Vec::new();
        while self.peek() != Tok::RBrace {
            let parsed = self.attributes()?;
            let vis = self.vis()?;
            match self.peek() {
                Tok::Fn => {
                    let mut def = self.fn_def_inner(true)?;
                    def.vis = vis;
                    def.attrs = parsed.attrs;
                    fns.push(def);
                }
                Tok::Type => types.push(self.assoc_type()?),
                Tok::Const if matches!(self.peek_at(1), Tok::Ident(_) | Tok::Underscore) => consts.push(self.assoc_const()?),
                // Const fns in traits are unstable in Rust
                // (E0379) and unsupported here.
                Tok::Const if self.peek_at(1) == Tok::Fn => return Err(self.reject(C_CONST, "const functions in traits")),
                Tok::Const => return Err(self.reject(C_CONST, "const functions")),
                Tok::Unsafe => return Err(unsafe_error(self.span())),
                Tok::Async => return Err(async_error(self.span())),
                Tok::Ident(_) | Tok::SelfUpper if self.at_path_macro_call() => return Err(macro_error(self.span())),
                t => return Err(syntax(self.span(), format!("expected a trait item, found {}", tok_name(t)))),
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(TraitDef {
            name,
            name_span,
            is_unsafe: false,
            is_auto: false,
            generics,
            bounds,
            where_clause,
            fns,
            consts,
            types,
            span: start.to(self.prev_span()),
        })
    }

    /// An inherent or trait impl. The header before the `{` is
    /// either a Self type or `TraitRef for SelfType`: a path is
    /// parsed once, and a following `for` makes it the trait ref.
    fn impl_def(&mut self, is_unsafe: bool) -> PResult<ImplDef> {
        let start = self.expect(Tok::Impl, "`impl`")?;
        let generics = self.generics(true)?;
        let is_negative = self.eat(Tok::Bang);
        let (trait_ref, self_ty) = if matches!(self.peek(), Tok::Ident(_) | Tok::SelfUpper) {
            let header_start = self.span();
            let path = self.trait_path()?;
            if self.eat(Tok::For) {
                let self_ty = self.ty()?;
                (Some(TraitRefExpr { path }), self_ty)
            } else if is_negative {
                return Err(syntax(header_start, "expected `for` after the trait in a negative impl"));
            } else {
                let span = header_start.to(self.prev_span());
                (None, self.push_ty(TyExpr::Path(path), span))
            }
        } else {
            let self_ty = self.ty()?;
            if self.peek() == Tok::For {
                return Err(syntax(self.span(), "expected a trait path before `for` in an impl"));
            }
            (None, self_ty)
        };
        if trait_ref.is_some() || is_negative {}
        let where_clause = self.where_clause()?;
        self.expect(Tok::LBrace, "`{`")?;
        let mut fns = Vec::new();
        let mut consts = Vec::new();
        let mut types = Vec::new();
        while self.peek() != Tok::RBrace {
            let parsed = self.attributes()?;
            let vis = self.vis()?;
            let is_test = parsed.is_test;
            match self.peek() {
                Tok::Fn => {
                    let mut def = self.fn_def()?;
                    def.is_test = is_test;
                    def.vis = vis;
                    def.attrs = parsed.attrs;
                    fns.push(def);
                }
                Tok::Type if trait_ref.is_some() => types.push(self.assoc_type()?),
                Tok::Type => return Err(self.reject(C_ASSOC, "associated types in inherent impls")),
                Tok::Const if matches!(self.peek_at(1), Tok::Ident(_) | Tok::Underscore) => consts.push(self.assoc_const()?),
                Tok::Const if self.peek_at(1) == Tok::Fn => {
                    self.bump();
                    let mut def = self.fn_def()?;
                    def.is_test = is_test;
                    def.vis = vis;
                    def.attrs = parsed.attrs;
                    def.qual.is_const = true;
                    fns.push(def);
                }
                Tok::Const => return Err(self.reject(C_CONST, "const functions")),
                Tok::Unsafe => return Err(unsafe_error(self.span())),
                Tok::Async => return Err(async_error(self.span())),
                Tok::Ident(_) | Tok::SelfUpper if self.at_path_macro_call() => return Err(macro_error(self.span())),
                t => return Err(syntax(self.span(), format!("expected an impl item, found {}", tok_name(t)))),
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(ImplDef { generics, is_unsafe, is_negative, trait_ref, self_ty, where_clause, fns, consts, types, span: start })
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
                // Written lifetimes are recorded; regions are erased
                // in this milestone, and collect decides which
                // written forms the subset accepts.
                let lifetime = if matches!(self.peek(), Tok::Lifetime(_)) {
                    let lt = self.lifetime_here()?;
                    Some(lt)
                } else {
                    None
                };
                let mutable = self.eat(Tok::Mut);
                let inner = self.ty()?;
                let span = start.to(self.prev_span());
                let mut t = self.push_ty(TyExpr::Ref { lifetime, mutable, inner }, span);
                if double {
                    t = self.push_ty(TyExpr::Ref { lifetime: None, mutable: false, inner: t }, span);
                }
                Ok(t)
            }
            Tok::LParen => {
                self.bump();
                if self.eat(Tok::RParen) {
                    return Ok(self.push_ty(TyExpr::Unit, start.to(self.prev_span())));
                }
                let mut elems = vec![self.ty()?];
                let mut tuple = false;
                while self.eat(Tok::Comma) {
                    tuple = true;
                    if self.peek() == Tok::RParen {
                        break;
                    }
                    elems.push(self.ty()?);
                }
                self.expect(Tok::RParen, "`)`")?;
                if tuple { Ok(self.push_ty(TyExpr::Tuple(elems), start.to(self.prev_span()))) } else { Ok(elems[0]) }
            }
            Tok::LBracket => {
                self.bump();
                let inner = self.ty()?;
                if self.eat(Tok::Semi) {
                    let len = self.expr()?;
                    self.expect(Tok::RBracket, "`]`")?;
                    Ok(self.push_ty(TyExpr::Array { inner, len }, start.to(self.prev_span())))
                } else {
                    self.expect(Tok::RBracket, "`]`")?;
                    Ok(self.push_ty(TyExpr::Slice(inner), start.to(self.prev_span())))
                }
            }
            Tok::Impl => {
                self.bump();
                let bounds = self.bounds()?;
                Ok(self.push_ty(TyExpr::ImplTrait { bounds }, start.to(self.prev_span())))
            }
            Tok::Dyn => {
                self.bump();
                let binder = self.opt_binder()?;
                let mut bounds = self.bounds()?;
                // A trailing lifetime bound is the dyn lifetime.
                let lifetime = match bounds.last() {
                    Some(TraitBound::Lifetime(lt)) if bounds.len() > 1 => {
                        let lt = *lt;
                        bounds.pop();
                        Some(lt)
                    }
                    _ => None,
                };
                Ok(self.push_ty(TyExpr::Dyn { binder, bounds, lifetime }, start.to(self.prev_span())))
            }
            Tok::Fn => Err(not_yet(C_TY, start, "function pointer types")),
            Tok::Star => {
                self.bump();
                let mutable = if self.eat(Tok::Mut) {
                    true
                } else if self.eat(Tok::Const) {
                    false
                } else {
                    return Err(syntax(self.span(), "expected `const` or `mut` after `*` in a raw pointer type"));
                };
                let inner = self.ty()?;
                Ok(self.push_ty(TyExpr::Ptr { mutable, inner }, start.to(self.prev_span())))
            }
            Tok::Bang => {
                // The never type: its AST shape is `TyExpr::Never` (S3b) and
                // check already unifies it. Its parser lands with S5 because
                // the first source std fn (`std::process::exit`) returns it.
                self.bump();
                Ok(self.push_ty(TyExpr::Never, start.to(self.prev_span())))
            }
            Tok::Underscore => {
                self.bump();
                Ok(self.push_ty(TyExpr::Infer, start.to(self.prev_span())))
            }
            Tok::Unsafe => Err(unsafe_error(start)),
            Tok::Extern => Err(not_yet(C_TY, start, "extern function types")),
            Tok::Lt => {
                let (self_ty, trait_path, segs) = self.qpath_parts()?;
                Ok(self.push_ty(TyExpr::QPath { self_ty, trait_path, segs }, start.to(self.prev_span())))
            }
            Tok::For => {
                if self.peek_at(1) == Tok::Lt && matches!(self.peek_at(2), Tok::Lifetime(_)) {
                    Err(lifetime_error(self.toks[self.pos + 2].span))
                } else {
                    Err(not_yet(C_TRAIT, start, "higher-ranked (`for<..>`) types and bounds"))
                }
            }
            Tok::Ident(_) | Tok::SelfUpper if self.at_path_macro_call() => Err(macro_error(start)),
            _ => {
                let path = self.path(true)?;
                Ok(self.push_ty(TyExpr::Path(path), start.to(self.prev_span())))
            }
        }
    }

    /// The parts of a qualified path, current token at `<`:
    /// `<SelfTy as Trait>::Segs`, or `<SelfTy>::Segs` with an empty
    /// trait path. Shared by type and expression position.
    fn qpath_parts(&mut self) -> PResult<(TyId, Vec<PathSeg>, Vec<PathSeg>)> {
        self.expect(Tok::Lt, "`<`")?;
        let self_ty = self.ty()?;
        let trait_path = if self.eat(Tok::As) { self.trait_path()? } else { Vec::new() };
        self.expect(Tok::Gt, "`>`")?;
        self.expect(Tok::PathSep, "`::`")?;
        let segs = self.path(true)?;
        Ok((self_ty, trait_path, segs))
    }

    /// A const generic argument expression: a literal, a path to a
    /// const item or parameter, a negated literal, or a braced
    /// block. Anything that would need an operator must be braced,
    /// as in Rust, so `>` is never eaten as a comparison here.
    fn const_arg_expr(&mut self) -> PResult<ExprId> {
        match self.peek() {
            Tok::Minus => self.prefix(false),
            Tok::LBrace => self.block_like_expr(),
            Tok::Int(..) | Tok::Str(_) | Tok::Char(_) | Tok::True | Tok::False | Tok::Ident(_) | Tok::SelfUpper => self.primary(false),
            _ => Err(self.reject(C_CONST, "const generic arguments in this form")),
        }
    }

    /// Angle generic arguments, starting at the `<` and eating through
    /// the matching `>`: types, lifetimes (still rejected, L0203),
    /// consts, and associated bindings (`Item = u8`, `Item: Clone`).
    fn generic_args(&mut self) -> PResult<Vec<GenericArg>> {
        self.expect(Tok::Lt, "`<`")?;
        let mut args = Vec::new();
        while self.peek() != Tok::Gt {
            match self.peek() {
                Tok::Lifetime(_) => args.push(GenericArg::Lifetime(self.lifetime_here()?)),
                Tok::Ident(name) if self.peek_at(1) == Tok::Eq => {
                    let span = self.span();
                    self.bump();
                    self.bump();
                    let kind = match self.peek() {
                        Tok::Int(..) | Tok::Str(_) | Tok::Char(_) | Tok::True | Tok::False | Tok::Minus | Tok::LBrace => {
                            BindingKind::EqConst(self.const_arg_expr()?)
                        }
                        _ => BindingKind::EqTy(self.ty()?),
                    };
                    args.push(GenericArg::Binding { name, span, kind });
                }
                Tok::Ident(name) if self.peek_at(1) == Tok::Colon => {
                    let span = self.span();
                    self.bump();
                    self.bump();
                    let bounds = self.bounds()?;
                    args.push(GenericArg::Binding { name, span, kind: BindingKind::Constraint(bounds) });
                }
                Tok::Int(..) | Tok::Str(_) | Tok::Char(_) | Tok::True | Tok::False | Tok::Minus | Tok::LBrace => {
                    args.push(GenericArg::Const(self.const_arg_expr()?));
                }
                _ => args.push(GenericArg::Type(self.ty()?)),
            }
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::Gt, "`>`")?;
        Ok(args)
    }

    /// Parses `a::b::<T>::c`. In type position (`in_type`), generics need no `::`.
    /// Module anchors parse as plain first segments named `crate`,
    /// `self`, or `super` (the resolver reads them, as in use trees); a
    /// leading `::` becomes a first segment named `::`, which the
    /// resolver also reads and removes. Without the resolver these
    /// paths reach collect/check, which reject them as before.
    fn path(&mut self, in_type: bool) -> PResult<Vec<PathSeg>> {
        let mut segs = Vec::new();
        if self.eat(Tok::PathSep) {
            segs.push(PathSeg::plain(self.interner.intern("::")));
        }
        loop {
            let name = match self.peek() {
                Tok::Crate => {
                    self.bump();
                    self.interner.intern("crate")
                }
                Tok::Super => {
                    self.bump();
                    self.interner.intern("super")
                }
                Tok::SelfLower => {
                    self.bump();
                    self.known.self_value
                }
                _ => self.ident()?.0,
            };
            let turbofish = self.peek() == Tok::PathSep && self.peek_at(1) == Tok::Lt;
            let args = if (in_type && self.peek() == Tok::Lt) || turbofish {
                if turbofish {
                    self.bump();
                }
                GenericArgs::Angle(self.generic_args()?)
            } else {
                GenericArgs::None
            };
            segs.push(PathSeg { name, args });
            if self.peek() == Tok::PathSep
                && matches!(self.peek_at(1), Tok::Ident(_) | Tok::SelfUpper | Tok::Crate | Tok::Super | Tok::SelfLower)
            {
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
            // Statement attributes: parsed here so a `#[cfg]` on a statement
            // gets the attribute code; lint attributes are kept on `let`s.
            let stmt_attrs = self.part_attributes()?;
            // A function-local `use` is an item statement; the resolver
            // binds it for the rest of the block (docs/ARCH.md 1.3).
            if self.peek() == Tok::Use {
                let s = self.span();
                let tree_use = self.use_def()?;
                let idx = self.ast.stmt_items.len() as u32;
                self.ast.stmt_items.push(Item {
                    vis: Vis::Private,
                    attrs: stmt_attrs.attrs,
                    kind: ItemKind::Use(tree_use),
                    span: s.to(self.prev_span()),
                });
                stmts.push(Stmt::Item(idx));
                continue;
            }
            if matches!(
                self.peek(),
                Tok::Fn | Tok::Struct | Tok::Enum | Tok::Impl | Tok::Use | Tok::Mod | Tok::Trait | Tok::Static | Tok::Type | Tok::Extern
            ) || (self.peek() == Tok::Const && self.peek_at(1) != Tok::LBrace)
            {
                return Err(self.reject(C_CORE, "items inside function bodies"));
            }
            if self.peek() == Tok::Let {
                let s = self.bump().span;
                let pat = self.pattern()?;
                let ty = if self.eat(Tok::Colon) { Some(self.ty()?) } else { None };
                let init = if self.eat(Tok::Eq) { Some(self.expr()?) } else { None };
                if self.peek() == Tok::Else {
                    return Err(self.reject(C_CORE, "let-else"));
                }
                self.expect(Tok::Semi, "`;`")?;
                stmts.push(Stmt::Let { pat, ty, init, els: None, attrs: stmt_attrs.attrs, span: s.to(self.prev_span()) });
                continue;
            }
            let labeled = matches!(self.peek(), Tok::Lifetime(_)) && self.peek_at(1) == Tok::Colon;
            let block_like = labeled || matches!(self.peek(), Tok::If | Tok::Match | Tok::While | Tok::Loop | Tok::For | Tok::LBrace);
            let expr = if block_like {
                let e = if labeled { self.expr()? } else { self.block_like_expr()? };
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
                return Err(syntax(self.span(), format!("expected `;` or `}}`, found {}", tok_name(self.peek()))));
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

    /// True when the token `n` ahead can start a pattern literal.
    fn at_literal_start_at(&self, n: usize) -> bool {
        matches!(self.peek_at(n), Tok::Int(..) | Tok::Minus | Tok::Str(_) | Tok::Char(_) | Tok::True | Tok::False)
    }

    /// True when the next token can start a pattern literal.
    fn at_literal_start(&self) -> bool {
        matches!(self.peek(), Tok::Int(..) | Tok::Minus | Tok::Str(_) | Tok::Char(_) | Tok::True | Tok::False)
    }

    /// True when the next token can start a range pattern bound: a
    /// literal, or a path to a const (`u8::MAX`, `m::LO`, `LO`).
    fn at_bound_start(&self) -> bool {
        self.at_literal_start() || matches!(self.peek(), Tok::Ident(_) | Tok::SelfUpper)
    }

    /// Parses one range pattern bound: a literal (possibly negated) or
    /// a path. The checker evaluates it as a const expression.
    fn pattern_bound(&mut self) -> PResult<ExprId> {
        let start = self.span();
        if matches!(self.peek(), Tok::Ident(_) | Tok::SelfUpper) {
            let path = self.path(false)?;
            let span = start.to(self.prev_span());
            Ok(self.push_expr(Expr::Path(path), span))
        } else {
            self.literal_expr()
        }
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
                if self.eat(Tok::At) {
                    let inner = self.pattern_one()?;
                    Pat::At { name, mutable, by_ref, inner }
                } else {
                    Pat::Binding { name, mutable, by_ref }
                }
            }
            Tok::Int(..) | Tok::Minus | Tok::Str(_) | Tok::Char(_) | Tok::True | Tok::False => {
                let lo = self.literal_expr()?;
                if self.eat(Tok::DotDotEq) {
                    let hi = self.pattern_bound()?;
                    Pat::Range { lo: Some(lo), hi: Some(hi), inclusive: true }
                } else if self.eat(Tok::DotDot) {
                    if self.at_bound_start() {
                        let hi = self.pattern_bound()?;
                        Pat::Range { lo: Some(lo), hi: Some(hi), inclusive: false }
                    } else {
                        Pat::Range { lo: Some(lo), hi: None, inclusive: false }
                    }
                } else {
                    Pat::Lit(lo)
                }
            }
            Tok::DotDot => {
                self.bump();
                if self.at_bound_start() {
                    let hi = self.pattern_bound()?;
                    Pat::Range { lo: None, hi: Some(hi), inclusive: false }
                } else {
                    Pat::Rest
                }
            }
            Tok::DotDotEq => {
                self.bump();
                let hi = self.pattern_bound()?;
                Pat::Range { lo: None, hi: Some(hi), inclusive: true }
            }
            Tok::Float(_) | Tok::ByteStr | Tok::ByteChar => return Err(not_yet(C_LIT, start, "float and byte literals")),
            Tok::Lt => {
                let (self_ty, trait_path, segs) = self.qpath_parts()?;
                Pat::QPath { self_ty, trait_path, segs }
            }
            Tok::Ident(_) | Tok::SelfUpper if self.at_path_macro_call() => return Err(macro_error(start)),
            Tok::Ident(_) | Tok::SelfUpper => {
                let path = self.path(false)?;
                if self.peek() == Tok::DotDotEq || self.peek() == Tok::DotDot {
                    // A path as a range lower bound (`LO..=HI`, `u8::MIN..`).
                    let lo_span = start.to(self.prev_span());
                    let lo = self.push_expr(Expr::Path(path), lo_span);
                    if self.eat(Tok::DotDotEq) {
                        let hi = self.pattern_bound()?;
                        Pat::Range { lo: Some(lo), hi: Some(hi), inclusive: true }
                    } else {
                        self.bump();
                        if self.at_bound_start() {
                            let hi = self.pattern_bound()?;
                            Pat::Range { lo: Some(lo), hi: Some(hi), inclusive: false }
                        } else {
                            Pat::Range { lo: Some(lo), hi: None, inclusive: false }
                        }
                    }
                } else if self.peek() == Tok::At {
                    if path.len() != 1 || path[0].has_args() {
                        return Err(syntax(start, "expected a binding name before `@`"));
                    }
                    self.bump();
                    let inner = self.pattern_one()?;
                    Pat::At { name: path[0].name, mutable: false, by_ref: false, inner }
                } else {
                    match self.peek() {
                        Tok::LParen => {
                            self.bump();
                            let mut elems = Vec::new();
                            while self.peek() != Tok::RParen {
                                if self.peek() == Tok::DotDot {
                                    let s = self.span();
                                    self.bump();
                                    elems.push(self.push_pat(Pat::Rest, s));
                                } else {
                                    elems.push(self.pattern()?);
                                }
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
                                if matches!(self.peek(), Tok::Int(..)) {
                                    return Err(self.reject(C_CORE, "tuple struct patterns with field numbers"));
                                }
                                let _fattrs = self.part_attributes()?;
                                let by_ref = self.eat(Tok::Ref);
                                let mutable = self.eat(Tok::Mut);
                                let (fname, fspan) = self.ident()?;
                                let p = if self.eat(Tok::At) {
                                    let inner = self.pattern_one()?;
                                    self.push_pat(Pat::At { name: fname, mutable, by_ref, inner }, fstart.to(self.prev_span()))
                                } else if !by_ref && !mutable && self.eat(Tok::Colon) {
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
            }
            Tok::LParen => {
                self.bump();
                let mut elems = Vec::new();
                let mut tuple = false;
                while self.peek() != Tok::RParen {
                    if self.peek() == Tok::DotDot {
                        let s = self.span();
                        self.bump();
                        elems.push(self.push_pat(Pat::Rest, s));
                    } else {
                        elems.push(self.pattern()?);
                    }
                    if !self.eat(Tok::Comma) {
                        break;
                    }
                    tuple = true;
                }
                self.expect(Tok::RParen, "`)`")?;
                if !tuple && elems.len() == 1 {
                    return Ok(elems[0]);
                }
                Pat::Tuple(elems)
            }
            Tok::LBracket => {
                self.bump();
                let mut prefix: Vec<PatId> = Vec::new();
                let mut middle: Option<PatId> = None;
                let mut suffix: Vec<PatId> = Vec::new();
                let mut seen_rest = false;
                while self.peek() != Tok::RBracket {
                    if self.peek() == Tok::DotDot && !self.at_literal_start_at(1) {
                        let s = self.span();
                        self.bump();
                        if seen_rest {
                            return Err(syntax(s, "multiple `..` in a slice pattern"));
                        }
                        seen_rest = true;
                        middle = Some(self.push_pat(Pat::Rest, s));
                    } else {
                        let e = self.pattern()?;
                        // `rest @ ..` binds the middle slice itself.
                        let at_rest = match self.ast.pat(e) {
                            Pat::At { name, mutable, by_ref, inner } if matches!(self.ast.pat(*inner), Pat::Rest) => {
                                Some((*name, *mutable, *by_ref))
                            }
                            _ => None,
                        };
                        if let Some((name, mutable, by_ref)) = at_rest {
                            if seen_rest {
                                return Err(syntax(start, "multiple `..` in a slice pattern"));
                            }
                            seen_rest = true;
                            let espan = self.ast.pat_span(e);
                            middle = Some(self.push_pat(Pat::Binding { name, mutable, by_ref }, espan));
                        } else if seen_rest {
                            suffix.push(e);
                        } else {
                            prefix.push(e);
                        }
                    }
                    if !self.eat(Tok::Comma) {
                        break;
                    }
                }
                self.expect(Tok::RBracket, "`]`")?;
                Pat::Slice { prefix, middle, suffix }
            }
            Tok::Amp | Tok::AndAnd => {
                let double = self.bump().tok == Tok::AndAnd;
                let mutable = self.eat(Tok::Mut);
                let inner = self.pattern_one()?;
                let mut pat = Pat::Ref { mutable, inner };
                if double {
                    let s = start.to(self.prev_span());
                    let inner_id = self.push_pat(pat, s);
                    pat = Pat::Ref { mutable: false, inner: inner_id };
                }
                pat
            }
            Tok::Reserved(_) => return Err(self.reserved_error(start)),
            t => return Err(syntax(start, format!("expected a pattern, found {}", tok_name(t)))),
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
            t => return Err(syntax(start, format!("expected a literal, found {}", tok_name(t)))),
        };
        let span = start.to(self.prev_span());
        let id = self.push_expr(e, span);
        Ok(if neg { self.push_expr(Expr::Unary { op: UnOp::Neg, expr: id }, span) } else { id })
    }

    // ---------- Expressions ----------

    pub fn expr(&mut self) -> PResult<ExprId> {
        self.expr_ctx(false)
    }

    /// A closure: `move |params| -> Ret body`. Parameters are
    /// single patterns (no top-level `|` alternation, as in Rust);
    /// attributes on parameters are not parsed yet and fall out
    /// as a syntax error. The body is a full expression.
    fn closure_expr(&mut self, start: Span) -> PResult<ExprId> {
        let is_move = self.eat(Tok::Move);
        let mut params: Vec<ClosureParam> = Vec::new();
        if !self.eat(Tok::OrOr) {
            self.expect(Tok::Pipe, "`|`")?;
            loop {
                if self.eat(Tok::Pipe) {
                    break;
                }
                let pstart = self.span();
                let pat = self.pattern_one()?;
                let ty = if self.eat(Tok::Colon) { Some(self.ty()?) } else { None };
                let span = pstart.to(self.prev_span());
                params.push(ClosureParam { pat, ty, attrs: Vec::new(), span });
                if self.eat(Tok::Pipe) {
                    break;
                }
                self.expect(Tok::Comma, "`,` or `|`")?;
            }
        }
        let ret = if self.eat(Tok::Arrow) { Some(self.ty()?) } else { None };
        let body = self.expr()?;
        let span = start.to(self.prev_span());
        Ok(self.push_expr(Expr::Closure { is_move, is_async: false, params, ret, body }, span))
    }

    /// `no_struct` is set in `if`, `while`, `match`, and `for` heads, where `{` starts the body.
    fn expr_ctx(&mut self, no_struct: bool) -> PResult<ExprId> {
        let start = self.span();
        if matches!(self.peek(), Tok::Pipe | Tok::OrOr | Tok::Move) {
            // A closure head is not a struct-less head expression
            // either: `if |x| .. { }` stays rejected, as in Rust
            // without parentheses.
            if no_struct {
                return Err(not_yet(C_CORE, start, "closures"));
            }
            return self.closure_expr(start);
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
                if !double && self.at_ident("raw") && matches!(self.peek_at(1), Tok::Const | Tok::Mut) {
                    return Err(not_yet(C_CORE, start, "raw references (`&raw`)"));
                }
                let mutable = self.eat(Tok::Mut);
                let inner = self.prefix(no_struct)?;
                let span = start.to(self.prev_span());
                let mut id = self.push_expr(Expr::Ref { mutable, raw: false, expr: inner }, span);
                if double {
                    id = self.push_expr(Expr::Ref { mutable: false, raw: false, expr: id }, span);
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
            // In rustc a `<<` right after a cast type starts generic
            // arguments, it is not a shift: `a as u8 << 2` is an error. A
            // type that already ends in `>` is complete, so a shift after
            // it stays a shift.
            if self.peek() == Tok::Shl && self.toks[self.pos.saturating_sub(1)].tok != Tok::Gt {
                return Err(syntax(
                    self.span(),
                    "`<<` after a cast type is read as generic arguments, not as a shift: parenthesize the cast",
                ));
            }
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
                    if let Tok::Float(i) = self.peek() {
                        // `t.0.1` lexes the `0.1` as one float token; in field
                        // position it is two tuple indexes, as in rustc.
                        let text = self.ast.strings[(i + self.str_base) as usize].clone();
                        let parts: Vec<&str> = text.split('.').collect();
                        if parts.len() == 2 && parts.iter().all(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())) {
                            self.bump();
                            // A tuple index has no leading zero: `t.01.2`
                            // names no field (rustc E0609).
                            if parts.iter().any(|s| s.len() > 1 && s.starts_with('0')) {
                                return Err(syntax(self.span(), "tuple index has a leading zero"));
                            }
                            for part in parts {
                                let index: u32 = part.parse().map_err(|_| syntax(self.span(), "invalid tuple field index"))?;
                                e = self.push_expr(Expr::TupleField { base: e, index }, start.to(self.prev_span()));
                            }
                            continue;
                        }
                        return Err(syntax(self.span(), "expected identifier, found float literal"));
                    }
                    if let Tok::Int(v, suffix) = self.peek() {
                        if suffix.is_some() || v > u32::MAX as u128 {
                            return Err(syntax(self.span(), "invalid tuple field index"));
                        }
                        // A tuple index is written with no leading zero and
                        // no underscores: its text is exactly its decimal
                        // digits (rustc E0609 for `t.01`).
                        let sp = self.span();
                        if v.to_string().len() as u32 != sp.hi - sp.lo {
                            return Err(syntax(sp, "tuple index has a leading zero"));
                        }
                        let index = v as u32;
                        self.bump();
                        e = self.push_expr(Expr::TupleField { base: e, index }, start.to(self.prev_span()));
                        continue;
                    }
                    if self.peek() == Tok::Await {
                        return Err(async_error(self.span()));
                    }
                    let (name, name_span) = self.ident()?;
                    let mut generic_args = Vec::new();
                    if self.peek() == Tok::PathSep && self.peek_at(1) == Tok::Lt {
                        self.bump();
                        generic_args = self.generic_args()?;
                    }
                    if self.peek() == Tok::LParen {
                        let args = self.call_args()?;
                        e = self.push_expr(Expr::MethodCall { recv: e, name, name_span, generic_args, args }, start.to(self.prev_span()));
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
                Tok::Question => return Err(self.reject(C_CORE, "the `?` operator")),
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
        self.block_like_labeled(None)
    }

    fn block_like_labeled(&mut self, label: Option<Label>) -> PResult<ExprId> {
        let start = self.span();
        let e = match self.peek() {
            Tok::LBrace => match label {
                Some(label) => Expr::LabeledBlock { label, body: self.block()? },
                None => Expr::Block(self.block()?),
            },
            Tok::If => return self.if_expr(),
            Tok::While => {
                self.bump();
                let cond = self.condition()?;
                let body = self.block()?;
                Expr::While { label, cond, body }
            }
            Tok::Loop => {
                self.bump();
                Expr::Loop { label, body: self.block()? }
            }
            Tok::For => {
                self.bump();
                let pat = self.pattern()?;
                self.expect(Tok::In, "`in`")?;
                let iter = self.expr_ctx(true)?;
                let body = self.block()?;
                Expr::For { label, pat, iter, body }
            }
            Tok::Match => {
                self.bump();
                let scrut = self.expr_ctx(true)?;
                self.expect(Tok::LBrace, "`{`")?;
                let mut arms = Vec::new();
                while self.peek() != Tok::RBrace {
                    let aattrs = self.part_attributes()?;
                    let pat = self.pattern()?;
                    let guard = if self.eat(Tok::If) { Some(self.expr()?) } else { None };
                    self.expect(Tok::FatArrow, "`=>`")?;
                    let block_body = self.peek() == Tok::LBrace;
                    let body = if block_body { self.block_like_expr()? } else { self.expr()? };
                    arms.push(Arm { attrs: aattrs.attrs, pat, guard, body });
                    if !self.eat(Tok::Comma) && !block_body && self.peek() != Tok::RBrace {
                        return Err(syntax(self.span(), "expected `,` after match arm"));
                    }
                }
                self.expect(Tok::RBrace, "`}`")?;
                Expr::Match { scrut, arms }
            }
            _ if label.is_some() => return Err(syntax(start, "expected a loop or a block after the label")),
            _ => unreachable!(),
        };
        Ok(self.push_expr(e, start.to(self.prev_span())))
    }

    /// An `if` or `while` condition, where let chains may appear.
    fn condition(&mut self) -> PResult<ExprId> {
        let old = self.let_ok;
        self.let_ok = true;
        let r = self.expr_ctx(true);
        self.let_ok = old;
        r
    }

    fn if_expr(&mut self) -> PResult<ExprId> {
        let start = self.expect(Tok::If, "`if`")?;
        let cond = self.condition()?;
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

    fn primary(&mut self, no_struct: bool) -> PResult<ExprId> {
        let start = self.span();
        let e = match self.peek() {
            Tok::Int(v, s) => {
                self.bump();
                Expr::Int(v, s)
            }
            Tok::Float(i) => {
                self.bump();
                Expr::Float(i + self.str_base)
            }
            Tok::ByteStr | Tok::ByteChar => return Err(not_yet(C_LIT, start, "byte string and byte char literals")),
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
            Tok::Crate | Tok::Super | Tok::PathSep => {
                let path = self.path(false)?;
                if self.peek() == Tok::LBrace && !no_struct {
                    return self.struct_lit(path, start);
                }
                Expr::Path(path)
            }
            Tok::SelfLower if self.peek_at(1) == Tok::PathSep => {
                let path = self.path(false)?;
                if self.peek() == Tok::LBrace && !no_struct {
                    return self.struct_lit(path, start);
                }
                Expr::Path(path)
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
                    // A `let` in parentheses is never a let chain, even in a
                    // condition: rustc rejects `(let ...)` as a syntax error.
                    if self.peek() == Tok::Let {
                        return Err(syntax(start, "expected an expression, found `let`: parenthesized let chains are not allowed"));
                    }
                    let old_let = self.let_ok;
                    self.let_ok = false;
                    let first = self.expr();
                    let mut elems = match first {
                        Ok(e) => vec![e],
                        Err(d) => {
                            self.let_ok = old_let;
                            return Err(d);
                        }
                    };
                    let mut tuple = false;
                    while self.eat(Tok::Comma) {
                        tuple = true;
                        if self.peek() == Tok::RParen {
                            break;
                        }
                        match self.expr() {
                            Ok(e) => elems.push(e),
                            Err(d) => {
                                self.let_ok = old_let;
                                return Err(d);
                            }
                        }
                    }
                    let end = self.expect(Tok::RParen, "`)`");
                    self.let_ok = old_let;
                    end?;
                    if tuple {
                        Expr::Tuple(elems)
                    } else {
                        return Ok(elems[0]);
                    }
                }
            }
            Tok::LBracket => {
                self.bump();
                if self.eat(Tok::RBracket) {
                    Expr::Array(Vec::new())
                } else {
                    let first = self.expr()?;
                    if self.eat(Tok::Semi) {
                        let len = self.expr()?;
                        self.expect(Tok::RBracket, "`]`")?;
                        Expr::ArrayRepeat { value: first, len }
                    } else {
                        let mut elems = vec![first];
                        while self.eat(Tok::Comma) {
                            if self.peek() == Tok::RBracket {
                                break;
                            }
                            elems.push(self.expr()?);
                        }
                        self.expect(Tok::RBracket, "`]`")?;
                        Expr::Array(elems)
                    }
                }
            }
            Tok::If | Tok::Match | Tok::While | Tok::Loop | Tok::For | Tok::LBrace => return self.block_like_expr(),
            Tok::Break => {
                self.bump();
                let label = self.break_label();
                let val = if label.is_some() || self.can_start_expr() {
                    if self.can_start_expr() { Some(self.expr()?) } else { None }
                } else {
                    None
                };
                Expr::Break { label, value: val }
            }
            Tok::Continue => {
                self.bump();
                let label = self.break_label();
                Expr::Continue(label)
            }
            Tok::Return => {
                self.bump();
                let val = if self.can_start_expr() { Some(self.expr()?) } else { None };
                Expr::Return(val)
            }
            Tok::Lifetime(name) => {
                let span = self.span();
                self.bump();
                self.expect(Tok::Colon, "`:` after a label")?;
                let label = Label { name, span };
                return self.block_like_labeled(Some(label));
            }
            Tok::Pipe | Tok::OrOr | Tok::Move => return Err(not_yet(C_CORE, start, "closures")),
            Tok::Unsafe => return Err(unsafe_error(start)),
            Tok::Async => return Err(async_error(start)),
            Tok::Const => {
                self.bump();
                if self.peek() == Tok::LBrace {
                    Expr::ConstBlock(self.block()?)
                } else {
                    return Err(not_yet(C_CONST, start, "inline const blocks"));
                }
            }
            Tok::Let if self.let_ok => {
                self.bump();
                let pat = self.pattern()?;
                self.expect(Tok::Eq, "`=`")?;
                // The scrutinee stops before a chain `&&` (and before `||`):
                // only operators that bind tighter than `&&` are consumed.
                let scrut = self.binary(3, true)?;
                Expr::Let { pat, scrut }
            }
            Tok::Let => return Err(not_yet(C_CORE, start, "let chains outside conditions")),
            Tok::Lt => {
                let (self_ty, trait_path, segs) = self.qpath_parts()?;
                Expr::QPath { self_ty, trait_path, segs }
            }
            Tok::Underscore => return Err(not_yet(C_CORE, start, "inferred expressions (`_`)")),
            Tok::Ident(_) | Tok::SelfUpper => {
                if self.peek_at(1) == Tok::Bang {
                    return self.macro_call();
                }
                if self.at_offset_of_path() {
                    for _ in 0..6 {
                        self.bump();
                    }
                    return self.offset_of_body(start);
                }
                if self.at_path_macro_call() {
                    return Err(macro_error(start));
                }
                let path = self.path(false)?;
                if self.peek() == Tok::LBrace && !no_struct {
                    return self.struct_lit(path, start);
                }
                Expr::Path(path)
            }
            Tok::Reserved(_) => return Err(self.reserved_error(start)),
            t => return Err(syntax(start, format!("expected an expression, found {}", tok_name(t)))),
        };
        Ok(self.push_expr(e, start.to(self.prev_span())))
    }

    /// An optional label after `break` or `continue` (no colon follows it there).
    fn break_label(&mut self) -> Option<Label> {
        match self.peek() {
            Tok::Lifetime(name) => {
                let span = self.span();
                self.bump();
                Some(Label { name, span })
            }
            _ => None,
        }
    }

    fn can_start_expr(&self) -> bool {
        !matches!(self.peek(), Tok::Semi | Tok::RBrace | Tok::RParen | Tok::Comma | Tok::RBracket | Tok::Eof)
    }

    fn struct_lit(&mut self, path: Vec<PathSeg>, start: Span) -> PResult<ExprId> {
        self.expect(Tok::LBrace, "`{`")?;
        let mut fields = Vec::new();
        let mut update = None;
        while self.peek() != Tok::RBrace {
            if self.peek() == Tok::DotDot {
                self.bump();
                update = Some(self.expr()?);
                break;
            }
            // A tuple struct literal names fields by index: `T { 0: 5, ..a }`.
            // Tuple field names are the index text (collect).
            let (name, span) = if let Tok::Int(v, suffix) = self.peek() {
                if suffix.is_some() || v > u32::MAX as u128 {
                    return Err(syntax(self.span(), "invalid tuple field index"));
                }
                let index = v as u32;
                let span = self.bump().span;
                (self.interner.intern(&index.to_string()), span)
            } else {
                self.ident()?
            };
            let value = if self.eat(Tok::Colon) {
                self.expr()?
            } else {
                let seg = PathSeg::plain(name);
                self.push_expr(Expr::Path(vec![seg]), span)
            };
            fields.push((name, span, value));
            if !self.eat(Tok::Comma) {
                break;
            }
        }
        self.expect(Tok::RBrace, "`}`")?;
        Ok(self.push_expr(Expr::StructLit { path, fields, update }, start.to(self.prev_span())))
    }

    /// One step of an `offset_of!` field path: a field name, or an
    /// unsuffixed integer for a tuple field.
    fn offset_field(&mut self) -> PResult<crate::ast::OffsetField> {
        if let Tok::Int(v, suffix) = self.peek() {
            if suffix.is_some() || v > u32::MAX as u128 {
                return Err(syntax(self.span(), "invalid tuple field index"));
            }
            let index = v as u32;
            self.bump();
            return Ok(crate::ast::OffsetField::Index(index));
        }
        let (name, _) = self.ident()?;
        Ok(crate::ast::OffsetField::Name(name))
    }

    /// The body of an `offset_of!` call, after the `!`: `(Type, field)`,
    /// with a nested `a.b` field path allowed.
    fn offset_of_body(&mut self, start: Span) -> PResult<ExprId> {
        self.expect(Tok::LParen, "`(`")?;
        let ty = self.ty()?;
        self.expect(Tok::Comma, "`,`")?;
        let mut fields = vec![self.offset_field()?];
        while self.eat(Tok::Dot) {
            fields.push(self.offset_field()?);
        }
        self.eat(Tok::Comma);
        self.expect(Tok::RParen, "`)`")?;
        Ok(self.push_expr(Expr::OffsetOf { ty, fields }, start.to(self.prev_span())))
    }

    /// True at a `std::mem::offset_of!` or `core::mem::offset_of!` path call.
    fn at_offset_of_path(&self) -> bool {
        let name_at = |j: usize| match self.toks.get(j).map(|t| t.tok) {
            Some(Tok::Ident(s)) => Some(self.interner.get(s)),
            _ => None,
        };
        matches!(name_at(self.pos), Some("std" | "core"))
            && matches!(self.toks.get(self.pos + 1).map(|t| t.tok), Some(Tok::PathSep))
            && name_at(self.pos + 2) == Some("mem")
            && matches!(self.toks.get(self.pos + 3).map(|t| t.tok), Some(Tok::PathSep))
            && name_at(self.pos + 4) == Some("offset_of")
            && matches!(self.toks.get(self.pos + 5).map(|t| t.tok), Some(Tok::Bang))
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
        if self.interner.get(name) == "offset_of" {
            return self.offset_of_body(start);
        }
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
                        return Err(self.reject(C_LIT, "named format arguments"));
                    }
                    extra.push(self.expr()?);
                }
                let s = self.ast.strings[(si + self.str_base) as usize].clone();
                let base = args.len();
                // A format string a macro produced (concat! and kin) may
                // not capture variables, as in rustc.
                fmt = self.format_string(&s, lit_span, base, &mut extra, !crate::diag::is_no_capture(lit_span.ctxt))?;
                args.extend(extra);
            } else if self.peek() != close {
                return Err(syntax(self.span(), "expected a format string literal"));
            }
        }
        self.expect(close, "closing delimiter")?;
        Ok(self.push_expr(Expr::Macro { kind, args, fmt, repeat }, start.to(self.prev_span())))
    }

    /// Splits a format string into pieces. `{name}` captures become extra path arguments.
    /// With `allow_capture` false (a macro-produced format string), a named
    /// capture is an error, as in rustc.
    fn format_string(&mut self, s: &str, span: Span, base: usize, extra: &mut Vec<ExprId>, allow_capture: bool) -> PResult<Vec<FmtPiece>> {
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
                    _ => return Err(not_yet(C_LIT, span, &format!("format spec `{{:{fmt}}}`"))),
                };
                let index = if name.is_empty() {
                    next += 1;
                    next - 1
                } else if let Ok(n) = name.parse::<usize>() {
                    n
                } else if !allow_capture {
                    return Err(syntax(
                        span,
                        format!("there is no argument named `{name}`: a format string expanded from a macro cannot capture variables"),
                    ));
                } else {
                    let sym = self.interner.intern(name);
                    let seg = PathSeg::plain(sym);
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
        "this macro call has no expanded form yet",
        "User macros and most built-in macros expand before parsing. This form (such as format_args!) has no expanded form in the subset yet.",
    )
}
