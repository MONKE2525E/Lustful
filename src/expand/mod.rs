// Macro expansion (docs/ARCH.md section 6): `macro_rules!` matching and
// transcription over token trees, builtin macros, and the single-file
// macro scope rules (textual order, `#[macro_export]`, `#[macro_use]`,
// `use` imports) that run until the 6.1 outline worklist lands with
// W-RESOLVE. Expansion runs here on the lexed token stream of one file
// (or one driver chunk), before scan and parse, so items and functions a
// macro generates are scanned and parsed like written code.
//
// The frozen worklist interface is `compile_macro` plus `expand_call`:
// expand one `MacroCall` against one compiled definition to token trees.
// `lookup_macro` is the one place macro names resolve; it swaps to the
// frozen `Binding` query fns (S7) without touching callers.
pub mod assert_msg;
pub mod builtin;
pub mod lazy;
pub mod match_;
pub mod recognize;
pub mod transcribe;

use crate::ast::{MacroCall, MacroRulesDef};
use crate::def::DefId;
use crate::diag::{CtxtId, Diag, HygieneMark, Span, mark_no_capture, register_expansion, register_hygiene};
use crate::intern::{FxMap, Interner, Known, Sym};
use crate::lexer::{Delim, Lexed, Tok, Token, TokenTree, build_trees};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

// Diagnostic codes (docs/errors/REGISTRY.md, macro range).
pub const C_CAP: &str = "L0801"; // expansion caps
pub const C_UNKNOWN: &str = "L0802"; // unknown macro
pub const C_INCLUDE: &str = "L0803"; // include file not found
pub const C_AMBIG: &str = "L0805"; // local ambiguity
pub const C_CALL: &str = "L0806"; // invalid macro call or builtin input
pub const C_DEF: &str = "L0807"; // invalid macro definition
pub const C_UNSUPPORTED: &str = "L0809"; // known macro form lust does not support yet
const C_SYNTAX: &str = "L0001"; // syntax error (a malformed `recursion_limit`)
const C_ATTR: &str = "L0522"; // known attribute lust does not support yet

/// One expansion error, in the house shape (code, span, message, fix).
pub fn err(code: &'static str, span: Span, message: impl Into<String>, fix: impl Into<String>) -> Diag {
    Diag::new(code, span, message, fix)
}

/// A macro fragment kind, as written after `$name:` in a matcher.
/// `expr` and `expr_2021` are distinct kinds: the 2024 expression
/// grammar adds the `_` expression and const blocks, which an
/// `expr_2021` fragment must not match (ARCH 6.2).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FragKind {
    Expr,
    Expr2021,
    Ident,
    Ty,
    Pat,
    PatParam,
    Path,
    Stmt,
    Block,
    Item,
    Meta,
    Vis,
    Literal,
    Lifetime,
    Tt,
}

impl FragKind {
    /// The kind a matcher name stands for, or None for an unknown name.
    pub fn from_name(name: &str) -> Option<FragKind> {
        Some(match name {
            "expr" => FragKind::Expr,
            "expr_2021" => FragKind::Expr2021,
            "ident" => FragKind::Ident,
            "ty" => FragKind::Ty,
            "pat" => FragKind::Pat,
            "pat_param" => FragKind::PatParam,
            "path" => FragKind::Path,
            "stmt" => FragKind::Stmt,
            "block" => FragKind::Block,
            "item" => FragKind::Item,
            "meta" => FragKind::Meta,
            "vis" => FragKind::Vis,
            "literal" => FragKind::Literal,
            "lifetime" => FragKind::Lifetime,
            "tt" => FragKind::Tt,
            _ => return None,
        })
    }
    /// The matcher spelling of this kind, for diagnostics.
    pub fn name(self) -> &'static str {
        match self {
            FragKind::Expr => "expr",
            FragKind::Expr2021 => "expr_2021",
            FragKind::Ident => "ident",
            FragKind::Ty => "ty",
            FragKind::Pat => "pat",
            FragKind::PatParam => "pat_param",
            FragKind::Path => "path",
            FragKind::Stmt => "stmt",
            FragKind::Block => "block",
            FragKind::Item => "item",
            FragKind::Meta => "meta",
            FragKind::Vis => "vis",
            FragKind::Literal => "literal",
            FragKind::Lifetime => "lifetime",
            FragKind::Tt => "tt",
        }
    }
    /// Transparent kinds stay visible token by token to an inner matcher
    /// (ARCH 6.2); every other kind is one opaque unit when forwarded.
    pub fn transparent(self) -> bool {
        matches!(self, FragKind::Ident | FragKind::Lifetime | FragKind::Tt)
    }
}

/// One token tree in the expander. Like `lexer::TokenTree`, plus matched
/// fragments, which keep their kind and identity when forwarded into
/// another macro call (ARCH 6.2).
#[derive(Clone, Debug)]
pub enum Tt {
    Tok(Token),
    Delim(Delim, Vec<Tt>, Span),
    /// A matched fragment: its kind and the trees it was matched from.
    Frag(FragKind, Vec<Tt>, Span),
}

impl Tt {
    /// This tree's span (a group's opening delimiter span).
    pub fn span(&self) -> Span {
        match self {
            Tt::Tok(t) => t.span,
            Tt::Delim(_, _, span) | Tt::Frag(_, _, span) => *span,
        }
    }
    /// True when this tree is the single token `tok`.
    pub fn is_tok(&self, tok: Tok) -> bool {
        matches!(self, Tt::Tok(t) if t.tok == tok)
    }
}

/// Builds expander trees from lexer token trees.
pub fn tt_from_tree(tree: &TokenTree) -> Tt {
    match tree {
        TokenTree::Token(t) => Tt::Tok(*t),
        TokenTree::Delim(d, inner, span) => Tt::Delim(*d, inner.iter().map(tt_from_tree).collect(), *span),
    }
}

/// Turns expander trees back into lexer token trees. A fragment becomes
/// its inner trees (a statement also its `;`, see `match_::stmt_semi`):
/// the lexer form has no fragment case.
pub fn trees_from_tts(trees: &[Tt], out: &mut Vec<TokenTree>) {
    for tree in trees {
        match tree {
            Tt::Tok(t) => {
                let mut flat = Vec::new();
                push_split_token(&mut flat, t);
                out.extend(flat.into_iter().map(TokenTree::Token));
            }
            Tt::Delim(d, inner, span) => {
                let mut converted = Vec::new();
                trees_from_tts(inner, &mut converted);
                out.push(TokenTree::Delim(*d, converted, *span));
            }
            Tt::Frag(kind, inner, _) => {
                trees_from_tts(inner, out);
                if *kind == FragKind::Stmt
                    && let Some(semi) = match_::stmt_semi(inner)
                {
                    out.push(TokenTree::Token(semi));
                }
            }
        }
    }
}

/// Pushes one token into a flat token list, splitting a fused
/// `>>` or `>>=` back into the two halves the parser reads (it
/// joins them itself where a shift belongs). Every path from
/// token trees back to the parser goes through here.
pub fn push_split_token(out: &mut Vec<Token>, t: &Token) {
    match t.tok {
        Tok::Shr => {
            let mid = t.span.lo + 1;
            out.push(Token { tok: Tok::Gt, span: Span { hi: mid.min(t.span.hi), ..t.span } });
            out.push(Token { tok: Tok::Gt, span: Span { lo: mid.min(t.span.hi), ..t.span } });
        }
        Tok::ShrEq => {
            let mid = t.span.lo + 1;
            out.push(Token { tok: Tok::Gt, span: Span { hi: mid.min(t.span.hi), ..t.span } });
            out.push(Token { tok: Tok::Ge, span: Span { lo: mid.min(t.span.hi), ..t.span } });
        }
        _ => out.push(*t),
    }
}

/// Counts flat tokens in trees, groups included, for the 6.1 caps.
pub fn count_tokens(trees: &[Tt]) -> usize {
    trees
        .iter()
        .map(|t| match t {
            Tt::Tok(_) => 1,
            Tt::Delim(_, inner, _) => 2 + count_tokens(inner),
            Tt::Frag(_, inner, _) => count_tokens(inner),
        })
        .sum()
}

/// What one metavariable binds to. `Seq` nests once per repetition level
/// the variable was matched under; `Empty` is a variable inside an
/// optional group or repetition iteration that did not run.
#[derive(Clone, Debug)]
pub enum Bind {
    Leaf(Vec<Tt>),
    Seq(Vec<Bind>),
    Empty,
}

/// All metavariable bindings from one matched arm.
pub type BindMap = FxMap<Sym, Bind>;

/// Hashes one token for cache keys and matcher probes: what the token is,
/// what it names, and its hygiene context, but not its position, so code
/// that only moved still hits the expansion cache (ARCH 6.5).
pub fn hash_token(h: &mut impl Hasher, tok: &Token, strings: &[String]) {
    std::mem::discriminant(&tok.tok).hash(h);
    tok.span.ctxt.0.hash(h);
    match tok.tok {
        Tok::Ident(s) | Tok::Reserved(s) | Tok::Lifetime(s) => s.0.hash(h),
        Tok::Int(v, suffix, _) => {
            v.hash(h);
            suffix.map(|s| s as u8).hash(h);
        }
        Tok::Char(c, _) => c.hash(h),
        _ => {}
    }
    // Strings, including a literal's written text, which matching and
    // `stringify!` read: `0x1` and `1` are different inputs.
    for i in tok.tok.string_indices() {
        strings.get(i as usize).hash(h);
    }
}

/// Hashes token trees with `hash_token`.
pub fn hash_tts(trees: &[Tt], strings: &[String]) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    fn go(h: &mut impl Hasher, trees: &[Tt], strings: &[String]) {
        trees.len().hash(h);
        for tree in trees {
            match tree {
                Tt::Tok(t) => hash_token(h, t, strings),
                Tt::Delim(d, inner, _) => {
                    (*d as u8).hash(h);
                    go(h, inner, strings);
                }
                Tt::Frag(kind, inner, _) => {
                    0xffu8.hash(h);
                    (*kind as u8).hash(h);
                    go(h, inner, strings);
                }
            }
        }
    }
    go(&mut h, trees, strings);
    h.finish()
}

/// Hashes the spans of token trees against `base`: each token's file
/// and its byte range minus `base`, in tree order. With the first
/// token's start as base this is the trees' spacing shape, unchanged
/// when the code only moves; with base 0 it is the absolute layout.
/// Expansion reads spans (`line!`, `stringify!` spacing), so cache
/// keys and definition fingerprints must include what they read.
pub fn span_hash_tts(trees: &[Tt], base: u32) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    fn go(h: &mut impl Hasher, trees: &[Tt], base: u32) {
        for tree in trees {
            let span = tree.span();
            span.file.0.hash(h);
            span.lo.wrapping_sub(base).hash(h);
            span.hi.wrapping_sub(base).hash(h);
            if let Tt::Delim(_, inner, _) | Tt::Frag(_, inner, _) = tree {
                go(h, inner, base);
            }
        }
    }
    go(&mut h, trees, base);
    h.finish()
}

/// True when a token can be one segment of a macro path.
fn is_seg_tok(tok: Tok) -> bool {
    matches!(tok, Tok::Ident(_) | Tok::SelfUpper | Tok::SelfLower | Tok::Crate | Tok::Super)
}

/// The token at `trees[i]` when it is a plain token.
pub fn tok_at(trees: &[Tt], i: usize) -> Option<Token> {
    match trees.get(i) {
        Some(Tt::Tok(t)) => Some(*t),
        _ => None,
    }
}

/// The name a path-segment token stands for, as a string.
pub fn seg_text(tok: Tok, interner: &Interner) -> Option<String> {
    Some(match tok {
        Tok::Ident(s) => interner.get(s).to_string(),
        Tok::SelfUpper => "Self".to_string(),
        Tok::SelfLower => "self".to_string(),
        Tok::Crate => "crate".to_string(),
        Tok::Super => "super".to_string(),
        _ => return None,
    })
}

/// The symbol a metavariable name token stands for. Macro authors may
/// name a metavariable with a keyword (`$trait:ident` occurs in the
/// wild), so keywords count, as they do in rustc's matcher.
pub fn meta_sym(tok: Tok, interner: &Interner) -> Option<Sym> {
    match tok {
        Tok::Ident(s) => Some(s),
        Tok::As
        | Tok::Break
        | Tok::Const
        | Tok::Continue
        | Tok::Else
        | Tok::Enum
        | Tok::Fn
        | Tok::For
        | Tok::If
        | Tok::Impl
        | Tok::In
        | Tok::Let
        | Tok::Loop
        | Tok::Match
        | Tok::Mod
        | Tok::Mut
        | Tok::Pub
        | Tok::Ref
        | Tok::Return
        | Tok::SelfLower
        | Tok::SelfUpper
        | Tok::Static
        | Tok::Struct
        | Tok::Trait
        | Tok::Type
        | Tok::Unsafe
        | Tok::Use
        | Tok::Where
        | Tok::While
        | Tok::Async
        | Tok::Dyn
        | Tok::Move
        | Tok::Crate
        | Tok::Super
        | Tok::Extern
        | Tok::Await => Some(interner.intern(&tok_text(&tok, &[], interner))),
        _ => None,
    }
}

/// The symbol a path-segment token stands for.
pub fn seg_sym(tok: Tok, interner: &Interner) -> Option<Sym> {
    match tok {
        Tok::Ident(s) => Some(s),
        _ => seg_text(tok, interner).map(|text| interner.intern(&text)),
    }
}

/// The source text of one token, for `stringify!` and for reading literal
/// arguments to builtin macros.
pub fn tok_text(tok: &Tok, strings: &[String], interner: &Interner) -> String {
    use Tok::*;
    match tok {
        Ident(s) | Reserved(s) => return interner.get(*s).to_string(),
        Lifetime(s) => return format!("'{}", interner.get(*s)),
        // Literals print as written (see `lexer::lit_text`).
        Int(..) | Float(_) | Str(..) | DocStr(_) | ByteStr(_) | ByteChar(_) | Char(..) => {
            return crate::lexer::lit_text(tok, strings).unwrap_or_default().into_owned();
        }
        As => "as",
        Break => "break",
        Const => "const",
        Continue => "continue",
        Else => "else",
        Enum => "enum",
        False => "false",
        Fn => "fn",
        For => "for",
        If => "if",
        Impl => "impl",
        In => "in",
        Let => "let",
        Loop => "loop",
        Match => "match",
        Mod => "mod",
        Mut => "mut",
        Pub => "pub",
        Ref => "ref",
        Return => "return",
        SelfLower => "self",
        SelfUpper => "Self",
        Static => "static",
        Struct => "struct",
        Trait => "trait",
        True => "true",
        Type => "type",
        Unsafe => "unsafe",
        Use => "use",
        Where => "where",
        While => "while",
        Async => "async",
        Dyn => "dyn",
        Move => "move",
        Crate => "crate",
        Super => "super",
        Extern => "extern",
        Await => "await",
        LParen => "(",
        RParen => ")",
        LBrace => "{",
        RBrace => "}",
        LBracket => "[",
        RBracket => "]",
        Comma => ",",
        Semi => ";",
        Colon => ":",
        PathSep => "::",
        Dot => ".",
        DotDot => "..",
        DotDotEq => "..=",
        Ellipsis => "...",
        Arrow => "->",
        FatArrow => "=>",
        Eq => "=",
        EqEq => "==",
        Ne => "!=",
        Lt => "<",
        Le => "<=",
        Gt => ">",
        Ge => ">=",
        Plus => "+",
        Minus => "-",
        Star => "*",
        Slash => "/",
        Percent => "%",
        PlusEq => "+=",
        MinusEq => "-=",
        StarEq => "*=",
        SlashEq => "/=",
        PercentEq => "%=",
        AmpEq => "&=",
        PipeEq => "|=",
        CaretEq => "^=",
        ShlEq => "<<=",
        Amp => "&",
        AndAnd => "&&",
        Pipe => "|",
        OrOr => "||",
        Caret => "^",
        Bang => "!",
        Pound => "#",
        Question => "?",
        Underscore => "_",
        Shl => "<<",
        Shr => ">>",
        ShrEq => ">>=",
        Dollar => "$",
        At => "@",
        Eof => "",
    }
    .to_string()
}

/// True when two plain tokens match as token-tree literals in a matcher:
/// the same token, and a literal with the same written text, as rustc
/// compares them (`0x1` is not `1`, `'\x61'` is not `'a'`, and a doc
/// comment's `/// a` is `#[doc = r" a"]`). Span and context do not take part.
pub fn tok_matches(pattern: &Tok, input: &Tok, strings: &[String]) -> bool {
    match crate::lexer::lit_text(pattern, strings) {
        Some(text) => crate::lexer::lit_text(input, strings).is_some_and(|t| t == text),
        None => pattern == input,
    }
}

/// One metavariable of a matcher arm, with the repetition depth it was
/// bound at. Compile-time tables use the full record; matching reads
/// only names today, so the fields are write-only in this walk.
#[derive(Clone, Copy, Debug)]
#[allow(dead_code)]
pub struct VarInfo {
    pub kind: FragKind,
    pub depth: u32,
}

/// One arm of a compiled macro definition.
pub struct Arm {
    pub matcher: match_::ArmMatcher,
    pub template: Vec<Tt>,
}

/// A compiled `macro_rules!` definition.
pub struct MacroDef {
    pub name: Sym,
    pub name_span: Span,
    pub arms: Vec<Arm>,
    /// Whether the def carried `#[macro_export]`. Registration acts on
    /// it at store time; the worklist reads it from the def record.
    #[allow(dead_code)]
    pub exported: bool,
    /// The def was written inside a body (not at item level), so its
    /// tokens may read locals bound before the definition (ARCH 6.3).
    pub local_def: bool,
    pub def_span: Span,
    /// Hash of the definition's raw tokens (ARCH 6.5 cache key input).
    pub fingerprint: u64,
    /// The macro name alone, for diagnostics.
    pub name_text: String,
    /// A template mentions `stringify!`, `line!`, `column!`, or
    /// `file!`: its expansion reads token positions or spacing, so
    /// the expansion cache key must include the input layout.
    pub pos_sensitive: bool,
}

/// True when template trees contain a position-reading builtin call
/// (`stringify!` spacing, `line!`/`column!`/`file!` positions).
fn template_pos_sensitive(trees: &[Tt], interner: &Interner) -> bool {
    trees.iter().enumerate().any(|(i, t)| match t {
        Tt::Tok(tok) => {
            matches!(tok.tok, Tok::Ident(s2) if matches!(interner.get(s2), "stringify" | "line" | "column" | "file"))
                && tok_at(trees, i + 1).map(|n| n.tok) == Some(Tok::Bang)
        }
        Tt::Delim(_, inner, _) => template_pos_sensitive(inner, interner),
        Tt::Frag(_, inner, _) => template_pos_sensitive(inner, interner),
    })
}

/// Hashes the span layout of input trees (every token and group
/// position), for position-sensitive expansion cache keys.
fn span_layout_hash(trees: &[Tt]) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    fn go(h: &mut impl Hasher, trees: &[Tt]) {
        for tree in trees {
            let span = tree.span();
            span.lo.hash(h);
            span.hi.hash(h);
            match tree {
                Tt::Delim(_, inner, _) | Tt::Frag(_, inner, _) => go(h, inner),
                Tt::Tok(_) => {}
            }
        }
    }
    go(&mut h, trees);
    h.finish()
}

/// Compiles the arms inside one `macro_rules!` body group into a
/// definition (matcher trees, templates, follow-set and template checks).
pub fn compile_macro(
    name: Sym,
    name_span: Span,
    body: &[Tt],
    exported: bool,
    def_span: Span,
    strings: &[String],
    interner: &Interner,
) -> Result<MacroDef, Diag> {
    let mut arms = Vec::new();
    let mut i = 0;
    while i < body.len() {
        let Some(Tt::Delim(_, matcher, mspan)) = body.get(i) else {
            let span = body.get(i).map_or(def_span, |t| t.span());
            return Err(err(C_DEF, span, "expected a macro rule", "Write each rule as `( matcher ) => { expansion };`."));
        };
        let matcher = matcher.clone();
        let mspan = *mspan;
        if tok_at(body, i + 1).map(|t| t.tok) != Some(Tok::FatArrow) {
            return Err(err(C_DEF, mspan, "expected `=>` after a macro matcher", "Write each rule as `( matcher ) => { expansion };`."));
        }
        let Some(Tt::Delim(_, template, _)) = body.get(i + 2) else {
            return Err(err(C_DEF, mspan, "expected a macro expansion group", "Write each rule as `( matcher ) => { expansion };`."));
        };
        let template = template.clone();
        let (matcher, vars) = match_::compile_arm(&matcher, mspan, interner)?;
        transcribe::check_template_vars(&template, &vars, interner)?;
        arms.push(Arm { matcher, template });
        i += 3;
        if tok_at(body, i).map(|t| t.tok) == Some(Tok::Semi) {
            i += 1;
        } else if i < body.len() {
            return Err(err(C_DEF, mspan, "expected `;` between macro rules", "End each rule with `;`."));
        }
    }
    if arms.is_empty() {
        return Err(err(C_DEF, def_span, "a macro must contain at least one rule", "Add a rule such as `() => {};`."));
    }
    let pos_sensitive = arms.iter().any(|a| template_pos_sensitive(&a.template, interner));
    Ok(MacroDef {
        name,
        name_span,
        arms,
        exported,
        local_def: false,
        def_span,
        // The fingerprint includes the body's spacing shape: an edit
        // that only respaces a template (`stringify!(x+y)` to
        // `stringify!(x + y)`) must not hit a cached transcription.
        fingerprint: hash_tts(body, strings) ^ span_hash_tts(body, body.first().map_or(0, |t| t.span().lo)),
        name_text: interner.get(name).to_string(),
        pos_sensitive,
    })
}

/// Compiles an AST `MacroRulesDef` (the shape the 6.1 worklist carries)
/// into an expander definition. The worklist is its first caller.
#[allow(dead_code)]
pub fn compile_ast_macro(def: &MacroRulesDef, exported: bool, strings: &[String], interner: &Interner) -> Result<MacroDef, Diag> {
    let body: Vec<Tt> = def.tokens.iter().map(tt_from_tree).collect();
    compile_macro(def.name, def.name_span, &body, exported, def.span, strings, interner)
}

/// The driver facts expansion needs: who interns, which file this is
/// (for `file!` and relative `include!`), the file's text (for `line!`
/// and `column!`), and the cfg environment.
pub struct ExpandCtx<'a> {
    pub interner: &'a Interner,
    pub known: &'a Known,
    pub file_path: String,
    pub src: &'a str,
    pub cfg: builtin::CfgEnv,
    /// The module path (from the crate root) of the file being expanded.
    /// Empty for a crate root file and for single-file programs. The
    /// resolve worklist sets it per module file so `super::mac!`,
    /// `self::mac!`, and prescan module tables read from the right module.
    pub module_path: Vec<Sym>,
    /// The crate name `module_path!` starts with. The resolve worklist
    /// sets it from the crate being resolved (the Cargo package or the
    /// single-file crate name); None falls back to the current file's
    /// stem, which is right only for a crate root file.
    pub crate_name: Option<String>,
    /// The requesting client's env and shown paths (`for_file` gives `ClientView::PROCESS`).
    pub client: &'a ClientView,
}

/// What expansion reads from the client that asked for the compile
/// rather than from this process: the env `env!` sees, and how source
/// paths show in `file!` and `dbg!`. The driver builds one per request
/// from `protocol::Client`, so a daemon started under one env answers
/// another client as that client's own one-shot compile would.
#[derive(Clone, Default, Debug)]
pub struct ClientView {
    /// The client's env. None reads this process's start env (`builtin::compile_env`).
    pub env: Option<std::sync::Arc<Vec<(String, String)>>>,
    /// (absolute dir, shown dir): a path under the absolute dir shows as
    /// the shown dir joined with the rest, as rustc shows paths relative
    /// to the root path it was given. None shows paths as they are.
    pub shown_root: Option<(std::path::PathBuf, std::path::PathBuf)>,
}

impl ClientView {
    /// This process's env, paths shown as they are.
    pub const PROCESS: ClientView = ClientView { env: None, shown_root: None };

    /// The value of env var `name` for `env!` and `option_env!`.
    pub fn env_var(&self, name: &str) -> Option<String> {
        match &self.env {
            Some(env) => env.iter().find(|(k, _)| k == name).map(|(_, v)| v.clone()),
            None => builtin::compile_env(name),
        }
    }

    /// `path` as `file!` shows it.
    pub fn shown(&self, path: &str) -> String {
        match &self.shown_root {
            Some((abs, shown)) => match std::path::Path::new(path).strip_prefix(abs) {
                Ok(rest) => shown.join(rest).to_string_lossy().into_owned(),
                Err(_) => path.to_string(),
            },
            None => path.to_string(),
        }
    }
}

impl<'a> ExpandCtx<'a> {
    /// A context for one file under `file_path` with text `src`.
    pub fn for_file(interner: &'a Interner, known: &'a Known, file_path: &std::path::Path, src: &'a str, test: bool) -> ExpandCtx<'a> {
        ExpandCtx {
            interner,
            known,
            file_path: file_path.to_string_lossy().to_string(),
            src,
            cfg: builtin::CfgEnv { test, debug_assertions: true, facts: Vec::new(), panic_unwind: false },
            module_path: Vec::new(),
            crate_name: None,
            client: &ClientView::PROCESS,
        }
    }
    /// The crate name `module_path!` starts with: the name the resolve
    /// worklist set for this crate, or the file stem with `-` read as
    /// `_` (as rustc names a single-file crate) when none was set.
    pub fn crate_name(&self) -> String {
        if let Some(name) = &self.crate_name {
            return name.replace('-', "_");
        }
        let path = std::path::Path::new(&self.file_path);
        path.file_stem().map_or_else(|| "crate".to_string(), |s| s.to_string_lossy().replace('-', "_"))
    }
}

/// One input expansion read from outside the source text: a file an
/// `include!` family macro read (path plus a hash of its bytes), or an
/// environment variable an `env!`/`option_env!` read (name plus the
/// value seen, None when unset). The driver stores these with the
/// chunk they expanded into and drops the chunk when one changes
/// (ARCH 6.4, 6.5), so a daemon never answers from an expansion of a
/// file or environment that no longer exists in that form.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Dep {
    File {
        path: std::path::PathBuf,
        hash: u64,
    },
    Env {
        name: String,
        value: Option<String>,
    },
    /// The expansion read a token position (`line!` or `column!`):
    /// a chunk carrying it must not be reused at a different start
    /// line, which the driver checks (see `deps_stale`).
    Position,
    /// The expansion showed a source path (`file!`, `dbg!`): `path` as
    /// it was, and the text it showed under the client's view then.
    Shown {
        path: String,
        shown: String,
    },
}

/// Hashes bytes for a file dependency record.
fn dep_bytes_hash(bytes: &[u8]) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    bytes.hash(&mut h);
    h.finish()
}

/// True when any recorded dependency no longer reads as it did at
/// expansion time, judging env names through `env` (the compile-time
/// env snapshot the expander itself reads). A file that cannot be
/// read counts as changed: re-expanding then reports the real error.
pub fn deps_stale_with(deps: &[Dep], env: &dyn Fn(&str) -> Option<String>) -> bool {
    deps.iter().any(|dep| match dep {
        Dep::File { path, hash } => std::fs::read(path).map_or(true, |bytes| dep_bytes_hash(&bytes) != *hash),
        Dep::Env { name, value } => env(name) != *value,
        Dep::Position | Dep::Shown { .. } => false,
    })
}

/// `deps_stale_with` against `client`, the view this request expands
/// under (ARCH 6.4): its env, and how it shows the paths `file!` read.
pub fn deps_stale(deps: &[Dep], client: &ClientView) -> bool {
    deps_stale_with(deps, &|name| client.env_var(name))
        || deps.iter().any(|dep| matches!(dep, Dep::Shown { path, shown } if client.shown(path) != *shown))
}

/// One segment of a macro call path.
#[derive(Clone)]
pub struct Seg {
    pub sym: Sym,
    pub text: String,
    pub span: Span,
}

/// A macro call the walker found: its path, the head trees as written,
/// and the delimited argument trees.
pub struct Call {
    pub segs: Vec<Seg>,
    pub leading_colon: bool,
    pub head: Vec<Tt>,
    pub delim: Delim,
    pub inner: Vec<Tt>,
    pub group_span: Span,
    pub span: Span,
}

impl Call {
    /// The last path segment as text (the macro's own name).
    pub fn name_text(&self) -> &str {
        self.segs.last().map_or("", |s| &s.text)
    }
    /// The full written path, for diagnostics.
    pub fn path_text(&self) -> String {
        let mut out = String::new();
        if self.leading_colon {
            out.push_str("::");
        }
        for (i, seg) in self.segs.iter().enumerate() {
            if i > 0 {
                out.push_str("::");
            }
            out.push_str(&seg.text);
        }
        out
    }
}

// ---- Expansion cache (ARCH 6.5) ----

#[derive(PartialEq, Eq, Hash)]
struct CacheKey {
    def_fingerprint: u64,
    input_hash: u64,
    /// Absolute input layout and the call site: a transcription embeds
    /// the caller's token spans, and `line!` and `stringify!` in the
    /// output read them, so the same tokens at a new position or with
    /// new spacing are a different expansion.
    input_span_hash: u64,
    call_file: u32,
    call_lo: u32,
    call_hi: u32,
    call_ctxt: u32,
    cfg_hash: u64,
    edition: u16,
    deps_hash: u64,
    /// Input span layout for position-sensitive templates, else 0:
    /// `f(a,b)` and `f( a , b )` hash alike as tokens but stringify
    /// apart, so they must not share a cached transcription.
    layout: u64,
}

/// One cached expansion: its trees, the strings they name as a table of
/// their own (see `own_strings`), and the expansion context it carried.
type CachedExpansion = (Vec<Tt>, Vec<String>, CtxtId);

fn expansion_cache() -> &'static std::sync::Mutex<FxMap<CacheKey, CachedExpansion>> {
    static CACHE: std::sync::OnceLock<std::sync::Mutex<FxMap<CacheKey, CachedExpansion>>> = std::sync::OnceLock::new();
    CACHE.get_or_init(|| std::sync::Mutex::new(FxMap::default()))
}

/// Moves the strings that tokens in `trees` name from `strings` into
/// `out`, re-indexing the tokens into `out`. The expansion cache outlives
/// one run's string table (a daemon serves many), so a cached expansion
/// keeps its strings; a hit appends them to the new table (`shift_tts`).
fn own_strings(trees: &mut [Tt], strings: &[String], out: &mut Vec<String>) {
    for tree in trees {
        match tree {
            Tt::Tok(t) => {
                for i in t.tok.string_indices_mut().into_iter().flatten() {
                    out.push(strings.get(*i as usize).cloned().unwrap_or_default());
                    *i = out.len() as u32 - 1;
                }
            }
            Tt::Delim(_, inner, _) | Tt::Frag(_, inner, _) => own_strings(inner, strings, out),
        }
    }
}

/// Adds `offset` to every string index in `trees` (see `own_strings`).
fn shift_tts(trees: &mut [Tt], offset: u32) {
    for tree in trees {
        match tree {
            Tt::Tok(t) => t.tok.shift_strings(offset),
            Tt::Delim(_, inner, _) | Tt::Frag(_, inner, _) => shift_tts(inner, offset),
        }
    }
}

static CACHE_HITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static CACHE_MISSES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// (hits, misses) of the expansion cache since process start. A daemon
/// re-check of an unchanged macro call shows up here as a hit.
pub fn cache_stats() -> (u64, u64) {
    use std::sync::atomic::Ordering;
    (CACHE_HITS.load(Ordering::Relaxed), CACHE_MISSES.load(Ordering::Relaxed))
}

/// True when a flat token list can contain work for the expander: a
/// `macro_rules` definition, a call to a macro the parser does not own,
/// a cfg attribute, or a `recursion_limit` the expander reads. A
/// macro-free file pays one token scan and runs the unchanged pipeline.
pub fn needs_expansion(tokens: &[Token], interner: &Interner) -> bool {
    let macro_rules = interner.intern("macro_rules");
    for (i, t) in tokens.iter().enumerate() {
        match t.tok {
            Tok::Ident(s) if s == macro_rules => return true,
            Tok::Bang => {
                // `name!`: the token before the bang names the macro.
                // A path-qualified parser macro (`std::println!`) also
                // needs the expander: it strips the prefix for the parser.
                if let Some(prev) = i.checked_sub(1).map(|j| tokens[j].tok)
                    && let Some(name) = seg_text(prev, interner)
                    && (!builtin::is_passthrough(&name) || tokens.get(i.wrapping_sub(2)).map(|t| t.tok) == Some(Tok::PathSep))
                {
                    return true;
                }
            }
            Tok::Pound => {
                // `#[cfg...]` or `#[macro...]`: the attribute's first name.
                let mut j = i + 1;
                if tokens.get(j).map(|t| t.tok) == Some(Tok::Bang) {
                    j += 1;
                }
                if tokens.get(j).map(|t| t.tok) == Some(Tok::LBracket)
                    && let Some(name) = tokens.get(j + 1).and_then(|t| seg_text(t.tok, interner))
                    && (name == "cfg" || name == "cfg_attr" || name == "macro_use" || name == "macro_export" || name == "recursion_limit" || name == "test")
                {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Per-file expander state. One `expand_lexed` run builds one of these.
pub struct Expander<'a> {
    ctx: &'a ExpandCtx<'a>,
    strings: Vec<String>,
    defs: Vec<Arc<MacroDef>>,
    /// Textually visible macros, in definition order. Lookups scan in
    /// reverse, so a later definition shadows an earlier one.
    textual: Vec<(Sym, u32)>,
    /// Names brought in by `use` in scope here, same order rule.
    imports: Vec<(Sym, u32)>,
    /// `use std::vec as v;` style renames of builtin macros seen
    /// during the walk: bound name to canonical macro name.
    builtin_imports: Vec<(Sym, Sym)>,
    /// The same, per module, from the prescan.
    module_builtin_alias: FxMap<(Vec<Sym>, Sym), Sym>,
    /// `#[macro_export]` macros, visible by name at the crate root.
    exported: FxMap<Sym, u32>,
    /// Macros addressable by module path (a `pub use` made them so).
    by_path: FxMap<(Vec<Sym>, Sym), u32>,
    /// Every macro definition by its defining module, from the prescan:
    /// the table `use` resolution reads (a plain macro call still needs
    /// textual order, and does not read this).
    module_defs: FxMap<(Vec<Sym>, Sym), u32>,
    /// Macro names `use` brings into each module, from the prescan:
    /// imports apply to a whole module, not from a text point.
    module_imports: FxMap<(Vec<Sym>, Sym), u32>,
    /// The module path of the code being walked, from the crate root.
    module: Vec<Sym>,
    /// The file `file!` and relative includes currently refer to, and
    /// its text for `line!` / `column!`. `include!` swaps these.
    cur_file: String,
    cur_src: String,
    /// The file id of the tokens being expanded (the first input token's),
    /// so `assert_msg` can tell a macro body in this file from one in
    /// another file.
    root_file: Option<crate::diag::FileId>,
    /// Hash of files and env vars read by builtins during this run
    /// (it feeds cache keys, ARCH 6.5).
    deps_hash: u64,
    /// The outside inputs this run read, in read order. The driver
    /// stores them next to the expanded chunk (see `Dep`).
    deps: Vec<Dep>,
    /// Expansion depth cap for this file: 128, or the crate root's
    /// `#![recursion_limit = "N"]` up to `RECURSION_CAP`.
    recursion_limit: u32,
    /// True when the crate asked for more depth than `RECURSION_CAP`.
    limit_capped: bool,
    total_tokens: usize,
    /// The native stack segment expansion runs on (see `expand_list`):
    /// where it began, the bytes it may use, and the bytes used by the
    /// segments below it.
    stack_base: usize,
    stack_room: usize,
    stack_below: usize,
}

/// The most expansion depth lust honors, whatever the crate's
/// `#![recursion_limit]` asks for.
const RECURSION_CAP: u32 = 2048;
/// rustc's default recursion limit.
const DEFAULT_RECURSION_LIMIT: u32 = 128;
/// Stack bytes expansion may use on its caller's thread before it
/// continues on a thread of its own. Kept small on purpose: expansion
/// also runs on threads lust does not size (unit tests, probes).
const STACK_FIRST: usize = 256 << 10;
/// The stack size of each thread expansion continues on, and the bytes
/// one such segment uses before the next; the rest is headroom for
/// work below `expand_list` (matching, transcription, fragment parses).
const STACK_HOP: usize = 64 << 20;
const STACK_HOP_ROOM: usize = 48 << 20;
/// Expansion stack, all segments together, past which a file is
/// rejected (L0801) instead of growing without bound.
const STACK_TOTAL: usize = 1 << 30;

/// The address of a local: how deep the current thread's stack is.
fn stack_addr() -> usize {
    let marker = 0u8;
    std::hint::black_box(&marker) as *const u8 as usize
}

impl<'a> Expander<'a> {
    fn new(ctx: &'a ExpandCtx<'a>, strings: Vec<String>) -> Expander<'a> {
        Expander {
            ctx,
            strings,
            defs: Vec::new(),
            textual: Vec::new(),
            imports: Vec::new(),
            builtin_imports: Vec::new(),
            module_builtin_alias: FxMap::default(),
            exported: FxMap::default(),
            by_path: FxMap::default(),
            module_defs: FxMap::default(),
            module_imports: FxMap::default(),
            module: ctx.module_path.clone(),
            cur_file: ctx.file_path.clone(),
            cur_src: ctx.src.to_string(),
            root_file: None,
            deps_hash: 0,
            deps: Vec::new(),
            recursion_limit: DEFAULT_RECURSION_LIMIT,
            limit_capped: false,
            total_tokens: 0,
            stack_base: stack_addr(),
            stack_room: STACK_FIRST,
            stack_below: 0,
        }
    }

    /// Stores a string literal value and returns its index.
    pub fn push_string(&mut self, text: String) -> u32 {
        self.strings.push(text);
        self.strings.len() as u32 - 1
    }

    /// A string literal tree holding `text` at `span`.
    pub fn str_tree(&mut self, text: &str, span: Span) -> Tt {
        let i = self.push_string(text.to_string());
        Tt::Tok(Token { tok: Tok::Str(i, None), span })
    }

    /// A byte string literal tree for `bytes` at `span`: the verbatim
    /// `b"..."` text a `ByteStr` token holds, with every byte that is not
    /// printable ASCII (and `"`, `\\`) as a `\xNN` escape. `include_bytes!`
    /// makes one, so its value is the byte string's `&'static [u8; N]`.
    pub fn byte_str_tree(&mut self, bytes: &[u8], span: Span) -> Tt {
        let mut text = String::with_capacity(bytes.len() + 3);
        text.push_str("b\"");
        for &b in bytes {
            if (0x20..0x7f).contains(&b) && b != b'"' && b != b'\\' {
                text.push(b as char);
            } else {
                let _ = std::fmt::Write::write_fmt(&mut text, format_args!("\\x{b:02x}"));
            }
        }
        text.push('"');
        let i = self.push_string(text);
        Tt::Tok(Token { tok: Tok::ByteStr(i), span })
    }

    /// An identifier tree for `name` at `span`.
    pub fn ident_tree(&mut self, name: &str, span: Span) -> Tt {
        Tt::Tok(Token { tok: Tok::Ident(self.ctx.interner.intern(name)), span })
    }

    /// Folds one dependency read into the running deps hash.
    fn fold_dep(&mut self, what: &str, bytes: &[u8]) {
        let mut h = crate::intern::FxHasher::default();
        self.deps_hash.hash(&mut h);
        what.hash(&mut h);
        bytes.hash(&mut h);
        self.deps_hash = h.finish();
    }

    /// Records a file a builtin read: its path and a hash of the bytes
    /// seen, so the driver can tell when the file changes (`Dep`).
    pub fn read_dep_file(&mut self, path: &std::path::Path, bytes: &[u8]) {
        self.fold_dep(&path.to_string_lossy(), bytes);
        let dep = Dep::File { path: path.to_path_buf(), hash: dep_bytes_hash(bytes) };
        if !self.deps.contains(&dep) {
            self.deps.push(dep);
        }
    }

    /// Records that this expansion read a token position (`line!`
    /// or `column!`), whose baked value depends on the chunk's line.
    pub fn read_dep_position(&mut self) {
        if !self.deps.contains(&Dep::Position) {
            self.deps.push(Dep::Position);
        }
    }

    /// The current file as `file!` shows it, recorded as a `Dep::Shown`.
    pub fn read_dep_shown(&mut self) -> String {
        let path = self.cur_file.clone();
        let shown = self.ctx.client.shown(&path);
        self.fold_dep("shown", shown.as_bytes());
        let dep = Dep::Shown { path, shown: shown.clone() };
        if !self.deps.contains(&dep) {
            self.deps.push(dep);
        }
        shown
    }

    /// Records an env var a builtin read and the value it saw.
    pub fn read_dep_env(&mut self, name: &str, value: Option<&str>) {
        self.fold_dep(&format!("env:{name}"), value.unwrap_or("").as_bytes());
        let dep = Dep::Env { name: name.to_string(), value: value.map(str::to_string) };
        if !self.deps.contains(&dep) {
            self.deps.push(dep);
        }
    }

    /// 1-based line and column of `span` in the current file's text,
    /// following expansions out to the call site (ARCH 6.3/6.4).
    pub fn line_col(&self, span: Span) -> (u32, u32) {
        let lo = span.lo as usize;
        let src = self.cur_src.as_bytes();
        let upto = lo.min(src.len());
        let line = src[..upto].iter().filter(|&&b| b == b'\n').count() as u32 + 1;
        let line_start = src[..upto].iter().rposition(|&b| b == b'\n').map_or(0, |p| p + 1);
        let col = self.cur_src[line_start..upto].chars().count() as u32 + 1;
        (line, col)
    }

    /// Lexes a small built-in template and returns its trees, stamped
    /// with `span`. Placeholder idents in the template are spliced by
    /// the caller with `splice_placeholders`.
    pub fn lex_template(&mut self, src: &str, span: Span) -> Vec<Tt> {
        let mini = crate::lexer::lex(src, span.file, 0, self.ctx.interner).expect("builtin templates lex");
        let offset = self.strings.len() as u32;
        self.strings.extend(mini.strings.iter().cloned());
        let (trees, _) = build_trees(&mini.tokens);
        fn remap(trees: &[Tt], offset: u32, span: Span) -> Vec<Tt> {
            trees
                .iter()
                .map(|t| match t {
                    Tt::Tok(tok) => {
                        let mut tok = tok.tok;
                        tok.shift_strings(offset);
                        Tt::Tok(Token { tok, span })
                    }
                    Tt::Delim(d, inner, _) => Tt::Delim(*d, remap(inner, offset, span), span),
                    Tt::Frag(k, inner, s) => Tt::Frag(*k, remap(inner, offset, span), *s),
                })
                .collect()
        }
        remap(&trees.iter().map(tt_from_tree).collect::<Vec<_>>(), offset, span)
    }

    /// Lexes an included file's text into trees in this expander's string
    /// table, keeping the file's own spans (offsets are in that file).
    pub fn lex_file_trees(&mut self, src: &str, file: crate::diag::FileId) -> Result<Vec<Tt>, Diag> {
        let mini = crate::lexer::lex(src, file, 0, self.ctx.interner)?;
        let offset = self.strings.len() as u32;
        self.strings.extend(mini.strings.iter().cloned());
        let (trees, balanced) = build_trees(&mini.tokens);
        if !balanced {
            return Err(err("L0001", Span::new(file, 0, 0), "unbalanced delimiters in included file", "Fix the syntax."));
        }
        fn remap(trees: &[Tt], offset: u32) -> Vec<Tt> {
            trees
                .iter()
                .map(|t| match t {
                    Tt::Tok(tok) => {
                        let mut kind = tok.tok;
                        kind.shift_strings(offset);
                        Tt::Tok(Token { tok: kind, span: tok.span })
                    }
                    Tt::Delim(d, inner, span) => Tt::Delim(*d, remap(inner, offset), *span),
                    Tt::Frag(k, inner, span) => Tt::Frag(*k, remap(inner, offset), *span),
                })
                .collect()
        }
        Ok(remap(&trees.iter().map(tt_from_tree).collect::<Vec<_>>(), offset))
    }
}

/// Replaces every `$`-free identifier tree named `name` in `trees` with
/// `replacement`. Builtin templates name their holes this way.
pub fn splice_placeholders(trees: Vec<Tt>, name: &str, replacement: &[Tt], interner: &Interner) -> Vec<Tt> {
    let mut out = Vec::new();
    for tree in trees {
        match tree {
            Tt::Tok(t) if matches!(t.tok, Tok::Ident(s) if interner.get(s) == name) => out.extend(replacement.iter().cloned()),
            Tt::Delim(d, inner, span) => out.push(Tt::Delim(d, splice_placeholders(inner, name, replacement, interner), span)),
            other => out.push(other),
        }
    }
    out
}

/// One macro definition the worklist hands to the expander before a
/// file walk (ARCH 6.1): a `macro_rules!` definition written in another
/// file or crate, addressable by a module path from the expanding
/// crate's root. An empty path is the crate root itself, which is where
/// `#[macro_export]` macros of this crate live (`crate::name!`); a path
/// of one segment names a dependency crate (`dep::name!`); longer paths
/// name a public re-export module (`crate::m::name!`). Seeds never enter
/// textual scope: a plain `name!` call still needs textual order or a
/// `use` in the expanding file, exactly as in Rust. `tokens` is the
/// flat token slice of the definition (from `macro_rules` to its
/// closing group and optional `;`), and `strings` is the string table
/// those tokens index into; the expander remaps them into its own table
/// and compiles the definition there, so string values stay exact.
#[derive(Clone)]
pub struct MacroSeed {
    pub path: Vec<Sym>,
    pub tokens: Vec<Token>,
    pub strings: Vec<String>,
    /// When set, this seed also answers plain `name!` calls in this
    /// module path: it records a glob import (`use a::*;`) of this
    /// macro into that module, which the worklist resolved. Plain
    /// seeds leave it None and stay path-only, as before.
    pub import_into: Option<Vec<Sym>>,
}

/// The value of a `recursion_limit` attribute from the trees after its
/// name (`= "N"`), read as rustc reads it (`usize` from the whole
/// string). A malformed one is an error in rustc, wherever it is, even
/// in a module where a valid one is ignored; so it is one here too.
fn recursion_limit_value(after_name: &[Tt], strings: &[String], span: Span) -> Result<usize, Diag> {
    match after_name {
        [Tt::Tok(eq), Tt::Tok(Token { tok: Tok::Str(idx, _), .. })] if eq.tok == Tok::Eq => {
            strings.get(*idx as usize).and_then(|s| s.parse::<usize>().ok())
        }
        _ => None,
    }
    .ok_or_else(|| {
        err(C_SYNTAX, span, "malformed `recursion_limit` attribute", "Write `#![recursion_limit = \"N\"]` with N a non-negative integer.")
    })
}

/// The crate's `#![recursion_limit = "N"]` among a root file's leading
/// inner attributes, with its span. The first one wins, as in rustc.
fn scan_recursion_limit(trees: &[Tt], strings: &[String], interner: &Interner) -> Result<Option<(usize, Span)>, Diag> {
    let mut found = None;
    let mut i = 0;
    while tok_at(trees, i).map(|t| t.tok) == Some(Tok::Pound) && tok_at(trees, i + 1).map(|t| t.tok) == Some(Tok::Bang) {
        let Some(Tt::Delim(Delim::Bracket, body, span)) = trees.get(i + 2) else { break };
        if seg_text(tok_at(body, 0).map_or(Tok::Eof, |t| t.tok), interner).as_deref() == Some("recursion_limit") {
            let n = recursion_limit_value(&body[1..], strings, *span)?;
            found.get_or_insert((n, *span));
        }
        i += 3;
    }
    Ok(found)
}

/// Expands every macro in one lexed file or chunk, returning the
/// expanded token list. A file that cannot contain macros comes back
/// unchanged (the same `Lexed`).
pub fn expand_lexed(lexed: Lexed, ctx: &ExpandCtx) -> Result<Lexed, Diag> {
    expand_lexed_seeded(lexed, ctx, &[])
}

/// `expand_lexed` with worklist macro seeds registered in the path
/// tables before the prescan, so this file's own `use` items and path
/// calls can resolve macros defined in other files and crates.
/// `expand_lexed_seeded_with_deps` without the dependency record.
pub fn expand_lexed_seeded(lexed: Lexed, ctx: &ExpandCtx, seeds: &[MacroSeed]) -> Result<Lexed, Diag> {
    expand_lexed_seeded_with_deps(lexed, ctx, seeds).map(|(lexed, _deps)| lexed)
}

/// `expand_lexed_seeded_with_deps` with no seeds: expands one lexed
/// file or chunk and returns the outside inputs expansion read
/// (`Dep` records for `include!` files and `env!` values).
pub fn expand_lexed_with_deps(lexed: Lexed, ctx: &ExpandCtx) -> Result<(Lexed, Vec<Dep>), Diag> {
    expand_lexed_seeded_with_deps(lexed, ctx, &[])
}

/// The first delimiter error in `tokens`: a closer that does not match
/// the open group, or else the innermost group still open at the end.
/// None when every delimiter is balanced (as `build_trees` judges).
pub fn delimiter_error(tokens: &[Token]) -> Option<Diag> {
    let mut open: Vec<(Tok, Span)> = Vec::new();
    for t in tokens {
        let want = match t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => {
                open.push((t.tok, t.span));
                continue;
            }
            Tok::RParen => Tok::LParen,
            Tok::RBracket => Tok::LBracket,
            Tok::RBrace => Tok::LBrace,
            _ => continue,
        };
        if open.last().map(|o| o.0) != Some(want) {
            return Some(err("L0001", t.span, "unexpected closing delimiter", "Remove it, or close the groups opened before it first."));
        }
        open.pop();
    }
    let (_, span) = open.pop()?;
    Some(err("L0001", span, "this file contains an unclosed delimiter", "Close the group this delimiter opens."))
}

/// The seeded, dependency-returning expansion both wrappers use.
/// A file that cannot contain macros comes back unchanged (the
/// same `Lexed`, no deps). Static init closures then move into hidden
/// fns (`lazy::hoist_static_closures`, W-STD-C), so every pipeline that
/// expands sees the same items.
pub fn expand_lexed_seeded_with_deps(lexed: Lexed, ctx: &ExpandCtx, seeds: &[MacroSeed]) -> Result<(Lexed, Vec<Dep>), Diag> {
    let (lexed, deps) = expand_macros(lexed, ctx, seeds)?;
    Ok((lazy::hoist_static_closures(lexed, ctx.interner), deps))
}

/// Macro expansion proper, for `expand_lexed_seeded_with_deps`.
fn expand_macros(lexed: Lexed, ctx: &ExpandCtx, seeds: &[MacroSeed]) -> Result<(Lexed, Vec<Dep>), Diag> {
    if !needs_expansion(&lexed.tokens, ctx.interner) {
        return Ok((lexed, Vec::new()));
    }
    let (trees, balanced) = build_trees(&lexed.tokens);
    if !balanced {
        // rustc reports this while lexing, before any macro or parse
        // error; the parser would stop at the first unexpanded call.
        if let Some(d) = delimiter_error(&lexed.tokens) {
            return Err(d);
        }
        return Ok((lexed, Vec::new()));
    }
    let eof = lexed.tokens.last().cloned().unwrap_or(Token { tok: Tok::Eof, span: Span::default() });
    let mut st = Expander::new(ctx, lexed.strings);
    st.root_file = lexed.tokens.first().map(|t| t.span.file);
    for seed in seeds {
        st.seed_macro(seed)?;
    }
    let tts: Vec<Tt> = trees.iter().map(tt_from_tree).collect();
    // Only the crate root's `#![recursion_limit]` counts, as in rustc,
    // where a module's copy is an unused attribute.
    let limit = if ctx.module_path.is_empty() { scan_recursion_limit(&tts, &st.strings, ctx.interner)? } else { None };
    if let Some((n, _)) = limit {
        st.recursion_limit = n.min(RECURSION_CAP as usize) as u32;
        st.limit_capped = n > RECURSION_CAP as usize;
    }
    st.prescan(&tts)?;
    let out = st.expand_list(tts, 0, true, false, 0)?;
    // rustc also checks type, trait, and layout depth against a lowered
    // limit, and lust does not track those: a crate that lowers it is
    // rejected (after its macros got rustc's own depth error, if any).
    if let Some((n, span)) = limit
        && n < DEFAULT_RECURSION_LIMIT as usize
    {
        return Err(err(
            C_ATTR,
            span,
            "a `#![recursion_limit]` below the default 128 is not supported yet",
            "Remove the attribute, or set it to 128 or more.",
        ));
    }
    if std::env::var_os("LUST_EXPAND_STATS").is_some() {
        let (hits, misses) = cache_stats();
        eprintln!("expand cache: {hits} hits, {misses} misses");
    }
    let mut tokens = Vec::new();
    flatten_final(&out, &mut tokens);
    if std::env::var_os("LUST_EXPAND_DEBUG").is_some() {
        let texts: Vec<String> = tokens.iter().map(|t| tok_text(&t.tok, &st.strings, ctx.interner)).collect();
        eprintln!("expanded tokens: {}", texts.join(" "));
    }
    tokens.push(eof);
    Ok((Lexed { tokens, strings: st.strings }, st.deps))
}

/// The frozen worklist interface (ARCH 6.1): expand one call against one
/// compiled definition. `strings` must be the same table the call's
/// tokens index into. The worklist is its first caller.
#[allow(dead_code)]
pub fn expand_call(call: &MacroCall, def: &MacroDef, strings: &[String], ctx: &ExpandCtx) -> Result<Vec<TokenTree>, Diag> {
    let mut st = Expander::new(ctx, strings.to_vec());
    let inner: Vec<Tt> = call.tokens.iter().map(tt_from_tree).collect();
    let syn = Call {
        segs: call.path.iter().map(|seg| Seg { sym: seg.name, text: ctx.interner.get(seg.name).to_string(), span: call.span }).collect(),
        leading_colon: false,
        head: Vec::new(),
        delim: call.delim,
        inner,
        group_span: call.span,
        span: call.span,
    };
    let out = st.transcribe_call(def, &syn, 0)?;
    let mut trees = Vec::new();
    trees_from_tts(&out, &mut trees);
    Ok(trees)
}

/// `lust expand <file.rs>`: prints the file's expanded token stream to
/// stdout, one space between tokens. This is lust's own expansion (the
/// parser's builtin macros such as `println!` stay in their written
/// form); the macro corpus compares it against rustc's
/// `-Zunpretty=expanded` through tests/macros/normalize.py, which
/// canonicalizes the forms the two compilers print differently.
/// Returns the process exit code.
pub fn run_expand(args: &[String]) -> i32 {
    let [file] = args else {
        eprintln!("usage: lust expand <file.rs>");
        return 2;
    };
    let path = std::path::Path::new(file);
    let src = match std::fs::read_to_string(path) {
        Ok(src) => src,
        Err(e) => {
            eprintln!("error: cannot read {}: {e}", path.display());
            return 2;
        }
    };
    let mut map = crate::diag::SourceMap::default();
    map.add_file(file, &src);
    let interner = Interner::default();
    let known = Known::new(&interner);
    let out = crate::lexer::lex(&src, crate::diag::FileId(0), 0, &interner).and_then(|lexed| {
        let ctx = ExpandCtx::for_file(&interner, &known, path, &src, false);
        expand_lexed_with_deps(lexed, &ctx).map(|(lexed, _deps)| lexed)
    });
    match out {
        Ok(lexed) => {
            let mut text = String::new();
            for tok in &lexed.tokens {
                if tok.tok == Tok::Eof {
                    continue;
                }
                if !text.is_empty() {
                    text.push(' ');
                }
                text.push_str(&tok_text(&tok.tok, &lexed.strings, &interner));
            }
            println!("{text}");
            0
        }
        Err(mut d) => {
            eprint!("{}", crate::diag::render(std::slice::from_mut(&mut d), &map, &src, false, 20));
            1
        }
    }
}

/// True when a tree sequence already reads as one atomic operand in a
/// flat token stream, so precedence parens around it would only add
/// noise: a single tree, a place or call shape (`a.b`, `f(x)`,
/// `vec![x]`, `a[i]`), or a block-like expression head.
fn atomic_shaped(trees: &[Tt]) -> bool {
    if trees.len() == 1 {
        return true;
    }
    if matches!(trees.first(), Some(Tt::Tok(t)) if matches!(t.tok, Tok::Match | Tok::If | Tok::Loop | Tok::While | Tok::For)) {
        return true;
    }
    fn place_tok(tok: Tok) -> bool {
        matches!(
            tok,
            Tok::Ident(_)
                | Tok::SelfUpper
                | Tok::SelfLower
                | Tok::Crate
                | Tok::Super
                | Tok::Dot
                | Tok::PathSep
                | Tok::Int(..)
                | Tok::Bang
                | Tok::Lt
                | Tok::Gt
                | Tok::Comma
                | Tok::Lifetime(_)
        )
    }
    // A call or index shape: place tokens, then one trailing group.
    if let Some((last, head)) = trees.split_last()
        && matches!(last, Tt::Delim(_, _, _))
        && !head.is_empty()
        && head.iter().all(|t| matches!(t, Tt::Tok(tok) if place_tok(tok.tok)) || matches!(t, Tt::Delim(Delim::Bracket, _, _)))
    {
        return true;
    }
    trees.iter().all(|t| match t {
        Tt::Tok(tok) => matches!(tok.tok, Tok::Ident(_) | Tok::SelfUpper | Tok::SelfLower | Tok::Dot | Tok::PathSep | Tok::Int(..)),
        Tt::Delim(Delim::Bracket, _, _) => true,
        _ => false,
    })
}

/// Flattens expanded trees for the parser. An expression fragment with
/// more than one token gets parens, so forwarding one into a larger
/// expression keeps its rustc atomic shape in the flat token stream,
/// and a statement fragment gets its `;` (see `match_::stmt_semi`).
fn flatten_final(trees: &[Tt], out: &mut Vec<Token>) {
    for tree in trees {
        match tree {
            // A doc comment's string bound as a `literal` or `expr` is the
            // raw string literal rustc's tokens hold; the parser reads a
            // string token there.
            Tt::Frag(FragKind::Literal | FragKind::Expr | FragKind::Expr2021, inner, _)
                if matches!(inner.as_slice(), [Tt::Tok(t)] if matches!(t.tok, Tok::DocStr(_))) =>
            {
                if let [Tt::Tok(Token { tok: Tok::DocStr(i), span })] = inner.as_slice() {
                    out.push(Token { tok: Tok::Str(*i, None), span: *span });
                }
            }
            // A negative literal fragment (`-2`) is one operand; without
            // parens `- 2 . pow(..)` would read as `-(2.pow(..))`.
            Tt::Frag(FragKind::Literal, inner, span) if matches!(inner.first(), Some(Tt::Tok(t)) if t.tok == Tok::Minus) => {
                out.push(Token { tok: Tok::LParen, span: *span });
                flatten_final(inner, out);
                out.push(Token { tok: Tok::RParen, span: *span });
            }
            Tt::Frag(k, inner, span)
                if matches!(k, FragKind::Expr | FragKind::Expr2021) && count_tokens(inner) > 1 && !atomic_shaped(inner) =>
            {
                out.push(Token { tok: Tok::LParen, span: *span });
                flatten_final(inner, out);
                out.push(Token { tok: Tok::RParen, span: *span });
            }
            Tt::Tok(t) => push_split_token(out, t),
            Tt::Delim(d, inner, span) => {
                let (open, close) = match d {
                    Delim::Paren => (Tok::LParen, Tok::RParen),
                    Delim::Bracket => (Tok::LBracket, Tok::RBracket),
                    Delim::Brace => (Tok::LBrace, Tok::RBrace),
                };
                out.push(Token { tok: open, span: *span });
                flatten_final(inner, out);
                out.push(Token { tok: close, span: *span });
            }
            Tt::Frag(kind, inner, _) => {
                flatten_final(inner, out);
                if *kind == FragKind::Stmt
                    && let Some(semi) = match_::stmt_semi(inner)
                {
                    out.push(semi);
                }
            }
        }
    }
}

impl builtin::CfgRead for Expander<'_> {
    fn ident_text(&self, tok: Tok) -> Option<String> {
        match tok {
            Tok::Ident(s) => Some(self.ctx.interner.get(s).to_string()),
            _ => seg_text(tok, self.ctx.interner),
        }
    }
    fn string_text(&self, tok: Tok) -> Option<String> {
        match tok {
            Tok::Str(i, _) => self.strings.get(i as usize).cloned(),
            _ => None,
        }
    }
}

impl<'a> Expander<'a> {
    /// Finds macro definitions and module-level `use` items anywhere in
    /// the file before the main walk. Path forms (`crate::name!`) and
    /// imports apply to a whole module, not from a text point, so uses
    /// below a call site still import (ARCH 6.1). Plain calls keep
    /// textual order in the main walk; this pass only feeds the path
    /// and import tables.
    fn prescan(&mut self, trees: &[Tt]) -> Result<(), Diag> {
        type UseSite = (Vec<Sym>, Vec<Seg>, bool, Sym, bool);
        fn walk(st: &mut Expander, trees: &[Tt], module: &mut Vec<Sym>, at_module_list: bool, uses: &mut Vec<UseSite>) -> Result<(), Diag> {
            let mut i = 0;
            let mut exported = false;
            let mut cfg_off = false;
            while i < trees.len() {
                if let Some(attr) = attr_at(trees, i, st.ctx.interner) {
                    if attr.path == "macro_export" {
                        exported = true;
                    }
                    if attr.path == "cfg" {
                        cfg_off = !builtin::eval_cfg(&attr.inner, &st.ctx.cfg, st, attr.span)?;
                    }
                    if attr.path == "cfg_attr" {
                        // `cfg_attr(cond, macro_export)` exports under
                        // cond; `cfg_attr(cond, cfg(..))` gates likewise.
                        let split = attr.inner.iter().position(|t| t.is_tok(Tok::Comma)).unwrap_or(attr.inner.len());
                        if builtin::eval_cfg(&attr.inner[..split], &st.ctx.cfg, st, attr.span)? {
                            let rest = &attr.inner[split + 1.min(attr.inner.len() - split)..];
                            let head = rest.first().and_then(|t| match t {
                                Tt::Tok(tok) => seg_text(tok.tok, st.ctx.interner),
                                _ => None,
                            });
                            match head.as_deref() {
                                Some("macro_export") => exported = true,
                                Some("cfg") => {
                                    if let Some(Tt::Delim(_, group, _)) = rest.get(1) {
                                        cfg_off = !builtin::eval_cfg(group, &st.ctx.cfg, st, attr.span)?;
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    i = attr.end;
                    continue;
                }
                if let Some(def) = macro_rules_at(trees, i, st.ctx.interner) {
                    if !cfg_off {
                        let body = match &trees[def.group] {
                            Tt::Delim(_, inner, _) => inner.clone(),
                            _ => unreachable!(),
                        };
                        st.check_dup_export(def.name, def.name_span, exported)?;
                        check_def_form(trees, &def)?;
                        let mut compiled = compile_macro(def.name, def.name_span, &body, exported, def.span, &st.strings, st.ctx.interner)?;
                        compiled.local_def = !at_module_list;
                        let idx = st.register(Arc::new(compiled), exported, false);
                        if at_module_list {
                            st.module_defs.insert((module.clone(), def.name), idx);
                        }
                    }
                    exported = false;
                    cfg_off = false;
                    i = def.end;
                    continue;
                }
                // Any other tree here is the node the pending
                // attributes attach to, so they are spent: a `#[cfg]`
                // on a plain item must not leak onto a macro
                // definition that comes later in the same list.
                exported = false;
                cfg_off = false;
                if tok_at(trees, i).map(|t| t.tok) == Some(Tok::Mod)
                    && matches!(tok_at(trees, i + 1).map(|t| t.tok), Some(Tok::Ident(_)))
                    && matches!(trees.get(i + 2), Some(Tt::Delim(Delim::Brace, _, _)))
                {
                    let sym = tok_at(trees, i + 1).and_then(|t| seg_sym(t.tok, st.ctx.interner));
                    let Tt::Delim(_, inner, _) = &trees[i + 2] else { unreachable!() };
                    let inner = inner.clone();
                    if let Some(sym) = sym {
                        module.push(sym);
                    }
                    let r = walk(st, &inner, module, true, uses);
                    if sym.is_some() {
                        module.pop();
                    }
                    r?;
                    i += 3;
                    continue;
                }
                if at_module_list && let Some((public, content, end)) = use_span_at(trees, i) {
                    for (segs, leading, alias) in collect_use_sites(&trees[content..end - 1], &[], st.ctx.interner) {
                        uses.push((module.clone(), segs, leading, alias, public));
                    }
                    i = end;
                    continue;
                }
                if let Tt::Delim(_, inner, _) = &trees[i] {
                    let inner = inner.clone();
                    walk(st, &inner, module, false, uses)?;
                }
                i += 1;
            }
            Ok(())
        }
        let mut uses: Vec<UseSite> = Vec::new();
        let mut module: Vec<Sym> = self.ctx.module_path.clone();
        walk(self, trees, &mut module, true, &mut uses)?;
        // Public re-exports first, so other modules' imports can resolve
        // through the path table they create.
        for (module, segs, leading, alias, public) in &uses {
            if *public && let Some(idx) = self.resolve_for_use(segs, *leading, module) {
                self.by_path.insert((module.clone(), *alias), idx);
            }
        }
        for (module, segs, leading, alias, _) in &uses {
            if let Some(idx) = self.resolve_for_use(segs, *leading, module) {
                self.module_imports.insert((module.clone(), *alias), idx);
            } else if self.ctx.interner.get(*alias) != "_"
                && let Some(canon) = self.std_builtin_macro(segs)
            {
                self.module_builtin_alias.insert((module.clone(), *alias), canon);
            }
        }
        Ok(())
    }

    /// Resolves a `use` target in the prescan tables, from `from` module:
    /// exported names, `pub use` path entries, and the defining module's
    /// own definitions (for same-module re-exports).
    fn resolve_for_use(&self, segs: &[Seg], leading_colon: bool, from: &[Sym]) -> Option<u32> {
        if segs.is_empty() {
            return None;
        }
        let last = segs[segs.len() - 1].sym;
        let texts: Vec<&str> = segs.iter().map(|s| s.text.as_str()).collect();
        let middle: Vec<Sym> = segs[..segs.len() - 1].iter().map(|s| s.sym).collect();
        let path = |module: &[Sym]| self.by_path.get(&(module.to_vec(), last)).copied();
        match texts[0] {
            _ if segs.len() == 1 && !leading_colon => {
                self.module_defs.get(&(from.to_vec(), last)).copied().or_else(|| self.module_imports.get(&(from.to_vec(), last)).copied())
            }
            "crate" => {
                let module = &middle[1.min(middle.len())..];
                if module.is_empty() { self.exported.get(&last).copied() } else { path(module) }
            }
            "self" => {
                let mut module = from.to_vec();
                module.extend_from_slice(&middle[1.min(middle.len())..]);
                path(&module).or_else(|| self.module_defs.get(&(module, last)).copied())
            }
            "super" => {
                let supers = texts.iter().take_while(|&&t| t == "super").count();
                let keep = from.len().saturating_sub(supers);
                let mut module: Vec<Sym> = from[..keep].to_vec();
                module.extend_from_slice(&middle[supers.min(middle.len())..]);
                path(&module)
            }
            _ => {
                if leading_colon {
                    return if middle.is_empty() { self.exported.get(&last).copied() } else { path(&middle) };
                }
                let mut module = from.to_vec();
                module.extend_from_slice(&middle);
                path(&module).or_else(|| path(&middle)).or_else(|| self.module_defs.get(&(module.clone(), last)).copied())
            }
        }
    }

    /// Compiles one worklist macro seed into this expander's path
    /// tables. The seed's string table is appended to this run's table
    /// and its tokens are remapped before compilation, so the compiled
    /// definition reads strings from the right table. A seed whose
    /// tokens hold no `macro_rules!` definition is ignored: the
    /// worklist only seeds outline-proven definitions.
    fn seed_macro(&mut self, seed: &MacroSeed) -> Result<(), Diag> {
        let offset = self.strings.len() as u32;
        self.strings.extend(seed.strings.iter().cloned());
        let toks: Vec<Token> = seed
            .tokens
            .iter()
            .map(|t| {
                let mut tok = t.tok;
                tok.shift_strings(offset);
                Token { tok, span: t.span }
            })
            .collect();
        let (trees, balanced) = build_trees(&toks);
        if !balanced {
            return Ok(());
        }
        let tts: Vec<Tt> = trees.iter().map(tt_from_tree).collect();
        let mut i = 0;
        while i < tts.len() {
            if let Some(attr) = attr_at(&tts, i, self.ctx.interner) {
                i = attr.end;
                continue;
            }
            if let Some(def) = macro_rules_at(&tts, i, self.ctx.interner) {
                let body = match &tts[def.group] {
                    Tt::Delim(_, inner, _) => inner.clone(),
                    _ => return Ok(()),
                };
                let at_root = seed.path.is_empty();
                let compiled = compile_macro(def.name, def.name_span, &body, at_root, def.span, &self.strings, self.ctx.interner)?;
                let idx = self.register(Arc::new(compiled), at_root, false);
                self.by_path.insert((seed.path.clone(), def.name), idx);
                if let Some(module) = &seed.import_into {
                    self.module_imports.insert((module.clone(), def.name), idx);
                }
                return Ok(());
            }
            i += 1;
        }
        Ok(())
    }

    /// Stores a compiled definition. `path` also puts it in the crate
    /// root table; `textual` makes it visible from this point on.
    /// Two `#[macro_export]` definitions under one name do not shadow:
    /// the second is a definition error (rustc E0428). The same def
    /// seen again (same name span, from the walk after the prescan)
    /// is not a duplicate.
    fn check_dup_export(&self, name: Sym, name_span: Span, exported: bool) -> Result<(), Diag> {
        if exported
            && let Some(&idx) = self.exported.get(&name)
            && self.defs[idx as usize].name_span != name_span
        {
            return Err(err(
                C_DEF,
                name_span,
                format!("macro `{}` is exported more than once", self.ctx.interner.get(name)),
                "Rename one of the exported macros.",
            )
            .with_label(self.defs[idx as usize].name_span, "first exported here"));
        }
        Ok(())
    }

    fn register(&mut self, def: Arc<MacroDef>, path: bool, textual: bool) -> u32 {
        let idx = self.defs.len() as u32;
        if path {
            self.exported.insert(def.name, idx);
        }
        if textual {
            self.textual.push((def.name, idx));
        }
        self.defs.push(def);
        idx
    }

    /// Resolves a macro call path to a definition index. This is the
    /// single macro lookup entry point: today it reads this single
    /// file's textual scope, imports, and path tables. S7's frozen
    /// `Program::macro_binding` query is landed, but it answers from a
    /// collected `Program`, which holds no macro defs yet (expansion
    /// runs before parse and collect, and macro answers are `Absent`
    /// there by design until W-RESOLVE). When the 6.1 worklist makes
    /// collect own macro defs, this function is the one place that
    /// moves behind `macro_binding`; nothing else changes.
    fn lookup_macro(&self, segs: &[Seg], leading_colon: bool) -> Option<u32> {
        if segs.is_empty() {
            return None;
        }
        let last = segs[segs.len() - 1].sym;
        let texts: Vec<&str> = segs.iter().map(|s| s.text.as_str()).collect();
        let by_module = |module: &[Sym]| -> Option<u32> { self.by_path.get(&(module.to_vec(), last)).copied() };
        if !leading_colon && segs.len() == 1 {
            if let Some(&(_, idx)) = self.imports.iter().rev().find(|(n, _)| *n == last) {
                return Some(idx);
            }
            if let Some(&(_, idx)) = self.textual.iter().rev().find(|(n, _)| *n == last) {
                return Some(idx);
            }
            if let Some(idx) = self.module_imports.get(&(self.module.clone(), last)).copied() {
                return Some(idx);
            }
            // An exported macro lives in the crate root's macro
            // namespace, so a plain call in the root module finds it
            // whatever the textual order.
            return if self.module.is_empty() { self.exported.get(&last).copied() } else { None };
        }
        // Path forms, resolved against module paths from the crate root.
        let middle: Vec<Sym> = segs[..segs.len() - 1].iter().map(|s| s.sym).collect();
        match texts[0] {
            "crate" => {
                let module = &middle[1.min(middle.len())..];
                if module.is_empty() { self.exported.get(&last).copied().or_else(|| by_module(module)) } else { by_module(module) }
            }
            "self" => {
                let mut module = self.module.clone();
                module.extend_from_slice(&middle[1.min(middle.len())..]);
                if module.is_empty() { self.exported.get(&last).copied().or_else(|| by_module(&module)) } else { by_module(&module) }
            }
            "super" => {
                let supers = texts.iter().take_while(|&&t| t == "super").count();
                let keep = self.module.len().saturating_sub(supers);
                let mut module: Vec<Sym> = self.module[..keep].to_vec();
                module.extend_from_slice(&middle[supers.min(middle.len())..]);
                by_module(&module)
            }
            _ => {
                if leading_colon {
                    return if middle.is_empty() { self.exported.get(&last).copied() } else { by_module(&middle) };
                }
                // Relative to the current module, then from the root, as
                // a plain path resolves in one crate.
                let mut module = self.module.clone();
                module.extend_from_slice(&middle);
                by_module(&module)
                    .or_else(|| by_module(&middle))
                    .or_else(|| if middle.is_empty() { self.exported.get(&last).copied() } else { None })
            }
        }
    }

    /// Matches and transcribes one user macro call against `def`, with
    /// the expansion cache in front (ARCH 6.5). The result is one
    /// expansion step only, never chased: callers re-walk it.
    pub fn transcribe_call(&mut self, def: &MacroDef, call: &Call, depth: u32) -> Result<Vec<Tt>, Diag> {
        use std::sync::atomic::Ordering;
        self.check_depth(depth, 0, call.span, || def.name_text.clone())?;
        let key = CacheKey {
            def_fingerprint: def.fingerprint,
            input_hash: hash_tts(&call.inner, &self.strings),
            input_span_hash: span_hash_tts(&call.inner, 0),
            call_file: call.span.file.0,
            call_lo: call.span.lo,
            call_hi: call.span.hi,
            call_ctxt: call.span.ctxt.0,
            cfg_hash: self.ctx.cfg.hash(),
            edition: 2024,
            deps_hash: 0,
            layout: if def.pos_sensitive { span_layout_hash(&call.inner) } else { 0 },
        };
        if let Some((cached, strings, old_ctxt)) = expansion_cache().lock().unwrap().get(&key).cloned() {
            CACHE_HITS.fetch_add(1, Ordering::Relaxed);
            let ctxt =
                register_expansion(crate::diag::Expansion { macro_def: DefId::PLACEHOLDER, call_span: call.span, parent: call.span.ctxt });
            register_hygiene(ctxt, HygieneMark { def_span: def.name_span, local_def: def.local_def });
            let mut out = cached;
            shift_tts(&mut out, self.strings.len() as u32);
            self.strings.extend(strings);
            restamp_ctxt(&mut out, old_ctxt, ctxt);
            return Ok(out);
        }
        CACHE_MISSES.fetch_add(1, Ordering::Relaxed);
        let mut chosen: Option<(usize, BindMap)> = None;
        let mut matcher = match_::Matcher::new(self.ctx.interner, self.ctx.known, &self.strings, call.span);
        for (arm_i, arm) in def.arms.iter().enumerate() {
            match match_::match_arm(&mut matcher, &arm.matcher, &call.inner)? {
                match_::ArmMatch::Match(binds) => {
                    chosen = Some((arm_i, binds));
                    break;
                }
                match_::ArmMatch::NoMatch => {}
                // Local ambiguity is fatal: rustc stops at the first
                // ambiguous token, it does not fall through to a later arm.
                match_::ArmMatch::Ambiguous => {
                    return Err(err(
                        C_AMBIG,
                        call.span,
                        format!("local ambiguity when calling macro `{}!`", def.name_text),
                        "Make the matcher decide each token's role without guessing between fragments.",
                    )
                    .with_label(def.def_span, "the macro is defined here"));
                }
                // A fragment parser that began and failed is rustc's
                // hard error: the call fails here instead of falling
                // through to a later arm that token-matches the input.
                match_::ArmMatch::BadFragment => {
                    return Err(err(
                        C_CALL,
                        call.span,
                        format!("a fragment in this call to `{}!` does not parse", def.name_text),
                        "Check the call tokens against the fragment kinds in the macro's rules.",
                    )
                    .with_label(def.def_span, "the macro is defined here"));
                }
            }
        }
        let Some((arm_i, binds)) = chosen else {
            return Err(err(
                C_CALL,
                call.span,
                format!("no rules expected this input to macro `{}!`", def.name_text),
                "Check the call against the macro's rules.",
            )
            .with_label(def.def_span, "the macro is defined here"));
        };
        let ctxt =
            register_expansion(crate::diag::Expansion { macro_def: DefId::PLACEHOLDER, call_span: call.span, parent: call.span.ctxt });
        register_hygiene(ctxt, HygieneMark { def_span: def.name_span, local_def: def.local_def });
        let out = transcribe::transcribe(&def.arms[arm_i].template, &binds, ctxt, call.span, self.ctx.interner)
            .map_err(|d| d.with_label(def.def_span, "the macro is defined here"))?;
        let count = count_tokens(&out);
        if count > 1_000_000 {
            return Err(err(
                C_CAP,
                call.span,
                format!("expansion of `{}!` is too large", def.name_text),
                "Simplify the macro or the call.",
            ));
        }
        self.total_tokens += count;
        if self.total_tokens > 16_000_000 {
            return Err(err(C_CAP, call.span, "total expanded size limit reached", "Simplify the macros in this file."));
        }
        let mut cached = out.clone();
        let mut strings = Vec::new();
        own_strings(&mut cached, &self.strings, &mut strings);
        expansion_cache().lock().unwrap().insert(key, (cached, strings, ctxt));
        Ok(out)
    }
}

/// Re-contexts cached output: tokens stamped with the cached expansion's
/// context take the new expansion's context instead (ARCH 6.5).
fn restamp_ctxt(trees: &mut [Tt], old: CtxtId, new: CtxtId) {
    fn fix(span: &mut Span, old: CtxtId, new: CtxtId) {
        if span.ctxt == old {
            span.ctxt = new;
        }
    }
    for tree in trees {
        match tree {
            Tt::Tok(t) => fix(&mut t.span, old, new),
            Tt::Delim(_, inner, span) => {
                fix(span, old, new);
                restamp_ctxt(inner, old, new);
            }
            // Fragment tokens are the caller's, not the macro body's.
            Tt::Frag(_, _, _) => {}
        }
    }
}

/// An attribute the walker found at a list position.
pub struct AttrInfo {
    /// Path as written, segments joined by `::`.
    pub path: String,
    /// The trees inside the brackets, after the path (raw, with any
    /// leading `=` or group intact, starting past the path tokens).
    pub inner: Vec<Tt>,
    /// Index just past this attribute in the list it was found in.
    pub end: usize,
    pub span: Span,
    pub inner_attr: bool,
}

/// If an attribute (`#[...]` or `#![...]`) starts at `trees[i]`, reads it.
pub fn attr_at(trees: &[Tt], i: usize, interner: &Interner) -> Option<AttrInfo> {
    if !matches!(trees.get(i), Some(Tt::Tok(t)) if t.tok == Tok::Pound) {
        return None;
    }
    let span = trees[i].span();
    let mut j = i + 1;
    let mut inner_attr = false;
    if tok_at(trees, j).map(|t| t.tok) == Some(Tok::Bang) {
        inner_attr = true;
        j += 1;
    }
    let Tt::Delim(Delim::Bracket, body, _) = trees.get(j)? else { return None };
    // `#[unsafe(..)]` reads as one attribute named `unsafe`, so no
    // attribute the expander acts on (cfg and kin) matches it.
    if tok_at(body, 0).map(|t| t.tok) == Some(Tok::Unsafe)
        && let Some(Tt::Delim(Delim::Paren, group, _)) = body.get(1)
    {
        return Some(AttrInfo { path: "unsafe".to_string(), inner: group.clone(), end: j + 1, span, inner_attr });
    }
    // Path: segments joined by :: from the front of the body. A leading
    // `::` stays in the path text, so `#[::cfg(..)]` is not `cfg`.
    let global = tok_at(body, 0).map(|t| t.tok) == Some(Tok::PathSep);
    let mut segs = Vec::new();
    let mut k = usize::from(global);
    loop {
        match tok_at(body, k).map(|t| t.tok) {
            Some(t) if is_seg_tok(t) => {
                segs.push(t);
                k += 1;
            }
            _ => break,
        }
        if tok_at(body, k).map(|t| t.tok) == Some(Tok::PathSep) {
            k += 1;
        } else {
            break;
        }
    }
    if segs.is_empty() {
        return None;
    }
    // cfg and friends read only the group's trees; a `path(...)` attr
    // keeps the group as its input, a `path = v` keeps from the `=` on.
    let inner = match body.get(k) {
        Some(Tt::Delim(_, group, _)) => group.clone(),
        _ => body[k..].to_vec(),
    };
    let path = segs.iter().filter_map(|t| seg_text(*t, interner)).collect::<Vec<_>>().join("::");
    let path = if global { format!("::{path}") } else { path };
    Some(AttrInfo { path, inner, end: j + 1, span, inner_attr })
}

/// A `macro_rules! name <group>` definition found in a tree list.
pub struct DefStart {
    pub name: Sym,
    pub name_span: Span,
    pub group: usize,
    pub end: usize,
    pub span: Span,
    /// The delimiter of the definition body group.
    pub delim: Delim,
}

/// A `macro_rules!` definition whose body is not brace-delimited must
/// end with `;`, like every item macro call (rustc: "macros that
/// expand to items must be delimited with braces or followed by a
/// semicolon").
fn check_def_form(trees: &[Tt], def: &DefStart) -> Result<(), Diag> {
    if def.delim != Delim::Brace && tok_at(trees, def.group + 1).map(|t| t.tok) != Some(Tok::Semi) {
        return Err(err(
            C_CALL,
            def.span,
            "a macro definition not delimited with braces must end with `;`",
            "Write the definition with braces or end it with `;`.",
        ));
    }
    Ok(())
}

/// If a `macro_rules!` definition starts at `trees[i]`, describes it.
pub fn macro_rules_at(trees: &[Tt], i: usize, interner: &Interner) -> Option<DefStart> {
    let head = tok_at(trees, i)?;
    if seg_text(head.tok, interner).as_deref() != Some("macro_rules") {
        return None;
    }
    if tok_at(trees, i + 1).map(|t| t.tok) != Some(Tok::Bang) {
        return None;
    }
    let name_tok = tok_at(trees, i + 2)?;
    let Tok::Ident(name) = name_tok.tok else { return None };
    match trees.get(i + 3) {
        Some(Tt::Delim(d, _, group_span)) => {
            let mut end = i + 4;
            if *d != Delim::Brace && tok_at(trees, end).map(|t| t.tok) == Some(Tok::Semi) {
                end += 1;
            }
            Some(DefStart { name, name_span: name_tok.span, group: i + 3, end, span: head.span.to(*group_span), delim: *d })
        }
        _ => None,
    }
}

/// If a macro call starts at `trees[i]`, describes it (path, head trees,
/// and the index of its argument group).
fn path_call_at(trees: &[Tt], i: usize, interner: &Interner) -> Option<(Vec<Seg>, bool, usize)> {
    let mut j = i;
    let mut leading_colon = false;
    if tok_at(trees, j).map(|t| t.tok) == Some(Tok::PathSep) {
        leading_colon = true;
        j += 1;
    }
    let mut segs: Vec<Seg> = Vec::new();
    loop {
        let seg_tok = tok_at(trees, j)?;
        let sym = seg_sym(seg_tok.tok, interner)?;
        let text = seg_text(seg_tok.tok, interner)?;
        segs.push(Seg { sym, text, span: seg_tok.span });
        j += 1;
        match tok_at(trees, j).map(|t| t.tok) {
            Some(Tok::Bang) => {
                return match trees.get(j + 1) {
                    Some(Tt::Delim(_, _, _)) => Some((segs, leading_colon, j + 1)),
                    _ => None,
                };
            }
            Some(Tok::PathSep) => j += 1,
            _ => return None,
        }
    }
}

/// True when the item at `i` is a function: item qualifiers, then `fn`.
/// A `#[test]` attribute drops only this shape in a non-test build.
fn next_is_fn(trees: &[Tt], mut i: usize) -> bool {
    loop {
        match tok_at(trees, i).map(|t| t.tok) {
            Some(Tok::Pub) => {
                i += 1;
                if matches!(trees.get(i), Some(Tt::Delim(Delim::Paren, _, _))) {
                    i += 1;
                }
            }
            Some(Tok::Const | Tok::Async | Tok::Unsafe | Tok::Extern | Tok::Str(..)) => i += 1,
            Some(Tok::Fn) => return true,
            _ => return false,
        }
    }
}

/// True when trees start an item (`fn`, `pub struct`, an attribute, ...),
/// for the item-position macro rules. A leading item fragment counts,
/// and any other fragment is looked through to its first tokens.
fn starts_item(trees: &[Tt], interner: &Interner) -> bool {
    // Only the head is read: attributes and qualifiers, then the keyword
    // and one tree after it. Copy that much, not the whole tail callers
    // pass (a copy per call made long macro inputs quadratic).
    let head_tree = |t: &Tt| match t {
        Tt::Frag(..) | Tt::Delim(Delim::Bracket | Delim::Paren, _, _) => true,
        Tt::Tok(t) => matches!(t.tok, Tok::Pound | Tok::Bang | Tok::Pub | Tok::Const | Tok::Async | Tok::Unsafe | Tok::Extern),
        Tt::Delim(..) => false,
    };
    let head = trees.iter().take_while(|t| head_tree(t)).count() + 2;
    // Splice leading fragments in place so a vis fragment before the
    // item keyword (as in `$v:vis fn`) still reads as an item start.
    let mut flat: Vec<Tt> = trees[..head.min(trees.len())].to_vec();
    loop {
        match flat.first() {
            Some(Tt::Frag(FragKind::Item, _, _)) => return true,
            Some(Tt::Frag(_, inner, _)) => {
                let inner = inner.clone();
                flat.splice(0..1, inner);
            }
            _ => break,
        }
    }
    let trees: &[Tt] = &flat;
    let mut i = 0;
    // Skip attributes and item qualifiers to the item keyword. An
    // attribute whose body is a fragment (`#[$m]`) has no readable
    // path for attr_at; skip its two trees directly.
    loop {
        if let Some(attr) = attr_at(trees, i, interner) {
            i = attr.end;
        } else if tok_at(trees, i).map(|t| t.tok) == Some(Tok::Pound) && matches!(trees.get(i + 1), Some(Tt::Delim(Delim::Bracket, _, _))) {
            i += 2;
        } else {
            break;
        }
    }
    loop {
        match tok_at(trees, i).map(|t| t.tok) {
            Some(Tok::Pub) => {
                i += 1;
                if matches!(trees.get(i), Some(Tt::Delim(Delim::Paren, _, _))) {
                    i += 1;
                }
            }
            Some(Tok::Const) => {
                // `const fn` is a qualified fn; `const NAME` is the item.
                if matches!(tok_at(trees, i + 1).map(|t| t.tok), Some(Tok::Ident(_) | Tok::Underscore)) {
                    return true;
                }
                i += 1;
            }
            Some(Tok::Async | Tok::Unsafe | Tok::Extern) => i += 1,
            // The ABI string of `extern "C" fn`.
            Some(Tok::Str(..)) if i > 0 && tok_at(trees, i - 1).map(|t| t.tok) == Some(Tok::Extern) => i += 1,
            Some(Tok::Fn | Tok::Struct | Tok::Enum | Tok::Impl | Tok::Mod | Tok::Trait | Tok::Type | Tok::Static | Tok::Use) => {
                return true;
            }
            Some(t) if seg_text(t, interner).as_deref() == Some("macro_rules") => return true,
            _ => return false,
        }
    }
}

/// The end index of one item starting at `start` in a tree list, for
/// dropping `#[cfg(off)]` items before expansion (ARCH 6.1 step order).
/// None when the item shape is not one this can bound with confidence.
fn item_end(trees: &[Tt], start: usize, interner: &Interner) -> Option<usize> {
    if !starts_item(&trees[start..], interner) && tok_at(trees, start).map(|t| t.tok) != Some(Tok::Static) {
        // `static` and `const` items reach starts_item through the
        // qualifier loop only when directly named; accept them plainly.
        match tok_at(trees, start).map(|t| t.tok) {
            Some(Tok::Const | Tok::Static) => {}
            _ => return None,
        }
    }
    for j in start..trees.len() {
        match &trees[j] {
            Tt::Tok(t) if t.tok == Tok::Semi => return Some(j + 1),
            Tt::Delim(Delim::Brace, _, _) => {
                if tok_at(trees, j + 1).map(|t| t.tok) == Some(Tok::Semi) {
                    return Some(j + 2);
                }
                return Some(j + 1);
            }
            _ => {}
        }
    }
    None
}

/// True when the first call argument in `trees` is written as one string
/// literal (a fragment that holds one counts, as the literal was written
/// by the caller and only forwarded).
fn is_str_lit_arg(trees: &[Tt]) -> bool {
    let end = trees.iter().position(|t| t.is_tok(Tok::Comma)).unwrap_or(trees.len());
    match &trees[..end] {
        [Tt::Tok(t)] => matches!(t.tok, Tok::Str(..)),
        [Tt::Frag(_, inner, _)] => is_str_lit_arg(inner),
        _ => false,
    }
}

/// Stamps the first argument of an expanded format-macro call, when it is
/// one string literal, as macro-produced: the parser then rejects named
/// captures in it, as rustc does for `println!(concat!("{x}", ""))`.
fn mark_format_str(expanded: &mut [Tt], span: Span) {
    fn stamp(t: &mut Token, span: Span) {
        let ctxt = register_expansion(crate::diag::Expansion { macro_def: DefId::PLACEHOLDER, call_span: span, parent: t.span.ctxt });
        mark_no_capture(ctxt);
        t.span.ctxt = ctxt;
    }
    fn first_str(trees: &mut [Tt], span: Span) {
        match trees {
            [Tt::Tok(t)] if matches!(t.tok, Tok::Str(..)) => stamp(t, span),
            [Tt::Frag(_, inner, _)] => first_str(inner, span),
            _ => {}
        }
    }
    let end = expanded.iter().position(|t| t.is_tok(Tok::Comma)).unwrap_or(expanded.len());
    if end == 1 {
        first_str(&mut expanded[..1], span);
    }
}

/// The end index of one non-item node starting at `start`: a statement
/// (let, expression, or block-like), a match arm, or a comma-ended part
/// (struct field, enum variant, parameter). Delimited groups are one
/// tree, so a top-level `;`, `,`, `=>`, or a brace group bounds the
/// node. A brace group ends the node unless an operator, `else`, or
/// `;` follows it. With no terminator the node is the list's tail.
/// Used to drop `#[cfg(off)]` nodes exactly as rustc does. A brace
/// group in a head position does not end the node when what follows
/// it can only continue the head: a second brace group (the real
/// block after a struct literal scrutinee), `=>`, `if`, or `in` (a
/// struct pattern), or any operator. A brace group that starts the
/// node is the node's own block and always ends it.
fn node_end(trees: &[Tt], start: usize) -> Option<usize> {
    if start >= trees.len() {
        return None;
    }
    let mut j = start;
    while j < trees.len() {
        match &trees[j] {
            Tt::Tok(t) if t.tok == Tok::Semi => return Some(j + 1),
            Tt::Tok(t) if t.tok == Tok::Comma => return Some(j + 1),
            Tt::Tok(t) if t.tok == Tok::FatArrow => {
                // A match arm: a block body, or up to the next comma.
                if matches!(trees.get(j + 1), Some(Tt::Delim(Delim::Brace, _, _))) {
                    let e = j + 2;
                    return Some(if tok_at(trees, e).map(|t| t.tok) == Some(Tok::Comma) { e + 1 } else { e });
                }
                let mut k = j + 1;
                while k < trees.len() {
                    if matches!(&trees[k], Tt::Tok(t) if t.tok == Tok::Comma) {
                        return Some(k + 1);
                    }
                    k += 1;
                }
                return Some(trees.len());
            }
            Tt::Delim(Delim::Brace, _, _) if j > start && matches!(trees.get(j + 1), Some(Tt::Delim(Delim::Brace, _, _))) => {
                // A struct literal or pattern in a head position; the
                // next brace group is the node's block. Step over the
                // head group and let that group end the node.
                j += 1;
            }
            Tt::Delim(Delim::Brace, _, _) => match tok_at(trees, j + 1).map(|t| t.tok) {
                Some(Tok::Semi) => return Some(j + 2),
                Some(Tok::Comma) => return Some(j + 2),
                Some(Tok::Else) => j += 2,
                // A struct pattern's guard, arm arrow, or `for .. in`.
                Some(Tok::FatArrow | Tok::If | Tok::In) if j > start => j += 1,
                Some(
                    Tok::Dot
                    | Tok::Question
                    | Tok::Plus
                    | Tok::Minus
                    | Tok::Star
                    | Tok::Slash
                    | Tok::Percent
                    | Tok::EqEq
                    | Tok::Ne
                    | Tok::Lt
                    | Tok::Gt
                    | Tok::Le
                    | Tok::Ge
                    | Tok::AndAnd
                    | Tok::OrOr
                    | Tok::Amp
                    | Tok::Pipe
                    | Tok::Caret
                    | Tok::Shl
                    | Tok::As
                    | Tok::PlusEq
                    | Tok::MinusEq
                    | Tok::StarEq
                    | Tok::SlashEq
                    | Tok::PercentEq
                    | Tok::AmpEq
                    | Tok::PipeEq
                    | Tok::CaretEq
                    | Tok::ShlEq
                    | Tok::Shr
                    | Tok::ShrEq
                    | Tok::Eq
                    | Tok::DotDot
                    | Tok::DotDotEq,
                ) => j += 1,
                _ => return Some(j + 1),
            },
            _ => j += 1,
        }
    }
    Some(trees.len())
}

/// Takes `trees[i]` out by value, leaving a placeholder behind.
fn take(trees: &mut [Tt], i: usize) -> Tt {
    std::mem::replace(&mut trees[i], Tt::Tok(Token { tok: Tok::Eof, span: Span::default() }))
}

impl<'a> Expander<'a> {
    /// Errors when a call to `name()!` at `depth`, whose own expansion
    /// reaches `extra` levels deeper (see `builtin::rustc_depth`), would
    /// pass the recursion limit. Past `RECURSION_CAP` the limit is
    /// lust's, not the crate's, and the message says so.
    fn check_depth(&self, depth: u32, extra: u32, span: Span, name: impl FnOnce() -> String) -> Result<(), Diag> {
        if depth + extra < self.recursion_limit {
            return Ok(());
        }
        let name = name();
        if self.limit_capped {
            return Err(err(
                C_CAP,
                span,
                format!("expansion depth reached lust's limit of {RECURSION_CAP} while expanding `{name}!`"),
                "Lust expands macros at most 2048 levels deep, whatever the crate's recursion limit.",
            ));
        }
        Err(err(C_CAP, span, format!("recursion limit reached while expanding `{name}!`"), "Give the macro a base case it can reach."))
    }

    /// Expands one tree list, outermost first (ARCH 6.1). `depth` is the
    /// expansion nesting depth of this list; `item_list` marks the file
    /// root and module bodies, where item-position rules apply;
    /// `stmt_list` marks a block body, where a brace-delimited macro
    /// call at a statement boundary is a whole statement; `nest`
    /// bounds delimiter recursion so pathological input cannot overflow.
    /// Every recursion of expansion passes through here. When the
    /// current stack segment is used up, the list expands on a new
    /// thread with a fresh stack (rustc grows its stack the same way),
    /// so deep expansion cannot overflow the native stack, whatever
    /// thread it started on.
    pub fn expand_list(&mut self, trees: Vec<Tt>, depth: u32, item_list: bool, stmt_list: bool, nest: u32) -> Result<Vec<Tt>, Diag> {
        let used = self.stack_base.abs_diff(stack_addr());
        if used < self.stack_room {
            return self.expand_list_here(trees, depth, item_list, stmt_list, nest);
        }
        let span = trees.first().map_or(Span::default(), Tt::span);
        if self.stack_below + used > STACK_TOTAL {
            return Err(err(C_CAP, span, "macro expansion nests too deeply", "Simplify the macros or the nesting in this file."));
        }
        let saved = (self.stack_base, self.stack_room, self.stack_below);
        self.stack_below += used;
        let joined = std::thread::scope(|scope| {
            std::thread::Builder::new()
                .name("lust-expand".into())
                .stack_size(STACK_HOP)
                .spawn_scoped(scope, || {
                    self.stack_base = stack_addr();
                    self.stack_room = STACK_HOP_ROOM;
                    self.expand_list_here(trees, depth, item_list, stmt_list, nest)
                })
                .map(|thread| thread.join())
        });
        (self.stack_base, self.stack_room, self.stack_below) = saved;
        match joined {
            Ok(Ok(result)) => result,
            Ok(Err(panic)) => std::panic::resume_unwind(panic),
            Err(_) => Err(err(C_CAP, span, "macro expansion nests too deeply for this thread's stack", "Simplify the macros or the nesting in this file.")),
        }
    }

    /// `expand_list` on the current stack segment.
    fn expand_list_here(&mut self, mut trees: Vec<Tt>, depth: u32, item_list: bool, stmt_list: bool, nest: u32) -> Result<Vec<Tt>, Diag> {
        if nest > 1000 {
            return Ok(trees);
        }
        let mut out: Vec<Tt> = Vec::with_capacity(trees.len());
        let mut pending_macro_use = false;
        let mut i = 0;
        while i < trees.len() {
            // An attribute run: cfg stripping first (ARCH 6.1 step 1),
            // then macro definition attributes, then plain passthrough.
            if let Some(first) = attr_at(&trees, i, self.ctx.interner) {
                i = self.attr_run(&mut trees, i, first, &mut pending_macro_use, &mut out, item_list, depth)?;
                continue;
            }
            // A macro definition never reaches the parser.
            if let Some(def) = macro_rules_at(&trees, i, self.ctx.interner) {
                self.define_macro(&trees, &def, false, !item_list)?;
                i = def.end;
                pending_macro_use = false;
                continue;
            }
            // An inline module: its body is its own macro scope and path.
            if tok_at(&trees, i).map(|t| t.tok) == Some(Tok::Mod)
                && matches!(tok_at(&trees, i + 1).map(|t| t.tok), Some(Tok::Ident(_)))
                && matches!(trees.get(i + 2), Some(Tt::Delim(Delim::Brace, _, _)))
            {
                let (name_sym, name_ok) = match tok_at(&trees, i + 1) {
                    Some(t) => (seg_sym(t.tok, self.ctx.interner), true),
                    None => (None, false),
                };
                let _ = name_ok;
                let group = take(&mut trees, i + 2);
                let Tt::Delim(_, inner, gspan) = group else { unreachable!() };
                let textual_len = self.textual.len();
                let imports_len = self.imports.len();
                if let Some(sym) = name_sym {
                    self.module.push(sym);
                }
                let expanded = self.expand_list(inner, depth, true, false, nest + 1);
                if name_sym.is_some() {
                    self.module.pop();
                }
                let inner = expanded?;
                let added: Vec<(Sym, u32)> = self.textual[textual_len..].to_vec();
                self.textual.truncate(textual_len);
                self.imports.truncate(imports_len);
                if pending_macro_use {
                    self.textual.extend(added);
                }
                pending_macro_use = false;
                out.push(take(&mut trees, i));
                out.push(take(&mut trees, i + 1));
                out.push(Tt::Delim(Delim::Brace, inner, gspan));
                i += 3;
                continue;
            }
            // A `use` item: register what it imports, emit it unchanged.
            if let Some(end) = self.use_item_at(&trees, i, item_list) {
                for k in i..end {
                    let tree = take(&mut trees, k);
                    out.push(tree);
                }
                i = end;
                pending_macro_use = false;
                continue;
            }
            // A parser-owned macro call (println! and kin): emit it as
            // written, with its argument trees expanded. This is a
            // structural case, not an expansion step: re-walking the
            // same call as new output would never finish.
            if let Some((segs, leading_colon, group_idx)) = path_call_at(&trees, i, self.ctx.interner)
                && self.lookup_macro(&segs, leading_colon).is_none()
                && (segs.len() == 1 || matches!(segs.first().map(|s| s.text.as_str()), Some("std" | "core" | "alloc")))
                && builtin::is_passthrough(segs.last().map_or("", |s| &s.text))
            {
                let (delim, inner, group_span) = match &trees[group_idx] {
                    Tt::Delim(d, inner, span) => (*d, inner.clone(), *span),
                    _ => unreachable!(),
                };
                // The parser owns only the plain `name!` form, so a
                // path-qualified call (`std::println!`) keeps just its
                // last segment and the bang. The name spans the whole
                // path: rustc reports a panic at the path's start.
                let start = tok_at(&trees, i).map(|t| t.span);
                let mut name_tt = take(&mut trees, group_idx - 2);
                if let (Tt::Tok(t), Some(start)) = (&mut name_tt, start)
                    && (start.file, start.ctxt) == (t.span.file, t.span.ctxt)
                {
                    t.span = start.to(t.span);
                }
                out.push(name_tt);
                out.push(take(&mut trees, group_idx - 1));
                let fmt_name = segs.last().map_or("", |s| s.text.as_str());
                let written_lit = is_str_lit_arg(&inner);
                // A passthrough builtin counts depth as rustc's expansion
                // of it does (see `builtin::rustc_depth`).
                let (extra, args) = builtin::rustc_depth(fmt_name, &inner);
                let call_span = segs.first().map_or(group_span, |s| s.span.to(group_span));
                self.check_depth(depth, extra, call_span, || fmt_name.to_string())?;
                let msg = if fmt_name == "assert" { builtin::assert_message(self, &inner, call_span)? } else { Vec::new() };
                let mut expanded_inner = self.expand_list(inner, depth + args, false, false, nest + 1)?;
                expanded_inner.extend(msg);
                if !written_lit && matches!(fmt_name, "println" | "print" | "eprintln" | "eprint" | "format" | "panic") {
                    mark_format_str(&mut expanded_inner, group_span);
                }
                out.push(Tt::Delim(delim, expanded_inner, group_span));
                i = group_idx + 1;
                pending_macro_use = false;
                continue;
            }
            // A macro call.
            if let Some((segs, leading_colon, group_idx)) = path_call_at(&trees, i, self.ctx.interner) {
                let (delim, inner, group_span) = match &trees[group_idx] {
                    Tt::Delim(d, inner, span) => (*d, inner.clone(), *span),
                    _ => unreachable!(),
                };
                let head: Vec<Tt> = trees[i..group_idx].to_vec();
                let span = segs.first().map_or(group_span, |s| s.span.to(group_span));
                let call = Call { segs, leading_colon, head, delim, inner, group_span, span };
                let mut next = group_idx + 1;
                let expanded = self.expand_call(&call, depth)?;
                let mut expanded = self.expand_list(expanded, depth + 1, item_list, stmt_list, nest)?;
                let begins_item = starts_item(&expanded, self.ctx.interner);
                let next_is_semi = tok_at(&trees, next).map(|t| t.tok) == Some(Tok::Semi);
                if item_list && !expanded.is_empty() && begins_item && call.delim != Delim::Brace && !next_is_semi {
                    return Err(err(
                        C_CALL,
                        call.span,
                        "a macro that expands to items needs `{ }` or a trailing `;`",
                        "Write the call with braces or end it with `;`.",
                    ));
                }
                // The call's own `;` is consumed with an empty or item
                // expansion only at a statement or item boundary. In
                // expression position the empty expansion is an error,
                // and dropping the `;` would let the flat stream read
                // the next statement as the expression.
                let stmt_boundary = item_list
                    || out.is_empty()
                    || matches!(out.last(), Some(Tt::Tok(t)) if t.tok == Tok::Semi)
                    || matches!(out.last(), Some(Tt::Delim(Delim::Brace, _, _)));
                if next_is_semi && begins_item {
                    next += 1;
                } else if next_is_semi && expanded.is_empty() && stmt_boundary {
                    next += 1;
                }
                // A statement-position expansion whose last statement
                // is a `let` without its own `;` is incomplete: the
                // call's `;` belongs to the macro statement, it does
                // not finish the let.
                if !item_list && stmt_boundary && ends_with_unfinished_let(&expanded) {
                    return Err(err(
                        C_CALL,
                        call.span,
                        "this macro expansion ends with an incomplete `let` statement",
                        "End the `let` with `;` inside the macro expansion.",
                    ));
                }
                if should_wrap(&expanded, &out, tok_at(&trees, next).map(|t| t.tok), trees.get(next), self.ctx.interner) {
                    expanded = vec![Tt::Delim(Delim::Paren, expanded, call.span)];
                }
                // A brace-delimited call in statement position is a
                // whole statement in rustc: `m!{} - 1;` is the call,
                // then a separate `-1` statement. The flat stream
                // would glue the operator onto the expansion's last
                // expression, so close the statement where rustc
                // does. Only statement lists qualify: in expression
                // position the operator belongs to the expansion.
                let brace_stmt = stmt_list
                    && !item_list
                    && stmt_boundary
                    && call.delim == Delim::Brace
                    && !expanded.is_empty()
                    && !begins_item
                    && !next_is_semi
                    && !matches!(expanded.last(), Some(Tt::Tok(t)) if t.tok == Tok::Semi)
                    && !matches!(expanded.first(), Some(Tt::Tok(t)) if t.tok == Tok::Let)
                    && matches!(
                        tok_at(&trees, next).map(|t| t.tok),
                        Some(
                            Tok::Minus
                                | Tok::Plus
                                | Tok::Star
                                | Tok::Slash
                                | Tok::Percent
                                | Tok::EqEq
                                | Tok::Ne
                                | Tok::Lt
                                | Tok::Le
                                | Tok::Gt
                                | Tok::Ge
                                | Tok::AndAnd
                                | Tok::OrOr
                                | Tok::Amp
                                | Tok::Pipe
                                | Tok::Caret
                                | Tok::Shl
                                | Tok::Shr
                                | Tok::Dot
                                | Tok::Question
                                | Tok::As
                                | Tok::DotDot
                                | Tok::DotDotEq
                                | Tok::Eq
                                | Tok::PlusEq
                                | Tok::MinusEq
                                | Tok::StarEq
                                | Tok::SlashEq
                                | Tok::PercentEq
                                | Tok::AmpEq
                                | Tok::PipeEq
                                | Tok::CaretEq
                                | Tok::ShlEq
                                | Tok::ShrEq
                        )
                    );
                out.extend(expanded);
                if brace_stmt {
                    out.push(Tt::Tok(Token { tok: Tok::Semi, span: call.span }));
                }
                i = next;
                pending_macro_use = false;
                continue;
            }
            // Any other group: expand inside, under its own scope.
            if matches!(trees.get(i), Some(Tt::Delim(_, _, _))) {
                let tree = take(&mut trees, i);
                let Tt::Delim(d, inner, gspan) = tree else { unreachable!() };
                let textual_len = self.textual.len();
                let imports_len = self.imports.len();
                let expanded = self.expand_list(inner, depth, false, d == Delim::Brace, nest + 1);
                self.textual.truncate(textual_len);
                self.imports.truncate(imports_len);
                out.push(Tt::Delim(d, expanded?, gspan));
                i += 1;
                pending_macro_use = false;
                continue;
            }
            if matches!(&trees[i], Tt::Tok(t) if t.tok != Tok::Eof) {
                out.push(take(&mut trees, i));
            } else if matches!(&trees[i], Tt::Frag(..)) {
                // Macro calls inside a fragment expand when the
                // fragment lands in place: matching captures them
                // unexpanded (`add!(add!(1, 2), 3)` binds the inner
                // call inside the expr fragment), so walk the
                // fragment's trees like any other list here.
                let tree = take(&mut trees, i);
                let Tt::Frag(kind, inner, fspan) = tree else { unreachable!() };
                let expanded = self.expand_list(inner, depth, false, false, nest + 1)?;
                out.push(Tt::Frag(kind, expanded, fspan));
            }
            i += 1;
        }
        Ok(out)
    }

    /// Grammar-checks one cfg-disabled node (`trees[start..end]`, its
    /// attribute run included) before it is dropped, as rustc parses
    /// all code before cfg stripping. The check parses syntax only:
    /// no macro inside expands, no name resolution or type check runs,
    /// and a disabled `mod name;` never loads a file (module loading
    /// stays with the outline, which already honors cfg).
    fn check_disabled_syntax(&self, trees: &[Tt], start: usize, end: usize, hint: crate::parser::CfgSyntaxHint) -> Result<(), Diag> {
        let mut toks = Vec::new();
        flatten_final(&trees[start..end], &mut toks);
        crate::parser::check_cfg_syntax(&toks, &self.strings, self.ctx.interner, self.ctx.known, hint)
    }

    /// Handles an attribute run starting at `i` in `trees`, appending any
    /// kept trees to `out`. Returns the next index to walk.
    fn attr_run(
        &mut self,
        trees: &mut Vec<Tt>,
        start: usize,
        first: AttrInfo,
        pending_macro_use: &mut bool,
        out: &mut Vec<Tt>,
        item_list: bool,
        _depth: u32,
    ) -> Result<usize, Diag> {
        // The expander reads `#![recursion_limit]` itself and the
        // parser has no form for it, so it is consumed here, once its
        // value is checked.
        if first.inner_attr && first.path == "recursion_limit" {
            recursion_limit_value(&first.inner, &self.strings, first.span)?;
            return Ok(first.end);
        }
        // An inner attribute applies to the enclosing item or crate:
        // nothing for the expander to do with it here.
        if first.inner_attr {
            for k in start..first.end {
                out.push(take(trees, k));
            }
            return Ok(first.end);
        }
        let mut attrs = vec![first];
        let mut after = attrs[0].end;
        while let Some(next) = attr_at(trees, after, self.ctx.interner) {
            after = next.end;
            attrs.push(next);
        }
        // cfg_attr(cond, attr): keep, drop, or substitute. One level is
        // enough for the shapes in use; a substituted cfg is honored by
        // falling through to the cfg check below with its own trees.
        let mut kept: Vec<(AttrInfo, usize)> = Vec::new();
        let mut pos = start;
        for attr in attrs {
            let attr_start = pos;
            pos = attr.end;
            if attr.path == "cfg_attr" {
                let split = attr.inner.iter().position(|t| t.is_tok(Tok::Comma)).unwrap_or(attr.inner.len());
                let on = builtin::eval_cfg(&attr.inner[..split], &self.ctx.cfg, self, attr.span)?;
                if !on {
                    continue;
                }
                // Rebuild as the inner attribute written plainly. An
                // inner attribute the expander itself acts on (cfg,
                // macro_export, macro_use) joins this run as if
                // written, so `cfg_attr(.., macro_export)` exports.
                let rest: Vec<Tt> = attr.inner[split + 1.min(attr.inner.len() - split)..].to_vec();
                let fake_path = rest.iter().find_map(|t| match t {
                    Tt::Tok(tok) => seg_text(tok.tok, self.ctx.interner),
                    _ => None,
                });
                let span = attr.span;
                let end = attr.end;
                drop(attr);
                if matches!(fake_path.as_deref(), Some("cfg" | "macro_export" | "macro_use")) {
                    let inner = match rest.get(1) {
                        Some(Tt::Delim(_, group, _)) => group.clone(),
                        _ => Vec::new(),
                    };
                    kept.push((AttrInfo { path: fake_path.unwrap(), inner, end, span, inner_attr: false }, usize::MAX));
                    continue;
                }
                out.push(Tt::Tok(Token { tok: Tok::Pound, span }));
                out.push(Tt::Delim(Delim::Bracket, rest, span));
                continue;
            }
            kept.push((attr, attr_start));
        }
        // A cfg that is off drops the item before expansion can see it,
        // so a disabled compile_error! or include! never runs (6.1).
        // The dropped node is still grammar-checked (rustc parses
        // before it strips), except a macro invocation or definition,
        // whose group rustc does not parse. A `#[test]` item outside a
        // test build drops the same way, as in rustc: it never reaches
        // name resolution.
        let mut exported = false;
        let mut macro_use_attr = false;
        for (attr, attr_start) in &kept {
            let mut off = false;
            match attr.path.as_str() {
                "cfg" => {
                    let on = builtin::eval_cfg(&attr.inner, &self.ctx.cfg, self, attr.span)?;
                    if !on {
                        if let Some(def) = macro_rules_at(trees, after, self.ctx.interner) {
                            // A definition body is token trees rustc
                            // does not grammar-check before stripping;
                            // only its outer form counts.
                            check_def_form(trees, &def)?;
                            return Ok(def.end);
                        }
                        // A macro call is boundable even though it is
                        // not a keyword item: path, `!`, its group,
                        // and an optional `;`. Dropping it here keeps
                        // a disabled `include!` or `compile_error!`
                        // from ever expanding (found in ts-rust's
                        // wasm-only bundled embed).
                        if let Some((_, _, group_idx)) = path_call_at(trees, after, self.ctx.interner) {
                            let mut end = group_idx + 1;
                            if tok_at(trees, end).map(|t| t.tok) == Some(Tok::Semi) {
                                end += 1;
                            }
                            return Ok(end);
                        }
                        if let Some(end) = item_end(trees, after, self.ctx.interner) {
                            self.check_disabled_syntax(trees, start, end, crate::parser::CfgSyntaxHint::Item)?;
                            return Ok(end);
                        }
                        // A statement, match arm, or comma-ended part:
                        // bounded at token level, dropped whole so
                        // nothing inside it expands.
                        if let Some(end) = node_end(trees, after) {
                            self.check_disabled_syntax(trees, start, end, crate::parser::CfgSyntaxHint::Node)?;
                            return Ok(end);
                        }
                        let _ = attr_start;
                        return Err(err(
                            C_UNSUPPORTED,
                            attr.span,
                            "`#[cfg]` on this statement form is not supported yet",
                            "Move the cfg to an item, or rewrite the statement with cfg!.",
                        ));
                    }
                }
                // Only a fn item drops: `#[test]` anywhere else is
                // an error in every build, and the parser reports it.
                "test" => off = !self.ctx.cfg.test && next_is_fn(trees, after),
                "macro_export" => exported = true,
                "macro_use" => macro_use_attr = true,
                _ => {}
            }
            if off {
                if let Some(def) = macro_rules_at(trees, after, self.ctx.interner) {
                    check_def_form(trees, &def)?;
                    return Ok(def.end);
                }
                // A macro call is boundable even though it is
                // not a keyword item: path, `!`, its group,
                // and an optional `;`. Dropping it here keeps
                // a disabled `include!` or `compile_error!`
                // from ever expanding (found in ts-rust's
                // wasm-only bundled embed).
                if let Some((_, _, group_idx)) = path_call_at(trees, after, self.ctx.interner) {
                    let mut end = group_idx + 1;
                    if tok_at(trees, end).map(|t| t.tok) == Some(Tok::Semi) {
                        end += 1;
                    }
                    return Ok(end);
                }
                if let Some(end) = item_end(trees, after, self.ctx.interner) {
                    self.check_disabled_syntax(trees, start, end, crate::parser::CfgSyntaxHint::Item)?;
                    return Ok(end);
                }
                // A statement, match arm, or comma-ended part:
                // bounded at token level, dropped whole so
                // nothing inside it expands.
                if let Some(end) = node_end(trees, after) {
                    self.check_disabled_syntax(trees, start, end, crate::parser::CfgSyntaxHint::Node)?;
                    return Ok(end);
                }
                let _ = attr_start;
                return Err(err(
                    C_UNSUPPORTED,
                    attr.span,
                    "`#[cfg]` on this statement form is not supported yet",
                    "Move the cfg to an item, or rewrite the statement with cfg!.",
                ));
            }
        }
        if exported || macro_rules_at(trees, after, self.ctx.interner).is_some() {
            if let Some(def) = macro_rules_at(trees, after, self.ctx.interner) {
                self.define_macro(trees, &def, exported, !item_list)?;
                return Ok(def.end);
            }
        }
        if macro_use_attr {
            *pending_macro_use = true;
        }
        // Keep attributes the expander does not own, minus the ones it
        // just acted on (a cfg that is on, macro_export/use markers).
        for (attr, attr_start) in &kept {
            if matches!(attr.path.as_str(), "cfg" | "macro_export" | "macro_use") {
                continue;
            }
            for k in *attr_start..attr.end {
                out.push(take(trees, k));
            }
        }
        let _ = item_list;
        Ok(after)
    }

    /// Compiles and registers the `macro_rules!` definition at `def`.
    fn define_macro(&mut self, trees: &[Tt], def: &DefStart, exported: bool, local_def: bool) -> Result<(), Diag> {
        // A `#[macro_export]` definition an expansion produced is only
        // a textual macro: rustc keeps it out of the crate root path
        // namespace ("macro-expanded macro_export macros cannot be
        // referred to by absolute paths"). Written defs carry the
        // root context; expansion output is stamped with its own.
        let exported = exported && def.span.ctxt == CtxtId::ROOT;
        self.check_dup_export(def.name, def.name_span, exported)?;
        check_def_form(trees, def)?;
        let Tt::Delim(_, body, _) = &trees[def.group] else { unreachable!() };
        let body = body.clone();
        // An exported def was already compiled in the prescan; the walk
        // still makes it textually visible from here on.
        if exported
            && let Some(&idx) = self.exported.get(&def.name)
            && self.defs[idx as usize].name_span == def.name_span
        {
            self.textual.push((def.name, idx));
            return Ok(());
        }
        let mut compiled = compile_macro(def.name, def.name_span, &body, exported, def.span, &self.strings, self.ctx.interner)?;
        compiled.local_def = local_def;
        self.register(Arc::new(compiled), exported, true);
        Ok(())
    }

    /// If a `use` item a macro cares about starts at `trees[i]`, registers
    /// its macro imports and returns the index just past the `;`.
    fn use_item_at(&mut self, trees: &[Tt], i: usize, item_list: bool) -> Option<usize> {
        let (public, content, end) = use_span_at(trees, i)?;
        for (segs, leading, alias) in collect_use_sites(&trees[content..end - 1], &[], self.ctx.interner) {
            self.import_macro(&segs, leading, alias, public && item_list);
        }
        Some(end)
    }

    /// The canonical builtin macro a `use` path names, when the
    /// path is an exact canonical std macro path lust expands by
    /// that name (`std::vec`, `core::panic`).
    fn std_builtin_macro(&self, segs: &[Seg]) -> Option<Sym> {
        let path: Vec<&str> = segs.iter().map(|s| s.text.as_str()).collect();
        if crate::ty::lang::std_path_kind(&path) != Some(crate::ty::lang::StdPathKind::Macro) {
            return None;
        }
        let last = segs.last()?;
        (builtin::is_token_builtin(&last.text) || builtin::is_passthrough(&last.text)).then_some(last.sym)
    }

    /// The builtin macro a plain call name was bound to by a std
    /// macro import rename, if any. Latest binding wins.
    fn builtin_alias_of(&self, name: Sym) -> Option<Sym> {
        if let Some(&(_, canon)) = self.builtin_imports.iter().rev().find(|(n, _)| *n == name) {
            return Some(canon);
        }
        self.module_builtin_alias.get(&(self.module.clone(), name)).copied()
    }

    /// Records `alias` for the macro `segs` names, if it names one.
    fn import_macro(&mut self, segs: &[Seg], leading_colon: bool, alias: Sym, public: bool) {
        if segs.is_empty() {
            return;
        }
        let module = self.module.clone();
        let found = self.lookup_macro(segs, leading_colon).or_else(|| self.resolve_for_use(segs, leading_colon, &module));
        if let Some(idx) = found {
            self.imports.push((alias, idx));
            if public {
                self.by_path.insert((self.module.clone(), alias), idx);
            }
        } else if self.ctx.interner.get(alias) != "_"
            && let Some(canon) = self.std_builtin_macro(segs)
        {
            self.builtin_imports.push((alias, canon));
        }
    }

    /// Expands one macro call one step: a user macro through the matcher,
    /// a token builtin through `builtin`, a parser macro through
    /// unchanged with its arguments expanded.
    pub fn expand_call(&mut self, call: &Call, depth: u32) -> Result<Vec<Tt>, Diag> {
        self.check_depth(depth, 0, call.span, || call.path_text())?;
        if let Some(idx) = self.lookup_macro(&call.segs, call.leading_colon) {
            let def = self.defs[idx as usize].clone();
            return self.transcribe_call(&def, call, depth);
        }
        // A plain name bound by a std macro import rename expands
        // exactly as the canonical builtin name.
        let alias = if call.segs.len() == 1 && !call.leading_colon { self.builtin_alias_of(call.segs[0].sym) } else { None };
        let name = match alias {
            Some(canon) => self.ctx.interner.get(canon).to_string(),
            None => call.name_text().to_string(),
        };
        let std_prefixed = matches!(call.segs.first().map(|s| s.text.as_str()), Some("std" | "core" | "alloc"));
        if call.segs.len() == 1 || std_prefixed {
            // A builtin counts depth as rustc's expansion of it does (see
            // `builtin::rustc_depth`): its arguments expand `args` levels
            // down, so a token builtin's own one-level-down expansions
            // run from `depth + args - 1`.
            let (extra, args) = builtin::rustc_depth(&name, &call.inner);
            if builtin::is_token_builtin(&name) {
                self.check_depth(depth, extra, call.span, || name.clone())?;
                return builtin::expand_builtin(self, &name, call, depth + args - 1);
            }
            if builtin::is_passthrough(&name) {
                self.check_depth(depth, extra, call.span, || name.clone())?;
                // The head already ends with the call's `!`. The parser
                // owns only the plain `name!` form, so keep just the
                // last segment and the bang of a qualified path.
                let head = &call.head[call.head.len().saturating_sub(2)..];
                let mut out: Vec<Tt> = head.to_vec();
                // The name spans the whole path, as in `expand_list`.
                if let (Some(Tt::Tok(tok)), Some(Tt::Tok(first))) = (out.first_mut(), call.head.first())
                    && (first.span.file, first.span.ctxt) == (tok.span.file, tok.span.ctxt)
                {
                    tok.span = first.span.to(tok.span);
                }
                // A renamed call keeps the canonical head name:
                // the parser owns only the plain builtin spellings.
                if let Some(canon) = alias
                    && let Some(Tt::Tok(tok)) = out.first_mut()
                    && matches!(tok.tok, Tok::Ident(_))
                {
                    tok.tok = Tok::Ident(canon);
                }
                let written_lit = is_str_lit_arg(&call.inner);
                let msg = if name == "assert" { builtin::assert_message(self, &call.inner, call.span)? } else { Vec::new() };
                let mut inner = self.expand_list(call.inner.clone(), depth + args, false, false, 0)?;
                inner.extend(msg);
                if !written_lit && matches!(name.as_str(), "println" | "print" | "eprintln" | "eprint" | "format" | "panic") {
                    mark_format_str(&mut inner, call.span);
                }
                out.push(Tt::Delim(call.delim, inner, call.group_span));
                return Ok(out);
            }
        }
        Err(err(
            C_UNKNOWN,
            call.span,
            format!("cannot find macro `{}` in this scope", call.path_text()),
            "Define it with macro_rules! above this point, export it, or import it with use.",
        ))
    }

    /// Expands trees that must come back as statements or expressions of
    /// their written shape (builtin arguments), one level from `depth`.
    pub fn expand_more(&mut self, trees: Vec<Tt>, depth: u32) -> Result<Vec<Tt>, Diag> {
        self.expand_list(trees, depth + 1, false, false, 0)
    }

    /// The current module path as `module_path!` prints it.
    pub fn module_path_text(&self) -> String {
        let mut parts = vec![self.ctx.crate_name()];
        for seg in &self.module {
            parts.push(self.ctx.interner.get(*seg).to_string());
        }
        parts.join("::")
    }
}

/// True when the last top-level statement segment of an expansion
/// starts with `let` and carries no `;` of its own.
fn ends_with_unfinished_let(expanded: &[Tt]) -> bool {
    let seg = match expanded.iter().rposition(|t| t.is_tok(Tok::Semi)) {
        Some(i) => &expanded[i + 1..],
        None => expanded,
    };
    matches!(seg.first(), Some(Tt::Tok(t)) if t.tok == Tok::Let)
}

/// True when a one-step expansion should be parenthesized in the flat
/// token stream. A macro call is one syntax node in rustc; in a flat
/// stream a multi-token expansion would re-bind under surrounding
/// operators, so expression-shaped output is wrapped. Item and
/// statement sequences, single trees, and type-looking positions are
/// left alone.
fn should_wrap(expanded: &[Tt], prev_out: &[Tt], next_tok: Option<Tok>, next_tree: Option<&Tt>, interner: &Interner) -> bool {
    if expanded.len() <= 1 || starts_item(expanded, interner) {
        return false;
    }
    if expanded.iter().any(|t| t.is_tok(Tok::Semi)) {
        // Statement sequences stand as written. In expression
        // position a `;` in the expansion is where rustc stops
        // ("trailing semicolon in macro used in expression
        // position", "macro expansion ignores ..."); wrapping makes
        // the flat stream reject there too instead of silently
        // reading the expansion as statements of the caller.
        let prev_expr = matches!(prev_out.last(), Some(Tt::Tok(t)) if matches!(
            t.tok,
            Tok::Eq
                | Tok::Comma
                | Tok::Colon
                | Tok::Plus
                | Tok::Minus
                | Tok::Star
                | Tok::Slash
                | Tok::Percent
                | Tok::EqEq
                | Tok::Ne
                | Tok::Lt
                | Tok::Le
                | Tok::Gt
                | Tok::Ge
                | Tok::AndAnd
                | Tok::OrOr
                | Tok::Amp
                | Tok::Pipe
                | Tok::Caret
                | Tok::Shl
                | Tok::PlusEq
                | Tok::MinusEq
                | Tok::StarEq
                | Tok::SlashEq
                | Tok::PercentEq
                | Tok::AmpEq
                | Tok::PipeEq
                | Tok::CaretEq
                | Tok::ShlEq
                    | Tok::Shr
                    | Tok::ShrEq
                | Tok::Dot
                | Tok::Question
                | Tok::As
                | Tok::Return
                | Tok::FatArrow
        ));
        let next_expr = matches!(
            next_tok,
            Some(
                Tok::Plus
                    | Tok::Minus
                    | Tok::Star
                    | Tok::Slash
                    | Tok::Percent
                    | Tok::EqEq
                    | Tok::Ne
                    | Tok::Lt
                    | Tok::Le
                    | Tok::Gt
                    | Tok::Ge
                    | Tok::AndAnd
                    | Tok::OrOr
                    | Tok::Amp
                    | Tok::Pipe
                    | Tok::Caret
                    | Tok::Shl
                    | Tok::PlusEq
                    | Tok::MinusEq
                    | Tok::StarEq
                    | Tok::SlashEq
                    | Tok::PercentEq
                    | Tok::AmpEq
                    | Tok::PipeEq
                    | Tok::CaretEq
                    | Tok::ShlEq
                    | Tok::Shr
                    | Tok::ShrEq
                    | Tok::Eq
                    | Tok::Dot
                    | Tok::Question
                    | Tok::As
                    | Tok::DotDot
                    | Tok::DotDotEq
            )
        );
        return prev_expr || next_expr;
    }
    if matches!(expanded.first(), Some(Tt::Tok(t)) if t.tok == Tok::Let) {
        return false;
    }
    // After `:` in a let or field, or inside `< ... >`, the expansion is
    // most often a type; parens would make it a tuple/paren type shape.
    if matches!(prev_out.last(), Some(Tt::Tok(t)) if matches!(t.tok, Tok::Colon | Tok::Lt | Tok::As)) {
        return false;
    }
    // One atomic operand (a call, a place, a block-like head) binds as
    // tightly as the macro call did, so it needs no parens.
    if atomic_shaped(expanded) {
        return false;
    }
    // A whole comma piece (a call argument, an array element) parses as
    // one expression in place; parens only matter when the expansion
    // itself would split the piece with a top-level comma.
    let piece_start = prev_out.is_empty() || matches!(prev_out.last(), Some(Tt::Tok(t)) if t.tok == Tok::Comma);
    let piece_end = next_tree.is_none() || next_tok == Some(Tok::Comma);
    if piece_start && piece_end && !expanded.iter().any(|t| t.is_tok(Tok::Comma)) {
        return false;
    }
    // A path-shaped expansion directly before a `{ }` group is most
    // often a struct literal head; parens would split it from its fields.
    let _ = next_tok;
    if matches!(next_tree, Some(Tt::Delim(Delim::Brace, _, _)))
        && expanded
            .iter()
            .all(|t| matches!(t, Tt::Tok(tok) if is_seg_tok(tok.tok) || matches!(tok.tok, Tok::PathSep | Tok::Lt | Tok::Gt | Tok::Comma)))
    {
        return false;
    }
    true
}

/// If a `use` item starts at `trees[i]`, returns whether it is public,
/// the content start (just past `use`), and the end (just past `;`).
fn use_span_at(trees: &[Tt], i: usize) -> Option<(bool, usize, usize)> {
    let mut j = i;
    let mut public = false;
    if tok_at(trees, j).map(|t| t.tok) == Some(Tok::Pub) {
        public = true;
        j += 1;
        if matches!(trees.get(j), Some(Tt::Delim(Delim::Paren, _, _))) {
            j += 1;
        }
    }
    if tok_at(trees, j).map(|t| t.tok) != Some(Tok::Use) {
        return None;
    }
    let end = (j..trees.len()).find(|&k| matches!(&trees[k], Tt::Tok(t) if t.tok == Tok::Semi))? + 1;
    Some((public, j + 1, end))
}

/// Every (target path, leading-colon flag, imported name) one `use`
/// tree brings in. `prefix` carries the path of an enclosing group.
fn collect_use_sites(trees: &[Tt], prefix: &[Seg], interner: &Interner) -> Vec<(Vec<Seg>, bool, Sym)> {
    let mut out = Vec::new();
    let mut segs: Vec<Seg> = prefix.to_vec();
    let mut i = 0;
    let mut leading_colon = false;
    if tok_at(trees, i).map(|t| t.tok) == Some(Tok::PathSep) {
        leading_colon = true;
        i += 1;
    }
    while i < trees.len() {
        match &trees[i] {
            Tt::Delim(Delim::Brace, group, _) => {
                let mut start = 0;
                for k in 0..=group.len() {
                    if k == group.len() || matches!(&group[k], Tt::Tok(t) if t.tok == Tok::Comma) {
                        if start < k {
                            out.extend(collect_use_sites(&group[start..k], &segs, interner));
                        }
                        start = k + 1;
                    }
                }
                return out;
            }
            Tt::Tok(t) if t.tok == Tok::As => {
                if let Some(rename) = tok_at(trees, i + 1).and_then(|t| seg_sym(t.tok, interner)) {
                    out.push((segs, leading_colon, rename));
                }
                return out;
            }
            Tt::Tok(t) if is_seg_tok(t.tok) => {
                let (Some(sym), Some(text)) = (seg_sym(t.tok, interner), seg_text(t.tok, interner)) else { return out };
                if text == "self" {
                    // `use a::{self, ..}` imports `a` itself, not a macro here.
                    return out;
                }
                segs.push(Seg { sym, text, span: t.span });
                i += 1;
            }
            Tt::Tok(t) if t.tok == Tok::PathSep => i += 1,
            // A glob import of macros is not tracked (textual macros
            // are not glob-importable in Rust).
            _ => return out,
        }
    }
    if let Some(last) = segs.last().map(|s| s.sym) {
        out.push((segs, leading_colon, last));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::FileId;

    fn expand_src(interner: &Interner, known: &Known, src: &str) -> Result<Vec<String>, Diag> {
        let lexed = crate::lexer::lex(src, FileId(0), 0, interner).expect("test source lexes");
        let ctx = ExpandCtx::for_file(interner, known, std::path::Path::new("test.rs"), src, false);
        let out = expand_lexed(lexed, &ctx)?;
        Ok(out.tokens.iter().map(|t| tok_text(&t.tok, &out.strings, interner)).collect())
    }

    /// A simple call expands, and expanding the same call again in the
    /// same process (what a daemon re-check does) hits the cache.
    #[test]
    fn expansion_cache_hits_on_repeat() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let src = "macro_rules! one { () => { 1 } }\nfn main() { let _x = one!(); }";
        let (hits0, _) = cache_stats();
        let first = expand_src(&interner, &known, src).expect("first expansion");
        let second = expand_src(&interner, &known, src).expect("second expansion");
        assert_eq!(first, second);
        let (hits1, _) = cache_stats();
        assert!(hits1 > hits0, "second identical expansion should hit the cache");
    }

    /// A cache hit in a later run (a daemon re-check after an edit) gets
    /// the strings its tokens name, though that run's string table holds
    /// other strings at those indexes: the edit adds a string literal
    /// before the call, at the same length, so the call's key is the same.
    #[test]
    fn expansion_cache_hit_keeps_its_strings() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let call = "macro_rules! cached_s { ($x:expr) => { ($x, \"tpl\", stringify!(0x10)) } }\nfn main() { let a = ";
        let tail = "; let _v = cached_s!(\"bee\"); }";
        let before = expand_src(&interner, &known, &format!("{call}12345{tail}")).expect("first expansion");
        let (hits0, _) = cache_stats();
        let after = expand_src(&interner, &known, &format!("{call}\"123\"{tail}")).expect("second expansion");
        let (hits1, _) = cache_stats();
        assert!(hits1 > hits0, "the second call should hit the cache");
        for out in [&before, &after] {
            for text in ["\"bee\"", "\"tpl\"", "\"0x10\""] {
                assert!(out.iter().any(|t| t == text), "{text} missing from {out:?}");
            }
        }
    }

    /// A macro body's locals carry a non-root context; an ident the
    /// caller passes in keeps the root context (ARCH 6.3).
    #[test]
    fn hygiene_contexts_on_tokens() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let src = "macro_rules! w { ($e:expr) => {{ let tmp = 1; tmp + $e }} }\nfn main() { let tmp = 2; let _x = w!(tmp); }";
        let lexed = crate::lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ctx = ExpandCtx::for_file(&interner, &known, std::path::Path::new("test.rs"), src, false);
        let out = expand_lexed(lexed, &ctx).expect("expansion");
        let tmps: Vec<CtxtId> =
            out.tokens.iter().filter(|t| matches!(t.tok, Tok::Ident(s) if interner.get(s) == "tmp")).map(|t| t.span.ctxt).collect();
        assert_eq!(tmps.len(), 4, "caller let, macro let, macro use, caller arg");
        assert_eq!(tmps[0], CtxtId::ROOT, "caller's own binding");
        assert_ne!(tmps[1], CtxtId::ROOT, "macro-introduced binding has the expansion context");
        assert_eq!(tmps[1], tmps[2], "macro binding and its use share a context");
        assert_eq!(tmps[3], CtxtId::ROOT, "the passed-in ident keeps the caller's context");
    }

    /// Local ambiguity and follow-set violations are hard errors with
    /// their stable codes, not silent first-match wins.
    #[test]
    fn ambiguity_and_follow_errors() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let amb = expand_src(&interner, &known, "macro_rules! m { ($($i:ident)* $j:ident) => { () } }\nfn main() { m!(x); }");
        assert_eq!(amb.unwrap_err().code, C_AMBIG);
        let follow = expand_src(&interner, &known, "macro_rules! m { ($e:expr +) => { $e } }\nfn main() {}");
        assert_eq!(follow.unwrap_err().code, C_DEF);
    }

    /// A fragment parse that began and failed is a hard error, even
    /// when a later arm token-matches the input (rustc does not fall
    /// through). With the token arm first, the same call expands.
    #[test]
    fn fragment_hard_failure_stops_arm_search() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let hard = expand_src(&interner, &known, "macro_rules! m { ($e:expr ;) => { 1 }; (1 +) => { 2 } }\nfn main() { let _ = m!(1 +); }");
        assert_eq!(hard.unwrap_err().code, C_CALL);
        let first =
            expand_src(&interner, &known, "macro_rules! m { (1 +) => { 2 }; ($e:expr ;) => { 1 } }\nfn main() { let _ = m!(1 +); }");
        assert!(first.expect("token arm first wins").iter().any(|t| t == "2"));
        // A fragment that cannot begin on the first token kills only
        // its own arm, so the next arm still gets its try.
        let soft = expand_src(&interner, &known, "macro_rules! m { ($e:expr) => { 1 }; (+) => { 2 } }\nfn main() { let _ = m!(+); }");
        assert!(soft.expect("soft fragment failure falls through").iter().any(|t| t == "2"));
    }

    /// Edition 2024 follow sets, separator rules, and empty repetitions
    /// are definition errors; an unbound template name is not.
    #[test]
    fn definition_checks_match_rustc() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        for src in [
            "macro_rules! m { ($p:pat |) => { 0 } }\nfn main() {}",
            "macro_rules! m { ($t:ty >=) => { 0 } }\nfn main() {}",
            "macro_rules! m { ($($i:ident),?) => { 1 } }\nfn main() {}",
            "macro_rules! m { ($($i:ident),*) => { $($i),? } }\nfn main() {}",
            "macro_rules! m { ($($v:vis)*) => { 1 } }\nfn main() {}",
        ] {
            assert_eq!(expand_src(&interner, &known, src).unwrap_err().code, C_DEF, "src: {src}");
        }
        let unbound = expand_src(&interner, &known, "macro_rules! m { () => { $y } }\nfn main() {}");
        assert!(unbound.is_ok(), "an uncalled arm's unbound name is not a definition error");
    }

    /// Fragment validation does not care that the template only
    /// stringifies the fragment: token soup inside a group is not an
    /// expr, and byte string patterns distinguish their bytes.
    #[test]
    fn invalid_fragments_do_not_bind() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let soup =
            expand_src(&interner, &known, "macro_rules! m { ($e:expr) => { stringify!($e) } }\nfn main() { let _s = m!((1 2, 3)); }");
        assert_eq!(soup.unwrap_err().code, C_CALL);
        let bytes =
            expand_src(&interner, &known, "macro_rules! m { (b\"a\") => { 1 }; ($t:tt) => { 2 } }\nfn main() { let _ = m!(b\"b\"); }")
                .expect("tt arm takes the other byte string");
        assert!(bytes.iter().any(|t| t == "2"), "tokens: {bytes:?}");
    }

    /// An `include_str!` read records a file dependency whose hash
    /// goes stale when the file changes; an `option_env!` read records
    /// the value it saw (ARCH 6.4). The daemon drops a chunk on stale
    /// deps instead of serving the old expansion.
    #[test]
    fn include_and_env_reads_record_deps() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let dir = std::env::temp_dir().join(format!("lust-deps-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let data = dir.join("data.txt");
        std::fs::write(&data, "one").unwrap();
        let main_rs = dir.join("main.rs");
        let src = "fn main() { let _s = include_str!(\"data.txt\"); let _e = option_env!(\"LUST_DEPS_TEST_UNSET\"); }";
        let lexed = crate::lexer::lex(src, FileId(0), 0, &interner).unwrap();
        let ctx = ExpandCtx::for_file(&interner, &known, &main_rs, src, false);
        let (_out, deps) = expand_lexed_with_deps(lexed, &ctx).expect("expansion");
        assert!(deps.iter().any(|d| matches!(d, Dep::File { path, .. } if *path == data)), "deps: {deps:?}");
        assert!(deps.iter().any(|d| matches!(d, Dep::Env { name, value: None } if name == "LUST_DEPS_TEST_UNSET")), "deps: {deps:?}");
        assert!(!deps_stale(&deps, &ClientView::PROCESS), "fresh deps are not stale");
        assert!(deps_stale_with(&deps, &|_: &str| Some("now set".to_string())), "a changed env value is stale");
        std::fs::write(&data, "two").unwrap();
        assert!(deps_stale(&deps, &ClientView::PROCESS), "a changed included file is stale");
        std::fs::remove_dir_all(&dir).ok();
    }

    /// stringify! keeps the source's own spacing between tokens.
    #[test]
    fn stringify_keeps_spacing() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let out = expand_src(&interner, &known, "fn main() { let _s = stringify!(a+b); }").expect("expansion");
        assert!(out.iter().any(|t| t == "\"a+b\""), "tokens: {out:?}");
    }

    /// Two calls of one macro whose inputs differ only in spacing are
    /// different expansions for `stringify!`: the cache key reads the
    /// input spans, so the second call does not reuse the first's.
    #[test]
    fn stringify_spacing_not_cached_across_calls() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let src = "macro_rules! s { ($e:expr) => { stringify!($e) }; }\nfn main() { let _a = s!(f(a,b)); let _b = s!(f( a , b )); }";
        let out = expand_src(&interner, &known, src).expect("expansion");
        assert!(out.iter().any(|t| t == "\"f(a,b)\""), "tokens: {out:?}");
        assert!(out.iter().any(|t| t == "\"f(a, b)\""), "tokens: {out:?}");
    }

    /// `n` chained macros after `attrs`: `m0!()` expands to `m1!()`, and
    /// so on, so the last one expands at depth `n`, one token per level.
    fn chain_src(n: usize, attrs: &str) -> String {
        let mut src = attrs.to_string();
        for i in 0..n {
            src.push_str(&format!("macro_rules! m{i} {{ () => {{ m{}!() }} }}\n", i + 1));
        }
        src.push_str(&format!("macro_rules! m{n} {{ () => {{ 0 }} }}\nfn main() {{ let _x = m0!(); }}\n"));
        src
    }

    /// Expands `src` on a thread with a 512 KB stack (a pool thread has
    /// 2 MB), returning the error code and message on failure.
    fn expand_on_small_stack(src: String) -> Result<(), (&'static str, String)> {
        std::thread::Builder::new()
            .stack_size(512 << 10)
            .spawn(move || {
                let interner = Interner::default();
                let known = Known::new(&interner);
                expand_src(&interner, &known, &src).map(|_| ()).map_err(|d| (d.code, d.message))
            })
            .unwrap()
            .join()
            .unwrap()
    }

    /// The default limit allows depth 127 and stops at 128, as rustc.
    /// Deep expansion moves to fresh stacks as it goes, so 2000 levels
    /// fit on a small thread; past lust's cap of 2048 it stops with
    /// L0801 whatever the crate's limit. The first limit attribute wins.
    #[test]
    fn expansion_depth_limits_on_a_small_stack() {
        assert_eq!(expand_on_small_stack(chain_src(127, "")), Ok(()));
        assert_eq!(expand_on_small_stack(chain_src(128, "")).unwrap_err().0, "L0801");
        assert_eq!(expand_on_small_stack(chain_src(2000, "#![recursion_limit = \"2048\"]\n")), Ok(()));
        let capped = expand_on_small_stack(chain_src(2100, "#![recursion_limit = \"5000\"]\n")).unwrap_err();
        assert_eq!(capped.0, "L0801");
        assert!(capped.1.contains("lust's limit of 2048"), "{}", capped.1);
        let first_wins = "#![recursion_limit = \"300\"]\n#![recursion_limit = \"2\"]\n";
        assert_eq!(expand_on_small_stack(chain_src(200, first_wins)), Ok(()));
    }

    /// A macro whose recursion doubles its input stops at a cap in well
    /// under a second: repetition matching is linear in the input. It
    /// used to take minutes, then overflow the stack.
    #[test]
    fn doubling_macro_stops_at_a_cap() {
        let src = "macro_rules! count { () => { 0 }; ($h:tt $($t:tt)*) => { 1 + count!($(pub $t)*) }; }\nfn main() { let _x = count!(a b c); }";
        assert_eq!(expand_on_small_stack(src.to_string()).unwrap_err().0, "L0801");
    }
}
