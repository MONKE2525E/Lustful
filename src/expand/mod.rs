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
pub mod builtin;
pub mod match_;
pub mod transcribe;

use crate::ast::{MacroCall, MacroRulesDef};
use crate::def::DefId;
use crate::diag::{CtxtId, Diag, HygieneMark, Span, mark_no_capture, register_expansion, register_hygiene};
use crate::intern::{FxMap, Interner, Known, Sym};
use crate::lexer::{Delim, Lexed, Tok, Token, TokenTree, build_trees};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

// Diagnostic codes (docs/errors/REGISTRY.md, macro range).
pub const C_CAP: &str = "L0801"; // expansion caps
pub const C_UNKNOWN: &str = "L0802"; // unknown macro
pub const C_INCLUDE: &str = "L0803"; // include file not found
pub const C_AMBIG: &str = "L0805"; // local ambiguity
pub const C_CALL: &str = "L0806"; // invalid macro call or builtin input
pub const C_DEF: &str = "L0807"; // invalid macro definition
pub const C_UNSUPPORTED: &str = "L0809"; // known macro form lust does not support yet

/// One expansion error, in the house shape (code, span, message, fix).
pub fn err(code: &'static str, span: Span, message: impl Into<String>, fix: impl Into<String>) -> Diag {
    Diag::new(code, span, message, fix)
}

/// A macro fragment kind, as written after `$name:` in a matcher.
/// `expr_2021` reads as `Expr`: all lust source is edition 2024 today, and
/// the definition's edition is carried in the expansion cache key (6.2,
/// 6.5), so the kind set can split later without reshaping matches.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FragKind {
    Expr,
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
            "expr" | "expr_2021" => FragKind::Expr,
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
/// its inner trees: the lexer form has no fragment case.
pub fn trees_from_tts(trees: &[Tt], out: &mut Vec<TokenTree>) {
    for tree in trees {
        match tree {
            Tt::Tok(t) => out.push(TokenTree::Token(*t)),
            Tt::Delim(d, inner, span) => {
                let mut converted = Vec::new();
                trees_from_tts(inner, &mut converted);
                out.push(TokenTree::Delim(*d, converted, *span));
            }
            Tt::Frag(_, inner, _) => trees_from_tts(inner, out),
        }
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
        Tok::Int(v, suffix) => {
            v.hash(h);
            suffix.map(|s| s as u8).hash(h);
        }
        Tok::Str(i) | Tok::Float(i) | Tok::DocStr(i) => strings.get(i as usize).hash(h),
        Tok::Char(c) => c.hash(h),
        _ => {}
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
        Int(v, suffix) => {
            let suf = suffix.map_or("", |s| match s {
                crate::lexer::IntSuffix::I8 => "i8",
                crate::lexer::IntSuffix::I16 => "i16",
                crate::lexer::IntSuffix::I32 => "i32",
                crate::lexer::IntSuffix::I64 => "i64",
                crate::lexer::IntSuffix::Isize => "isize",
                crate::lexer::IntSuffix::U8 => "u8",
                crate::lexer::IntSuffix::U16 => "u16",
                crate::lexer::IntSuffix::U32 => "u32",
                crate::lexer::IntSuffix::U64 => "u64",
                crate::lexer::IntSuffix::Usize => "usize",
            });
            return format!("{v}{suf}");
        }
        Float(i) => return strings.get(*i as usize).cloned().unwrap_or_default(),
        Str(i) => return format!("{:?}", strings.get(*i as usize).map_or("", String::as_str)),
        // A doc comment's literal prints as the raw string rustc uses
        // for it in token streams, with enough `#`s to close safely.
        DocStr(i) => {
            let text = strings.get(*i as usize).map_or("", String::as_str);
            let mut hashes = 0usize;
            let bytes = text.as_bytes();
            for (j, &b) in bytes.iter().enumerate() {
                if b == b'"' {
                    let run = bytes[j + 1..].iter().take_while(|&&c| c == b'#').count();
                    hashes = hashes.max(run + 1);
                }
            }
            let marks = "#".repeat(hashes);
            return format!("r{marks}\"{text}\"{marks}");
        }
        ByteStr => return "b\"\"".to_string(),
        ByteChar => return "b'?'".to_string(),
        Char(c) => return format!("{c:?}"),
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
        Dollar => "$",
        At => "@",
        Eof => "",
    }
    .to_string()
}

/// True when two plain tokens match as token-tree literals in a matcher:
/// same kind and same value. Span and context do not take part.
pub fn tok_matches(pattern: &Tok, input: &Tok, strings: &[String]) -> bool {
    match (pattern, input) {
        (Tok::Str(a), Tok::Str(b)) | (Tok::Float(a), Tok::Float(b)) | (Tok::DocStr(a), Tok::DocStr(b)) => {
            strings.get(*a as usize) == strings.get(*b as usize)
        }
        _ => pattern == input,
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
    pub nodes: Vec<match_::MNode>,
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
        let (nodes, vars) = match_::compile_arm(&matcher, mspan, interner)?;
        transcribe::check_template_vars(&template, &vars, interner)?;
        arms.push(Arm { nodes, template });
        i += 3;
        if tok_at(body, i).map(|t| t.tok) == Some(Tok::Semi) {
            i += 1;
        }
    }
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
}

impl<'a> ExpandCtx<'a> {
    /// A context for one file under `file_path` with text `src`.
    pub fn for_file(interner: &'a Interner, known: &'a Known, file_path: &std::path::Path, src: &'a str, test: bool) -> ExpandCtx<'a> {
        ExpandCtx {
            interner,
            known,
            file_path: file_path.to_string_lossy().to_string(),
            src,
            cfg: builtin::CfgEnv { test, debug_assertions: true, facts: Vec::new() },
        }
    }
    /// The crate name `module_path!` starts with: the file stem, with
    /// `-` read as `_`, as rustc names a single-file crate.
    pub fn crate_name(&self) -> String {
        let path = std::path::Path::new(&self.file_path);
        path.file_stem().map_or_else(|| "crate".to_string(), |s| s.to_string_lossy().replace('-', "_"))
    }
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
}

fn expansion_cache() -> &'static std::sync::Mutex<FxMap<CacheKey, (Vec<Tt>, CtxtId)>> {
    static CACHE: std::sync::OnceLock<std::sync::Mutex<FxMap<CacheKey, (Vec<Tt>, CtxtId)>>> = std::sync::OnceLock::new();
    CACHE.get_or_init(|| std::sync::Mutex::new(FxMap::default()))
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
/// or a cfg attribute. A macro-free file pays one token scan and runs
/// the unchanged pipeline.
pub fn needs_expansion(tokens: &[Token], interner: &Interner) -> bool {
    for (i, t) in tokens.iter().enumerate() {
        match t.tok {
            Tok::Ident(s) if interner.get(s) == "macro_rules" => return true,
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
                    && (name == "cfg" || name == "cfg_attr" || name == "macro_use" || name == "macro_export")
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
    defs: Vec<Rc<MacroDef>>,
    /// Textually visible macros, in definition order. Lookups scan in
    /// reverse, so a later definition shadows an earlier one.
    textual: Vec<(Sym, u32)>,
    /// Names brought in by `use` in scope here, same order rule.
    imports: Vec<(Sym, u32)>,
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
    /// Hashes of files and env vars read by builtins during this run
    /// (they feed cache keys and would feed the dep graph, ARCH 8).
    deps_hash: u64,
    total_tokens: usize,
}

impl<'a> Expander<'a> {
    fn new(ctx: &'a ExpandCtx<'a>, strings: Vec<String>) -> Expander<'a> {
        Expander {
            ctx,
            strings,
            defs: Vec::new(),
            textual: Vec::new(),
            imports: Vec::new(),
            exported: FxMap::default(),
            by_path: FxMap::default(),
            module_defs: FxMap::default(),
            module_imports: FxMap::default(),
            module: Vec::new(),
            cur_file: ctx.file_path.clone(),
            cur_src: ctx.src.to_string(),
            deps_hash: 0,
            total_tokens: 0,
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
        Tt::Tok(Token { tok: Tok::Str(i), span })
    }

    /// An identifier tree for `name` at `span`.
    pub fn ident_tree(&mut self, name: &str, span: Span) -> Tt {
        Tt::Tok(Token { tok: Tok::Ident(self.ctx.interner.intern(name)), span })
    }

    /// Records one file or env dependency read into the deps hash.
    pub fn read_dep(&mut self, what: &str, bytes: &[u8]) {
        let mut h = crate::intern::FxHasher::default();
        self.deps_hash.hash(&mut h);
        what.hash(&mut h);
        bytes.hash(&mut h);
        self.deps_hash = h.finish();
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
                        let tok = match tok.tok {
                            Tok::Str(i) => Tok::Str(i + offset),
                            Tok::Float(i) => Tok::Float(i + offset),
                            Tok::DocStr(i) => Tok::DocStr(i + offset),
                            other => other,
                        };
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
                        let kind = match tok.tok {
                            Tok::Str(i) => Tok::Str(i + offset),
                            Tok::Float(i) => Tok::Float(i + offset),
                            Tok::DocStr(i) => Tok::DocStr(i + offset),
                            other => other,
                        };
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

/// Expands every macro in one lexed file or chunk, returning the
/// expanded token list. A file that cannot contain macros comes back
/// unchanged (the same `Lexed`).
pub fn expand_lexed(lexed: Lexed, ctx: &ExpandCtx) -> Result<Lexed, Diag> {
    if !needs_expansion(&lexed.tokens, ctx.interner) {
        return Ok(lexed);
    }
    let (trees, balanced) = build_trees(&lexed.tokens);
    if !balanced {
        // The parser gives the real syntax error on the flat tokens.
        return Ok(lexed);
    }
    let eof = lexed.tokens.last().cloned().unwrap_or(Token { tok: Tok::Eof, span: Span::default() });
    let mut st = Expander::new(ctx, lexed.strings);
    let tts: Vec<Tt> = trees.iter().map(tt_from_tree).collect();
    st.prescan(&tts)?;
    let out = st.expand_list(tts, 0, true, 0)?;
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
    Ok(Lexed { tokens, strings: st.strings })
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

/// Flattens expanded trees for the parser. An expression fragment with
/// more than one token gets parens, so forwarding one into a larger
/// expression keeps its rustc atomic shape in the flat token stream.
fn flatten_final(trees: &[Tt], out: &mut Vec<Token>) {
    fn place_shaped(trees: &[Tt]) -> bool {
        trees.iter().all(|t| match t {
            Tt::Tok(tok) => matches!(tok.tok, Tok::Ident(_) | Tok::SelfUpper | Tok::SelfLower | Tok::Dot | Tok::PathSep | Tok::Int(..)),
            Tt::Delim(Delim::Bracket, _, _) => true,
            _ => false,
        })
    }
    for tree in trees {
        match tree {
            Tt::Frag(FragKind::Expr, inner, span) if count_tokens(inner) > 1 && !place_shaped(inner) => {
                out.push(Token { tok: Tok::LParen, span: *span });
                flatten_final(inner, out);
                out.push(Token { tok: Tok::RParen, span: *span });
            }
            Tt::Tok(t) => out.push(*t),
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
            Tt::Frag(_, inner, _) => flatten_final(inner, out),
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
            Tok::Str(i) => self.strings.get(i as usize).cloned(),
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
                    i = attr.end;
                    continue;
                }
                if let Some(def) = macro_rules_at(trees, i, st.ctx.interner) {
                    if !cfg_off {
                        let body = match &trees[def.group] {
                            Tt::Delim(_, inner, _) => inner.clone(),
                            _ => unreachable!(),
                        };
                        let mut compiled = compile_macro(def.name, def.name_span, &body, exported, def.span, &st.strings, st.ctx.interner)?;
                        compiled.local_def = !at_module_list;
                        let idx = st.register(Rc::new(compiled), exported, false);
                        if at_module_list {
                            st.module_defs.insert((module.clone(), def.name), idx);
                        }
                    }
                    exported = false;
                    cfg_off = false;
                    i = def.end;
                    continue;
                }
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
        let mut module: Vec<Sym> = Vec::new();
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

    /// Stores a compiled definition. `path` also puts it in the crate
    /// root table; `textual` makes it visible from this point on.
    fn register(&mut self, def: Rc<MacroDef>, path: bool, textual: bool) -> u32 {
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
            return self.module_imports.get(&(self.module.clone(), last)).copied();
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
                by_module(&module)
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
        if depth >= 128 {
            return Err(err(
                C_CAP,
                call.span,
                format!("recursion limit reached while expanding `{}!`", def.name_text),
                "Give the macro a base case it can reach.",
            ));
        }
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
        };
        if let Some((cached, old_ctxt)) = expansion_cache().lock().unwrap().get(&key).cloned() {
            CACHE_HITS.fetch_add(1, Ordering::Relaxed);
            let ctxt =
                register_expansion(crate::diag::Expansion { macro_def: DefId::PLACEHOLDER, call_span: call.span, parent: call.span.ctxt });
            register_hygiene(ctxt, HygieneMark { def_span: def.name_span, local_def: def.local_def });
            let mut out = cached;
            restamp_ctxt(&mut out, old_ctxt, ctxt);
            return Ok(out);
        }
        CACHE_MISSES.fetch_add(1, Ordering::Relaxed);
        let mut chosen: Option<(usize, BindMap)> = None;
        for (arm_i, arm) in def.arms.iter().enumerate() {
            let mut matcher = match_::Matcher::new(self.ctx.interner, self.ctx.known, &self.strings, call.span);
            let matches = match_::match_arm(&mut matcher, &arm.nodes, &call.inner)?;
            if matches.is_empty() {
                continue;
            }
            let ambiguous = matcher.ambiguous() || {
                // Two full matches with different bindings are ambiguous
                // in effect even when no fragment shared a token.
                let first = bind_hash(&matches[0], &self.strings);
                matches[1..].iter().any(|b| bind_hash(b, &self.strings) != first)
            };
            if ambiguous {
                return Err(err(
                    C_AMBIG,
                    call.span,
                    format!("local ambiguity when calling macro `{}!`", def.name_text),
                    "Make the matcher decide each token's role without guessing between fragments.",
                )
                .with_label(def.def_span, "the macro is defined here"));
            }
            chosen = Some((arm_i, matches.into_iter().next().unwrap()));
            break;
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
        expansion_cache().lock().unwrap().insert(key, (out.clone(), ctxt));
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

/// A stable fingerprint of one match's bindings, for the
/// distinct-bindings ambiguity check.
fn bind_hash(binds: &BindMap, strings: &[String]) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    let mut names: Vec<Sym> = binds.keys().copied().collect();
    names.sort();
    fn go(h: &mut impl Hasher, bind: &Bind, strings: &[String]) {
        match bind {
            Bind::Leaf(trees) => {
                1u8.hash(h);
                hash_tts(trees, strings).hash(h);
            }
            Bind::Seq(items) => {
                2u8.hash(h);
                items.len().hash(h);
                for item in items {
                    go(h, item, strings);
                }
            }
            Bind::Empty => 3u8.hash(h),
        }
    }
    for name in names {
        name.0.hash(&mut h);
        go(&mut h, &binds[&name], strings);
    }
    h.finish()
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
    // Path: segments joined by :: from the front of the body.
    let mut segs = Vec::new();
    let mut k = 0;
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
    Some(AttrInfo { path, inner, end: j + 1, span, inner_attr })
}

/// A `macro_rules! name <group>` definition found in a tree list.
pub struct DefStart {
    pub name: Sym,
    pub name_span: Span,
    pub group: usize,
    pub end: usize,
    pub span: Span,
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
            Some(DefStart { name, name_span: name_tok.span, group: i + 3, end, span: head.span.to(*group_span) })
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

/// True when trees start an item (`fn`, `pub struct`, an attribute, ...),
/// for the item-position macro rules. A leading item fragment counts,
/// and any other fragment is looked through to its first tokens.
fn starts_item(trees: &[Tt], interner: &Interner) -> bool {
    // Splice leading fragments in place so a vis fragment before the
    // item keyword (as in `$v:vis fn`) still reads as an item start.
    let mut flat: Vec<Tt> = trees.to_vec();
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
    // Skip attributes and item qualifiers to the item keyword.
    while let Some(attr) = attr_at(trees, i, interner) {
        i = attr.end;
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
        [Tt::Tok(t)] => matches!(t.tok, Tok::Str(_)),
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
            [Tt::Tok(t)] if matches!(t.tok, Tok::Str(_)) => stamp(t, span),
            [Tt::Frag(_, inner, _)] => first_str(inner, span),
            _ => {}
        }
    }
    let end = expanded.iter().position(|t| t.is_tok(Tok::Comma)).unwrap_or(expanded.len());
    if end == 1 {
        first_str(&mut expanded[..1], span);
    }
}

/// Takes `trees[i]` out by value, leaving a placeholder behind.
fn take(trees: &mut [Tt], i: usize) -> Tt {
    std::mem::replace(&mut trees[i], Tt::Tok(Token { tok: Tok::Eof, span: Span::default() }))
}

impl<'a> Expander<'a> {
    /// Expands one tree list, outermost first (ARCH 6.1). `depth` is the
    /// expansion nesting depth of this list; `item_list` marks the file
    /// root and module bodies, where item-position rules apply; `nest`
    /// bounds delimiter recursion so pathological input cannot overflow.
    pub fn expand_list(&mut self, mut trees: Vec<Tt>, depth: u32, item_list: bool, nest: u32) -> Result<Vec<Tt>, Diag> {
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
                let expanded = self.expand_list(inner, depth, true, nest + 1);
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
                // last segment and the bang.
                out.push(take(&mut trees, group_idx - 2));
                out.push(take(&mut trees, group_idx - 1));
                let fmt_name = segs.last().map_or("", |s| s.text.as_str());
                let written_lit = is_str_lit_arg(&inner);
                let mut expanded_inner = self.expand_list(inner, depth, false, nest + 1)?;
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
                let mut expanded = self.expand_list(expanded, depth + 1, item_list, nest)?;
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
                if next_is_semi && (expanded.is_empty() || begins_item) {
                    next += 1;
                }
                if should_wrap(&expanded, &out, tok_at(&trees, next).map(|t| t.tok), trees.get(next), self.ctx.interner) {
                    expanded = vec![Tt::Delim(Delim::Paren, expanded, call.span)];
                }
                out.extend(expanded);
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
                let expanded = self.expand_list(inner, depth, false, nest + 1);
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
                out.push(take(&mut trees, i));
            }
            i += 1;
        }
        Ok(out)
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
                // Rebuild as the inner attribute written plainly.
                let rest: Vec<Tt> = attr.inner[split + 1.min(attr.inner.len() - split)..].to_vec();
                let fake_path = rest.iter().find_map(|t| match t {
                    Tt::Tok(tok) => seg_text(tok.tok, self.ctx.interner),
                    _ => None,
                });
                let span = attr.span;
                drop(attr);
                out.push(Tt::Tok(Token { tok: Tok::Pound, span }));
                out.push(Tt::Delim(Delim::Bracket, rest, span));
                let _ = fake_path;
                continue;
            }
            kept.push((attr, attr_start));
        }
        // A cfg that is off drops the item before expansion can see it,
        // so a disabled compile_error! or include! never runs (6.1).
        let mut exported = false;
        let mut macro_use_attr = false;
        for (attr, attr_start) in &kept {
            match attr.path.as_str() {
                "cfg" => {
                    let on = builtin::eval_cfg(&attr.inner, &self.ctx.cfg, self, attr.span)?;
                    if !on {
                        if let Some(def) = macro_rules_at(trees, after, self.ctx.interner) {
                            return Ok(def.end);
                        }
                        if let Some(end) = item_end(trees, after, self.ctx.interner) {
                            return Ok(end);
                        }
                        // Cannot bound the annotated node: leave the
                        // attribute for the parser to reject, and do not
                        // expand inside what could be called a statement.
                        let _ = attr_start;
                    }
                }
                "macro_export" => exported = true,
                "macro_use" => macro_use_attr = true,
                _ => {}
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
        self.register(Rc::new(compiled), exported, true);
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
        }
    }

    /// Expands one macro call one step: a user macro through the matcher,
    /// a token builtin through `builtin`, a parser macro through
    /// unchanged with its arguments expanded.
    pub fn expand_call(&mut self, call: &Call, depth: u32) -> Result<Vec<Tt>, Diag> {
        if depth >= 128 {
            return Err(err(
                C_CAP,
                call.span,
                format!("recursion limit reached while expanding `{}!`", call.path_text()),
                "Give the macro a base case it can reach.",
            ));
        }
        if let Some(idx) = self.lookup_macro(&call.segs, call.leading_colon) {
            let def = self.defs[idx as usize].clone();
            return self.transcribe_call(&def, call, depth);
        }
        let name = call.name_text().to_string();
        let std_prefixed = matches!(call.segs.first().map(|s| s.text.as_str()), Some("std" | "core" | "alloc"));
        if call.segs.len() == 1 || std_prefixed {
            if builtin::is_token_builtin(&name) {
                return builtin::expand_builtin(self, &name, call, depth);
            }
            if builtin::is_passthrough(&name) {
                // The head already ends with the call's `!`. The parser
                // owns only the plain `name!` form, so keep just the
                // last segment and the bang of a qualified path.
                let head = &call.head[call.head.len().saturating_sub(2)..];
                let mut out: Vec<Tt> = head.to_vec();
                let written_lit = is_str_lit_arg(&call.inner);
                let mut inner = self.expand_list(call.inner.clone(), depth, false, 0)?;
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
        self.expand_list(trees, depth + 1, false, 0)
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
        return false;
    }
    if matches!(expanded.first(), Some(Tt::Tok(t)) if t.tok == Tok::Let) {
        return false;
    }
    // After `:` in a let or field, or inside `< ... >`, the expansion is
    // most often a type; parens would make it a tuple/paren type shape.
    if matches!(prev_out.last(), Some(Tt::Tok(t)) if matches!(t.tok, Tok::Colon | Tok::Lt | Tok::As)) {
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
}
