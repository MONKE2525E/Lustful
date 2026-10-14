// Lexer: turns source bytes into a flat token list. Identifiers are interned here.
use crate::diag::{Diag, FileId, Span};
use crate::intern::{FxMap, Interner, Sym};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum IntSuffix {
    I8,
    I16,
    I32,
    I64,
    Isize,
    U8,
    U16,
    U32,
    U64,
    Usize,
    I128,
    U128,
}

impl IntSuffix {
    /// The suffix as written (`u8`).
    pub fn name(self) -> &'static str {
        match self {
            IntSuffix::I8 => "i8",
            IntSuffix::I16 => "i16",
            IntSuffix::I32 => "i32",
            IntSuffix::I64 => "i64",
            IntSuffix::Isize => "isize",
            IntSuffix::U8 => "u8",
            IntSuffix::U16 => "u16",
            IntSuffix::U32 => "u32",
            IntSuffix::U64 => "u64",
            IntSuffix::Usize => "usize",
            IntSuffix::I128 => "i128",
            IntSuffix::U128 => "u128",
        }
    }
}

/// Literal tokens keep their written text, because rustc compares
/// literal tokens in macro matchers by it (`0x1` is not `1`) and
/// `stringify!` prints it. `Int`, `Str`, and `Char` carry the value the
/// parser reads plus an optional text index into `Lexed::strings`: None
/// when the text is the canonical form `lit_text` prints from the value
/// (`1`, `"a"`, `'a'`), which is also the text of a token a builtin
/// macro makes. `Float`, `ByteStr`, and `ByteChar` hold only their text.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Tok {
    Ident(Sym),
    /// A Rust 2024 keyword that cannot be used as an identifier (`gen`, `try`, `await`, and kin).
    /// The parser rejects it wherever an identifier is expected, with a clearer message.
    Reserved(Sym),
    /// Value, suffix, and written text (see above).
    Int(u128, Option<IntSuffix>, Option<u32>),
    /// Index into `Lexed::strings`, holding the literal text (the parser rejects floats for now).
    Float(u32),
    /// Indexes into `Lexed::strings`: the value, and the written text (see above).
    Str(u32, Option<u32>),
    /// The string of a doc comment (`///`, `/** */`, and kin). The lexer
    /// emits a doc comment as the `#[doc = ...]` tokens it stands for in
    /// rustc's token trees; this is the literal's index into
    /// `Lexed::strings`, holding the comment text. `stringify!` prints it
    /// as the raw string rustc prints (`r" hi"`).
    DocStr(u32),
    /// A byte string (`b".."`, `br".."`) or C string (`c".."`, `cr".."`) literal.
    /// Index into `Lexed::strings`, holding the token's verbatim source text (prefix
    /// and quotes included). The parser rejects the form before any value is needed;
    /// the text is what macro token matching and `stringify!` compare and print, so
    /// two byte literals with different bytes must not look equal here.
    ByteStr(u32),
    /// A byte char literal (`b'x'`). Like `ByteStr`, the index holds verbatim source text.
    ByteChar(u32),
    /// Value and written text (see above).
    Char(char, Option<u32>),
    /// A lifetime or loop label name, without the leading `'` (`'a`, `'static`, `'_`).
    Lifetime(Sym),
    // Keywords.
    As,
    Break,
    Const,
    Continue,
    Else,
    Enum,
    False,
    Fn,
    For,
    If,
    Impl,
    In,
    Let,
    Loop,
    Match,
    Mod,
    Mut,
    Pub,
    Ref,
    Return,
    SelfLower,
    SelfUpper,
    Static,
    Struct,
    Trait,
    True,
    Type,
    Unsafe,
    Use,
    Where,
    While,
    Async,
    Dyn,
    Move,
    Crate,
    Super,
    Extern,
    Await,
    // Punctuation.
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Semi,
    Colon,
    PathSep,
    Dot,
    DotDot,
    DotDotEq,
    /// `...`: one token tree in rustc, so macro matching and tt
    /// counting must see it whole, not as `..` plus `.`.
    Ellipsis,
    Arrow,
    FatArrow,
    Eq,
    EqEq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,
    AmpEq,
    PipeEq,
    CaretEq,
    ShlEq,
    Amp,
    AndAnd,
    Pipe,
    OrOr,
    Caret,
    Bang,
    Pound,
    Question,
    Underscore,
    Shl,
    /// `>>` as one token tree. The lexer never emits this from
    /// source (it emits two `Gt` so generics parse without
    /// splitting); the expander merges two touching `Gt` into one
    /// `Shr` when it builds token trees, because rustc's token
    /// trees hold `>>` whole, and splits it again before the
    /// parser. `ShrEq` is the same for `>>=`.
    Shr,
    ShrEq,
    Dollar,
    At,
    Eof,
}

impl Tok {
    /// The `Lexed::strings` indexes this token carries, writable: `Float`,
    /// `DocStr`, `ByteStr`, and `ByteChar` hold one, `Str` a value and
    /// maybe a text, `Int` and `Char` maybe a text. This is the one list
    /// of such kinds. Every pass that moves token streams between string
    /// tables (concat, splice, slice) or hashes their strings goes
    /// through it, so a new kind is added here only.
    pub fn string_indices_mut(&mut self) -> [Option<&mut u32>; 2] {
        match self {
            Tok::Float(i) | Tok::DocStr(i) | Tok::ByteStr(i) | Tok::ByteChar(i) => [Some(i), None],
            Tok::Str(i, text) => [Some(i), text.as_mut()],
            Tok::Int(_, _, text) | Tok::Char(_, text) => [text.as_mut(), None],
            _ => [None, None],
        }
    }

    /// The `Lexed::strings` indexes this token carries (see `string_indices_mut`).
    pub fn string_indices(mut self) -> impl Iterator<Item = u32> {
        self.string_indices_mut().map(|i| i.map(|i| *i)).into_iter().flatten()
    }

    /// Adds `offset` to every `Lexed::strings` index this token carries:
    /// the token moved to a table whose strings start `offset` later.
    pub fn shift_strings(&mut self, offset: u32) {
        for i in self.string_indices_mut().into_iter().flatten() {
            *i += offset;
        }
    }
}

/// The written text of a literal token (`0x1`, `'\x61'`, `r"a"`, a doc
/// comment's `r" hi"`), or None for any other token. rustc's macro
/// matcher compares literal tokens by this text, and `stringify!` prints
/// it. A token with no text index prints canonically from its value.
pub fn lit_text<'s>(tok: &Tok, strings: &'s [String]) -> Option<std::borrow::Cow<'s, str>> {
    use std::borrow::Cow;
    let at = |i: u32| strings.get(i as usize).map_or("", String::as_str);
    Some(match *tok {
        Tok::Int(_, _, Some(t)) | Tok::Str(_, Some(t)) | Tok::Char(_, Some(t)) | Tok::Float(t) | Tok::ByteStr(t) | Tok::ByteChar(t) => {
            Cow::Borrowed(at(t))
        }
        Tok::Int(v, suffix, None) => Cow::Owned(format!("{v}{}", suffix.map_or("", IntSuffix::name))),
        // rustc's form for a string it makes (`escape_string_symbol`).
        Tok::Str(i, None) => Cow::Owned(format!("\"{}\"", at(i).escape_debug())),
        Tok::Char(c, None) => Cow::Owned(format!("{c:?}")),
        // A doc comment's literal is the raw string rustc uses for it in
        // token streams, with enough `#`s to close safely.
        Tok::DocStr(i) => {
            let text = at(i);
            let mut hashes = 0usize;
            let bytes = text.as_bytes();
            for (j, &b) in bytes.iter().enumerate() {
                if b == b'"' {
                    let run = bytes[j + 1..].iter().take_while(|&&c| c == b'#').count();
                    hashes = hashes.max(run + 1);
                }
            }
            let marks = "#".repeat(hashes);
            Cow::Owned(format!("r{marks}\"{text}\"{marks}"))
        }
        _ => return None,
    })
}

/// A delimiter kind for token trees.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Delim {
    Paren,
    Bracket,
    Brace,
}

/// One token tree: a single token, or a delimited group of trees. Macro calls and
/// attributes in the AST hold token trees; the expander (docs/ARCH.md section 6) is
/// their first consumer. The parser builds trees only for the shapes it stores.
#[allow(dead_code)] // Delimiter kinds and spans are first read by macro expansion.
#[derive(Clone, Debug)]
pub enum TokenTree {
    Token(Token),
    Delim(Delim, Vec<TokenTree>, Span),
}

#[derive(Clone, Copy, Debug)]
pub struct Token {
    pub tok: Tok,
    pub span: Span,
}

/// Groups a flat token slice into nested token trees, skipping a final `Eof`
/// token. Returns the trees and true when every delimiter was balanced. On
/// unbalanced input the trees nest on a best-effort basis (an unclosed group
/// runs to the end) and the flag is false; callers that need balance check it.
pub fn build_trees(toks: &[Token]) -> (Vec<TokenTree>, bool) {
    fn open(t: Tok) -> Option<Delim> {
        match t {
            Tok::LParen => Some(Delim::Paren),
            Tok::LBracket => Some(Delim::Bracket),
            Tok::LBrace => Some(Delim::Brace),
            _ => None,
        }
    }
    fn closes(d: Delim, t: Tok) -> bool {
        matches!((d, t), (Delim::Paren, Tok::RParen) | (Delim::Bracket, Tok::RBracket) | (Delim::Brace, Tok::RBrace))
    }
    fn is_close(t: Tok) -> bool {
        matches!(t, Tok::RParen | Tok::RBracket | Tok::RBrace)
    }
    // One stack frame per open delimiter: its kind, opening span, and trees so far.
    let mut stack: Vec<(Delim, Span, Vec<TokenTree>)> = Vec::new();
    let mut out: Vec<TokenTree> = Vec::new();
    let mut balanced = true;
    for t in toks {
        if t.tok == Tok::Eof {
            break;
        }
        if let Some(d) = open(t.tok) {
            stack.push((d, t.span, Vec::new()));
            continue;
        }
        if is_close(t.tok) {
            match stack.last() {
                Some((d, _, _)) if closes(*d, t.tok) => {
                    let (d, span, inner) = stack.pop().unwrap();
                    // A group's span covers both delimiters, so spacing
                    // readers (`stringify!`) can see where it ends.
                    let tree = TokenTree::Delim(d, inner, span.to(t.span));
                    match stack.last_mut() {
                        Some((_, _, parent)) => parent.push(tree),
                        None => out.push(tree),
                    }
                }
                _ => {
                    balanced = false;
                    match stack.last_mut() {
                        Some((_, _, parent)) => parent.push(TokenTree::Token(*t)),
                        None => out.push(TokenTree::Token(*t)),
                    }
                }
            }
            continue;
        }
        match stack.last_mut() {
            Some((_, _, parent)) => parent.push(TokenTree::Token(*t)),
            None => out.push(TokenTree::Token(*t)),
        }
    }
    if !stack.is_empty() {
        balanced = false;
        // Close what is left, innermost first, so no token is dropped.
        while let Some((d, span, inner)) = stack.pop() {
            let tree = TokenTree::Delim(d, inner, span);
            match stack.last_mut() {
                Some((_, _, parent)) => parent.push(tree),
                None => out.push(tree),
            }
        }
    }
    (out, balanced)
}

/// Flattens token trees back into a flat token list, re-creating the closing
/// delimiter tokens from each group's kind and span. The worklist path
/// (ARCH 6.1) reads this when it owns expansion; today's expander
/// flattens its own tree type.
#[allow(dead_code)]
pub fn flatten_trees(trees: &[TokenTree], out: &mut Vec<Token>) {
    for tree in trees {
        match tree {
            TokenTree::Token(t) => out.push(*t),
            TokenTree::Delim(d, inner, span) => {
                let (open, close) = match d {
                    Delim::Paren => (Tok::LParen, Tok::RParen),
                    Delim::Bracket => (Tok::LBracket, Tok::RBracket),
                    Delim::Brace => (Tok::LBrace, Tok::RBrace),
                };
                out.push(Token { tok: open, span: *span });
                flatten_trees(inner, out);
                out.push(Token { tok: close, span: *span });
            }
        }
    }
}

#[derive(Clone)]
pub struct Lexed {
    pub tokens: Vec<Token>,
    pub strings: Vec<String>,
}

fn keyword(s: &str) -> Option<Tok> {
    Some(match s {
        "as" => Tok::As,
        "break" => Tok::Break,
        "const" => Tok::Const,
        "continue" => Tok::Continue,
        "else" => Tok::Else,
        "enum" => Tok::Enum,
        "false" => Tok::False,
        "fn" => Tok::Fn,
        "for" => Tok::For,
        "if" => Tok::If,
        "impl" => Tok::Impl,
        "in" => Tok::In,
        "let" => Tok::Let,
        "loop" => Tok::Loop,
        "match" => Tok::Match,
        "mod" => Tok::Mod,
        "mut" => Tok::Mut,
        "pub" => Tok::Pub,
        "ref" => Tok::Ref,
        "return" => Tok::Return,
        "self" => Tok::SelfLower,
        "Self" => Tok::SelfUpper,
        "static" => Tok::Static,
        "struct" => Tok::Struct,
        "trait" => Tok::Trait,
        "true" => Tok::True,
        "type" => Tok::Type,
        "unsafe" => Tok::Unsafe,
        "use" => Tok::Use,
        "where" => Tok::Where,
        "while" => Tok::While,
        "async" => Tok::Async,
        "dyn" => Tok::Dyn,
        "move" => Tok::Move,
        "crate" => Tok::Crate,
        "super" => Tok::Super,
        "extern" => Tok::Extern,
        "await" => Tok::Await,
        "_" => Tok::Underscore,
        _ => return None,
    })
}

/// Keywords of Rust 2024 (strict and reserved) that have no token of their own here.
/// Weak keywords such as `union`, `safe`, and `macro_rules` stay usable as identifiers, as in rustc.
/// `crate`, `super`, `extern`, and `await` have their own tokens so the parser can
/// recognize paths, extern items, and `.await` and reject them with the right code.
fn reserved(s: &str) -> bool {
    matches!(
        s,
        "abstract"
            | "become"
            | "box"
            | "do"
            | "final"
            | "gen"
            | "macro"
            | "override"
            | "priv"
            | "try"
            | "typeof"
            | "unsized"
            | "virtual"
            | "yield"
    )
}

/// Names that rustc does not allow even as raw identifiers (`r#self` and friends).
fn raw_ident_invalid(s: &str) -> bool {
    matches!(s, "self" | "Self" | "super" | "crate" | "_")
}

/// True when a lifetime token named `name` was written raw (`'r#fn`): the
/// token keeps only the name, and its span also covers the `r#`.
pub fn lifetime_is_raw(name: &str, span: Span) -> bool {
    span.hi.saturating_sub(span.lo) as usize == name.len() + 3
}

/// The error rustc's parser reports for a lifetime (or, with `label`, a
/// loop label) named by a keyword, such as `'fn` or `'gen`, or None when
/// the name is fine. A raw name (`'r#fn`) is fine, and so are the
/// lifetimes `'_` and `'static` (not the labels). Token trees may hold
/// such names (`stringify!('fn)`): the error is for parsed lifetime and
/// label positions only, which call this.
pub fn keyword_lifetime_error(name: &str, raw: bool, label: bool, span: Span) -> Option<Diag> {
    if raw || (keyword(name).is_none() && !reserved(name)) || (!label && matches!(name, "_" | "static")) {
        return None;
    }
    let what = if label { "labels" } else { "lifetimes" };
    Some(Diag::new("L0001", span, format!("{what} cannot use keyword names"), format!("Rename `'{name}`, for example to `'a`.")))
}

fn suffix(s: &str) -> Option<Option<IntSuffix>> {
    use IntSuffix::*;
    Some(Some(match s {
        "" => return Some(None),
        "i8" => I8,
        "i16" => I16,
        "i32" => I32,
        "i64" => I64,
        "isize" => Isize,
        "u8" => U8,
        "u16" => U16,
        "u32" => U32,
        "u64" => U64,
        "usize" => Usize,
        "i128" => I128,
        "u128" => U128,
        _ => return None,
    }))
}

/// Emits one doc comment as the attribute tokens it stands for:
/// `#[doc = "content"]`, or `#![doc = "content"]` for an inner comment.
/// Spans tile the comment's own bytes in token order (with one-byte gaps
/// where `stringify!` prints spaces), so positions stay inside the
/// comment and the tokens that follow keep their own.
#[allow(clippy::too_many_arguments)]
fn push_doc_tokens(
    tokens: &mut Vec<Token>,
    strings: &mut Vec<String>,
    interner: &Interner,
    file: FileId,
    base: u32,
    start: usize,
    end: usize,
    content: &str,
    inner: bool,
) {
    let at = |lo: usize, hi: usize| Span::new(file, base + lo as u32, base + hi as u32);
    let s = start;
    let shift = |n: usize| if inner { n + 1 } else { n };
    tokens.push(Token { tok: Tok::Pound, span: at(s, s + 1) });
    if inner {
        tokens.push(Token { tok: Tok::Bang, span: at(s + 1, s + 2) });
    }
    tokens.push(Token { tok: Tok::LBracket, span: at(shift(s + 1), shift(s + 2)) });
    tokens.push(Token { tok: Tok::Ident(interner.intern("doc")), span: at(shift(s + 2), shift(s + 3)) });
    tokens.push(Token { tok: Tok::Eq, span: at(shift(s + 4), shift(s + 5)) });
    let content = push_text(strings, content);
    tokens.push(Token { tok: Tok::DocStr(content), span: at(shift(s + 6).min(end), end) });
    tokens.push(Token { tok: Tok::RBracket, span: at(end, end) });
}

/// Lexes `src`, which starts at byte `base` of file `file`. Every token span names that
/// file with the root context. Stops at the first error.
pub fn lex(src: &str, file: FileId, base: u32, interner: &Interner) -> Result<Lexed, Diag> {
    let b = src.as_bytes();
    let mut tokens = Vec::with_capacity(src.len() / 4);
    let mut strings = Vec::new();
    let mut i = 0usize;
    // Local cache in front of the shared interner, so repeated names skip its lock.
    let mut cache: FxMap<&str, Sym> = FxMap::default();
    let err = |start: usize, end: usize, msg: &str| {
        Diag::new("L0001", Span::new(file, base + start as u32, base + end as u32), msg, "Fix the syntax.")
    };
    // A shebang line (`#!/usr/bin/env ...`) at the very start of a file is
    // skipped, as in rustc. `#!` followed (after spaces) by `[` is an inner
    // attribute, not a shebang. Only a file's first bytes qualify: `base`
    // is zero exactly for a whole file, not for a chunk of one.
    if base == 0 && b.get(..2) == Some(b"#!") {
        let mut j = 2;
        while matches!(b.get(j), Some(b' ' | b'\t')) {
            j += 1;
        }
        if b.get(j) != Some(&b'[') {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
        }
    }
    while i < b.len() {
        let c = b[i];
        let start = i;
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        if c == b'/' && b.get(i + 1) == Some(&b'/') {
            while i < b.len() && b[i] != b'\n' {
                i += 1;
            }
            // A doc comment is tokens (`#[doc = ...]`), not whitespace:
            // macro inputs count it as two token trees. `////` is plain.
            let inner = b.get(start + 2) == Some(&b'!');
            if inner || (b.get(start + 2) == Some(&b'/') && b.get(start + 3) != Some(&b'/')) {
                let content = src[start + 3..i].strip_suffix('\r').unwrap_or(&src[start + 3..i]);
                if let Some(at) = bare_cr(content.as_bytes()) {
                    return Err(err(start + 3 + at, start + 4 + at, "bare CR not allowed in doc-comment"));
                }
                push_doc_tokens(&mut tokens, &mut strings, interner, file, base, start, i, content, inner);
            }
            continue;
        }
        if c == b'/' && b.get(i + 1) == Some(&b'*') {
            let mut depth = 0;
            while i < b.len() {
                if b[i] == b'/' && b.get(i + 1) == Some(&b'*') {
                    depth += 1;
                    i += 2;
                } else if b[i] == b'*' && b.get(i + 1) == Some(&b'/') {
                    depth -= 1;
                    i += 2;
                    if depth == 0 {
                        break;
                    }
                } else {
                    i += 1;
                }
            }
            if depth != 0 {
                return Err(err(start, i, "unterminated block comment"));
            }
            // `/*! .. */` and `/** .. */` are doc comments; `/***` and
            // `/**/` are plain block comments.
            let inner = b.get(start + 2) == Some(&b'!');
            let outer = b.get(start + 2) == Some(&b'*') && b.get(start + 3) != Some(&b'*') && &b[start..i] != b"/**/";
            if (inner || outer) && i >= start + 5 {
                if let Some(at) = bare_cr(&b[start + 3..i - 2]) {
                    return Err(err(start + 3 + at, start + 4 + at, "bare CR not allowed in doc-comment"));
                }
                push_doc_tokens(&mut tokens, &mut strings, interner, file, base, start, i, &src[start + 3..i - 2], inner);
            }
            continue;
        }
        if c == b'#' && b.get(i + 1) == Some(&b'#') {
            return Err(err(start, i + 2, "reserved multi-hash token is forbidden"));
        }
        if c == b'#' && b.get(i + 1) == Some(&b'"') {
            return Err(err(start, i + 2, "invalid string literal"));
        }
        let tok = if c.is_ascii_alphabetic() || c == b'_' || c >= 0x80 {
            while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] >= 0x80) {
                i += 1;
            }
            let s = &src[start..i];
            // Literal prefixes: raw strings (`r".."`, `r#".."#`), byte strings and C
            // strings (`b".."`, `br".."`, `c".."`, `cr".."`) and byte chars (`b'x'`).
            // A raw string is an ordinary string with the same value, so it lexes to
            // `Tok::Str`. Byte and C forms lex to their own tokens for the parser to reject.
            if let ("r" | "br" | "cr", Some(hashes)) = (s, raw_open(b, i)) {
                let plain = s == "r";
                i += hashes + 1; // `#` run plus the opening quote
                let content = i;
                let mut close = None;
                while i < b.len() {
                    if b[i] == b'"' && (0..hashes).all(|k| b.get(i + 1 + k) == Some(&b'#')) {
                        close = Some(i);
                        break;
                    }
                    i += 1;
                }
                let Some(close) = close else {
                    return Err(err(start, i, "unterminated raw string literal"));
                };
                if let Some(at) = bare_cr(&b[content..close]) {
                    return Err(err(content + at, content + at + 1, "bare CR not allowed in raw string"));
                }
                i = close + 1 + hashes;
                if plain {
                    // The value, then the written text (never canonical: it has the `r`).
                    strings.push(src[content..close].replace("\r\n", "\n"));
                    let value = strings.len() as u32 - 1;
                    Tok::Str(value, Some(push_text(&mut strings, &src[start..i])))
                } else {
                    Tok::ByteStr(push_text(&mut strings, &src[start..i]))
                }
            } else if (s == "b" || s == "c") && b.get(i) == Some(&b'"') {
                i += 1;
                loop {
                    match b.get(i) {
                        None => return Err(err(start, i, "unterminated byte or C string literal")),
                        Some(b'"') => {
                            i += 1;
                            break;
                        }
                        Some(b'\\') => i = (i + 2).min(b.len()),
                        Some(b'\r') if b.get(i + 1) != Some(&b'\n') => {
                            return Err(err(i, i + 1, "bare CR not allowed in string, use `\\r` instead"));
                        }
                        Some(_) => i += 1,
                    }
                }
                Tok::ByteStr(push_text(&mut strings, &src[start..i]))
            } else if s == "b" && b.get(i) == Some(&b'\'') {
                i += 1;
                if b.get(i) == Some(&b'\\') {
                    i += 2;
                    if b.get(i.wrapping_sub(1)) == Some(&b'x') {
                        i = (i + 2).min(b.len());
                    }
                } else if let Some(ch) = src[i..].chars().next() {
                    if let Some(esc) = must_escape(ch) {
                        return Err(err(i, i + ch.len_utf8(), &format!("byte constant must be escaped: `{esc}`")));
                    }
                    i += ch.len_utf8();
                }
                if b.get(i) != Some(&b'\'') {
                    return Err(err(start, i, "unterminated byte char literal"));
                }
                i += 1;
                strings.push(src[start..i].to_string());
                Tok::ByteChar(strings.len() as u32 - 1)
            } else if raw_open(b, i).is_some() || b.get(i) == Some(&b'\'') {
                // An identifier right against a quote is a reserved
                // literal prefix (`f"x"`, `f#"x"#`, `f'x'`): rustc
                // rejects every prefix but the ones handled above.
                return Err(Diag::new(
                    "L0001",
                    Span::new(file, base + start as u32, base + i as u32),
                    format!("prefix `{s}` is unknown"),
                    "Prefixed identifiers and literals are reserved. Insert whitespace, or use a known prefix (r, b, c, br, cr).",
                ));
            }
            // A raw identifier: `r#name`. The name may be any keyword except a few (see above).
            else if s == "r"
                && b.get(i) == Some(&b'#')
                && b.get(i + 1).is_some_and(|&n| n.is_ascii_alphabetic() || n == b'_' || n >= 0x80)
            {
                i += 1;
                let name_start = i;
                while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_' || b[i] >= 0x80) {
                    i += 1;
                }
                let name = &src[name_start..i];
                if raw_ident_invalid(name) {
                    return Err(Diag::new(
                        "L0001",
                        Span::new(file, base + start as u32, base + i as u32),
                        format!("`r#{name}` is not a valid identifier"),
                        "Use a different name. `self`, `Self`, `super`, `crate`, and `_` cannot be raw identifiers.",
                    ));
                }
                Tok::Ident(*cache.entry(name).or_insert_with(|| interner.intern(name)))
            } else if let Some(k) = keyword(s) {
                k
            } else if reserved(s) {
                Tok::Reserved(*cache.entry(s).or_insert_with(|| interner.intern(s)))
            } else {
                Tok::Ident(*cache.entry(s).or_insert_with(|| interner.intern(s)))
            }
        } else if c.is_ascii_digit() {
            lex_number(src, &mut i, &mut strings).ok_or_else(|| err(start, i, "invalid number literal"))?
        } else if c == b'"' {
            i += 1;
            let mut s = String::new();
            // The text is canonical (`lit_text` prints it back from the
            // value) with no escape and only printable ASCII but `'`.
            let mut canonical = true;
            loop {
                match b.get(i) {
                    None => return Err(err(start, i, "unterminated string literal")),
                    Some(b'"') => {
                        i += 1;
                        break;
                    }
                    Some(b'\\') => {
                        canonical = false;
                        // A backslash before a newline skips the newline and
                        // the spaces, tabs, and newlines after it.
                        let newline = match (b.get(i + 1), b.get(i + 2)) {
                            (Some(b'\n'), _) => 1,
                            (Some(b'\r'), Some(b'\n')) => 2,
                            _ => 0,
                        };
                        if newline > 0 {
                            i += 1 + newline;
                            while i < b.len() && matches!(b[i], b' ' | b'\t' | b'\n' | b'\r') {
                                i += 1;
                            }
                            continue;
                        }
                        let ch = lex_escape(src, &mut i).ok_or_else(|| err(i, i + 2, "invalid escape"))?;
                        s.push(ch);
                    }
                    // rustc reads CRLF as LF (the LF is read next round); a bare CR is an error.
                    Some(b'\r') => {
                        if b.get(i + 1) != Some(&b'\n') {
                            return Err(err(i, i + 1, "bare CR not allowed in string, use `\\r` instead"));
                        }
                        canonical = false;
                        i += 1;
                    }
                    Some(_) => {
                        let ch = src[i..].chars().next().unwrap();
                        canonical &= (' '..='~').contains(&ch) && ch != '\'';
                        s.push(ch);
                        i += ch.len_utf8();
                    }
                }
            }
            strings.push(s);
            let value = strings.len() as u32 - 1;
            Tok::Str(value, (!canonical).then(|| push_text(&mut strings, &src[start..i])))
        } else if c == b'\'' {
            // Either a char literal or a lifetime.
            let next = src[i + 1..].chars().next();
            let after = next.map(|ch| i + 1 + ch.len_utf8());
            if next.is_some_and(|ch| ch.is_alphabetic() || ch == '_') && after.and_then(|a| b.get(a)) != Some(&b'\'') {
                i += 1;
                let mut name_start = i;
                while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                    i += 1;
                }
                // A raw lifetime: `'r#name`. The token keeps the name; its
                // span still covers the `r#`, which macro matching reads.
                if &src[name_start..i] == "r" && b.get(i) == Some(&b'#') && b.get(i + 1).is_some_and(|&n| n.is_ascii_alphabetic() || n == b'_') {
                    i += 1;
                    name_start = i;
                    while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                        i += 1;
                    }
                    let name = &src[name_start..i];
                    if raw_ident_invalid(name) {
                        return Err(Diag::new(
                            "L0001",
                            Span::new(file, base + start as u32, base + i as u32),
                            format!("`{name}` cannot be a raw lifetime"),
                            "Use a different name. `self`, `Self`, `super`, `crate`, and `_` cannot be raw lifetimes.",
                        ));
                    }
                }
                let name = &src[name_start..i];
                Tok::Lifetime(*cache.entry(name).or_insert_with(|| interner.intern(name)))
            } else {
                i += 1;
                let escaped = b.get(i) == Some(&b'\\');
                let ch = if escaped {
                    lex_escape(src, &mut i).ok_or_else(|| err(i, i + 2, "invalid escape"))?
                } else {
                    let ch = src[i..].chars().next().ok_or_else(|| err(start, i, "bad char literal"))?;
                    if let Some(esc) = must_escape(ch) {
                        return Err(err(i, i + ch.len_utf8(), &format!("character constant must be escaped: `{esc}`")));
                    }
                    i += ch.len_utf8();
                    ch
                };
                if b.get(i) != Some(&b'\'') {
                    return Err(err(start, i, "unterminated char literal"));
                }
                i += 1;
                // Canonical text (see the string case): unescaped printable ASCII.
                let canonical = !escaped && (' '..='~').contains(&ch);
                Tok::Char(ch, (!canonical).then(|| push_text(&mut strings, &src[start..i])))
            }
        } else {
            // `#` runs are reserved in edition 2024: a guarded string
            // (`#"x"#`) and a multi-hash (`##`) are lexer errors, not
            // a `#` token next to a literal or another `#`.
            if c == b'#' && b.get(i + 1) == Some(&b'"') {
                return Err(err(start, start + 2, "invalid string literal: unprefixed guarded strings are reserved"));
            }
            if c == b'#' && b.get(i + 1) == Some(&b'#') {
                return Err(err(start, start + 2, "reserved multi-hash token is forbidden"));
            }
            let two = if i + 1 < b.len() { &b[i..i + 2] } else { &b[i..i + 1] };
            let three = if i + 2 < b.len() { &b[i..i + 3] } else { &[][..] };
            let (t, n) = if three == b"..=" {
                (Tok::DotDotEq, 3)
            } else if three == b"..." {
                (Tok::Ellipsis, 3)
            } else if three == b"<<=" {
                (Tok::ShlEq, 3)
            } else {
                match two {
                    b"::" => (Tok::PathSep, 2),
                    b".." => (Tok::DotDot, 2),
                    b"->" => (Tok::Arrow, 2),
                    b"=>" => (Tok::FatArrow, 2),
                    b"==" => (Tok::EqEq, 2),
                    b"!=" => (Tok::Ne, 2),
                    b"<=" => (Tok::Le, 2),
                    b">=" => (Tok::Ge, 2),
                    b"+=" => (Tok::PlusEq, 2),
                    b"-=" => (Tok::MinusEq, 2),
                    b"*=" => (Tok::StarEq, 2),
                    b"/=" => (Tok::SlashEq, 2),
                    b"%=" => (Tok::PercentEq, 2),
                    b"&=" => (Tok::AmpEq, 2),
                    b"|=" => (Tok::PipeEq, 2),
                    b"^=" => (Tok::CaretEq, 2),
                    b"&&" => (Tok::AndAnd, 2),
                    b"||" => (Tok::OrOr, 2),
                    b"<<" => (Tok::Shl, 2),
                    _ => (
                        match c {
                            b'(' => Tok::LParen,
                            b')' => Tok::RParen,
                            b'{' => Tok::LBrace,
                            b'}' => Tok::RBrace,
                            b'[' => Tok::LBracket,
                            b']' => Tok::RBracket,
                            b',' => Tok::Comma,
                            b';' => Tok::Semi,
                            b':' => Tok::Colon,
                            b'.' => Tok::Dot,
                            b'=' => Tok::Eq,
                            b'<' => Tok::Lt,
                            b'>' => Tok::Gt,
                            b'+' => Tok::Plus,
                            b'-' => Tok::Minus,
                            b'*' => Tok::Star,
                            b'/' => Tok::Slash,
                            b'%' => Tok::Percent,
                            b'&' => Tok::Amp,
                            b'|' => Tok::Pipe,
                            b'^' => Tok::Caret,
                            b'!' => Tok::Bang,
                            b'#' => Tok::Pound,
                            b'?' => Tok::Question,
                            b'$' => Tok::Dollar,
                            b'@' => Tok::At,
                            _ => return Err(err(start, start + 1, "unexpected character")),
                        },
                        1,
                    ),
                }
            };
            i += n;
            t
        };
        tokens.push(Token { tok, span: Span::new(file, base + start as u32, base + i as u32) });
    }
    let end = base + b.len() as u32;
    tokens.push(Token { tok: Tok::Eof, span: Span::new(file, end, end) });
    Ok(Lexed { tokens, strings })
}

// `>>` is never lexed as one token, so generics like `Vec<Vec<i64>>` parse without splitting.
// The parser joins two `>` tokens into a shift when they touch.

/// Stores a literal's written text and returns its `Lexed::strings`
/// index. rustc reads the file with every CRLF as LF, so the text does.
fn push_text(strings: &mut Vec<String>, text: &str) -> u32 {
    strings.push(if text.contains('\r') { text.replace("\r\n", "\n") } else { text.to_string() });
    strings.len() as u32 - 1
}

/// The offset of the first CR in `bytes` that does not start a CRLF:
/// rustc rejects one inside a string literal.
fn bare_cr(bytes: &[u8]) -> Option<usize> {
    (0..bytes.len()).find(|&k| bytes[k] == b'\r' && bytes.get(k + 1) != Some(&b'\n'))
}

/// How rustc spells a char that a char or byte literal must escape, or
/// None when it may stand as written.
fn must_escape(ch: char) -> Option<&'static str> {
    Some(match ch {
        '\'' => "'",
        '\n' => "\\n",
        '\r' => "\\r",
        '\t' => "\\t",
        _ => return None,
    })
}

/// If a raw string opening (`#` run plus `"`) starts at `i`, returns the `#` count.
fn raw_open(b: &[u8], i: usize) -> Option<usize> {
    let mut hashes = 0;
    while b.get(i + hashes) == Some(&b'#') {
        hashes += 1;
    }
    (b.get(i + hashes) == Some(&b'"')).then_some(hashes)
}

/// Stores a float literal's text in `strings` and returns its token.
fn float_tok(src: &str, start: usize, end: usize, strings: &mut Vec<String>) -> Tok {
    strings.push(src[start..end].to_string());
    Tok::Float(strings.len() as u32 - 1)
}

fn lex_number(src: &str, i: &mut usize, strings: &mut Vec<String>) -> Option<Tok> {
    let b = src.as_bytes();
    let start = *i;
    let (radix, digits_start) = match (b[start], b.get(start + 1)) {
        (b'0', Some(b'x')) => (16, start + 2),
        (b'0', Some(b'o')) => (8, start + 2),
        (b'0', Some(b'b')) => (2, start + 2),
        _ => (10, start),
    };
    *i = digits_start;
    while *i < b.len() && (b[*i].is_ascii_hexdigit() && radix == 16 || b[*i].is_ascii_digit() || b[*i] == b'_') {
        *i += 1;
    }
    // A float literal: `1.5`, `1.`, or `1e3`. Not `1..2` (range) and
    // not `1.foo()` (field): the dot joins the float unless another
    // dot or an identifier start follows it.
    let dot_joins = radix == 10
        && b.get(*i) == Some(&b'.')
        && !matches!(b.get(*i + 1), Some(c) if *c == b'.' || *c == b'_' || c.is_ascii_alphabetic() || *c >= 0x80);
    if dot_joins {
        *i += 1;
        while *i < b.len() && (b[*i].is_ascii_alphanumeric() || b[*i] == b'_') {
            *i += 1;
        }
        // An exponent sign right after `e` belongs to the literal (`1.5e-3`).
        if *i >= 2 && (b[*i - 1] == b'e' || b[*i - 1] == b'E') && matches!(b.get(*i), Some(b'+' | b'-')) {
            *i += 1;
            while *i < b.len() && (b[*i].is_ascii_alphanumeric() || b[*i] == b'_') {
                *i += 1;
            }
        }
        return Some(float_tok(src, start, *i, strings));
    }
    // A trailing dot with no digits after it is still a float (`1.`) when
    // the dot does not start a range (`1..2`) or a field or method name
    // (`1.foo()`): rustc lexes it as one float literal token.
    if radix == 10
        && b.get(*i) == Some(&b'.')
        && b.get(*i + 1) != Some(&b'.')
        && !b.get(*i + 1).is_some_and(|c| c.is_ascii_alphabetic() || *c == b'_' || *c >= 0x80)
    {
        *i += 1;
        return Some(float_tok(src, start, *i, strings));
    }
    // An exponent with no dot: `1e3`, `1e-3`, `1e3f64`. Not an identifier suffix:
    // the exponent needs at least one digit after the optional sign.
    if radix == 10 && matches!(b.get(*i), Some(b'e' | b'E')) {
        let mut j = *i + 1;
        if matches!(b.get(j), Some(b'+' | b'-')) {
            j += 1;
        }
        if b.get(j).is_some_and(|c| c.is_ascii_digit()) {
            *i = j;
            while *i < b.len() && (b[*i].is_ascii_alphanumeric() || b[*i] == b'_') {
                *i += 1;
            }
            return Some(float_tok(src, start, *i, strings));
        }
    }
    let digits_end = *i;
    let suf_start = *i;
    while *i < b.len() && (b[*i].is_ascii_alphanumeric() || b[*i] == b'_') {
        *i += 1;
    }
    let suf = &src[suf_start..*i];
    if suf == "f32" || suf == "f64" {
        return Some(float_tok(src, start, *i, strings));
    }
    // Accumulate digits directly; underscores are separators.
    let mut value: u128 = 0;
    let mut any = false;
    for &c in &b[digits_start..digits_end] {
        if c == b'_' {
            continue;
        }
        let d = (c as char).to_digit(radix)? as u128;
        value = value.checked_mul(radix as u128)?.checked_add(d)?;
        any = true;
    }
    if !any {
        return None;
    }
    let suffix = suffix(suf)?;
    // The text is canonical (`lit_text` prints it back from the value)
    // when it is plain decimal: no radix prefix, `_`, or leading zero.
    let text = &src[start..*i];
    let canonical = radix == 10 && !text.contains('_') && !(text.len() > 1 && text.starts_with('0') && b[start + 1].is_ascii_digit());
    Some(Tok::Int(value, suffix, (!canonical).then(|| push_text(strings, text))))
}

fn lex_escape(src: &str, i: &mut usize) -> Option<char> {
    let b = src.as_bytes();
    let c = *b.get(*i + 1)?;
    *i += 2;
    Some(match c {
        b'n' => '\n',
        b't' => '\t',
        b'r' => '\r',
        b'0' => '\0',
        b'\\' => '\\',
        b'\'' => '\'',
        b'"' => '"',
        b'x' => {
            let v = u8::from_str_radix(src.get(*i..*i + 2)?, 16).ok()?;
            *i += 2;
            if v > 0x7f {
                return None;
            }
            v as char
        }
        b'u' => {
            if b.get(*i) != Some(&b'{') {
                return None;
            }
            let end = src[*i..].find('}')? + *i;
            let v = u32::from_str_radix(&src[*i + 1..end].replace('_', ""), 16).ok()?;
            *i = end + 1;
            char::from_u32(v)?
        }
        _ => return None,
    })
}
