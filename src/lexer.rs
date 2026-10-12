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

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Tok {
    Ident(Sym),
    /// A Rust 2024 keyword that cannot be used as an identifier (`gen`, `try`, `await`, and kin).
    /// The parser rejects it wherever an identifier is expected, with a clearer message.
    Reserved(Sym),
    Int(u128, Option<IntSuffix>),
    /// Index into `Lexed::strings`, holding the literal text (the parser rejects floats for now).
    Float(u32),
    /// Index into `Lexed::strings`.
    Str(u32),
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
    Char(char),
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
    strings.push(content.to_string());
    tokens.push(Token { tok: Tok::DocStr(strings.len() as u32 - 1), span: at(shift(s + 6).min(end), end) });
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
                let text = if plain { Some(src[content..close].to_string()) } else { None };
                i = close + 1 + hashes;
                match text {
                    Some(text) => {
                        strings.push(text);
                        Tok::Str(strings.len() as u32 - 1)
                    }
                    None => {
                        strings.push(src[start..i].to_string());
                        Tok::ByteStr(strings.len() as u32 - 1)
                    }
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
                        Some(_) => i += 1,
                    }
                }
                strings.push(src[start..i].to_string());
                Tok::ByteStr(strings.len() as u32 - 1)
            } else if s == "b" && b.get(i) == Some(&b'\'') {
                i += 1;
                if b.get(i) == Some(&b'\\') {
                    i += 2;
                    if b.get(i.wrapping_sub(1)) == Some(&b'x') {
                        i = (i + 2).min(b.len());
                    }
                } else if i < b.len() {
                    i += src[i..].chars().next().map_or(1, |ch| ch.len_utf8());
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
            loop {
                match b.get(i) {
                    None => return Err(err(start, i, "unterminated string literal")),
                    Some(b'"') => {
                        i += 1;
                        break;
                    }
                    Some(b'\\') => {
                        // A backslash before a newline skips the newline and leading whitespace.
                        if b.get(i + 1) == Some(&b'\n') {
                            i += 2;
                            while i < b.len() && b[i].is_ascii_whitespace() {
                                i += 1;
                            }
                            continue;
                        }
                        let ch = lex_escape(src, &mut i).ok_or_else(|| err(i, i + 2, "invalid escape"))?;
                        s.push(ch);
                    }
                    Some(_) => {
                        let ch = src[i..].chars().next().unwrap();
                        s.push(ch);
                        i += ch.len_utf8();
                    }
                }
            }
            strings.push(s);
            Tok::Str(strings.len() as u32 - 1)
        } else if c == b'\'' {
            // Either a char literal or a lifetime.
            let next = src[i + 1..].chars().next();
            let after = next.map(|ch| i + 1 + ch.len_utf8());
            if next.is_some_and(|ch| ch.is_alphabetic() || ch == '_') && after.and_then(|a| b.get(a)) != Some(&b'\'') {
                i += 1;
                let name_start = i;
                while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                    i += 1;
                }
                let name = &src[name_start..i];
                Tok::Lifetime(*cache.entry(name).or_insert_with(|| interner.intern(name)))
            } else {
                i += 1;
                let ch = if b.get(i) == Some(&b'\\') {
                    lex_escape(src, &mut i).ok_or_else(|| err(i, i + 2, "invalid escape"))?
                } else {
                    let ch = src[i..].chars().next().ok_or_else(|| err(start, i, "bad char literal"))?;
                    i += ch.len_utf8();
                    ch
                };
                if b.get(i) != Some(&b'\'') {
                    return Err(err(start, i, "unterminated char literal"));
                }
                i += 1;
                Tok::Char(ch)
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
    Some(Tok::Int(value, suffix(suf)?))
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
