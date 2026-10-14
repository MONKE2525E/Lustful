// The text rustc puts after "assertion failed: " for `assert!(cond)` with
// no message. rustc prints the parsed condition with its expression
// pretty printer (pprust::expr_to_string), so the spacing is normalized:
// binary operators and `as` get one space on each side, a comma one space
// after it, unary operators, calls, method calls, fields, and indexes none.
// Parentheses stay as written, and a macro call inside prints its tokens
// with their source spacing. This file works on the unexpanded token
// trees of the condition, so a nested macro call is still visible.
// rustc's printer breaks a text of more than 78 bytes, and a block that
// holds an item, over several lines; lust does not, so `cond_text` gives
// None for those and the caller rejects (L0809). Not covered (the text
// can differ from rustc's): generic arguments outside a turbofish or an
// `as` type.
use super::*;
use crate::lexer::Tok;

#[derive(Clone, Copy, PartialEq)]
enum Kind {
    Tok(Tok),
    Open(Delim),
    Close(Delim),
}

struct Piece {
    text: String,
    kind: Kind,
    span: Span,
    /// The role this piece has in the expression (set by `roles`).
    role: Role,
}

#[derive(Clone, Copy, PartialEq)]
enum Role {
    Plain,
    /// A binary operator or `as`: one space on each side.
    Binary,
    /// A prefix operator: no space after it.
    Unary,
    /// The `|` pair of closure parameters (`||` alone is both).
    ClosureOpen,
    ClosureClose,
    /// `<` and `>` of a turbofish or a type after `as`.
    Generic,
    /// A macro call's group and everything in it: source spacing.
    Raw,
    /// The second `>` of a `>>` operator, merged into the first.
    Gone,
}

/// rustc's pretty printer margin: a longer text breaks over lines.
const MARGIN: usize = 78;

/// The pretty-printed condition of `assert!(trees)` (expander side), or
/// None when rustc prints it over several lines.
pub fn assert_cond_text(st: &Expander, trees: &[Tt]) -> Option<String> {
    let mut flat = Vec::new();
    flatten(st, trees, &mut flat);
    cond_text(flat)
}

/// The pretty-printed condition from flat tokens: each token's text, kind
/// (delimiters as their own tokens), and span, or None when rustc prints
/// it over several lines. The parser calls this for a file the expander
/// skipped.
pub fn cond_text(flat: Vec<(String, Tok, Span)>) -> Option<String> {
    // A block that holds an item always breaks (and `unsafe` or `const`
    // blocks are not modeled): leave those to rustc.
    let item = |t: Tok| {
        use Tok::*;
        matches!(t, Fn | Struct | Enum | Impl | Trait | Use | Static | Mod | Type | Extern | Const | Unsafe)
    };
    if flat.iter().any(|(_, t, _)| item(*t)) {
        return None;
    }
    let mut pieces: Vec<Piece> = flat
        .into_iter()
        .map(|(text, tok, span)| {
            let kind = match tok {
                Tok::LParen => Kind::Open(Delim::Paren),
                Tok::LBracket => Kind::Open(Delim::Bracket),
                Tok::LBrace => Kind::Open(Delim::Brace),
                Tok::RParen => Kind::Close(Delim::Paren),
                Tok::RBracket => Kind::Close(Delim::Bracket),
                Tok::RBrace => Kind::Close(Delim::Brace),
                t => Kind::Tok(t),
            };
            Piece { text, kind, span, role: Role::Plain }
        })
        .collect();
    let mut pieces = match_commas(pieces);
    roles(&mut pieces);
    pieces.retain(|p| p.role != Role::Gone);
    let mut out = String::new();
    for i in 0..pieces.len() {
        if i > 0 && space_before(&pieces[i - 1], &pieces[i]) {
            out.push(' ');
        }
        out.push_str(&pieces[i].text);
    }
    (out.len() <= MARGIN).then_some(out)
}

/// rustc prints a comma after every match arm whose body is not a plain
/// block, and none after a block body, whatever the source wrote.
fn match_commas(p: Vec<Piece>) -> Vec<Piece> {
    let mut out = Vec::with_capacity(p.len() + 2);
    let mut p: Vec<Option<Piece>> = p.into_iter().map(Some).collect();
    let n = p.len();
    commas_in(&mut p, 0, n, &mut out);
    out
}

fn kind_at(p: &[Option<Piece>], i: usize) -> Option<Kind> {
    p.get(i).and_then(|q| q.as_ref()).map(|q| q.kind)
}

/// The index of the delimiter that closes the one at `open` (or `hi`).
fn close_at(p: &[Option<Piece>], open: usize, hi: usize) -> usize {
    let mut depth = 0i32;
    for j in open..hi {
        match kind_at(p, j) {
            Some(Kind::Open(_)) => depth += 1,
            Some(Kind::Close(_)) => {
                depth -= 1;
                if depth == 0 {
                    return j;
                }
            }
            _ => {}
        }
    }
    hi
}

/// The first index in `lo..hi` at depth 0 whose kind is `k` (or `hi`).
fn find_at_depth0(p: &[Option<Piece>], lo: usize, hi: usize, k: Kind) -> usize {
    let mut depth = 0i32;
    for j in lo..hi {
        match kind_at(p, j) {
            Some(x) if x == k && depth == 0 => return j,
            Some(Kind::Open(_)) => depth += 1,
            Some(Kind::Close(_)) => depth -= 1,
            _ => {}
        }
    }
    hi
}

/// Moves `p[lo..hi]` to `out`, fixing the arm commas of each `match`.
fn commas_in(p: &mut [Option<Piece>], lo: usize, hi: usize, out: &mut Vec<Piece>) {
    let mut i = lo;
    while i < hi {
        let open = if kind_at(p, i) == Some(Kind::Tok(Tok::Match)) { find_at_depth0(p, i + 1, hi, Kind::Open(Delim::Brace)) } else { hi };
        if open >= hi {
            out.extend(p[i].take());
            i += 1;
            continue;
        }
        // The scrutinee holds no brace at depth 0: the first `{` opens the arms.
        let close = close_at(p, open, hi);
        out.extend(p[i].take());
        commas_in(p, i + 1, open + 1, out);
        let mut j = open + 1;
        while j < close {
            let arrow = find_at_depth0(p, j, close, Kind::Tok(Tok::FatArrow));
            commas_in(p, j, (arrow + 1).min(close), out);
            if arrow >= close {
                break;
            }
            let body = arrow + 1;
            if kind_at(p, body) == Some(Kind::Open(Delim::Brace)) {
                let end = close_at(p, body, close);
                commas_in(p, body, end + 1, out);
                j = end + 1;
                if j < close && kind_at(p, j) == Some(Kind::Tok(Tok::Comma)) {
                    p[j] = None;
                    j += 1;
                }
            } else {
                let end = find_at_depth0(p, body, close, Kind::Tok(Tok::Comma));
                commas_in(p, body, end, out);
                let span = out.last().map(|q| q.span).unwrap_or_default();
                out.push(Piece { text: ",".into(), kind: Kind::Tok(Tok::Comma), span, role: Role::Plain });
                if end < close {
                    p[end] = None;
                }
                j = (end + 1).min(close);
            }
        }
        commas_in(p, j.min(close), close + 1, out);
        i = close + 1;
    }
}

fn flatten(st: &Expander, trees: &[Tt], out: &mut Vec<(String, Tok, Span)>) {
    for tree in trees {
        match tree {
            Tt::Tok(t) => {
                // `>>` is one tree here; split it back into two `>`.
                if t.tok == Tok::Shr {
                    for k in 0..2 {
                        out.push((">".into(), Tok::Gt, Span { lo: t.span.lo + k, hi: t.span.lo + k + 1, ..t.span }));
                    }
                    continue;
                }
                out.push((builtin::stringify_tok_text(st, t), t.tok, t.span))
            }
            Tt::Delim(d, inner, span) => {
                let (open, close) = match d {
                    Delim::Paren => (("(", Tok::LParen), (")", Tok::RParen)),
                    Delim::Bracket => (("[", Tok::LBracket), ("]", Tok::RBracket)),
                    Delim::Brace => (("{", Tok::LBrace), ("}", Tok::RBrace)),
                };
                out.push((open.0.into(), open.1, Span { hi: span.lo + 1, ..*span }));
                flatten(st, inner, out);
                let lo = span.hi.saturating_sub(1).max(span.lo + 1);
                out.push((close.0.into(), close.1, Span { lo, hi: lo + 1, ..*span }));
            }
            Tt::Frag(_, inner, _) => flatten(st, inner, out),
        }
    }
}

fn is_word(k: Kind) -> bool {
    matches!(
        k,
        Kind::Tok(
            Tok::Ident(_)
                | Tok::Reserved(_)
                | Tok::Int(..)
                | Tok::Float(_)
                | Tok::Str(..)
                | Tok::ByteStr(_)
                | Tok::ByteChar(_)
                | Tok::Char(..)
                | Tok::Lifetime(_)
                | Tok::True
                | Tok::False
                | Tok::SelfLower
                | Tok::SelfUpper
                | Tok::Crate
                | Tok::Super
                | Tok::Underscore
        )
    )
}

/// True when the piece ends an operand, so a following `-`, `*`, `&`,
/// `|` is binary.
fn ends_operand(p: &Piece) -> bool {
    is_word(p.kind) || matches!(p.kind, Kind::Close(_) | Kind::Tok(Tok::Question)) || p.role == Role::Generic && p.text == ">"
}

fn binary_tok(t: Tok) -> bool {
    use Tok::*;
    matches!(
        t,
        EqEq | Ne
            | Lt
            | Le
            | Gt
            | Ge
            | Plus
            | Minus
            | Star
            | Slash
            | Percent
            | Amp
            | AndAnd
            | Pipe
            | OrOr
            | Caret
            | Shl
            | Shr
            | Eq
            | PlusEq
            | MinusEq
            | StarEq
            | SlashEq
            | PercentEq
            | AmpEq
            | PipeEq
            | CaretEq
            | ShlEq
            | ShrEq
            | As
            | FatArrow
            | Arrow
            | If
            | Else
            | Match
            | In
            | Let
            | Return
            | Move
            | For
            | While
            | Loop
    )
}

fn roles(p: &mut [Piece]) {
    let mut i = 0;
    let mut generic_depth = 0u32;
    while i < p.len() {
        let prev_ends = i > 0 && ends_operand(&p[i - 1]);
        match p[i].kind {
            // A macro call: `name ! (..)`: its group keeps source spacing.
            Kind::Tok(Tok::Bang) if i > 0 && is_word(p[i - 1].kind) && matches!(p.get(i + 1).map(|q| q.kind), Some(Kind::Open(_))) => {
                let mut depth = 0;
                let mut j = i + 1;
                while j < p.len() {
                    match p[j].kind {
                        Kind::Open(_) => depth += 1,
                        Kind::Close(_) => depth -= 1,
                        _ => {}
                    }
                    p[j].role = Role::Raw;
                    j += 1;
                    if depth == 0 {
                        break;
                    }
                }
                i = j;
                continue;
            }
            Kind::Tok(Tok::Minus | Tok::Star | Tok::Amp | Tok::AndAnd | Tok::Bang) if !prev_ends => p[i].role = Role::Unary,
            // `&mut x` and `&raw const x`: the keyword hugs the `&`.
            Kind::Tok(Tok::Mut) if i > 0 && p[i - 1].role == Role::Unary => {}
            Kind::Tok(Tok::OrOr) if !prev_ends => p[i].role = Role::ClosureClose,
            Kind::Tok(Tok::Pipe) if !prev_ends => {
                p[i].role = Role::ClosureOpen;
                if let Some(j) = (i + 1..p.len()).find(|&j| p[j].kind == Kind::Tok(Tok::Pipe)) {
                    p[j].role = Role::ClosureClose;
                    // A `&` pattern in the parameters hugs what follows (`|&x|`, `|(a, &b)|`).
                    for k in i + 1..j {
                        if matches!(p[k].kind, Kind::Tok(Tok::Amp | Tok::AndAnd)) {
                            p[k].role = Role::Unary;
                        }
                    }
                    i = j + 1;
                    continue;
                }
            }
            // A turbofish `::<..>`, or a generic type after `as`.
            Kind::Tok(Tok::Lt) if i > 0 && (p[i - 1].kind == Kind::Tok(Tok::PathSep) || generic_depth > 0) => {
                p[i].role = Role::Generic;
                generic_depth += 1;
            }
            Kind::Tok(Tok::Gt) if generic_depth > 0 => {
                p[i].role = Role::Generic;
                generic_depth -= 1;
            }
            Kind::Tok(Tok::Lt) if i > 1 && p[i - 2].kind == Kind::Tok(Tok::As) => {
                p[i].role = Role::Generic;
                generic_depth += 1;
            }
            // `>` `>` touching, outside generics: the `>>` operator.
            Kind::Tok(Tok::Gt)
                if generic_depth == 0
                    && p.get(i + 1).is_some_and(|q| q.kind == Kind::Tok(Tok::Gt) && q.span.lo == p[i].span.hi && q.span.ctxt == p[i].span.ctxt) =>
            {
                p[i].text = ">>".into();
                p[i].role = Role::Binary;
                p[i + 1].role = Role::Gone;
                i += 2;
                continue;
            }
            Kind::Tok(t) if binary_tok(t) => p[i].role = Role::Binary,
            _ => {}
        }
        i += 1;
    }
}

fn space_before(prev: &Piece, cur: &Piece) -> bool {
    if cur.role == Role::Raw && prev.role == Role::Raw {
        // Source spacing inside a macro call's group.
        return cur.span.file != prev.span.file || cur.span.ctxt != prev.span.ctxt || cur.span.lo > prev.span.hi;
    }
    if prev.kind == Kind::Tok(Tok::Bang) && cur.role == Role::Raw {
        return false;
    }
    // A keyword that opens an expression (`move`, `match`, `if`) right after `(` or `[`.
    if cur.role == Role::Binary && matches!(prev.kind, Kind::Open(Delim::Paren | Delim::Bracket)) {
        return false;
    }
    if cur.role == Role::Binary || prev.role == Role::Binary {
        return true;
    }
    if prev.role == Role::ClosureClose {
        return true;
    }
    if prev.role == Role::ClosureOpen || cur.role == Role::ClosureClose {
        return false;
    }
    if prev.role == Role::Unary || prev.role == Role::Generic || cur.role == Role::Generic {
        // `&mut x`: a space after the keyword.
        return false;
    }
    if prev.kind == Kind::Tok(Tok::Mut) {
        return true;
    }
    match cur.kind {
        Kind::Tok(
            Tok::Comma | Tok::Semi | Tok::Dot | Tok::Question | Tok::PathSep | Tok::Colon | Tok::DotDot | Tok::DotDotEq | Tok::Bang,
        ) => {
            return false;
        }
        Kind::Close(Delim::Paren | Delim::Bracket) => return false,
        Kind::Close(Delim::Brace) => return prev.kind != Kind::Open(Delim::Brace),
        Kind::Open(Delim::Paren | Delim::Bracket) => {
            if ends_operand(prev) {
                return false;
            }
        }
        _ => {}
    }
    match prev.kind {
        Kind::Tok(Tok::Dot | Tok::PathSep | Tok::DotDot | Tok::DotDotEq) => false,
        Kind::Open(Delim::Paren | Delim::Bracket) => false,
        _ => true,
    }
}
