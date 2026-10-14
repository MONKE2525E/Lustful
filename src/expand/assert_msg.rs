// The text rustc puts after "assertion failed: " for `assert!(cond)` with
// no message. rustc prints the parsed condition with its expression
// pretty printer (pprust::expr_to_string), so the spacing is normalized:
// binary operators and `as` get one space on each side, a comma one space
// after it, unary operators, calls, method calls, fields, and indexes none.
// Parentheses stay as written, and a macro call inside prints its tokens
// with their source spacing. This file works on the unexpanded token
// trees of the condition, so a nested macro call is still visible.
// Not covered (the text can differ from rustc's): blocks with statements
// (pprust breaks them over lines), labels, and generic arguments outside
// a turbofish or an `as` type.
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
}

/// The pretty-printed condition of `assert!(trees)` (expander side).
pub fn assert_cond_text(st: &Expander, trees: &[Tt]) -> String {
    let mut flat = Vec::new();
    flatten(st, trees, &mut flat);
    cond_text(flat)
}

/// The pretty-printed condition from flat tokens: each token's text, kind
/// (delimiters as their own tokens), and span. The parser calls this for
/// a file the expander skipped.
pub fn cond_text(flat: Vec<(String, Tok, Span)>) -> String {
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
    roles(&mut pieces);
    let mut out = String::new();
    for i in 0..pieces.len() {
        if i > 0 && space_before(&pieces[i - 1], &pieces[i]) {
            out.push(' ');
        }
        out.push_str(&pieces[i].text);
    }
    out
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
