// Input and target checks for the built-in attributes the parser accepts
// and otherwise ignores (`inline`, `cold`, `must_use`, `deprecated`,
// `repr` targets, `test`, and the lint levels). rustc rejects a malformed
// input or a wrong target for these, so ignoring the attribute would be a
// false accept. A lint raised to deny or forbid is L0531: rustc would
// reject code that triggers the lint, and lust does not check lints.
use super::PResult;
use crate::ast::{Attr, AttrInput};
use crate::diag::Diag;
use crate::intern::Interner;
use crate::lexer::{Delim, Tok, TokenTree};

/// The code for a built-in attribute with a malformed input or on a
/// target rustc does not permit.
const C_ATTR_USE: &str = "L0524";

/// Lint tools whose lints rustc itself never raises: a level on one of
/// them cannot reject a program under rustc.
const LINT_TOOLS: &[&str] = &["clippy", "rustdoc"];

/// Checks the input shape of one single-segment attribute named `name`.
/// Called for every attribute the parser keeps; names it does not judge
/// pass.
pub(super) fn check_input(name: &str, attr: &Attr, interner: &Interner) -> PResult<()> {
    let ok = match name {
        "inline" => match &attr.input {
            AttrInput::None => true,
            AttrInput::List(Delim::Paren, t) => {
                matches!(t.as_slice(), [TokenTree::Token(x)] if matches!(x.tok, Tok::Ident(s) if matches!(interner.get(s), "always" | "never")))
            }
            _ => false,
        },
        "cold" | "test" => matches!(attr.input, AttrInput::None),
        "must_use" => matches!(&attr.input, AttrInput::None) || eq_str(&attr.input),
        "deprecated" => match &attr.input {
            AttrInput::None => true,
            AttrInput::List(Delim::Paren, t) => deprecated_list(t, interner),
            other => eq_str(other),
        },
        "allow" | "warn" | "deny" | "forbid" => return lint_list(name, attr, interner),
        _ => true,
    };
    if ok { Ok(()) } else { Err(malformed(name, attr)) }
}

/// Rejects `inline` and `repr` on a target that is not a function or
/// an ADT. `what` names the target in rustc's words ("structs",
/// "constants"); `is_fn` and `is_adt` say which attributes it takes.
pub(super) fn check_target(attrs: &[Attr], what: &str, is_fn: bool, is_adt: bool, interner: &Interner) -> PResult<()> {
    for a in attrs {
        if a.path.len() != 1 {
            continue;
        }
        let name = interner.get(a.path[0].name);
        let bad = (name == "inline" && !is_fn) || (name == "repr" && !is_adt);
        if bad {
            return Err(Diag::new(
                C_ATTR_USE,
                a.span,
                format!("the `{name}` attribute cannot be used on {what}"),
                format!("Remove the `#[{name}]` attribute."),
            ));
        }
    }
    Ok(())
}

/// The malformed-input error for attribute `name`.
fn malformed(name: &str, attr: &Attr) -> Diag {
    Diag::new(C_ATTR_USE, attr.span, format!("malformed `{name}` attribute input"), "Write the attribute in one of the forms Rust documents for it.")
}

/// True for an `= "text"` input (a plain or raw string literal).
fn eq_str(input: &AttrInput) -> bool {
    matches!(input, AttrInput::List(Delim::Bracket, t)
        if matches!(t.as_slice(), [TokenTree::Token(e), TokenTree::Token(s)] if e.tok == Tok::Eq && matches!(s.tok, Tok::Str(..))))
}

/// Splits trees at top-level commas; a trailing comma adds no piece.
fn comma_pieces(trees: &[TokenTree]) -> Vec<&[TokenTree]> {
    let mut out: Vec<&[TokenTree]> =
        trees.split(|t| matches!(t, TokenTree::Token(x) if x.tok == Tok::Comma)).collect();
    if out.last().is_some_and(|p| p.is_empty()) {
        out.pop();
    }
    out
}

/// The name of a `key = "text"` piece, or None for any other shape.
fn key_str(piece: &[TokenTree], interner: &Interner) -> Option<String> {
    match piece {
        [TokenTree::Token(k), TokenTree::Token(e), TokenTree::Token(v)] if e.tok == Tok::Eq && matches!(v.tok, Tok::Str(..)) => match k.tok {
            Tok::Ident(s) => Some(interner.get(s).to_string()),
            _ => None,
        },
        _ => None,
    }
}

/// `deprecated(since = "..", note = "..")`: each key once, nothing else.
fn deprecated_list(trees: &[TokenTree], interner: &Interner) -> bool {
    let mut seen: Vec<String> = Vec::new();
    for piece in comma_pieces(trees) {
        match key_str(piece, interner) {
            Some(k) if (k == "since" || k == "note") && !seen.contains(&k) => seen.push(k),
            _ => return false,
        }
    }
    true
}

/// A lint level list: lint paths (`name` or `tool::name`), then an
/// optional final `reason = "text"`. A lint lust does not check at
/// deny or forbid is L0531.
fn lint_list(level: &str, attr: &Attr, interner: &Interner) -> PResult<()> {
    let AttrInput::List(Delim::Paren, trees) = &attr.input else {
        return Err(malformed(level, attr));
    };
    let pieces = comma_pieces(trees);
    for (i, piece) in pieces.iter().enumerate() {
        if key_str(piece, interner).as_deref() == Some("reason") && i + 1 == pieces.len() {
            continue;
        }
        let Some(path) = lint_path(piece, interner) else {
            return Err(Diag::new(C_ATTR_USE, attr.span, "malformed lint attribute input", "Name each lint as `name` or `tool::name`."));
        };
        let tool = path.split_once("::").map(|(t, _)| t);
        if let Some(t) = tool
            && !LINT_TOOLS.contains(&t)
        {
            return Err(Diag::new(
                C_ATTR_USE,
                attr.span,
                format!("unknown lint tool `{t}` in `{path}`"),
                "Lust knows the `clippy` and `rustdoc` lint tools.",
            ));
        }
        // `unsafe_code` needs no lint pass: lust rejects `unsafe`
        // itself, so denying it can never hide a rustc reject.
        if matches!(level, "deny" | "forbid") && tool.is_none() && path != "unsafe_code" {
            return Err(Diag::new(
                "L0531",
                attr.span,
                format!("lint `{path}` is set to {level}, but lust does not check it"),
                format!("Remove the `#[{level}]` or lower it to warn, or build this crate with Cargo."),
            ));
        }
    }
    Ok(())
}

/// The text of a lint path piece (`a` or `a::b::c`), or None.
fn lint_path(piece: &[TokenTree], interner: &Interner) -> Option<String> {
    let mut out = String::new();
    for (i, t) in piece.iter().enumerate() {
        let TokenTree::Token(t) = t else { return None };
        match (i % 2, t.tok) {
            (0, Tok::Ident(s)) => out.push_str(interner.get(s)),
            (1, Tok::PathSep) => out.push_str("::"),
            _ => return None,
        }
    }
    (!out.is_empty() && !out.ends_with("::")).then_some(out)
}

