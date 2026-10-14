// Static init closures (W-STD-C): `static NAME: TY = PATH(|| BODY);`.
//
// A `static LazyLock` (or any static whose initializer is one call with a
// zero-parameter closure as its only argument) needs a fn pointer in static
// data: the closure coerces to `F = fn() -> T`. The const evaluator has fn
// item values (`ConstValue::FnPtr`), not closures, so this pass moves the
// closure body into a hidden fn right after the static, at the token level:
//
//     static NAME: TY = PATH(__lust_lazy$NAME);
//     fn __lust_lazy$NAME() -> T { BODY }
//
// `T` is the closure's written return type, else the first type argument
// of the last `LazyLock<..>` / `LazyCell<..>` in `TY`; other statics are
// left alone (and reject in the const evaluator as before). It runs after
// macro expansion and before the item scanner and the parser, so the
// daemon's token scan and the Ast see the same fns in the same order.
//
// Rule zero: a closure there can capture nothing (a static initializer
// has no locals at that position), so the fn has the closure's meaning.
// The name holds a `$`, which no source identifier can, so user code
// cannot name the fn. Elided references in `T` get `'static`, the
// lifetime a static's type elides to.
use crate::diag::Span;
use crate::intern::Interner;
use crate::lexer::{Lexed, Tok, Token};

/// Rewrites every hoistable static init closure in `lexed`. A file with
/// no `static` followed by `||` comes back unchanged.
pub fn hoist_static_closures(lexed: Lexed, interner: &Interner) -> Lexed {
    let toks = &lexed.tokens;
    if !toks.iter().any(|t| t.tok == Tok::Static) || !toks.iter().any(|t| t.tok == Tok::OrOr) {
        return lexed;
    }
    let mut out: Vec<Token> = Vec::with_capacity(toks.len() + 16);
    let mut i = 0;
    while i < toks.len() {
        if toks[i].tok == Tok::Static
            && let Some(h) = hoistable(toks, i, interner)
        {
            out.extend_from_slice(&toks[i..h.open + 1]);
            out.push(Token { tok: Tok::Ident(h.name), span: h.span });
            out.extend_from_slice(&toks[h.close..h.semi + 1]);
            out.extend(cfg_attrs(toks, i, interner));
            let sp = h.span;
            out.push(Token { tok: Tok::Fn, span: sp });
            out.push(Token { tok: Tok::Ident(h.name), span: sp });
            out.push(Token { tok: Tok::LParen, span: sp });
            out.push(Token { tok: Tok::RParen, span: sp });
            out.push(Token { tok: Tok::Arrow, span: sp });
            out.extend(h.ret);
            out.push(Token { tok: Tok::LBrace, span: sp });
            out.extend_from_slice(&toks[h.body.clone()]);
            out.push(Token { tok: Tok::RBrace, span: sp });
            i = h.semi + 1;
            continue;
        }
        out.push(toks[i].clone());
        i += 1;
    }
    Lexed { tokens: out, strings: lexed.strings }
}

/// One static whose initializer closure moves into a hidden fn.
struct Hoist {
    /// The hidden fn's name.
    name: crate::intern::Sym,
    /// Span for the synthetic tokens: the closure's `||`.
    span: Span,
    /// Token index of the call's `(` and `)`, and of the static's `;`.
    open: usize,
    close: usize,
    semi: usize,
    /// The closure body tokens.
    body: std::ops::Range<usize>,
    /// The hidden fn's return type tokens.
    ret: Vec<Token>,
}

/// The hoist for the `static` keyword at `at`, when the item has the
/// shape `static NAME: TY = PATH(<move> || BODY);`.
fn hoistable(toks: &[Token], at: usize, interner: &Interner) -> Option<Hoist> {
    let Tok::Ident(name) = toks.get(at + 1)?.tok else { return None }; // `static mut` stays
    if toks.get(at + 2)?.tok != Tok::Colon {
        return None;
    }
    let ty_start = at + 3;
    let eq = scan_to(toks, ty_start, |t| t == Tok::Eq)?;
    let semi = scan_to(toks, eq + 1, |t| t == Tok::Semi)?;
    // PATH: identifiers and `::` (a turbofish is not supported here).
    let mut open = eq + 1;
    while matches!(toks.get(open)?.tok, Tok::Ident(_) | Tok::PathSep) {
        open += 1;
    }
    if open == eq + 1 || toks[open].tok != Tok::LParen {
        return None;
    }
    let close = semi - 1;
    if toks[close].tok != Tok::RParen || matching_close(toks, open)? != close {
        return None;
    }
    let mut k = open + 1;
    if toks[k].tok == Tok::Move {
        k += 1;
    }
    if toks.get(k)?.tok != Tok::OrOr {
        return None;
    }
    let span = toks[k].span;
    k += 1;
    let (ret, body) = if toks.get(k)?.tok == Tok::Arrow {
        // `|| -> R { .. }`: the body is the block after the written type.
        let lb = scan_to(toks, k + 1, |t| t == Tok::LBrace)?;
        if lb >= close || matching_close(toks, lb)? != close - 1 {
            return None;
        }
        (toks[k + 1..lb].to_vec(), lb..close)
    } else {
        // One argument only: no `,` at depth 0 inside the call.
        if scan_to(toks, k, |t| t == Tok::Comma).is_some_and(|c| c < close) {
            return None;
        }
        (lazy_value_ty(&toks[ty_start..eq], interner)?, k..close)
    };
    if body.is_empty() {
        return None;
    }
    let hidden = interner.intern(&format!("__lust_lazy${}", interner.get(name)));
    Some(Hoist { name: hidden, span, open, close, semi, body, ret: static_lifetimes(ret, span, interner) })
}

/// The first index at or after `from` whose token satisfies `want`, at
/// bracket depth 0 (parens, brackets, braces, and angle brackets), or
/// None when the enclosing group closes first.
fn scan_to(toks: &[Token], from: usize, want: impl Fn(Tok) -> bool) -> Option<usize> {
    let mut depth = 0i32;
    for (i, t) in toks.iter().enumerate().skip(from) {
        if depth == 0 && want(t.tok) {
            return Some(i);
        }
        match t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace | Tok::Lt => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace | Tok::Gt => {
                depth -= 1;
                if depth < 0 {
                    return None;
                }
            }
            Tok::Eof => return None,
            _ => {}
        }
    }
    None
}

/// The index of the token closing the group opened at `open`.
fn matching_close(toks: &[Token], open: usize) -> Option<usize> {
    let mut depth = 0i32;
    for (i, t) in toks.iter().enumerate().skip(open) {
        match t.tok {
            Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
            Tok::RParen | Tok::RBracket | Tok::RBrace => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            Tok::Eof => return None,
            _ => {}
        }
    }
    None
}

/// `T` of the last `LazyLock<T, ..>` or `LazyCell<T, ..>` in a static's
/// type tokens.
fn lazy_value_ty(ty: &[Token], interner: &Interner) -> Option<Vec<Token>> {
    let at = ty.iter().rposition(|t| matches!(t.tok, Tok::Ident(s) if matches!(interner.get(s), "LazyLock" | "LazyCell")))?;
    if ty.get(at + 1)?.tok != Tok::Lt {
        return None;
    }
    let mut depth = 0i32;
    for (i, t) in ty.iter().enumerate().skip(at + 2) {
        match t.tok {
            Tok::Lt | Tok::LParen | Tok::LBracket => depth += 1,
            Tok::Gt | Tok::RParen | Tok::RBracket if depth > 0 => depth -= 1,
            Tok::Gt | Tok::Comma if depth == 0 => return if i > at + 2 { Some(ty[at + 2..i].to_vec()) } else { None },
            _ => {}
        }
    }
    None
}

/// Gives every elided reference in a return type the `'static` lifetime
/// (`&str` to `&'static str`, `'_` to `'static`), as the static's type
/// means them.
fn static_lifetimes(ty: Vec<Token>, span: Span, interner: &Interner) -> Vec<Token> {
    let st = Tok::Lifetime(interner.intern("static"));
    let mut out = Vec::with_capacity(ty.len() + 2);
    for (i, t) in ty.iter().enumerate() {
        let next_is_lifetime = matches!(ty.get(i + 1).map(|x| x.tok), Some(Tok::Lifetime(_)));
        match t.tok {
            Tok::Amp => {
                out.push(t.clone());
                if !next_is_lifetime {
                    out.push(Token { tok: st, span });
                }
            }
            // `&&T`: the outer `&` is always elided here.
            Tok::AndAnd => {
                out.push(Token { tok: Tok::Amp, span: t.span });
                out.push(Token { tok: st, span });
                out.push(Token { tok: Tok::Amp, span: t.span });
                if !next_is_lifetime {
                    out.push(Token { tok: st, span });
                }
            }
            Tok::Lifetime(s) if interner.get(s) == "_" => out.push(Token { tok: st, span: t.span }),
            _ => out.push(t.clone()),
        }
    }
    out
}

/// The `#[cfg(..)]` attributes in front of the `static` at `at` (after
/// any visibility), so the hidden fn exists exactly when the static does.
fn cfg_attrs(toks: &[Token], at: usize, interner: &Interner) -> Vec<Token> {
    // Step back over `pub`, `pub(crate)`, `pub(in path)`.
    let mut s = at;
    if s > 0 && toks[s - 1].tok == Tok::RParen {
        let mut j = s - 1;
        let mut depth = 0;
        loop {
            match toks[j].tok {
                Tok::RParen => depth += 1,
                Tok::LParen => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            if j == 0 {
                return Vec::new();
            }
            j -= 1;
        }
        if j > 0 && toks[j - 1].tok == Tok::Pub {
            s = j - 1;
        }
    } else if s > 0 && toks[s - 1].tok == Tok::Pub {
        s -= 1;
    }
    // Then over `#[..]` groups, keeping the `cfg` ones in order.
    let mut groups: Vec<std::ops::Range<usize>> = Vec::new();
    while s >= 3 && toks[s - 1].tok == Tok::RBracket {
        let mut j = s - 1;
        let mut depth = 0;
        loop {
            match toks[j].tok {
                Tok::RBracket => depth += 1,
                Tok::LBracket => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                _ => {}
            }
            if j == 0 {
                return Vec::new();
            }
            j -= 1;
        }
        if j == 0 || toks[j - 1].tok != Tok::Pound {
            break;
        }
        groups.push(j - 1..s);
        s = j - 1;
    }
    let mut out = Vec::new();
    for g in groups.into_iter().rev() {
        let is_cfg = matches!(toks.get(g.start + 2).map(|t| t.tok), Some(Tok::Ident(n)) if interner.get(n) == "cfg")
            && toks.get(g.start + 3).is_some_and(|t| t.tok == Tok::LParen);
        if is_cfg {
            out.extend_from_slice(&toks[g]);
        }
    }
    out
}
