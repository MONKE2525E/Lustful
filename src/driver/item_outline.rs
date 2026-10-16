// The outline of a fn item (sigedit PLAN R1): what name resolution,
// imports, globs, and the module tree read from one fn or method. The
// item patch (patch.rs `find_item_edit`) re-parses an edited fn whole
// only when its old and new outline are the same; a fn's parameter
// types, return type, where clause, bounds, and body are not part of
// it (the item's own path rewrite reads them, with the frozen tables).
//
// The outline is read from tokens, as text: every token from the item's
// start through the fn name (attributes, visibility, qualifiers), but
// not doc comments, then each generic parameter's kind and name. A
// header that holds a macro call or a `$` has no outline (R2).
use crate::lexer::{Tok, Token};

/// One fn's outline, or None when its header holds a `!` or `$`, or
/// its tokens do not start like a fn item. `toks` are the item's tokens
/// (attributes first, through the body), `text` the file text their
/// spans index. The header ends at the body's `{` (depth 0).
pub(crate) fn fn_outline(toks: &[Token], text: &str) -> Option<Vec<String>> {
    let src = |t: &Token| text.get(t.span.lo as usize..t.span.hi as usize).map(str::to_owned);
    let mut depth = 0usize;
    let mut body = None;
    for (i, t) in toks.iter().enumerate() {
        match t.tok {
            Tok::Bang | Tok::Dollar => return None,
            Tok::LParen | Tok::LBracket => depth += 1,
            Tok::RParen | Tok::RBracket => depth = depth.checked_sub(1)?,
            Tok::LBrace if depth == 0 => {
                body = Some(i);
                break;
            }
            _ => {}
        }
    }
    let head = &toks[..body?];
    let at_fn = head.iter().position(|t| t.tok == Tok::Fn)?;
    let name = head.get(at_fn + 1).filter(|t| matches!(t.tok, Tok::Ident(_)))?;
    let mut out: Vec<String> = head[..at_fn].iter().filter(|t| !matches!(t.tok, Tok::DocStr(_))).map(src).collect::<Option<_>>()?;
    out.push("fn".into());
    out.push(src(name)?);
    // Generic params: `<` right after the name, to its `>` at depth 1.
    if head.get(at_fn + 2).is_some_and(|t| t.tok == Tok::Lt) {
        let mut angle = 0usize;
        let mut start = true;
        for t in &head[at_fn + 2..] {
            match t.tok {
                Tok::Lt => angle += 1,
                Tok::Gt => {
                    angle -= 1;
                    if angle == 0 {
                        break;
                    }
                }
                Tok::Shr => {
                    angle = angle.saturating_sub(2);
                    if angle == 0 {
                        break;
                    }
                }
                Tok::Comma if angle == 1 => start = true,
                _ if angle == 1 && start => {
                    // A parameter's first token: its kind, then its name.
                    start = false;
                    match t.tok {
                        Tok::Lifetime(_) => out.push(format!("'{}", src(t)?)),
                        Tok::Const => out.push("const".into()),
                        _ => out.push(format!("T {}", src(t)?)),
                    }
                }
                _ if angle == 1 && out.last().is_some_and(|l| l == "const") => {
                    // `const N`: the name.
                    out.push(src(t)?);
                }
                _ => {}
            }
        }
    }
    Some(out)
}

/// The tokens of an item's header (through the body's opening brace)
/// hold an `impl` in a parameter type (APIT): it adds generic params
/// the rewrite numbers, so the item patch leaves it to a full resolve.
pub(crate) fn has_apit(toks: &[Token]) -> bool {
    let Some(at_fn) = toks.iter().position(|t| t.tok == Tok::Fn) else { return true };
    let Some(open) = toks[at_fn..].iter().position(|t| t.tok == Tok::LParen) else { return true };
    let mut depth = 0usize;
    for t in &toks[at_fn + open..] {
        match t.tok {
            Tok::LParen => depth += 1,
            Tok::RParen => {
                depth -= 1;
                if depth == 0 {
                    return false;
                }
            }
            Tok::Impl => return true,
            _ => {}
        }
    }
    true
}
