// Token-level scan for incremental compilation. Finds every function body (top level and in impl
// blocks) without parsing, and hashes:
//   - each body's tokens (what can change without affecting any other function), and
//   - every token outside the bodies (the "environment": types, signatures, item order).
// Hashes ignore positions, so moving code around does not invalidate anything.
use crate::intern::{FxHasher, Sym};
use crate::lexer::{Lexed, Tok};
use std::hash::{Hash, Hasher};

pub struct FnScan {
    pub body_hash: u64,
    /// Byte offset of the `fn` keyword.
    pub fn_offset: u32,
    /// Token range of the body, from `{` to `}` inclusive, within the chunk's tokens.
    pub body: std::ops::Range<usize>,
}

/// One top-level item, without function bodies.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ItemScan {
    pub hash: u64,
    /// The name, for a top-level `fn` item (whose hash is then its signature).
    pub fn_name: Option<Sym>,
}

pub struct ChunkScan {
    pub fns: Vec<FnScan>,
    /// Top-level items in order. Chunks always start at an item, so the concatenated list is
    /// the same however the file was split.
    pub items: Vec<ItemScan>,
    /// Identifiers used in each function body (parallel to `fns`), to find the bodies that
    /// mention a function whose signature changed.
    pub body_idents: Vec<Vec<Sym>>,
}

/// Combines item hashes in order into the environment hash.
pub fn env_hash<'a>(items: impl Iterator<Item = &'a ItemScan>) -> u64 {
    let mut h = FxHasher::default();
    for i in items {
        i.hash.hash(&mut h);
    }
    h.finish()
}

fn hash_tok(h: &mut FxHasher, t: &Tok, strings: &[String]) {
    std::mem::discriminant(t).hash(h);
    match t {
        Tok::Ident(s) | Tok::Reserved(s) => s.hash(h),
        Tok::Int(v, suf) => {
            v.hash(h);
            suf.map(|s| s as u8).hash(h);
        }
        Tok::Str(i) => strings[*i as usize].hash(h),
        Tok::Char(c) => c.hash(h),
        _ => {}
    }
}

/// Scans one lexed chunk. Chunks start at top-level items, so brace depth starts at 0.
pub fn scan(lexed: &Lexed) -> ChunkScan {
    let toks = &lexed.tokens;
    let mut env = FxHasher::default();
    let mut items = Vec::new();
    let mut fns = Vec::new();
    let mut body_idents = Vec::new();
    let mut depth = 0usize;
    let mut impl_pending = false;
    let mut in_impl = false;
    let mut i = 0;
    while i < toks.len() {
        let t = &toks[i].tok;
        let fn_here = *t == Tok::Fn && (depth == 0 || (depth == 1 && in_impl));
        if fn_here {
            // The body is the first `{` at this depth after the signature.
            let mut j = i;
            while j < toks.len() && toks[j].tok != Tok::LBrace && toks[j].tok != Tok::Eof {
                hash_tok(&mut env, &toks[j].tok, &lexed.strings);
                j += 1;
            }
            if j >= toks.len() || toks[j].tok != Tok::LBrace {
                break;
            }
            let mut k = j;
            let mut d = 0usize;
            let mut body = FxHasher::default();
            let mut idents = Vec::new();
            while k < toks.len() {
                match toks[k].tok {
                    Tok::LBrace => d += 1,
                    Tok::RBrace => d -= 1,
                    Tok::Ident(s) => idents.push(s),
                    Tok::Eof => break,
                    _ => {}
                }
                hash_tok(&mut body, &toks[k].tok, &lexed.strings);
                if d == 0 {
                    break;
                }
                k += 1;
            }
            fns.push(FnScan { body_hash: body.finish(), fn_offset: toks[i].span.start, body: j..k + 1 });
            idents.sort_unstable();
            idents.dedup();
            body_idents.push(idents);
            if depth == 0 {
                let fn_name = match toks.get(i + 1).map(|t| t.tok) {
                    Some(Tok::Ident(s)) => Some(s),
                    _ => None,
                };
                items.push(ItemScan { hash: std::mem::take(&mut env).finish(), fn_name });
            }
            i = k + 1;
            continue;
        }
        if *t == Tok::Eof {
            break;
        }
        hash_tok(&mut env, t, &lexed.strings);
        match t {
            Tok::Impl if depth == 0 => impl_pending = true,
            Tok::LBrace => {
                if depth == 0 && impl_pending {
                    in_impl = true;
                    impl_pending = false;
                }
                depth += 1;
            }
            Tok::RBrace => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    in_impl = false;
                    items.push(ItemScan { hash: std::mem::take(&mut env).finish(), fn_name: None });
                }
            }
            Tok::Semi if depth == 0 => items.push(ItemScan { hash: std::mem::take(&mut env).finish(), fn_name: None }),
            _ => {}
        }
        i += 1;
    }
    // A chunk ends at an item boundary, so leftover tokens are only possible on a syntax error.
    if env.finish() != FxHasher::default().finish() {
        items.push(ItemScan { hash: env.finish(), fn_name: None });
    }
    ChunkScan { fns, items, body_idents }
}
