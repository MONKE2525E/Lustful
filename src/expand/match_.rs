// Matcher compilation and token-tree matching (ARCH 6.2): a compiled
// matcher is a tree of token, fragment, group, and repetition nodes.
// Matching is bounded backtracking that records, at every input
// position, which matcher nodes successfully consume input starting
// there; two different consumers at one position where at least one is
// a fragment is the local-ambiguity error, as in rustc.
use super::*;
use crate::parser;

/// A repetition operator: `*`, `+`, or `?`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RepOp {
    Star,
    Plus,
    Question,
}

/// One compiled matcher node. Ids are unique across an arm; the
/// ambiguity check compares them. Some spans ride along for
/// definition-site diagnostics the worklist will read.
#[derive(Debug)]
#[allow(dead_code)]
pub enum MNode {
    Tok(Token, u32),
    Meta { name: Sym, kind: FragKind, id: u32, span: Span },
    Group(Delim, Vec<MNode>, u32),
    Rep { inner: Vec<MNode>, sep: Option<Token>, op: RepOp, id: u32, span: Span, vars: Vec<Sym> },
}

/// Every metavariable name bound in a node subtree, in order.
fn node_vars(nodes: &[MNode], out: &mut Vec<Sym>) {
    for node in nodes {
        match node {
            MNode::Meta { name, .. } => {
                if !out.contains(name) {
                    out.push(*name);
                }
            }
            MNode::Group(_, inner, _) | MNode::Rep { inner, .. } => node_vars(inner, out),
            MNode::Tok(_, _) => {}
        }
    }
}

struct Compile<'a> {
    interner: &'a Interner,
    next_id: u32,
    vars: FxMap<Sym, VarInfo>,
}

impl<'a> Compile<'a> {
    fn id(&mut self) -> u32 {
        self.next_id += 1;
        self.next_id
    }

    /// Compiles one sequence of matcher trees at repetition depth `depth`.
    fn seq(&mut self, trees: &[Tt], depth: u32) -> Result<Vec<MNode>, Diag> {
        let mut out = Vec::new();
        let mut i = 0;
        while i < trees.len() {
            match &trees[i] {
                Tt::Tok(t) if t.tok == Tok::Dollar => {
                    let span = t.span;
                    match trees.get(i + 1) {
                        // A repetition: `$( inner ) sep? op`.
                        Some(Tt::Delim(Delim::Paren, inner, _)) => {
                            let inner = self.seq(inner, depth + 1)?;
                            let (sep, op, used) = rep_tail(trees, i + 2).ok_or_else(|| {
                                err(
                                    C_DEF,
                                    span,
                                    "repetition has no operator",
                                    "Write `$(...)*`, `$(...)+`, or `$(...)?`, with an optional separator token.",
                                )
                            })?;
                            if depth >= 16 {
                                return Err(err(C_DEF, span, "repetitions nested too deep", "Split the macro into smaller macros."));
                            }
                            let id = self.id();
                            let mut vars = Vec::new();
                            node_vars(&inner, &mut vars);
                            out.push(MNode::Rep { inner, sep, op, id, span, vars });
                            i += 2 + used;
                        }
                        // A metavariable: `$name:kind`. `$crate` is
                        // transcription-only and never a matcher variable.
                        Some(Tt::Tok(name_tok)) => {
                            if name_tok.tok == Tok::Crate {
                                return Err(err(
                                    C_DEF,
                                    span,
                                    "`$crate` cannot be used in a matcher",
                                    "`$crate` is only allowed in the expanded side of a rule.",
                                ));
                            }
                            let Some(name) = meta_sym(name_tok.tok, self.interner) else {
                                return Err(err(
                                    C_DEF,
                                    span,
                                    "expected a metavariable name after `$`",
                                    "Write `$name:kind`, for example `$e:expr`.",
                                ));
                            };
                            let colon = tok_at(trees, i + 2);
                            let kind_tok = tok_at(trees, i + 3);
                            if colon.map(|t| t.tok) != Some(Tok::Colon) || kind_tok.is_none() {
                                return Err(err(C_DEF, span, "expected `$name:kind`", "Write `$name:kind`, for example `$e:expr`."));
                            }
                            let kind_name = seg_text(kind_tok.unwrap().tok, self.interner).unwrap_or_default();
                            let kind = FragKind::from_name(&kind_name).ok_or_else(|| {
                                err(
                                    C_DEF,
                                    kind_tok.unwrap().span,
                                    format!("unknown fragment kind `{kind_name}`"),
                                    "Use expr, ident, ty, pat, stmt, block, item, path, meta, vis, literal, lifetime, or tt.",
                                )
                            })?;
                            let name_span = name_tok.span;
                            if self.vars.insert(name, VarInfo { kind, depth }).is_some() {
                                return Err(err(
                                    C_DEF,
                                    name_span,
                                    format!("metavariable `{}` is bound more than once", self.interner.get(name)),
                                    "Rename one of the metavariables.",
                                ));
                            }
                            let id = self.id();
                            out.push(MNode::Meta { name, kind, id, span: name_span });
                            i += 4;
                        }
                        _ => {
                            return Err(err(
                                C_DEF,
                                span,
                                "expected a metavariable or repetition after `$`",
                                "Write `$name:kind` or `$(...)*`.",
                            ));
                        }
                    }
                }
                Tt::Tok(t) => {
                    let id = self.id();
                    out.push(MNode::Tok(*t, id));
                    i += 1;
                }
                Tt::Delim(d, inner, _) => {
                    let inner = self.seq(inner, depth)?;
                    let id = self.id();
                    out.push(MNode::Group(*d, inner, id));
                    i += 1;
                }
                Tt::Frag(_, _, span) => {
                    return Err(err(
                        C_DEF,
                        *span,
                        "a fragment cannot be used in a matcher",
                        "Macro definitions must be written as plain tokens.",
                    ));
                }
            }
        }
        Ok(out)
    }
}

/// Parses what follows a repetition's closing paren at `trees[i..]`:
/// an optional single separator token, then `*`, `+`, or `?`.
/// Returns the separator, the operator, and how many trees were used.
/// Also used by the transcriber, which reads the same repetition shape.
pub fn rep_tail(trees: &[Tt], i: usize) -> Option<(Option<Token>, RepOp, usize)> {
    fn as_op(tok: Tok) -> Option<RepOp> {
        Some(match tok {
            Tok::Star => RepOp::Star,
            Tok::Plus => RepOp::Plus,
            Tok::Question => RepOp::Question,
            _ => return None,
        })
    }
    match tok_at(trees, i) {
        Some(t) if as_op(t.tok).is_some() => Some((None, as_op(t.tok).unwrap(), 1)),
        Some(sep) => {
            // `$` cannot be a separator, and the operator must follow.
            if sep.tok == Tok::Dollar {
                return None;
            }
            let op = as_op(tok_at(trees, i + 1)?.tok)?;
            Some((Some(sep), op, 2))
        }
        None => None,
    }
}

/// What may follow a fragment of `kind` in a matcher (the follow set a
/// definition's edition fixes, ARCH 6.2). `frag` stands for another
/// fragment starting there; only the token check needs `tok`.
fn follow_ok(kind: FragKind, tok: Tok) -> bool {
    use Tok::*;
    match kind {
        FragKind::Expr | FragKind::Stmt => matches!(tok, FatArrow | Comma | Semi),
        FragKind::Ty | FragKind::Path => {
            matches!(tok, FatArrow | Comma | Eq | Pipe | Semi | Colon | Gt | Ge | LBracket | LBrace | As | Where)
        }
        FragKind::Pat | FragKind::PatParam => matches!(tok, FatArrow | Comma | Eq | Pipe | If | In),
        FragKind::Vis => matches!(
            tok,
            Comma | Ident(_) | Pub | Fn | Struct | Enum | Impl | Trait | Type | Const | Static | Mod | Use | Extern | Unsafe | Async
        ),
        _ => true,
    }
}

/// Kinds whose follow set is restricted: another fragment may not start
/// right after them either.
fn restricted(kind: FragKind) -> bool {
    matches!(kind, FragKind::Expr | FragKind::Stmt | FragKind::Ty | FragKind::Path | FragKind::Pat | FragKind::PatParam | FragKind::Vis)
}

/// The token a node starts with when it is a plain token or a group, for
/// follow checks. A group counts as its opening delimiter token.
fn first_tok(node: &MNode) -> Option<Tok> {
    match node {
        MNode::Tok(t, _) => Some(t.tok),
        MNode::Group(d, _, _) => Some(match d {
            Delim::Paren => Tok::LParen,
            Delim::Bracket => Tok::LBracket,
            Delim::Brace => Tok::LBrace,
        }),
        MNode::Rep { inner, .. } => inner.first().and_then(first_tok),
        MNode::Meta { .. } => None,
    }
}

/// True when a node can begin by matching a fragment.
fn starts_with_meta(node: &MNode) -> bool {
    match node {
        MNode::Meta { .. } => true,
        MNode::Rep { inner, op, .. } => {
            *op != RepOp::Question && inner.first().map_or(false, starts_with_meta)
                || *op == RepOp::Question && inner.first().map_or(false, starts_with_meta)
        }
        _ => false,
    }
}

/// Checks one fragment against what follows it: a following node, if any.
/// `after` is None at the end of a sequence.
fn check_one_follow(kind: FragKind, meta_span: Span, after: Option<&MNode>, sep: Option<Token>) -> Result<(), Diag> {
    if let Some(sep) = sep
        && !follow_ok(kind, sep.tok)
    {
        return Err(follow_err(kind, meta_span, sep.tok));
    }
    if let Some(node) = after {
        if let Some(tok) = first_tok(node)
            && !follow_ok(kind, tok)
        {
            return Err(follow_err(kind, meta_span, tok));
        }
        if starts_with_meta(node) && restricted(kind) {
            return Err(err(
                C_DEF,
                meta_span,
                format!("`{}` fragments cannot be followed by another fragment", kind.name()),
                "Put a token both sides can agree on between the fragments, such as `,` or `;`.",
            ));
        }
    }
    Ok(())
}

fn follow_err(kind: FragKind, span: Span, tok: Tok) -> Diag {
    let _ = tok;
    err(
        C_DEF,
        span,
        format!("`{}` fragments cannot be followed by this token", kind.name()),
        "Change the matcher so the fragment is followed by an allowed token (`=>`, `,`, or `;` always work).",
    )
    .with_label(span, format!("the `{}` fragment here", kind.name()))
}

/// The metavariables that can end a sequence: a trailing fragment, or
/// the trailing fragments of a trailing repetition.
fn end_metas(nodes: &[MNode]) -> Vec<(FragKind, Span)> {
    match nodes.last() {
        Some(MNode::Meta { kind, span, .. }) => vec![(*kind, *span)],
        Some(MNode::Rep { inner, .. }) => end_metas(inner),
        Some(MNode::Group(_, _, _)) | Some(MNode::Tok(_, _)) | None => Vec::new(),
    }
}

/// Follow-set check over one compiled arm, recursively.
fn check_follow(nodes: &[MNode], _arm_span: Span) -> Result<(), Diag> {
    for (j, node) in nodes.iter().enumerate() {
        let after = nodes.get(j + 1);
        match node {
            MNode::Meta { kind, span, .. } => check_one_follow(*kind, *span, after, None)?,
            MNode::Group(_, inner, _) => check_follow(inner, _arm_span)?,
            MNode::Rep { inner, sep, .. } => {
                check_follow(inner, _arm_span)?;
                // A fragment at the end of a repetition is also followed
                // by the separator, and by whatever follows the repetition.
                for (kind, span) in end_metas(inner) {
                    check_one_follow(kind, span, after, *sep)?;
                }
            }
            MNode::Tok(_, _) => {}
        }
    }
    Ok(())
}

/// Compiles one macro arm: matcher trees to matcher nodes plus the
/// metavariable table. Runs the follow-set check (ARCH 6.2).
pub fn compile_arm(matcher: &[Tt], span: Span, interner: &Interner) -> Result<(Vec<MNode>, FxMap<Sym, VarInfo>), Diag> {
    let mut c = Compile { interner, next_id: 0, vars: FxMap::default() };
    let nodes = c.seq(matcher, 0)?;
    check_follow(&nodes, span)?;
    Ok((nodes, c.vars))
}

/// How many full matches one arm collects before stopping: enough to see
/// that two different bindings match (an ambiguity), never unbounded.
const MAX_MATCHES: usize = 8;
/// Match steps for one call before the cap fires (ARCH 6.1, L0801).
pub const MATCH_BUDGET: u32 = 2_000_000;

/// Per-call matcher state: who to ask for fragment probes, the step
/// budget, probe memoization, and the ambiguity record.
pub struct Matcher<'a> {
    pub interner: &'a Interner,
    pub known: &'a Known,
    pub strings: &'a [String],
    pub budget: u32,
    pub probe_cache: FxMap<(FragKind, u64), bool>,
    /// Keyed by (input list pointer, list length, first span start,
    /// position): the (node id, is-fragment) pairs that consumed input
    /// starting at that position.
    pub consumers: FxMap<(usize, usize, u32, usize), Vec<(u32, bool)>>,
    call_span: Span,
}

impl<'a> Matcher<'a> {
    /// A fresh matcher for one macro call at `call_span`.
    pub fn new(interner: &'a Interner, known: &'a Known, strings: &'a [String], call_span: Span) -> Matcher<'a> {
        Matcher { interner, known, strings, budget: MATCH_BUDGET, probe_cache: FxMap::default(), consumers: FxMap::default(), call_span }
    }

    fn step(&mut self) -> Result<(), Diag> {
        self.budget = self.budget.saturating_sub(1);
        if self.budget == 0 {
            return Err(err(C_CAP, self.call_span, "macro matching exceeded its step limit", "Simplify the macro pattern or the call."));
        }
        Ok(())
    }

    fn record(&mut self, input: &[Tt], pos: usize, id: u32, is_frag: bool) {
        let first = input.first().map_or(0, |t| t.span().lo);
        let key = (input.as_ptr() as usize, input.len(), first, pos);
        self.consumers.entry(key).or_default().push((id, is_frag));
    }

    /// True when any recorded position had two different consumers and at
    /// least one was a fragment: the call is locally ambiguous.
    pub fn ambiguous(&self) -> bool {
        self.consumers.values().any(|list| {
            list.iter().any(|&(_, is_frag)| is_frag) && list.iter().map(|&(id, _)| id).collect::<std::collections::HashSet<_>>().len() > 1
        })
    }
}

/// Expands transparent fragments in an input list into their trees, so a
/// forwarded ident, lifetime, or tt can be matched token by token.
/// Opaque fragments stay single units.
pub fn splice_transparent(input: &[Tt]) -> Vec<Tt> {
    let mut out = Vec::with_capacity(input.len());
    for tree in input {
        match tree {
            Tt::Frag(kind, inner, _) if kind.transparent() => out.extend(splice_transparent(inner)),
            _ => out.push(tree.clone()),
        }
    }
    out
}

/// Matches one arm against input trees. Returns every full match's
/// bindings found (at most `MAX_MATCHES`, longest repetitions first).
pub fn match_arm(m: &mut Matcher, nodes: &[MNode], input: &[Tt]) -> Result<Vec<BindMap>, Diag> {
    m.consumers.clear();
    let input = splice_transparent(input);
    let mut results = Vec::new();
    let mut partial = Vec::new();
    match_seq(m, nodes, &input, 0, BindMap::default(), &mut partial)?;
    for (end, binds) in partial {
        if end == input.len() {
            results.push(binds);
            if results.len() >= MAX_MATCHES {
                break;
            }
        }
    }
    Ok(results)
}

/// Appends every (end position, bindings) that matches `nodes` against
/// `input` starting at `pos`.
fn match_seq(
    m: &mut Matcher,
    nodes: &[MNode],
    input: &[Tt],
    pos: usize,
    binds: BindMap,
    out: &mut Vec<(usize, BindMap)>,
) -> Result<(), Diag> {
    m.step()?;
    if out.len() > 4096 {
        return Ok(());
    }
    let Some((node, rest)) = nodes.split_first() else {
        out.push((pos, binds));
        return Ok(());
    };
    match node {
        MNode::Tok(pattern, id) => {
            if let Some(Tt::Tok(actual)) = input.get(pos)
                && tok_matches(&pattern.tok, &actual.tok, m.strings)
            {
                m.record(input, pos, *id, false);
                match_seq(m, rest, input, pos + 1, binds, out)?;
            }
            Ok(())
        }
        MNode::Meta { name, kind, id, span } => match_meta(m, *name, *kind, *id, *span, rest, input, pos, binds, out),
        MNode::Group(delim, inner, id) => {
            if let Some(Tt::Delim(d, inner_input, _)) = input.get(pos)
                && d == delim
            {
                let inner_input = splice_transparent(inner_input);
                let mut inner_results = Vec::new();
                match_seq(m, inner, &inner_input, 0, BindMap::default(), &mut inner_results)?;
                let mut any = false;
                for (end, inner_binds) in inner_results {
                    if end != inner_input.len() {
                        continue;
                    }
                    any = true;
                    let mut merged = binds.clone();
                    merged.extend(inner_binds);
                    match_seq(m, rest, input, pos + 1, merged, out)?;
                }
                if any {
                    m.record(input, pos, *id, false);
                }
            }
            Ok(())
        }
        MNode::Rep { inner, sep, op, id, vars, .. } => {
            let mut rep_results = Vec::new();
            match_rep(m, inner, *sep, *op, *id, vars, input, pos, &[], &mut rep_results)?;
            for (end, rep_binds) in rep_results {
                let mut merged = binds.clone();
                merged.extend(rep_binds);
                match_seq(m, rest, input, end, merged, out)?;
            }
            Ok(())
        }
    }
}

/// Matches one repetition node, longest runs first. Appends
/// (end, seq-merged bindings) for every valid iteration count.
fn match_rep(
    m: &mut Matcher,
    inner: &[MNode],
    sep: Option<Token>,
    op: RepOp,
    rep_id: u32,
    vars: &[Sym],
    input: &[Tt],
    pos: usize,
    iters: &[BindMap],
    out: &mut Vec<(usize, BindMap)>,
) -> Result<(), Diag> {
    m.step()?;
    if out.len() > 4096 {
        return Ok(());
    }
    let can_extend = op != RepOp::Question || iters.is_empty();
    if can_extend {
        let mut start = pos;
        let mut sep_ok = true;
        if !iters.is_empty()
            && let Some(sep_tok) = sep
        {
            match input.get(start) {
                Some(Tt::Tok(actual)) if tok_matches(&sep_tok.tok, &actual.tok, m.strings) => start += 1,
                _ => sep_ok = false,
            }
        }
        if sep_ok {
            let mut inner_results = Vec::new();
            match_seq(m, inner, input, start, BindMap::default(), &mut inner_results)?;
            for (end, iter_binds) in inner_results {
                // An iteration must consume input: a repetition that can
                // match empty never advances and rustc rejects the shape.
                if end == start {
                    continue;
                }
                if sep.is_some() && !iters.is_empty() {
                    m.record(input, pos, rep_id, false);
                }
                let mut next_iters: Vec<BindMap> = iters.to_vec();
                next_iters.push(iter_binds);
                match_rep(m, inner, sep, op, rep_id, vars, input, end, &next_iters, out)?;
            }
        }
    }
    let min_ok = op != RepOp::Plus || !iters.is_empty();
    if min_ok {
        // Merge per-iteration bindings: each variable the repetition
        // binds becomes one `Seq` deeper, with `Empty` where an
        // iteration did not bind it. Zero iterations still bind every
        // variable, to an empty `Seq`.
        let mut merged = BindMap::default();
        for &name in vars {
            let seq: Vec<Bind> = iters.iter().map(|it| it.get(&name).cloned().unwrap_or(Bind::Empty)).collect();
            merged.insert(name, Bind::Seq(seq));
        }
        out.push((pos, merged));
    }
    Ok(())
}

/// The span a fragment covers: first to last tree span in its slice.
fn frag_span(slice: &[Tt], at: Span) -> Span {
    match (slice.first(), slice.last()) {
        (Some(first), Some(last)) if first.span().file == last.span().file => first.span().to(last.span()),
        _ => at,
    }
}

/// Matches one metavariable node, then the rest of the sequence.
fn match_meta(
    m: &mut Matcher,
    name: Sym,
    kind: FragKind,
    id: u32,
    meta_span: Span,
    rest: &[MNode],
    input: &[Tt],
    pos: usize,
    binds: BindMap,
    out: &mut Vec<(usize, BindMap)>,
) -> Result<(), Diag> {
    let _ = meta_span;
    // A forwarded opaque fragment is one unit: it can only rebind to the
    // same kind, or be taken whole as one token tree (ARCH 6.2).
    if let Some(Tt::Frag(fk, _, _)) = input.get(pos)
        && !fk.transparent()
    {
        if *fk == kind || kind == FragKind::Tt {
            m.record(input, pos, id, true);
            let mut next = binds;
            next.insert(name, Bind::Leaf(vec![input[pos].clone()]));
            return match_seq(m, rest, input, pos + 1, next, out);
        }
        return Ok(());
    }
    let at = input.get(pos).map_or(m.call_span, |t| t.span());
    for end in fragment_ends(m, kind, input, pos)? {
        if end > pos {
            m.record(input, pos, id, true);
        }
        let slice: Vec<Tt> = input[pos..end].to_vec();
        let value = if kind.transparent() {
            // Transparent kinds keep their trees, so an inner matcher can
            // still see them token by token.
            Bind::Leaf(slice)
        } else {
            let slice = if kind == FragKind::Stmt { stmt_with_semi(slice) } else { slice };
            Bind::Leaf(vec![Tt::Frag(kind, slice.clone(), frag_span(&slice, at))])
        };
        let mut next = binds.clone();
        next.insert(name, value);
        match_seq(m, rest, input, end, next, out)?;
    }
    Ok(())
}

/// Gives a matched statement fragment the `;` form it transcribes with:
/// a statement whose last tree is not `;` and not a brace group carries
/// an explicit semicolon, matching rustc's statement output.
fn stmt_with_semi(mut slice: Vec<Tt>) -> Vec<Tt> {
    match slice.last() {
        Some(Tt::Tok(t)) if t.tok == Tok::Semi => return slice,
        Some(Tt::Delim(Delim::Brace, _, _)) => return slice,
        Some(Tt::Frag(FragKind::Block, _, _)) => return slice,
        _ => {}
    }
    // Items end where their own token shape ends (a trailing brace group
    // was handled above; a `;`-ended item already has its token).
    if let Some(Tt::Tok(t)) = slice.first()
        && matches!(t.tok, Tok::Fn | Tok::Struct | Tok::Enum | Tok::Impl | Tok::Mod | Tok::Trait)
    {
        return slice;
    }
    let span = slice.last().map_or(Span::default(), |t| t.span());
    slice.push(Tt::Tok(Token { tok: Tok::Semi, span }));
    slice
}

/// Every end position where a fragment of `kind` starting at `pos` can
/// stop. Scanner kinds are exact; parsed kinds try each end and keep the
/// ones the real parser accepts as exactly that fragment (ARCH 6.2:
/// fragment parsing reuses the real parser).
fn fragment_ends(m: &mut Matcher, kind: FragKind, input: &[Tt], pos: usize) -> Result<Vec<usize>, Diag> {
    let first = tok_at(input, pos).map(|t| t.tok);
    Ok(match kind {
        FragKind::Ident => match first {
            // An ident fragment matches an identifier or a keyword
            // (rustc accepts `self`, `fn`, `true`, `Self` here).
            Some(
                Tok::Ident(_)
                | Tok::Reserved(_)
                | Tok::As
                | Tok::Break
                | Tok::Const
                | Tok::Continue
                | Tok::Else
                | Tok::Enum
                | Tok::False
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
                | Tok::True
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
                | Tok::Await,
            ) => vec![pos + 1],
            _ => vec![],
        },
        FragKind::Lifetime => match first {
            Some(Tok::Lifetime(_)) => vec![pos + 1],
            _ => vec![],
        },
        FragKind::Literal => match first {
            Some(Tok::Int(..) | Tok::Float(_) | Tok::Str(_) | Tok::ByteStr | Tok::ByteChar | Tok::Char(_) | Tok::True | Tok::False) => {
                vec![pos + 1]
            }
            // A negative numeric literal is one literal fragment.
            Some(Tok::Minus) if matches!(tok_at(input, pos + 1).map(|t| t.tok), Some(Tok::Int(..) | Tok::Float(_))) => {
                vec![pos + 2]
            }
            _ => vec![],
        },
        FragKind::Tt => {
            if pos < input.len() {
                vec![pos + 1]
            } else {
                vec![]
            }
        }
        FragKind::Block => match input.get(pos) {
            Some(tree @ Tt::Delim(Delim::Brace, _, _)) if probe(m, kind, std::slice::from_ref(tree)) => vec![pos + 1],
            _ => vec![],
        },
        FragKind::Vis => {
            let mut ends = Vec::new();
            if first == Some(Tok::Pub) {
                if matches!(input.get(pos + 1), Some(Tt::Delim(Delim::Paren, _, _))) {
                    ends.push(pos + 2);
                }
                ends.push(pos + 1);
            }
            ends.push(pos);
            ends
        }
        FragKind::Meta => meta_end(input, pos).into_iter().collect(),
        FragKind::Path => path_ends(input, pos),
        // An item ends at its item boundary (or after a macro call
        // item's group and `;`): token trees make the boundary without
        // parsing, so item kinds the parser does not build yet can
        // still match and round-trip through transcription.
        FragKind::Item => {
            let mut ends = Vec::new();
            if let Some(end) = super::item_end(input, pos, m.interner) {
                ends.push(end);
            }
            if let Some(end) = macro_call_shape(input, pos) {
                ends.push(end);
                if input.get(end).is_some_and(|t| t.is_tok(Tok::Semi)) {
                    ends.push(end + 1);
                }
            }
            if ends.is_empty() {
                for end in pos + 1..=input.len() {
                    m.step()?;
                    if probe(m, kind, &input[pos..end]) {
                        ends.push(end);
                    }
                }
            }
            ends
        }
        FragKind::Expr | FragKind::Ty | FragKind::Pat | FragKind::PatParam | FragKind::Stmt => {
            let mut ends = Vec::new();
            for end in pos + 1..=input.len() {
                m.step()?;
                let slice = &input[pos..end];
                // A statement fragment never owns the `;` after it: a
                // matcher that wants it writes the token itself.
                if kind == FragKind::Stmt && matches!(slice.last(), Some(Tt::Tok(t)) if t.tok == Tok::Semi) {
                    continue;
                }
                if kind == FragKind::PatParam && slice.iter().any(|t| t.is_tok(Tok::Pipe)) {
                    continue;
                }
                if probe(m, kind, slice) {
                    ends.push(end);
                }
            }
            ends
        }
    })
}

/// The end of one `meta` fragment at `pos`: a path, then an optional
/// `= literal` or one delimited group.
fn meta_end(input: &[Tt], pos: usize) -> Option<usize> {
    let mut i = pos;
    // A path segment token: an identifier-like token (attribute names are
    // idents or keywords such as `derive`, `cfg`, `doc`).
    fn is_name(input: &[Tt], i: usize) -> bool {
        matches!(
            tok_at(input, i).map(|t| t.tok),
            Some(Tok::Ident(_) | Tok::Reserved(_) | Tok::SelfUpper | Tok::SelfLower | Tok::Crate | Tok::Super)
        )
    }
    if !is_name(input, i) {
        return None;
    }
    i += 1;
    while tok_at(input, i).map(|t| t.tok) == Some(Tok::PathSep) && is_name(input, i + 1) {
        i += 2;
    }
    match input.get(i) {
        Some(Tt::Tok(t)) if t.tok == Tok::Eq => {
            let lit = tok_at(input, i + 1).map(|t| t.tok);
            match lit {
                Some(Tok::Str(_) | Tok::Int(..) | Tok::Float(_) | Tok::Char(_) | Tok::True | Tok::False | Tok::ByteStr) => Some(i + 2),
                _ => None,
            }
        }
        Some(Tt::Delim(_, _, _)) => Some(i + 1),
        _ => Some(i),
    }
}

/// Candidate ends for a path fragment: segments with optional generic
/// arguments, longest first.
fn path_ends(input: &[Tt], pos: usize) -> Vec<usize> {
    fn angle_end(input: &[Tt], mut i: usize) -> Option<usize> {
        // `i` is at the opening `<`.
        let mut depth = 0i64;
        while i < input.len() {
            match tok_at(input, i).map(|t| t.tok) {
                Some(Tok::Lt) => depth += 1,
                Some(Tok::Shl) => depth += 2,
                Some(Tok::Gt) => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(i + 1);
                    }
                }
                Some(_) => {}
                None => return None,
            }
            i += 1;
        }
        None
    }
    let mut ends = Vec::new();
    let mut i = pos;
    if tok_at(input, i).map(|t| t.tok) == Some(Tok::PathSep) {
        i += 1;
    }
    loop {
        if !matches!(tok_at(input, i).map(|t| t.tok), Some(t) if is_seg_tok(t)) {
            break;
        }
        i += 1;
        // Generic arguments: `::<..>` (turbofish) or `<..>`.
        if tok_at(input, i).map(|t| t.tok) == Some(Tok::PathSep) && tok_at(input, i + 1).map(|t| t.tok) == Some(Tok::Lt) {
            match angle_end(input, i + 1) {
                Some(end) => i = end,
                None => break,
            }
        } else if tok_at(input, i).map(|t| t.tok) == Some(Tok::Lt) {
            match angle_end(input, i) {
                Some(end) => i = end,
                None => break,
            }
        }
        ends.push(i);
        if tok_at(input, i).map(|t| t.tok) == Some(Tok::PathSep) && matches!(tok_at(input, i + 1).map(|t| t.tok), Some(t) if is_seg_tok(t))
        {
            i += 1;
        } else {
            break;
        }
    }
    ends.reverse();
    ends
}

/// Flattens a fragment candidate slice for a parser probe. Two things in
/// a slice are not plain syntax yet and become placeholders of the right
/// shape: opaque fragments forwarded from an outer macro, and macro
/// calls, which parse as one node of the position they stand in.
fn probe_flatten(m: &Matcher, kind: FragKind, trees: &[Tt]) -> Vec<Token> {
    fn placeholder(m: &Matcher, kind: FragKind, span: Span, out: &mut Vec<Token>) {
        match kind {
            FragKind::Ty | FragKind::Path => out.push(Token { tok: Tok::Ident(m.interner.intern("u8")), span }),
            FragKind::Item => {
                out.push(Token { tok: Tok::Fn, span });
                out.push(Token { tok: Tok::Ident(m.interner.intern("__lust_probe")), span });
                out.push(Token { tok: Tok::LParen, span });
                out.push(Token { tok: Tok::RParen, span });
                out.push(Token { tok: Tok::LBrace, span });
                out.push(Token { tok: Tok::RBrace, span });
            }
            FragKind::Pat | FragKind::PatParam => out.push(Token { tok: Tok::Underscore, span }),
            FragKind::Block => {
                out.push(Token { tok: Tok::LBrace, span });
                out.push(Token { tok: Tok::RBrace, span });
            }
            FragKind::Vis => {}
            _ => out.push(Token { tok: Tok::Int(0, None), span }),
        }
    }
    fn go(m: &Matcher, kind: FragKind, trees: &[Tt], out: &mut Vec<Token>) {
        let mut i = 0;
        // Whether the tree just emitted at this level ends a value, so a
        // bracket group after it is an index, not an array literal.
        let mut after_value = false;
        while i < trees.len() {
            // A macro call shape: segments, `!`, one group.
            if let Some(end) = macro_call_shape(trees, i) {
                placeholder(m, kind, trees[i].span(), out);
                after_value = true;
                i = end;
                continue;
            }
            // Shapes the current parser rejects although rustc's
            // fragment parser accepts them: labels, array and tuple
            // literals, and lifetimes in types. They become supported
            // placeholders so matching picks rustc's arm; the real parse
            // of the expansion still rejects what lust cannot build.
            match &trees[i] {
                Tt::Tok(t) if matches!(t.tok, Tok::Lifetime(_)) && tok_at(trees, i + 1).map(|x| x.tok) == Some(Tok::Colon) => {
                    // A label definition `'a:` before a block or loop.
                    i += 2;
                    continue;
                }
                Tt::Tok(t) if matches!(t.tok, Tok::Break | Tok::Continue) => {
                    out.push(*t);
                    after_value = false;
                    i += 1;
                    if matches!(tok_at(trees, i).map(|x| x.tok), Some(Tok::Lifetime(_))) {
                        i += 1;
                    }
                    continue;
                }
                Tt::Tok(t) if matches!(t.tok, Tok::Lifetime(_)) && matches!(kind, FragKind::Ty | FragKind::Path) => {
                    // `&'a T` drops the lifetime; `F<'a>` reads it as a
                    // type argument, so the generic list still parses.
                    match out.last().map(|x| x.tok) {
                        Some(Tok::Lt | Tok::Comma) => out.push(Token { tok: Tok::Ident(m.interner.intern("u8")), span: t.span }),
                        _ => {}
                    }
                    after_value = false;
                    i += 1;
                    continue;
                }
                Tt::Delim(Delim::Bracket, inner, span) if kind == FragKind::Expr || kind == FragKind::Stmt => {
                    if after_value {
                        out.push(Token { tok: Tok::LBracket, span: *span });
                        out.push(Token { tok: Tok::Int(0, None), span: *span });
                        out.push(Token { tok: Tok::RBracket, span: *span });
                    } else {
                        // An array literal: one value.
                        out.push(Token { tok: Tok::Int(0, None), span: *span });
                    }
                    let _ = inner;
                    after_value = true;
                    i += 1;
                    continue;
                }
                Tt::Delim(Delim::Paren, inner, span)
                    if !after_value && inner.iter().any(|t| t.is_tok(Tok::Comma)) && kind != FragKind::Item =>
                {
                    // A tuple value or pattern shape reads as one value.
                    out.push(Token { tok: Tok::LParen, span: *span });
                    out.push(Token { tok: Tok::Int(0, None), span: *span });
                    out.push(Token { tok: Tok::RParen, span: *span });
                    after_value = true;
                    i += 1;
                    continue;
                }
                _ => {}
            }
            match &trees[i] {
                Tt::Tok(t) => {
                    after_value = matches!(
                        t.tok,
                        Tok::Ident(_)
                            | Tok::SelfUpper
                            | Tok::SelfLower
                            | Tok::Int(..)
                            | Tok::Str(_)
                            | Tok::Char(_)
                            | Tok::True
                            | Tok::False
                    );
                    out.push(*t);
                }
                Tt::Delim(d, inner, span) => {
                    after_value = true;
                    let (open, close) = match d {
                        Delim::Paren => (Tok::LParen, Tok::RParen),
                        Delim::Bracket => (Tok::LBracket, Tok::RBracket),
                        Delim::Brace => (Tok::LBrace, Tok::RBrace),
                    };
                    out.push(Token { tok: open, span: *span });
                    go(m, kind, inner, out);
                    out.push(Token { tok: close, span: *span });
                }
                Tt::Frag(fk, inner, span) => {
                    if fk.transparent() {
                        go(m, kind, inner, out);
                    } else if *fk == kind {
                        go(m, kind, inner, out);
                    } else {
                        placeholder(m, *fk, *span, out);
                    }
                }
            }
            i += 1;
        }
    }
    let mut out = Vec::new();
    go(m, kind, trees, &mut out);
    out
}

/// If a macro call (path segments, `!`, delimited group) starts at
/// `trees[i]`, returns the index just past its group.
pub fn macro_call_shape(trees: &[Tt], i: usize) -> Option<usize> {
    let mut j = i;
    if tok_at(trees, j).map(|t| t.tok) == Some(Tok::PathSep) {
        j += 1;
    }
    loop {
        if !matches!(tok_at(trees, j).map(|t| t.tok), Some(t) if is_seg_tok(t)) {
            return None;
        }
        j += 1;
        match tok_at(trees, j).map(|t| t.tok) {
            Some(Tok::Bang) => {
                return match trees.get(j + 1) {
                    Some(Tt::Delim(_, _, _)) => Some(j + 2),
                    _ => None,
                };
            }
            Some(Tok::PathSep) => j += 1,
            _ => return None,
        }
    }
}

/// True when `slice` parses as exactly one fragment of `kind` with the
/// real parser. Memoized on the slice's token hash per call.
fn probe(m: &mut Matcher, kind: FragKind, slice: &[Tt]) -> bool {
    let key = (kind, hash_tts(slice, m.strings));
    if let Some(&hit) = m.probe_cache.get(&key) {
        return hit;
    }
    let toks = probe_flatten(m, kind, slice);
    let ok = match kind {
        FragKind::Expr => parser::probe_expr(&toks, m.strings, m.interner, m.known),
        FragKind::Ty => parser::probe_ty(&toks, m.strings, m.interner, m.known),
        FragKind::Pat | FragKind::PatParam => parser::probe_pat(&toks, m.strings, m.interner, m.known),
        FragKind::Block => parser::probe_block(&toks, m.strings, m.interner, m.known),
        FragKind::Stmt => {
            parser::probe_stmt(&toks, m.strings, m.interner, m.known) || {
                // A `let` statement is written without its `;` in a macro
                // call; try again with one, as a block would need it.
                let span = toks.last().map_or(Span::default(), |t| t.span);
                let mut with_semi = toks.clone();
                with_semi.push(Token { tok: Tok::Semi, span });
                parser::probe_stmt(&with_semi, m.strings, m.interner, m.known)
            }
        }
        FragKind::Item => {
            let mut tokens = toks;
            let end = tokens.last().map_or(Span::default(), |t| t.span);
            tokens.push(Token { tok: Tok::Eof, span: end });
            let lexed = Lexed { tokens, strings: m.strings.to_vec() };
            parser::parse(&lexed, m.interner, m.known).map_or(false, |ast| ast.items.len() == 1)
        }
        _ => false,
    };
    m.probe_cache.insert(key, ok);
    ok
}
