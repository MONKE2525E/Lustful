// Matcher compilation and token-tree matching (ARCH 6.2): a compiled
// matcher is a tree of token, fragment, group, and repetition nodes.
// Fragment parsing follows rustc: a fragment parse is greedy and never
// backtracks into a fragment, and a parse that began and failed is a
// hard call error, not a cue to try the next arm `note_hard_fail`).
// Plain-token repetition still backtracks. The matcher records, at
// every input position, which nodes consume input starting there; two
// different consumers at one position where at least one is a fragment
// is the local-ambiguity error, as in rustc.
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
                            let (sep, op, used) = rep_tail(trees, i + 2, false).ok_or_else(|| {
                                err(
                                    C_DEF,
                                    span,
                                    "repetition has no operator",
                                    "Write `$(...)*`, `$(...)+`, or `$(...)?`, with an optional separator token.",
                                )
                            })?;
                            if sep.is_some() && op == RepOp::Question {
                                return Err(err(
                                    C_DEF,
                                    span,
                                    "the `?` repetition operator does not take a separator",
                                    "Drop the separator, or use `*` for a separated repetition.",
                                ));
                            }
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
                                if tok_at(trees, i + 2).map(|t| t.tok) != Some(Tok::Colon) {
                                    // A bare `$crate` in a matcher is the
                                    // two literal tokens `$` and `crate`.
                                    let id1 = self.id();
                                    let id2 = self.id();
                                    out.push(MNode::Tok(*t, id1));
                                    out.push(MNode::Tok(*name_tok, id2));
                                    i += 2;
                                    continue;
                                }
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
pub fn rep_tail(trees: &[Tt], i: usize, allow_dollar_sep: bool) -> Option<(Option<Token>, RepOp, usize)> {
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
            // `$` cannot be a matcher separator (it can be one in a
            // transcriber), and the operator must follow.
            if sep.tok == Tok::Dollar && !allow_dollar_sep {
                return None;
            }
            let op = as_op(tok_at(trees, i + 1)?.tok)?;
            Some((Some(sep), op, 2))
        }
        None => None,
    }
}

/// What may follow a fragment of `kind` in a matcher: the follow set
/// rustc 1.99 (edition 2024) enforces at definition time (ARCH 6.2).
/// Probed against rustc per kind and token; only the restricted kinds
/// have a set at all, the rest accept any following token.
fn follow_ok(kind: FragKind, tok: Tok) -> bool {
    use Tok::*;
    match kind {
        FragKind::Expr | FragKind::Expr2021 | FragKind::Stmt => matches!(tok, FatArrow | Comma | Semi),
        // `>>` lexes as two `Gt` tokens here, so `Gt` covers both.
        FragKind::Ty | FragKind::Path => {
            matches!(tok, FatArrow | Comma | Semi | Eq | Pipe | Colon | Gt | LBracket | LBrace | As | Where)
        }
        // In edition 2024 `pat` still eats a top-level `|`, so `|` itself
        // may not follow it; `pat_param` stops before `|`, so it may.
        FragKind::Pat => matches!(tok, FatArrow | Comma | Eq | If | In),
        FragKind::PatParam => matches!(tok, FatArrow | Comma | Eq | Pipe | If | In),
        FragKind::Vis => vis_follow_ok(tok),
        _ => true,
    }
}

/// The `vis` follow set: a comma, or a token that can begin an item or a
/// type. Probed against rustc: every keyword and identifier qualifies,
/// as do `::`, `<`, `<<`, `&`, `&&`, `*`, `?`, `!`, `_`, lifetimes, and
/// paren/bracket groups; operators, literals, `:` and brace groups do not.
fn vis_follow_ok(tok: Tok) -> bool {
    use Tok::*;
    matches!(
        tok,
        Comma
            | Ident(_)
            | Reserved(_)
            | Lifetime(_)
            | Underscore
            | PathSep
            | Star
            | Amp
            | AndAnd
            | Shl
            | Lt
            | Question
            | Bang
            | LParen
            | LBracket
            | As
            | Break
            | Const
            | Continue
            | Else
            | Enum
            | False
            | Fn
            | For
            | If
            | Impl
            | In
            | Let
            | Loop
            | Match
            | Mod
            | Mut
            | Pub
            | Ref
            | Return
            | SelfLower
            | SelfUpper
            | Static
            | Struct
            | Trait
            | True
            | Type
            | Unsafe
            | Use
            | Where
            | While
            | Async
            | Dyn
            | Move
            | Crate
            | Super
            | Extern
            | Await
    )
}

/// Kinds whose follow set is restricted (see `follow_ok`).
fn restricted(kind: FragKind) -> bool {
    matches!(
        kind,
        FragKind::Expr
            | FragKind::Expr2021
            | FragKind::Stmt
            | FragKind::Ty
            | FragKind::Path
            | FragKind::Pat
            | FragKind::PatParam
            | FragKind::Vis
    )
}

/// Whether a fragment of kind `next` may start right after a fragment of
/// kind `prev`, per rustc: almost never, except a `block` (it starts
/// with `{`, which is in the ty/path follow set) and the item-shaped
/// starts a `vis` can precede.
fn nt_follow_ok(prev: FragKind, next: FragKind) -> bool {
    if !restricted(prev) {
        return true;
    }
    matches!(
        (prev, next),
        (FragKind::Ty, FragKind::Block)
            | (FragKind::Path, FragKind::Block)
            | (FragKind::Vis, FragKind::Ty)
            | (FragKind::Vis, FragKind::Path)
            | (FragKind::Vis, FragKind::Ident)
    )
}

/// True when one matcher node can match zero input trees.
fn nullable(node: &MNode) -> bool {
    match node {
        MNode::Tok(_, _) | MNode::Group(_, _, _) => false,
        MNode::Meta { kind, .. } => *kind == FragKind::Vis,
        MNode::Rep { inner, op, .. } => *op != RepOp::Plus || inner.iter().all(nullable),
    }
}

/// One thing that can come next after a fragment, for follow checks.
#[derive(Clone, Copy)]
enum First {
    Tok(Tok),
    Meta(FragKind),
}

/// Appends every `First` a node sequence can start with. Returns true
/// when the whole sequence can match empty, so what follows the
/// sequence is also a follow target.
fn first_of_seq(nodes: &[MNode], out: &mut Vec<First>) -> bool {
    for node in nodes {
        if !first_of_node(node, out) {
            return false;
        }
    }
    true
}

/// Appends every `First` one node can start with. Returns true when the
/// node can match empty.
fn first_of_node(node: &MNode, out: &mut Vec<First>) -> bool {
    match node {
        MNode::Tok(t, _) => {
            out.push(First::Tok(t.tok));
            false
        }
        MNode::Group(d, _, _) => {
            out.push(First::Tok(match d {
                Delim::Paren => Tok::LParen,
                Delim::Bracket => Tok::LBracket,
                Delim::Brace => Tok::LBrace,
            }));
            false
        }
        MNode::Meta { kind, .. } => {
            out.push(First::Meta(*kind));
            *kind == FragKind::Vis
        }
        MNode::Rep { inner, op, .. } => {
            let inner_empty = first_of_seq(inner, out);
            *op != RepOp::Plus || inner_empty
        }
    }
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

/// Checks one fragment against every `First` that can follow it.
fn check_follow_firsts(kind: FragKind, span: Span, firsts: &[First]) -> Result<(), Diag> {
    for first in firsts {
        match first {
            First::Tok(tok) => {
                if !follow_ok(kind, *tok) {
                    return Err(follow_err(kind, span, *tok));
                }
            }
            First::Meta(next) => {
                if !nt_follow_ok(kind, *next) {
                    return Err(err(
                        C_DEF,
                        span,
                        format!("`{}` fragments cannot be followed by a `{}` fragment", kind.name(), next.name()),
                        "Put a token both sides can agree on between the fragments, such as `,` or `;`.",
                    ));
                }
            }
        }
    }
    Ok(())
}

/// The metavariables that can end a repetition body, with the nodes
/// after each inside the body already checked by the caller. Reaching
/// the end through a nullable tail also counts, so this walks the
/// sequence from the back while nodes are nullable.
fn end_metas(nodes: &[MNode]) -> Vec<(FragKind, Span)> {
    let mut out = Vec::new();
    for node in nodes.iter().rev() {
        match node {
            MNode::Meta { kind, span, .. } => out.push((*kind, *span)),
            MNode::Rep { inner, .. } => out.extend(end_metas(inner)),
            MNode::Group(_, _, _) | MNode::Tok(_, _) => {}
        }
        if !nullable(node) {
            break;
        }
    }
    out
}

/// Follow-set check over one matcher sequence, recursively. `after`
/// holds the `First`s that can follow this whole sequence (empty at an
/// arm end or a group end, where the fragment parser stops anyway).
fn check_follow_seq(nodes: &[MNode], after: &[First]) -> Result<(), Diag> {
    for (j, node) in nodes.iter().enumerate() {
        // What can follow node j: the rest of this sequence, then `after`.
        let mut next = Vec::new();
        if first_of_seq(&nodes[j + 1..], &mut next) {
            next.extend_from_slice(after);
        }
        match node {
            MNode::Meta { kind, span, .. } => check_follow_firsts(*kind, *span, &next)?,
            MNode::Group(_, inner, _) => check_follow_seq(inner, &[])?,
            MNode::Rep { inner, sep, .. } => {
                check_follow_seq(inner, &[])?;
                // A fragment at the end of the body is followed by the
                // separator between iterations and by whatever follows
                // the repetition after the last one. With no separator
                // rustc does not check the loop-back edge, so the body
                // start is not a follow target here.
                for (kind, span) in end_metas(inner) {
                    if let Some(sep) = sep {
                        check_follow_firsts(kind, span, &[First::Tok(sep.tok)])?;
                    }
                    check_follow_firsts(kind, span, &next)?;
                }
            }
            MNode::Tok(_, _) => {}
        }
    }
    Ok(())
}

/// rustc rejects a repetition whose body can match empty (it would not
/// make progress), unless a separator token stands between iterations.
fn check_empty_reps(nodes: &[MNode]) -> Result<(), Diag> {
    for node in nodes {
        match node {
            MNode::Rep { inner, sep, span, .. } => {
                if sep.is_none() && inner.iter().all(nullable) {
                    return Err(err(
                        C_DEF,
                        *span,
                        "repetition matches an empty token tree",
                        "Give the repetition a body that always consumes a token, or a separator.",
                    ));
                }
                check_empty_reps(inner)?;
            }
            MNode::Group(_, inner, _) => check_empty_reps(inner)?,
            MNode::Tok(_, _) | MNode::Meta { .. } => {}
        }
    }
    Ok(())
}

/// Compiles one macro arm: matcher trees to matcher nodes plus the
/// metavariable table. Runs the follow-set and empty-repetition
/// definition checks (ARCH 6.2).
pub fn compile_arm(matcher: &[Tt], span: Span, interner: &Interner) -> Result<(Vec<MNode>, FxMap<Sym, VarInfo>), Diag> {
    let mut c = Compile { interner, next_id: 0, vars: FxMap::default() };
    let nodes = c.seq(matcher, 0)?;
    check_empty_reps(&nodes)?;
    check_follow_seq(&nodes, &[])?;
    let _ = span;
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
    /// position): the (node id, is-fragment) pairs that were live at
    /// that position and could begin on the tree there (rustc's
    /// can-begin sets, not only successful parses).
    pub consumers: FxMap<(usize, usize, u32, usize), Vec<(u32, bool)>>,
    /// A fragment parser began a parse and failed (rustc's hard error:
    /// the call fails even when a later arm would token-match). Set
    /// during matching of one arm; read by the arm loop.
    pub hard_fail: bool,
    call_span: Span,
}

impl<'a> Matcher<'a> {
    /// A fresh matcher for one macro call at `call_span`.
    pub fn new(interner: &'a Interner, known: &'a Known, strings: &'a [String], call_span: Span) -> Matcher<'a> {
        Matcher {
            interner,
            known,
            strings,
            budget: MATCH_BUDGET,
            probe_cache: FxMap::default(),
            consumers: FxMap::default(),
            hard_fail: false,
            call_span,
        }
    }

    fn step(&mut self) -> Result<(), Diag> {
        self.budget = self.budget.saturating_sub(1);
        if self.budget == 0 {
            return Err(err(C_CAP, self.call_span, "macro matching exceeded its step limit", "Simplify the macro pattern or the call."));
        }
        Ok(())
    }

    /// Records one live matcher node at `pos` for the ambiguity check,
    /// when the node can begin on the tree there.
    fn attempt(&mut self, input: &[Tt], pos: usize, id: u32, is_frag: bool, begins: bool) {
        if !begins {
            return;
        }
        let first = input.first().map_or(0, |t| t.span().lo);
        let key = (input.as_ptr() as usize, input.len(), first, pos);
        self.consumers.entry(key).or_default().push((id, is_frag));
    }

    /// True when any position had two different live nodes that could
    /// begin there and at least one was a fragment: the call is
    /// locally ambiguous, whether or not either path later matches.
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
            let begins = matches!(input.get(pos), Some(Tt::Tok(actual)) if tok_matches(&pattern.tok, &actual.tok, m.strings));
            m.attempt(input, pos, *id, false, begins);
            if begins {
                match_seq(m, rest, input, pos + 1, binds, out)?;
            }
            Ok(())
        }
        MNode::Meta { name, kind, id, span } => match_meta(m, *name, *kind, *id, *span, rest, input, pos, binds, out),
        MNode::Group(delim, inner, id) => {
            let begins = matches!(input.get(pos), Some(Tt::Delim(d, _, _)) if d == delim);
            m.attempt(input, pos, *id, false, begins);
            if let Some(Tt::Delim(d, inner_input, _)) = input.get(pos)
                && d == delim
            {
                let inner_input = splice_transparent(inner_input);
                let mut inner_results = Vec::new();
                match_seq(m, inner, &inner_input, 0, BindMap::default(), &mut inner_results)?;
                for (end, inner_binds) in inner_results {
                    if end != inner_input.len() {
                        continue;
                    }
                    let mut merged = binds.clone();
                    merged.extend(inner_binds);
                    match_seq(m, rest, input, pos + 1, merged, out)?;
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
            let begins = matches!(input.get(start), Some(Tt::Tok(actual)) if tok_matches(&sep_tok.tok, &actual.tok, m.strings));
            m.attempt(input, pos, rep_id, false, begins);
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

/// True for tokens an `ident` fragment matches: an identifier or a
/// keyword (rustc accepts `self`, `fn`, `true`, `Self` here).
fn is_ident_tok(tok: Tok) -> bool {
    matches!(
        tok,
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
            | Tok::Await
    )
}

/// True for one literal token (a leading `-` is the caller's concern).
fn is_literal_tok(tok: Tok) -> bool {
    matches!(tok, Tok::Int(..) | Tok::Float(_) | Tok::Str(_) | Tok::ByteStr(_) | Tok::ByteChar(_) | Tok::Char(_) | Tok::True | Tok::False)
}

/// True when these trees read as exactly one literal: one literal
/// token, or `-` before one, splicing nested fragments open. A
/// forwarded fragment that holds just a literal can rebind to a
/// `literal` metavariable whatever kind first matched it.
fn trees_read_literal(trees: &[Tt]) -> bool {
    fn toks(trees: &[Tt], out: &mut Vec<Tok>) -> bool {
        trees.iter().all(|t| match t {
            Tt::Tok(tok) => {
                out.push(tok.tok);
                true
            }
            Tt::Frag(_, inner, _) => toks(inner, out),
            Tt::Delim(_, _, _) => false,
        })
    }
    let mut flat = Vec::new();
    if !toks(trees, &mut flat) {
        return false;
    }
    matches!(flat.as_slice(), [t] if is_literal_tok(*t)) || matches!(flat.as_slice(), [Tok::Minus, t] if is_literal_tok(*t))
}

/// True when a fragment of `kind` can begin at this input position
/// (rustc's can-begin sets). Drives the attempt record behind local
/// ambiguity: a `-` can begin a literal even when the literal parse
/// then fails, and `[` can begin a type.
fn meta_can_begin(m: &Matcher, kind: FragKind, input: &[Tt], pos: usize) -> bool {
    match input.get(pos) {
        None => false,
        Some(Tt::Frag(fk, inner, _)) if !fk.transparent() => {
            can_forward(*fk, kind) || (kind == FragKind::Literal && trees_read_literal(inner))
        }
        Some(_) => match kind {
            FragKind::Ident => matches!(tok_at(input, pos), Some(t) if is_ident_tok(t.tok)),
            FragKind::Lifetime => matches!(tok_at(input, pos).map(|t| t.tok), Some(Tok::Lifetime(_))),
            FragKind::Literal => matches!(tok_at(input, pos), Some(t) if is_literal_tok(t.tok) || t.tok == Tok::Minus),
            FragKind::Tt => true,
            FragKind::Vis => tok_at(input, pos).map(|t| t.tok) == Some(Tok::Pub),
            FragKind::Meta => tok_at(input, pos).is_some_and(|t| super::meta_sym(t.tok, m.interner).is_some()),
            _ => can_begin(m, kind, input, pos),
        },
    }
}

/// Binds `name` to the fragment slice ending at each of `ends` and
/// matches the rest of the sequence from there.
#[allow(clippy::too_many_arguments)]
fn match_meta_ends(
    m: &mut Matcher,
    name: Sym,
    kind: FragKind,
    ends: Vec<usize>,
    rest: &[MNode],
    input: &[Tt],
    pos: usize,
    binds: BindMap,
    out: &mut Vec<(usize, BindMap)>,
) -> Result<(), Diag> {
    let at = input.get(pos).map_or(m.call_span, |t| t.span());
    for end in ends {
        let slice: Vec<Tt> = input[pos..end].to_vec();
        // A whole forwarded fragment rebinds as itself, keeping its
        // kind identity; a longer re-parse wraps the new slice.
        let value = if let [Tt::Frag(..)] = slice.as_slice() {
            Bind::Leaf(slice)
        } else if kind.transparent() {
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
    m.attempt(input, pos, id, true, meta_can_begin(m, kind, input, pos));
    // A forwarded opaque fragment is one unit: it can rebind to a
    // compatible kind (ARCH 6.2), be taken whole as one token tree,
    // or, for a literal target, rebind when it holds just a literal.
    if let Some(Tt::Frag(fk, inner, _)) = input.get(pos)
        && !fk.transparent()
    {
        let fk = *fk;
        // Same-kind fragments re-parse with what follows: an outer
        // macro that forwards `$e + 1` into an `$a:expr` matcher must
        // read `2 + 1` as one expression, not stop at the fragment.
        if fk == kind && parsed_kind(kind) {
            let ends = fragment_ends(m, kind, input, pos)?;
            if !ends.is_empty() {
                return match_meta_ends(m, name, kind, ends, rest, input, pos, binds, out);
            }
        }
        if can_forward(fk, kind) || (kind == FragKind::Literal && trees_read_literal(inner)) {
            let mut next = binds;
            next.insert(name, Bind::Leaf(vec![input[pos].clone()]));
            return match_seq(m, rest, input, pos + 1, next, out);
        }
        return Ok(());
    }
    let ends = fragment_ends(m, kind, input, pos)?;
    match_meta_ends(m, name, kind, ends, rest, input, pos, binds, out)
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

/// Whether an opaque fragment matched as `from` in an outer macro can
/// rebind to a `to` metavariable in an inner macro. Probed against
/// rustc per kind pair; anything not listed (and not the same kind, and
/// not `tt`, which takes every fragment whole) does not rebind.
fn can_forward(from: FragKind, to: FragKind) -> bool {
    use FragKind::*;
    if from == to || to == Tt {
        return true;
    }
    let from = if from == Expr2021 { Expr } else { from };
    let to = if to == Expr2021 { Expr } else { to };
    matches!(
        (from, to),
        (Expr, Pat | PatParam | Stmt)
            | (Ty, Path | Meta)
            | (Path, Expr | Ty | Pat | PatParam | Stmt | Meta)
            | (Pat, PatParam)
            | (PatParam, Pat)
            | (Block, Expr | Stmt)
            | (Item, Stmt)
            | (Literal, Expr | Pat | PatParam | Stmt)
    )
}

/// Kinds rustc parses with its real fragment parser (as opposed to the
/// single-token scanner kinds). Only these can hard-fail a call.
fn parsed_kind(kind: FragKind) -> bool {
    matches!(
        kind,
        FragKind::Expr
            | FragKind::Expr2021
            | FragKind::Ty
            | FragKind::Pat
            | FragKind::PatParam
            | FragKind::Path
            | FragKind::Stmt
            | FragKind::Block
            | FragKind::Item
    )
}

/// True when `tree` can be the first tree of a fragment of `kind`, so
/// rustc's fragment parser would start a parse here. A first tree that
/// cannot start the fragment kills the arm silently instead.
fn can_begin(m: &Matcher, kind: FragKind, input: &[Tt], pos: usize) -> bool {
    use Tok::*;
    let tree = input.get(pos);
    if kind == FragKind::Item {
        // rustc's item parser starts on any tree and reports "expected
        // an item keyword" when it is not one, so every item attempt
        // with no item reading is a hard failure.
        let _ = m;
        return tree.is_some();
    }
    let Some(tree) = tree else { return false };
    if kind == FragKind::Stmt && super::starts_item(&input[pos..], m.interner) {
        return true;
    }
    match tree {
        Tt::Delim(d, _, _) => match kind {
            FragKind::Expr | FragKind::Expr2021 | FragKind::Stmt => true,
            FragKind::Ty | FragKind::Pat | FragKind::PatParam => *d != Delim::Brace,
            FragKind::Block => *d == Delim::Brace,
            _ => false,
        },
        Tt::Frag(_, _, _) => false,
        Tt::Tok(t) => {
            let expr_start = matches!(
                t.tok,
                Ident(_)
                    | Reserved(_)
                    | SelfUpper
                    | SelfLower
                    | Crate
                    | Super
                    | Int(..)
                    | Float(_)
                    | Str(_)
                    | ByteStr(_)
                    | ByteChar(_)
                    | Char(_)
                    | True
                    | False
                    | Lifetime(_)
                    | Minus
                    | Star
                    | Amp
                    | AndAnd
                    | Bang
                    | Pipe
                    | OrOr
                    | DotDot
                    | DotDotEq
                    | PathSep
                    | Underscore
                    | Lt
                    | If
                    | Match
                    | Loop
                    | While
                    | For
                    | Return
                    | Break
                    | Continue
                    | Move
                    | Unsafe
                    | Async
                    | Const
                    // An outer attribute on the expression (`#[a] 1`).
                    | Pound
            );
            match kind {
                FragKind::Expr => expr_start,
                // The 2021 expression grammar has no `_` expression
                // and no const blocks, so neither begins its parser.
                FragKind::Expr2021 => expr_start && !matches!(t.tok, Tok::Underscore | Tok::Const),
                FragKind::Stmt => expr_start || matches!(t.tok, Let | Semi),
                FragKind::Ty => matches!(
                    t.tok,
                    Ident(_)
                        | Reserved(_)
                        | SelfUpper
                        | SelfLower
                        | Crate
                        | Super
                        | Underscore
                        | Star
                        | Amp
                        | Bang
                        | PathSep
                        | Dyn
                        | Impl
                        | Fn
                        | Unsafe
                        | Extern
                        // A qualified path type (`<T as P>`).
                        | Lt
                ),
                FragKind::Pat | FragKind::PatParam => {
                    matches!(
                        t.tok,
                        Ident(_)
                            | Reserved(_)
                            | SelfUpper
                            | SelfLower
                            | Crate
                            | Super
                            | Underscore
                            | Int(..)
                            | Float(_)
                            | Str(_)
                            | ByteStr(_)
                            | ByteChar(_)
                            | Char(_)
                            | True
                            | False
                            | Minus
                            | Amp
                            | AndAnd
                            // `..` begins a rest or range-to pattern;
                            // `..=` does not begin a pattern fragment
                            // in rustc, so it is absent here.
                            | DotDot
                            | Mut
                            | Ref
                            | PathSep
                            // A qualified path pattern.
                            | Lt
                    ) || (kind == FragKind::Pat && t.tok == Pipe)
                }
                FragKind::Path => is_seg_tok(t.tok) || t.tok == PathSep || t.tok == Lt,
                FragKind::Block => false,
                _ => false,
            }
        }
    }
}

/// True when `tree`, standing right after a complete fragment of
/// `kind`, would make rustc's greedy fragment parser keep parsing
/// (and therefore fail hard when no longer fragment parses).
fn can_continue(kind: FragKind, tree: Option<&Tt>) -> bool {
    use Tok::*;
    let Some(tree) = tree else { return false };
    match tree {
        Tt::Delim(_, _, _) => {
            matches!(kind, FragKind::Expr | FragKind::Expr2021 | FragKind::Stmt)
                || kind == FragKind::Path && matches!(tree, Tt::Delim(Delim::Paren, _, _))
                // A struct or tuple-struct pattern body continues
                // a pattern (`S { .. }`, `S(..)`).
                || matches!(kind, FragKind::Pat | FragKind::PatParam)
                    && matches!(tree, Tt::Delim(Delim::Brace | Delim::Paren, _, _))
        }
        Tt::Frag(_, _, _) => false,
        Tt::Tok(t) => match kind {
            FragKind::Expr | FragKind::Expr2021 | FragKind::Stmt => matches!(
                t.tok,
                Plus | Minus
                    | Star
                    | Slash
                    | Percent
                    | EqEq
                    | Ne
                    | Lt
                    | Le
                    | Gt
                    | Ge
                    | AndAnd
                    | OrOr
                    | Amp
                    | Pipe
                    | Caret
                    | Shl
                    | PlusEq
                    | MinusEq
                    | StarEq
                    | SlashEq
                    | PercentEq
                    | AmpEq
                    | PipeEq
                    | CaretEq
                    | ShlEq
                    | Eq
                    | Dot
                    | Question
                    | As
                    | DotDot
                    | DotDotEq
            ),
            FragKind::Ty | FragKind::Path => matches!(t.tok, Lt | PathSep),
            FragKind::Pat => matches!(t.tok, Pipe | At | DotDot | DotDotEq),
            FragKind::PatParam => matches!(t.tok, At | DotDot | DotDotEq),
            _ => false,
        },
    }
}

/// Records rustc's fragment-parser hard failure for one fragment
/// attempt: the parser began (the first tree can start the kind) but
/// no complete parse exists, or the greedy parse is followed by a
/// tree the parser would have tried to continue with. The arm loop
/// turns this into a call error when the arm does not match anyway;
/// checking later arms after it is how a token arm could otherwise
/// accept a program rustc rejects.
fn note_hard_fail(m: &mut Matcher, kind: FragKind, input: &[Tt], pos: usize, ends: &[usize]) {
    if m.hard_fail || !parsed_kind(kind) {
        return;
    }
    match ends.iter().max() {
        None => {
            if can_begin(m, kind, input, pos) {
                m.hard_fail = true;
            }
        }
        Some(&g) => {
            if can_continue(kind, input.get(g)) {
                m.hard_fail = true;
                return;
            }
            // Continuations only some heads take: a `+` after a
            // `dyn`/`impl` type (more bounds), a `->` after a type
            // that ended in a parenthesized argument list (a fn
            // type's return), and `:`/`=`/`else` after a leading
            // `let` in a statement. A plain type or expression
            // statement stops before the same tokens, so the head
            // of the greedy slice decides.
            let head = tok_at(input, pos).map(|t| t.tok);
            let next = tok_at(input, g).map(|t| t.tok);
            let continues = match (kind, head, next) {
                (FragKind::Ty, Some(Tok::Dyn | Tok::Impl), Some(Tok::Plus)) => true,
                (FragKind::Stmt, Some(Tok::Let), Some(Tok::Colon | Tok::Eq | Tok::Else)) => true,
                (FragKind::Ty, _, Some(Tok::Arrow)) => {
                    g >= pos + 2 && matches!(input.get(g - 1), Some(Tt::Delim(Delim::Paren, _, _)))
                }
                _ => false,
            };
            if continues {
                m.hard_fail = true;
            }
        }
    }
}

/// The end positions where a fragment of `kind` starting at `pos` can
/// stop. Scanner kinds are exact. Parsed kinds try each end with the
/// real parser (ARCH 6.2) but keep only the longest parse: rustc's
/// fragment parser is greedy and never backtracks into a fragment to
/// let the rest of the matcher fit. A began parse with no complete
/// reading records the hard failure (see `note_hard_fail`).
fn fragment_ends(m: &mut Matcher, kind: FragKind, input: &[Tt], pos: usize) -> Result<Vec<usize>, Diag> {
    let first = tok_at(input, pos).map(|t| t.tok);
    let mut ends = match kind {
        FragKind::Ident => match first {
            Some(t) if is_ident_tok(t) => vec![pos + 1],
            _ => vec![],
        },
        FragKind::Lifetime => match first {
            Some(Tok::Lifetime(_)) => vec![pos + 1],
            _ => vec![],
        },
        FragKind::Literal => match first {
            Some(t) if is_literal_tok(t) => vec![pos + 1],
            // A `-` before any literal token is one literal fragment in
            // rustc (even `- "x"`, which only fails later if typed).
            Some(Tok::Minus) if matches!(tok_at(input, pos + 1), Some(t) if is_literal_tok(t.tok)) => {
                vec![pos + 2]
            }
            // A `-` began the literal parse and no literal followed:
            // rustc's hard failure, not a cue to try the next arm.
            Some(Tok::Minus) => {
                m.hard_fail = true;
                vec![]
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
            Some(tree @ Tt::Delim(Delim::Brace, _, _)) => {
                if probe(m, kind, std::slice::from_ref(tree)) {
                    vec![pos + 1]
                } else {
                    m.hard_fail = true;
                    vec![]
                }
            }
            _ => vec![],
        },
        FragKind::Vis => {
            // Greedy, like rustc: a `pub` here is the visibility, never
            // left for a later matcher token by matching empty instead.
            // The parenthesized form counts only for the restricted
            // paths (`pub(crate)`, `pub(in a::b)`); `pub(foo)` is just
            // `pub`. At the end of the input, rustc's vis parser has no
            // token to decide on and the call fails, so empty vis
            // needs a following tree.
            if first == Some(Tok::Pub) {
                if let Some(Tt::Delim(Delim::Paren, inner, _)) = input.get(pos + 1) {
                    let restricted = matches!(
                        inner.as_slice(),
                        [Tt::Tok(t)] if matches!(t.tok, Tok::Crate | Tok::SelfLower | Tok::Super)
                    ) || (tok_at(inner, 0).map(|t| t.tok) == Some(Tok::In)
                        && inner.len() > 1
                        && inner[1..].iter().all(|t| matches!(t, Tt::Tok(tok) if is_seg_tok(tok.tok) || tok.tok == Tok::PathSep)));
                    if restricted { vec![pos + 2] } else { vec![pos + 1] }
                } else {
                    vec![pos + 1]
                }
            } else if pos < input.len() {
                vec![pos]
            } else {
                vec![]
            }
        }
        FragKind::Meta => meta_end(input, pos, m.interner).into_iter().collect(),
        FragKind::Path => path_ends(m, input, pos),
        // An item ends at its item boundary (or after a macro call
        // item's group and `;`). A macro call shape is a valid item
        // token shape as written, so those ends stay unprobed; their
        // expansion is validated when it runs.
        FragKind::Item => {
            let mut ends = Vec::new();
            // The boundary alone is not validation: the slice must also
            // parse as exactly one item, or token soup with an item
            // keyword and a brace group would bind as an item fragment
            // rustc's item parser rejects.
            if let Some(end) = super::item_end(input, pos, m.interner) {
                if probe(m, kind, &input[pos..end]) {
                    ends.push(end);
                }
            }
            if let Some(end) = macro_call_shape(input, pos) {
                // A macro call is one item only when brace-delimited
                // or followed by `;` (the item macro rule rustc
                // applies inside a fragment too).
                if matches!(input.get(end - 1), Some(Tt::Delim(Delim::Brace, _, _))) {
                    ends.push(end);
                }
                if input.get(end).is_some_and(|t| t.is_tok(Tok::Semi)) {
                    ends.push(end + 1);
                }
            }
            // The probe fallback must not resurrect a macro call the
            // shape check just refused: this parser accepts a lone
            // paren macro call as a crate's last item, rustc does not.
            if ends.is_empty() && macro_call_shape(input, pos).is_none() {
                for end in pos + 1..=input.len() {
                    m.step()?;
                    if probe(m, kind, &input[pos..end]) {
                        ends.push(end);
                    }
                }
            }
            ends.sort_unstable();
            ends.dedup();
            ends
        }
        FragKind::Expr | FragKind::Expr2021 => {
            // One greedy parse, the way rustc's fragment parser runs:
            // flatten the rest of the input once and ask the parser
            // where one expression ends, instead of probing every
            // candidate end (which is cubic on long repetitions).
            m.step()?;
            if kind == FragKind::Expr2021
                && (matches!(input.get(pos), Some(Tt::Tok(t)) if t.tok == Tok::Underscore)
                    && !matches!(input.get(pos + 1), Some(Tt::Tok(t)) if t.tok == Tok::Eq)
                    || tok_at(input, pos).map(|t| t.tok) == Some(Tok::Const)
                        && matches!(input.get(pos + 1), Some(Tt::Delim(Delim::Brace, _, _))))
            {
                vec![]
            } else if kind == FragKind::Expr && matches!(input.get(pos), Some(Tt::Tok(t)) if t.tok == Tok::Underscore) {
                vec![pos + 1]
            } else {
                let (flat, bounds) = probe_flatten_bounded(m, kind, &input[pos..]);
                match parser::probe_expr_end(&flat, m.strings, m.interner, m.known) {
                    Some(flat_end) => match bounds.iter().rposition(|&b| b == flat_end) {
                        Some(k) if k > 0 => vec![pos + k],
                        _ => vec![],
                    },
                    // The subset parser refuses some valid forms
                    // (closures, `?`, `.await`, async and unsafe
                    // blocks); the recognizer knows their shapes
                    // and where they greedily end.
                    None => super::recognize::expr_end(input, pos, m.interner, kind == FragKind::Expr)
                        .map_or_else(Vec::new, |end| vec![end]),
                }
            }
        }
        FragKind::Ty | FragKind::Pat | FragKind::PatParam | FragKind::Stmt => {
            let mut ends = Vec::new();
            for end in pos + 1..=input.len() {
                m.step()?;
                let slice = &input[pos..end];
                // A statement fragment never owns the `;` after it: a
                // matcher that wants it writes the token itself. A lone
                // `;` is itself an (empty) statement in rustc. An item
                // statement is the exception: its own `;` belongs to
                // the item (`struct S;`), so an item-shaped slice may
                // end with it.
                if kind == FragKind::Stmt
                    && slice.len() > 1
                    && matches!(slice.last(), Some(Tt::Tok(t)) if t.tok == Tok::Semi)
                    && super::item_end(input, pos, m.interner) != Some(end)
                {
                    continue;
                }
                // A pattern fragment cannot start with `..=`: rustc's
                // fragment parser does not begin a pattern there (a
                // subpattern after `@` may start with one, but that is
                // not this slice's head). The subset parser accepts it
                // as a range, so refuse it here.
                if matches!(kind, FragKind::Pat | FragKind::PatParam) && matches!(slice.first(), Some(Tt::Tok(t)) if t.tok == Tok::DotDotEq) {
                    continue;
                }
                if kind == FragKind::Stmt && matches!(slice, [Tt::Tok(t)] if t.tok == Tok::Semi) {
                    ends.push(end);
                    continue;
                }
                if kind == FragKind::PatParam && slice.iter().any(|t| t.is_tok(Tok::Pipe)) {
                    continue;
                }
                if probe(m, kind, slice)
                    || (kind == FragKind::Stmt && super::item_end(input, pos, m.interner) == Some(end))
                    || (kind == FragKind::Ty && is_fn_type(m, slice))
                {
                    ends.push(end);
                }
            }
            ends
        }
    };
    // A fragment that ends in `..=` has no range end and does not
    // parse in rustc. The subset parser's range form accepts it,
    // so refuse those ends here for every parsed kind.
    if parsed_kind(kind) {
        ends.retain(|&end| !matches!(input.get(end.wrapping_sub(1)), Some(Tt::Tok(t)) if t.tok == Tok::DotDotEq));
    }
    if parsed_kind(kind) {
        note_hard_fail(m, kind, input, pos, &ends);
        // Parsed fragments are greedy (see the fn comment). Item and
        // block ends are boundary shapes, not parses to shorten.
        if matches!(
            kind,
            FragKind::Expr | FragKind::Expr2021 | FragKind::Ty | FragKind::Pat | FragKind::PatParam | FragKind::Stmt | FragKind::Path
        ) {
            if let Some(&g) = ends.iter().max() {
                ends = vec![g];
            }
        }
    }
    Ok(ends)
}

/// True when `slice` is one function pointer type (`fn(A) -> B`, with
/// optional `unsafe` and `extern "C"` prefixes). The parser has no fn
/// types yet, so `probe` cannot judge these; the shape is small enough
/// to validate directly, with each argument and the return type
/// probed as a type.
fn is_fn_type(m: &mut Matcher, slice: &[Tt]) -> bool {
    let mut i = 0;
    if tok_at(slice, i).map(|t| t.tok) == Some(Tok::Unsafe) {
        i += 1;
    }
    if tok_at(slice, i).map(|t| t.tok) == Some(Tok::Extern) {
        i += 1;
        if matches!(tok_at(slice, i).map(|t| t.tok), Some(Tok::Str(_))) {
            i += 1;
        }
    }
    if tok_at(slice, i).map(|t| t.tok) != Some(Tok::Fn) {
        return false;
    }
    let Some(Tt::Delim(Delim::Paren, args, _)) = slice.get(i + 1) else { return false };
    let args = args.clone();
    // Each argument piece reads as a type (a `name:` prefix is allowed
    // and not part of the type).
    let mut start = 0;
    for j in 0..=args.len() {
        if j < args.len() && !args[j].is_tok(Tok::Comma) {
            continue;
        }
        let piece = &args[start..j];
        start = j + 1;
        if piece.is_empty() {
            continue;
        }
        let ty_at = if piece.len() > 2 && tok_at(piece, 1).map(|t| t.tok) == Some(Tok::Colon) { 2 } else { 0 };
        if !probe(m, FragKind::Ty, &piece[ty_at..]) && !is_fn_type(m, &piece[ty_at..]) {
            return false;
        }
    }
    let rest = &slice[i + 2..];
    if rest.is_empty() {
        return true;
    }
    tok_at(rest, 0).map(|t| t.tok) == Some(Tok::Arrow)
        && rest.len() > 1
        && (probe(m, FragKind::Ty, &rest[1..]) || is_fn_type(m, &rest[1..]))
}

/// The end of one `meta` fragment at `pos`: a path (segments may be
/// keywords, as in `unsafe(x)`), then an optional `= literal` (a
/// negative numeric literal included) or one delimited group.
fn meta_end(input: &[Tt], pos: usize, interner: &Interner) -> Option<usize> {
    let mut i = pos;
    let is_name =
        |input: &[Tt], i: usize| tok_at(input, i).is_some_and(|t| super::meta_sym(t.tok, interner).is_some() || t.tok == Tok::Super);
    if !is_name(input, i) {
        return None;
    }
    i += 1;
    while tok_at(input, i).map(|t| t.tok) == Some(Tok::PathSep) && is_name(input, i + 1) {
        i += 2;
    }
    match input.get(i) {
        Some(Tt::Tok(t)) if t.tok == Tok::Eq => {
            if tok_at(input, i + 1).map(|t| t.tok) == Some(Tok::Minus)
                && matches!(tok_at(input, i + 2).map(|t| t.tok), Some(Tok::Int(..) | Tok::Float(_)))
            {
                return Some(i + 3);
            }
            // A macro call as the value (`doc = concat!("a")`).
            if let Some(end) = macro_call_shape(input, i + 1) {
                return Some(end);
            }
            match tok_at(input, i + 1).map(|t| t.tok) {
                Some(Tok::Str(_) | Tok::Int(..) | Tok::Float(_) | Tok::Char(_) | Tok::True | Tok::False | Tok::ByteStr(_)) => Some(i + 2),
                _ => None,
            }
        }
        Some(Tt::Delim(_, _, _)) => Some(i + 1),
        _ => Some(i),
    }
}

/// True when one comma piece of generic arguments has a reading as a
/// type, a const expression, a lifetime, or a `Name = ...` /
/// `Name: ...` binding. A piece with no reading (such as `1 2`) is
/// what rustc's path parser rejects; accepting it would bind a path
/// fragment rustc never accepts.
fn generic_arg_ok(m: &mut Matcher, piece: &[Tt]) -> bool {
    if piece.is_empty() {
        return false;
    }
    if matches!(piece, [Tt::Tok(t)] if matches!(t.tok, Tok::Lifetime(_))) {
        return true;
    }
    if probe(m, FragKind::Ty, piece) || probe(m, FragKind::Expr, piece) {
        return true;
    }
    // A binding: one name, then `=` or `:`, then a readable rest.
    if let (Some(name), Some(sep)) = (tok_at(piece, 0), tok_at(piece, 1))
        && super::meta_sym(name.tok, m.interner).is_some()
        && matches!(sep.tok, Tok::Eq | Tok::Colon)
        && piece.len() > 2
    {
        return generic_arg_ok(m, &piece[2..]);
    }
    false
}

/// True when the trees between a path's `<` and `>` read as generic
/// arguments (comma pieces, nested angles counted). Empty arguments
/// (`a<>`) are accepted by rustc's path parser, so they pass here too.
fn angle_args_ok(m: &mut Matcher, inner: &[Tt]) -> bool {
    if inner.is_empty() {
        return true;
    }
    let mut depth = 0i64;
    let mut start = 0;
    for i in 0..=inner.len() {
        let tok = tok_at(inner, i).map(|t| t.tok);
        match tok {
            Some(Tok::Lt) => depth += 1,
            Some(Tok::Shl) => depth += 2,
            Some(Tok::Gt) => depth -= 1,
            _ => {}
        }
        if i == inner.len() || (tok == Some(Tok::Comma) && depth == 0) {
            if !generic_arg_ok(m, &inner[start..i]) {
                return false;
            }
            start = i + 1;
        }
    }
    true
}

/// Candidate ends for a path fragment: segments with optional generic
/// arguments. The caller keeps only the longest (greedy, like rustc).
/// An angle group whose arguments have no reading ends the path
/// before it instead of being balanced blind.
fn path_ends(m: &mut Matcher, input: &[Tt], pos: usize) -> Vec<usize> {
    fn angle_end(input: &[Tt], mut i: usize) -> Option<usize> {
        // `i` is at the opening `<`. Group trees are single units here;
        // their contents cannot hold this angle's closing token.
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
                _ => {}
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
        let angle_at = if tok_at(input, i).map(|t| t.tok) == Some(Tok::PathSep) && tok_at(input, i + 1).map(|t| t.tok) == Some(Tok::Lt) {
            Some(i + 1)
        } else if tok_at(input, i).map(|t| t.tok) == Some(Tok::Lt) {
            Some(i)
        } else {
            None
        };
        if let Some(at) = angle_at {
            match angle_end(input, at) {
                Some(end) if angle_args_ok(m, &input[at + 1..end - 1]) => i = end,
                Some(end) => {
                    // The arguments started and failed: a began parse
                    // with no reading, which is rustc's hard failure
                    // when the arm does not match some other way. The
                    // ends collected so far stay candidates for the
                    // continuation check to judge.
                    let _ = end;
                    m.hard_fail = true;
                    break;
                }
                None => break,
            }
        }
        // Parenthesized arguments (`Fn(A, B)` sugar): the group is
        // part of the path when its pieces read as types, and a
        // following `-> T` return type belongs to it as well.
        if let Some(Tt::Delim(Delim::Paren, inner, _)) = input.get(i) {
            let inner = inner.clone();
            if angle_args_ok(m, &inner) {
                i += 1;
                if tok_at(input, i).map(|t| t.tok) == Some(Tok::Arrow) {
                    for end in (i + 2..=input.len()).rev() {
                        if probe(m, FragKind::Ty, &input[i + 1..end]) || is_fn_type(m, &input[i + 1..end]) {
                            i = end;
                            break;
                        }
                    }
                }
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
    ends
}

/// Flattens a fragment candidate slice for a parser probe. Two things in
/// a slice are not plain syntax yet and become placeholders of the right
/// shape: opaque fragments forwarded from an outer macro, and macro
/// calls, which parse as one node of the position they stand in.
fn probe_flatten(m: &Matcher, kind: FragKind, trees: &[Tt]) -> Vec<Token> {
    probe_flatten_impl(m, kind, trees, None)
}

/// `probe_flatten` plus, per top-level tree, the flat index where it
/// starts (with one final entry for the end). A greedy parser end in
/// flat tokens maps back to a tree index through these bounds.
fn probe_flatten_bounded(m: &Matcher, kind: FragKind, trees: &[Tt]) -> (Vec<Token>, Vec<usize>) {
    let mut bounds = Vec::with_capacity(trees.len() + 1);
    let out = probe_flatten_impl(m, kind, trees, Some(&mut bounds));
    bounds.push(out.len());
    (out, bounds)
}

fn probe_flatten_impl(m: &Matcher, kind: FragKind, trees: &[Tt], bounds: Option<&mut Vec<usize>>) -> Vec<Token> {
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
    fn go(m: &Matcher, kind: FragKind, trees: &[Tt], out: &mut Vec<Token>, bounds: Option<&mut Vec<usize>>) {
        let mut bounds = bounds;
        let mut i = 0;
        while i < trees.len() {
            if let Some(b) = &bounds {
                debug_assert_eq!(b.len(), i);
            }
            if let Some(b) = &mut bounds {
                b.push(out.len());
            }
            // A macro call shape: segments, `!`, one group. Its argument
            // trees are arbitrary tokens to the fragment parser, so the
            // call reads as one placeholder node of this kind.
            if let Some(end) = macro_call_shape(trees, i) {
                let at = out.len();
                placeholder(m, kind, trees[i].span(), out);
                if let Some(b) = &mut bounds {
                    for _ in i + 1..end {
                        b.push(at);
                    }
                }
                i = end;
                continue;
            }
            // Lifetimes in types are the one dropped token: the parser
            // has no lifetime types yet, and a lifetime is valid exactly
            // where the token after it decides (`&'a T`, `F<'a>`), which
            // the probe still judges. Everything else flattens as
            // written: a placeholder that discards group contents (an
            // array, tuple, or index body) would let token soup such as
            // `[1 2]` or `(1 2, 3)` probe as a valid fragment that
            // rustc's fragment parser rejects, and a template that only
            // stringifies the fragment would then accept the program.
            if let Tt::Tok(t) = &trees[i]
                && matches!(t.tok, Tok::Lifetime(_))
                && matches!(kind, FragKind::Ty | FragKind::Path)
            {
                match out.last().map(|x| x.tok) {
                    Some(Tok::Lt | Tok::Comma) => out.push(Token { tok: Tok::Ident(m.interner.intern("u8")), span: t.span }),
                    _ => {}
                }
                i += 1;
                continue;
            }
            match &trees[i] {
                Tt::Tok(t) => out.push(*t),
                Tt::Delim(d, inner, span) => {
                    let (open, close) = match d {
                        Delim::Paren => (Tok::LParen, Tok::RParen),
                        Delim::Bracket => (Tok::LBracket, Tok::RBracket),
                        Delim::Brace => (Tok::LBrace, Tok::RBrace),
                    };
                    out.push(Token { tok: open, span: *span });
                    go(m, kind, inner, out, None);
                    out.push(Token { tok: close, span: *span });
                }
                Tt::Frag(fk, inner, span) => {
                    if fk.transparent() {
                        go(m, kind, inner, out, None);
                    } else if *fk == kind {
                        go(m, kind, inner, out, None);
                    } else {
                        placeholder(m, *fk, *span, out);
                    }
                }
            }
            i += 1;
        }
    }
    let mut out = Vec::new();
    let mut trees = trees;
    if kind == FragKind::Item {
        while tok_at(trees, 0).map(|t| t.tok) == Some(Tok::Pound) && matches!(trees.get(1), Some(Tt::Delim(Delim::Bracket, _, _))) {
            trees = &trees[2..];
        }
    }
    go(m, kind, trees, &mut out, bounds);
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
    // The subset parser cannot yet parse every valid Rust form a
    // fragment can hold (closures, `?`, float patterns, a bare
    // `dyn`). rustc's fragment parser can, so a shape the parser
    // refuses gets one more chance from the token-tree recognizer,
    // which knows the full grammar but builds no AST.
    let ok = ok
        || match kind {
            FragKind::Expr => super::recognize::is_expr(slice, m.interner, true),
            FragKind::Expr2021 => super::recognize::is_expr(slice, m.interner, false),
            FragKind::Ty => super::recognize::is_ty(slice, m.interner),
            FragKind::Pat => super::recognize::is_pat(slice, m.interner, true),
            FragKind::PatParam => super::recognize::is_pat(slice, m.interner, false),
            FragKind::Stmt => super::recognize::is_stmt(slice, m.interner),
            FragKind::Item => super::recognize::is_item(slice, m.interner),
            FragKind::Block => matches!(slice, [one] if super::recognize::is_block(one, m.interner)),
            _ => false,
        };
    m.probe_cache.insert(key, ok);
    ok
}
