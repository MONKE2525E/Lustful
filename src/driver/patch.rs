// The body patch (docs/ARCH.md 8.3, step 4; W-INCR2): a warm request on
// the resolver path whose edits all sit inside fn bodies edits the
// merged Ast in place instead of resolving the crate again.
//
// A full resolve costs work in proportion to the crate: the std splice
// and its second resolve, discovery, expansion, the import fixpoint,
// rewrite, flatten, and the Ast scan. A body edit changes none of what
// those phases decide outside the edited body: module tree, bindings,
// flat names, item scans, and std needs all stand. So the patch
// re-reads the files the last resolve read, finds the one fn body each
// changed file's edit sits in, lexes and parses that body alone, moves
// the spans after the edit (driver/span_shift.rs), rewrites the body's
// paths against the last resolve's frozen tables, and rescans that one
// item. The shared tail then runs as for any bodies-mode request.
//
// Rule zero: the patched state must be the state a full resolve of the
// new text builds, up to arena order. Every condition below that cannot
// be proven from the edit alone gives up (`None`), and the caller
// resolves in full, which is always correct. It gives up when:
// - the crate selection inputs, the client view, or an expansion's
//   outside inputs changed, or an expansion read a position;
// - the root file changed and carries the std splice;
// - an edit is not strictly inside one top-level fn or method body;
// - the old or new body holds an item keyword, an attribute, a `$`, a
//   macro the expander owns (anything but the parser's own `println!`
//   family), or a parser macro while the crate defines macros;
// - the fn is a `const fn` or returns `impl Trait` (its body is part of
//   its item, and `const` values bake it in), or has parameter patterns
//   or expressions in its parameter types (see `find_body_edit`);
// - the file's std needs or std platform mention moved;
// - the new body does not lex, parse, or rewrite cleanly, or its item
//   scan moved (errors then come from the full path, in cold order);
// - the last full resolve's tables are shared, or patches grew the Ast
//   arenas past twice their resolved size.
use super::compile::{fn_def_at, fn_text_hash};
use super::session::{Caches, Front};
use super::span_shift::{self, Edit, FileRanges};
use crate::ast::{Ast, BlockId, FnDef, ItemKind, TyExpr};
use crate::diag::{FileId, SourceMap};
use crate::intern::{FxMap, Sym};
use crate::lexer::{self, Tok};
use crate::resolve::imports::ResolvedTables;
use crate::ty::lang::{ShippedCrate, StdFnDef, StdNeeds};
use std::sync::Arc;
use std::time::SystemTime;

/// A file's stat when its text entered the map: modification time and
/// size. Trusted only when the file was already older than the request
/// that read it, so a write in the same clock tick is never missed.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Stamp {
    mtime: SystemTime,
    len: u64,
}

/// What the last full resolve left for the next request's patch. The
/// merged Ast, source map, item scans, and slot state live in `Front`.
pub(crate) struct PatchBase {
    /// Fingerprint of the crate selection inputs (`inputs_fingerprint`).
    inputs: u64,
    /// The root file's text before any std splice.
    root_unspliced: String,
    /// True when the std splice follows the root text in file 0.
    spliced: bool,
    /// Per map file: the std needs and std platform mention of its own
    /// text (the root's before the splice).
    needs: Vec<(StdNeeds, bool)>,
    /// Per map file: the stat that proves its text unchanged, if any.
    stamps: Vec<Option<Stamp>>,
    /// Some file of the session defines a macro (`macro_rules`): a parser
    /// macro name in a body may then be the user's macro.
    user_macros: bool,
    tables: Arc<ResolvedTables>,
    /// `ResolvedTables::local_named_set`, built on the first patch.
    local_names: Option<FxMap<Sym, u8>>,
    std_ranges: Vec<(u32, u32, ShippedCrate)>,
    std_routes: Vec<&'static StdFnDef>,
    std_methods: (u32, u32),
    fn_lines: Vec<u32>,
    body_hashes: Vec<u64>,
    /// Expression arena length after the full resolve.
    arena_base: usize,
    /// Per map file, where its nodes sit (`span_shift::ranges_by_file`),
    /// when no macro or include can put a file's spans in another file's
    /// nodes; None walks the whole Ast for each edit.
    ranges: Option<Vec<FileRanges>>,
}

/// The crate selection inputs a patch must see unchanged: anything that
/// steers discovery, cfg, crate identity, or what expansions show.
pub(super) fn inputs_fingerprint(parts: &dyn std::fmt::Debug) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    std::hash::Hash::hash(&format!("{parts:?}"), &mut h);
    std::hash::Hasher::finish(&h)
}

/// The std needs and platform mention of one file's own text.
fn file_needs(text: &str) -> (StdNeeds, bool) {
    (crate::ty::lang::std_needs(text), crate::resolve::worklist::mentions_std_platform(text))
}

fn stamp_of(path: &str, request_start: SystemTime) -> Option<Stamp> {
    let md = std::fs::metadata(path).ok()?;
    let mtime = md.modified().ok()?;
    // A file modified within two seconds of the request that read it may
    // change again without its stat moving: never trust that stat.
    let old = request_start.duration_since(mtime).is_ok_and(|age| age.as_secs() >= 2);
    old.then_some(Stamp { mtime, len: md.len() })
}

impl PatchBase {
    /// The base a successful full resolve leaves (`resolved_setup`).
    #[allow(clippy::too_many_arguments)]
    pub(super) fn new(
        front: &Front,
        inputs: u64,
        root_unspliced: String,
        spliced: bool,
        tables: Arc<ResolvedTables>,
        std_out: (&[(u32, u32, ShippedCrate)], &[&'static StdFnDef], (u32, u32)),
        fn_lines: Vec<u32>,
        body_hashes: Vec<u64>,
        request_start: SystemTime,
    ) -> PatchBase {
        let map = &front.map;
        let n = map.file_count();
        let texts: Vec<(usize, &str)> =
            (0..n).map(|k| (k, if k == 0 { root_unspliced.as_str() } else { map.text(FileId(k as u32)).unwrap_or("") })).collect();
        let needs = super::compile::par_map(&texts, |&(_, t)| file_needs(t));
        let stamps = (0..n)
            .map(|k| {
                let path = map.path(FileId(k as u32));
                if path.is_empty() { None } else { stamp_of(path, request_start) }
            })
            .collect();
        let user_macros = texts.iter().any(|(_, t)| t.contains("macro_rules"));
        let includes = front.chunks.iter().any(|c| c.expand_deps.iter().any(|d| matches!(d, crate::expand::Dep::File { .. })));
        let ranges = (!user_macros && !includes).then(|| span_shift::ranges_by_file(&front.ast, n));
        PatchBase {
            inputs,
            root_unspliced,
            spliced,
            needs,
            stamps,
            user_macros,
            tables,
            local_names: None,
            std_ranges: std_out.0.to_vec(),
            std_routes: std_out.1.to_vec(),
            std_methods: std_out.2,
            fn_lines,
            body_hashes,
            arena_base: front.ast.exprs.len(),
            ranges,
        }
    }
}

/// A patched request's setup results, in `resolved_setup`'s shape.
pub(super) struct Patched {
    pub map: SourceMap,
    pub changed: Vec<usize>,
    pub fn_count: usize,
    pub fn_lines: Vec<u32>,
    pub body_hashes: Vec<u64>,
    pub tables: Arc<ResolvedTables>,
    pub std_ranges: Vec<(u32, u32, ShippedCrate)>,
    pub std_routes: Vec<&'static StdFnDef>,
    pub std_methods: (u32, u32),
    /// Files whose text changed, Ast nodes the patch built, bodies
    /// re-parsed, and spans moved.
    pub files: usize,
    pub nodes: usize,
    pub bodies: usize,
    pub spans: usize,
}

/// One edit proven to sit inside one fn body (`find_body_edit`).
struct BodyEdit {
    file: FileId,
    text: String,
    edit: Edit,
    /// The fn's index in `Front::fn_loc` order and its location.
    fn_index: usize,
    item: usize,
    sub: Option<usize>,
    /// The old body's byte range in the file.
    old_body: (u32, u32),
    /// The new body, parsed and rewritten into an Ast of its own
    /// (`apply` appends it to the merged Ast): its block and its
    /// expression and pattern ranges there.
    body_ast: Ast,
    body: BlockId,
    exprs: (u32, u32),
    pats: (u32, u32),
    needs: (StdNeeds, bool),
}

/// Tries the body patch for this request (see the module docs). `root`
/// is the root file's text before any std splice. On `Err` the caller
/// resolves in full; the reason names the first condition that failed
/// (the `why=` of `lust-visits:`). `front.patch` is then cleared if the
/// patch had started to edit the front state.
pub(super) fn try_patch(
    front: &mut Front,
    caches: &mut Caches,
    inputs: u64,
    root: &str,
    request_start: SystemTime,
) -> Result<Patched, &'static str> {
    let edits = find_edits(front, inputs, root, request_start)?;
    // Everything above only read; from here the front state changes, and
    // a failure must drop the base so no later request patches on it.
    let out = apply(front, caches, edits);
    if out.is_err() {
        front.patch = None;
    }
    out
}

/// The changed files and the body each edit sits in, or why some edit
/// is not a provable body edit. Reads only.
fn find_edits(front: &mut Front, inputs: u64, root: &str, request_start: SystemTime) -> Result<Vec<BodyEdit>, &'static str> {
    let base = front.patch.as_ref().ok_or("no base")?;
    if base.inputs != inputs {
        return Err("inputs");
    }
    if front.env_hash.is_none() || front.chunks.len() != 1 || Arc::strong_count(&base.tables) != 1 {
        return Err("state");
    }
    if front.ast.exprs.len() > base.arena_base.saturating_mul(2) + 65_536 {
        return Err("arena");
    }
    let deps = &front.chunks[0].expand_deps;
    if deps.iter().any(|d| matches!(d, crate::expand::Dep::Position)) || crate::expand::deps_stale(deps, &front.client) {
        return Err("expansion inputs");
    }
    let mut changed: Vec<(FileId, String)> = Vec::new();
    if root != base.root_unspliced {
        if base.spliced {
            return Err("spliced root");
        }
        changed.push((FileId(0), root.to_string()));
    }
    let mut fresh_stamps: Vec<(usize, Option<Stamp>)> = Vec::new();
    for k in 1..front.map.file_count() {
        let file = FileId(k as u32);
        let path = front.map.path(file);
        if path.is_empty() {
            continue;
        }
        let md = std::fs::metadata(path).map_err(|_| "file gone")?;
        if let (Some(st), Ok(mtime)) = (base.stamps.get(k).copied().flatten(), md.modified())
            && st == (Stamp { mtime, len: md.len() })
        {
            continue;
        }
        let text = std::fs::read_to_string(path).map_err(|_| "file gone")?;
        if front.map.text(file) == Some(text.as_str()) {
            fresh_stamps.push((k, stamp_of(path, request_start)));
            continue;
        }
        changed.push((file, text));
    }
    if !changed.is_empty() {
        let base = front.patch.as_mut().ok_or("no base")?;
        if base.local_names.is_none() {
            base.local_names = Some(base.tables.local_named_set());
        }
    }
    let mut edits = Vec::with_capacity(changed.len());
    for (file, text) in changed {
        edits.push(find_body_edit(front, file, text)?);
    }
    // The std splice and the platform crate follow every file's needs;
    // they stand when the union over files does.
    let base = front.patch.as_ref().ok_or("no base")?;
    let union = |needs: &[(StdNeeds, bool)]| {
        needs.iter().fold((StdNeeds::default(), false), |(a, p), (n, q)| {
            (StdNeeds { fns: a.fns || n.fns, methods: a.methods || n.methods, modules: a.modules || n.modules }, p || *q)
        })
    };
    let mut needs = base.needs.clone();
    for e in &edits {
        needs[e.file.0 as usize] = e.needs;
    }
    if union(&needs) != union(&base.needs) {
        return Err("std needs");
    }
    let base = front.patch.as_mut().ok_or("no base")?;
    for (k, st) in fresh_stamps {
        base.stamps[k] = st;
    }
    Ok(edits)
}

/// Proves that the edit from the map's text of `file` to `text` sits
/// strictly inside one top-level fn or method body, and lexes that body.
fn find_body_edit(front: &Front, file: FileId, text: String) -> Result<BodyEdit, &'static str> {
    let base = front.patch.as_ref().ok_or("no base")?;
    let old = front.map.text(file).ok_or("no text")?;
    let (p, s) = super::compile::common_ends(old.as_bytes(), text.as_bytes());
    let (a, b) = (p, old.len() - s);
    let d = text.len() as i64 - old.len() as i64;
    let ast = &front.ast;
    let (fn_index, &(item, sub)) = front
        .fn_loc
        .iter()
        .enumerate()
        .find(|&(_, &(item, sub))| {
            item != usize::MAX && {
                let def = fn_def_at(ast, item, sub);
                def.body.is_some_and(|bl| {
                    let sp = ast.blocks[bl.0 as usize].span;
                    sp.file == file && (sp.lo as usize) < a && b < sp.hi as usize
                })
            }
        })
        .ok_or("not in a fn body")?;
    let def = fn_def_at(ast, item, sub);
    if def.qual.is_const || def.ret.is_some_and(|t| matches!(ast.ty(t), TyExpr::ImplTrait { .. })) {
        return Err("const fn or impl Trait");
    }
    if !matches!(ast.items[item].kind, ItemKind::Fn(_) | ItemKind::Impl(_)) {
        return Err("not in a fn body");
    }
    let span = ast.blocks[def.body.ok_or("not in a fn body")?.0 as usize].span;
    // A fn's expression and pattern ranges (`FnDef::exprs`, closure
    // numbering reads them) start at its first parameter: the patch
    // sets them to the new body's ranges, which is the cold shape only
    // when no node sits between the parameters and the body.
    let starts_in_body = |(first, end): (u32, u32), spans: &[crate::diag::Span]| {
        first == end || spans.get(first as usize).is_some_and(|s| s.file == file && span.lo <= s.lo && s.hi <= span.hi)
    };
    if def.params.iter().any(|p| p.pat.is_some())
        || !starts_in_body(def.exprs, &ast.expr_spans)
        || !starts_in_body(def.pats, &ast.pat_spans)
    {
        return Err("signature nodes");
    }
    let (lo, hi) = (span.lo as usize, span.hi as usize);
    let new_hi = (hi as i64 + d) as usize;
    let lex = |t: Option<&str>| t.and_then(|t| lexer::lex(t, file, lo as u32, &front.interner).ok()).ok_or("body lex");
    let (old_body, new_body) = (lex(old.get(lo..hi))?, lex(text.get(lo..new_hi))?);
    let old_calls = body_tokens_ok(&old_body, lo, hi, &front.interner).ok_or("body tokens")?;
    let new_calls = body_tokens_ok(&new_body, lo, new_hi, &front.interner).ok_or("body tokens")?;
    if (old_calls || new_calls) && base.user_macros {
        return Err("macro in body");
    }
    // Parse and rewrite the new body on its own: an error there (a
    // half-typed edit) gives up before any state changes, so the base
    // stands for the next request.
    let toks = &new_body.tokens[..new_body.tokens.len() - 1];
    let mut body_ast = Ast::default();
    let (body, exprs, pats) =
        crate::parser::parse_body(toks, &new_body.strings, &mut body_ast, &front.interner, &front.known).map_err(|_| "body parse")?;
    let mut scratch = def.clone();
    scratch.body = Some(body);
    let outer = match &ast.items[item].kind {
        ItemKind::Impl(imp) => Some(&imp.generics),
        _ => None,
    };
    let module = *base.tables.fn_module.get(fn_index).ok_or("state")?;
    let diags = crate::resolve::worklist::rewrite_fn_body(
        &base.tables,
        &front.interner,
        base.local_names.as_ref().ok_or("state")?,
        base.tables.std_splice_lo,
        &mut body_ast,
        &scratch,
        outer,
        module,
    );
    if !diags.is_empty() {
        return Err("body rewrite");
    }
    let needs = file_needs(&text);
    Ok(BodyEdit {
        file,
        text,
        edit: Edit { file, a: a as u32, b: b as u32, d },
        fn_index,
        item,
        sub,
        old_body: (span.lo, span.hi),
        body_ast,
        body,
        exprs,
        pats,
        needs,
    })
}

/// Checks one lexed body (`{` at `lo` through `}` ending at `hi`, then
/// `Eof`): one balanced brace group, no item keyword, attribute, `$`,
/// or macro the expander owns. Returns whether it calls a parser macro
/// (`println!` and kin), or None when the body fails a check.
fn body_tokens_ok(lexed: &lexer::Lexed, lo: usize, hi: usize, interner: &crate::intern::Interner) -> Option<bool> {
    let toks = &lexed.tokens;
    let n = toks.len().checked_sub(1)?;
    if n < 2 || toks[n].tok != Tok::Eof || toks[0].tok != Tok::LBrace || toks[0].span.lo as usize != lo {
        return None;
    }
    if toks[n - 1].tok != Tok::RBrace || toks[n - 1].span.hi as usize != hi {
        return None;
    }
    if crate::expand::needs_expansion(&toks[..n], interner) {
        return None;
    }
    let (macro_rules, union) = (interner.intern("macro_rules"), interner.intern("union"));
    let mut depth = 0usize;
    let mut calls = false;
    for (i, t) in toks[..n].iter().enumerate() {
        match t.tok {
            Tok::LBrace | Tok::LParen | Tok::LBracket => depth += 1,
            Tok::RBrace | Tok::RParen | Tok::RBracket => {
                depth = depth.checked_sub(1)?;
                if depth == 0 && i != n - 1 {
                    return None;
                }
            }
            Tok::Fn
            | Tok::Struct
            | Tok::Enum
            | Tok::Impl
            | Tok::Trait
            | Tok::Mod
            | Tok::Use
            | Tok::Extern
            | Tok::Static
            | Tok::Const
            | Tok::Type
            | Tok::Pound
            | Tok::Dollar
            | Tok::DocStr(_) => return None,
            Tok::Ident(s) if s == macro_rules || s == union => return None,
            Tok::Bang => calls |= i > 0 && matches!(toks[i - 1].tok, Tok::Ident(_)),
            _ => {}
        }
    }
    (depth == 0).then_some(calls)
}

/// Applies the proven edits to the front state and runs the slot update.
fn apply(front: &mut Front, caches: &mut Caches, mut edits: Vec<BodyEdit>) -> Result<Patched, &'static str> {
    let mut base = front.patch.take().ok_or("no base")?;
    let (mut spans, files) = (0usize, edits.len());
    let nodes_before = super::compile::ast_nodes(&front.ast);
    for e in &edits {
        // The old body's nodes stay in the arenas, unreachable; blank them,
        // because some passes scan whole arenas (closures, `dyn`, `Cow`).
        let ranges = base.ranges.as_ref().and_then(|r| r.get(e.file.0 as usize));
        span_shift::blank_nodes(&mut front.ast, e.file, e.old_body, ranges);
        // Spans next: the new body is lexed at the new positions.
        spans += span_shift::shift_ast(&mut front.ast, e.edit, base.ranges.as_ref().and_then(|r| r.get(e.file.0 as usize)));
        let tables = Arc::get_mut(&mut base.tables).ok_or("state")?;
        shift_table_spans(tables, e.edit);
        let lines = front.map.lines(e.file).splice(&e.text, e.edit.a as usize, e.edit.b as usize, (e.edit.b as i64 + e.edit.d) as usize);
        front.map.replace_text(e.file, e.text.clone(), lines);
        if e.file == FileId(0) {
            front.src.clone_from(&e.text);
            front.chunks[0].text.clone_from(&e.text);
            base.root_unspliced.clone_from(&e.text);
        }
        base.needs[e.file.0 as usize] = e.needs;
        base.stamps[e.file.0 as usize] = None;
    }
    for e in edits.iter_mut() {
        let ast = &front.ast;
        let before = (ast.exprs.len(), ast.pats.len(), ast.tys.len(), ast.blocks.len(), ast.stmt_items.len());
        let stmt_base = before.4 as u32;
        let _ = front.ast.append_chunk(std::mem::take(&mut e.body_ast), stmt_base);
        let def = fn_def_at_mut(&mut front.ast, e.item, e.sub);
        def.body = Some(BlockId(e.body.0 + before.3 as u32));
        def.exprs = (e.exprs.0 + before.0 as u32, e.exprs.1 + before.0 as u32);
        def.pats = (e.pats.0 + before.1 as u32, e.pats.1 + before.1 as u32);
        // The new body's nodes join the file's ranges for later edits.
        if let Some(r) = base.ranges.as_mut().and_then(|r| r.get_mut(e.file.0 as usize)) {
            let ast = &front.ast;
            r.exprs.push(before.0..ast.exprs.len());
            r.pats.push(before.1..ast.pats.len());
            r.tys.push(before.2..ast.tys.len());
            r.blocks.push(before.3..ast.blocks.len());
            r.stmt_items.push(before.4..ast.stmt_items.len());
        }
        let (scan, bodies, inner) = super::ast_hash::scan_item(&front.ast, &front.ast.items[e.item]);
        if front.items.get(e.item) != Some(&scan) || !inner.is_empty() {
            return Err("item scan");
        }
        let (hash, idents) = bodies.into_iter().nth(e.sub.unwrap_or(0)).ok_or("item scan")?;
        let def = fn_def_at(&front.ast, e.item, e.sub);
        let line = front.map.line_col(def.name_span).0;
        let h = fn_text_hash(&front.ast, &front.map, def, line, hash);
        base.body_hashes[e.fn_index] = h;
        let chunk = &mut front.chunks[0];
        chunk.scan.fns.get_mut(e.fn_index).ok_or("state")?.body_hash = h;
        *chunk.scan.body_idents.get_mut(e.fn_index).ok_or("state")? = idents;
    }
    // Fn lines in the edited files: an edit that adds or drops lines
    // moves every fn after it.
    for (j, &(item, sub)) in front.fn_loc.iter().enumerate() {
        let span = fn_def_at(&front.ast, item, sub).name_span;
        if edits.iter().any(|e| e.file == span.file && span.lo >= (e.edit.b as i64 + e.edit.d) as u32) {
            base.fn_lines[j] = front.map.line_col(span).0;
        }
    }
    let changed = slot_update(front, caches, &base.body_hashes);
    let edits_len = edits.len();
    let out = Patched {
        map: front.map.clone(),
        changed,
        fn_count: front.ast_fn_count,
        fn_lines: base.fn_lines.clone(),
        body_hashes: base.body_hashes.clone(),
        tables: base.tables.clone(),
        std_ranges: base.std_ranges.clone(),
        std_routes: base.std_routes.clone(),
        std_methods: base.std_methods,
        files,
        nodes: super::compile::ast_nodes(&front.ast) - nodes_before,
        bodies: edits_len,
        spans,
    };
    front.patch = Some(base);
    Ok(out)
}

/// Moves the span keys and module spans of the resolver tables for one
/// edit (`const_init_module` keys are item spans collect looks up).
fn shift_table_spans(tables: &mut ResolvedTables, edit: Edit) {
    if tables.const_init_module.keys().any(|s| edit.plain(*s) != *s) {
        tables.const_init_module = std::mem::take(&mut tables.const_init_module).into_iter().map(|(s, m)| (edit.plain(s), m)).collect();
    }
    for m in &mut tables.modules {
        m.span = edit.plain(m.span);
    }
}

fn fn_def_at_mut(ast: &mut Ast, item: usize, sub: Option<usize>) -> &mut FnDef {
    match (&mut ast.items[item].kind, sub) {
        (ItemKind::Fn(d), None) => d,
        (ItemKind::Impl(imp), Some(k)) => &mut imp.fns[k],
        _ => unreachable!("fn_loc out of date"),
    }
}

/// The bodies-mode slot update for a patched request: the item list,
/// fn locations, slots, and heads stand, so only body hashes move. Same
/// rules as `compile::slot_update` in bodies mode: a fn rechecks when
/// its body hash moved, its last check failed, or its C names a dead
/// slot. Returns the fns to check.
fn slot_update(front: &mut Front, caches: &mut Caches, hashes: &[u64]) -> Vec<usize> {
    let n = front.ast_fn_count;
    let mut live = vec![false; front.slot_of.len()];
    for &s in &front.fn_slot[..n] {
        live[s as usize] = true;
    }
    let mut changed = Vec::new();
    for (i, &hash) in hashes.iter().enumerate().take(n) {
        let slot = front.fn_slot[i] as usize;
        if caches.slot_used[slot].iter().any(|&u| live.get(u as usize) == Some(&false) && !front.inst_slot[u as usize]) {
            caches.ok[slot] = false;
        }
        if front.slot_hash[slot] != hash || !caches.ok[slot] {
            caches.ok[slot] = false;
            caches.has_out[slot] = false;
            caches.slot_reads[slot] = None;
            front.slot_hash[slot] = hash;
            changed.push(i);
        }
    }
    changed
}

#[cfg(test)]
mod tests {
    use crate::driver::{Cmd, Request, Session, SessionKey, compile};
    use std::path::{Path, PathBuf};

    const MODULE: &str = "pub struct Acc {
    pub v: i64,
}

impl Acc {
    pub fn add(&mut self, x: i64) {
        self.v += x;
    }
    pub fn get(&self) -> i64 {
        self.v
    }
}

pub fn helper(x: i64) -> i64 {
    x * 2
}

pub fn run() -> i64 {
    let mut a = Acc { v: 0 };
    for i in 0..10 {
        a.add(helper(i));
    }
    a.get()
}
";

    /// Writes a crate root with `n` module files of `MODULE`.
    fn write_crate(dir: &Path, n: usize) -> PathBuf {
        let _ = std::fs::remove_dir_all(dir);
        std::fs::create_dir_all(dir).unwrap();
        let mut root = String::new();
        for k in 0..n {
            std::fs::write(dir.join(format!("m{k}.rs")), MODULE).unwrap();
            root.push_str(&format!("mod m{k};\n"));
        }
        root.push_str("\nfn main() {\n    let mut t = 0;\n");
        for k in 0..n {
            root.push_str(&format!("    t += m{k}::run();\n"));
        }
        root.push_str("    println!(\"{t}\");\n}\n");
        let path = dir.join("main.rs");
        std::fs::write(&path, root).unwrap();
        path
    }

    fn check(session: &mut Session, root: &Path) -> (i32, String) {
        let req = Request {
            cmd: Cmd::Check,
            session: SessionKey::synthetic(root, false),
            file: root.to_path_buf(),
            out: root.with_extension("bin"),
            json: false,
            timings: false,
            debug: false,
            emit_c: None,
            max_errors: 0,
            run_args: None,
            harness: false,
            client: Default::default(),
        };
        let resp = compile(&req, session);
        (resp.code, resp.stderr)
    }

    /// One field of a `lust-visits:` line.
    fn field<'a>(line: &'a str, name: &str) -> &'a str {
        line.split_whitespace().find_map(|kv| kv.strip_prefix(name).and_then(|v| v.strip_prefix('='))).unwrap_or("")
    }

    fn edit(path: &Path, old: &str, new: &str) {
        let text = std::fs::read_to_string(path).unwrap();
        assert!(text.contains(old), "{old}");
        std::fs::write(path, text.replacen(old, new, 1)).unwrap();
    }

    /// A body edit takes the body patch, and what its front end walks
    /// does not grow with the crate: the same edit in a 3-module and a
    /// 12-module crate re-reads one file, builds and moves the same
    /// number of nodes and spans, rescans one item, and checks one body.
    /// The answers match a cold session, and a syntax error in a body
    /// keeps the base for the fix. A signature edit resolves in full.
    /// (Collect still walks the whole crate: `collect` grows.)
    #[test]
    fn body_edit_work_does_not_grow_with_the_crate() {
        let mut per_size = Vec::new();
        for n in [3usize, 12] {
            let dir = std::env::temp_dir().join(format!("lust-patch-test-{}-{n}", std::process::id()));
            let root = write_crate(&dir, n);
            let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "resolve");
            let m1 = dir.join("m1.rs");
            // A body edit that adds a line: every later fn of the file moves.
            edit(&m1, "        self.v += x;\n", "        let y = x + 1;\n        self.v += y - 1;\n");
            assert_eq!(check(&mut warm, &root).0, 0);
            let v = warm.front.last_visits.clone();
            assert_eq!(field(&v, "path"), "patch", "{v}");
            assert_eq!((field(&v, "files"), field(&v, "scanned"), field(&v, "checked")), ("1", "1", "1"), "{v}");
            per_size.push((field(&v, "nodes").to_string(), field(&v, "spans").to_string()));
            // A body error: the warm answer is the cold answer.
            edit(&m1, "    a.get()\n", "    a.get() + true\n");
            let (code, err) = check(&mut warm, &root);
            assert_eq!(field(&warm.front.last_visits, "path"), "patch");
            let mut cold = Session::new(dir.join("obj-cold"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree on the error");
            assert_ne!(code, 0);
            // A syntax error resolves in full and fails as cold does; the
            // base stands, so the fix after it is a patch again.
            edit(&m1, "    a.get() + true\n", "    a.get( +\n");
            let (code, err) = check(&mut warm, &root);
            let mut cold = Session::new(dir.join("obj-cold2"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree on the syntax error");
            assert_ne!(code, 0);
            edit(&m1, "    a.get( +\n", "    a.get()\n");
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "patch", "{}", warm.front.last_visits);
            // A signature edit: a full resolve again.
            edit(&m1, "pub fn helper(x: i64) -> i64 {", "pub fn helper(x: i64, _k: u8) -> i64 {");
            edit(&m1, "a.add(helper(i));", "a.add(helper(i, 0));");
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "resolve");
            let _ = std::fs::remove_dir_all(&dir);
        }
        assert_eq!(per_size[0], per_size[1], "patch work (nodes, spans) for 3 and 12 modules");
    }
}
