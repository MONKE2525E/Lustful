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
//   family), or a parser macro while a user macro may take its name;
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
use crate::diag::{CtxtId, FileId, SourceMap};
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
    /// Some file of the session defines a macro (`macro_rules`): tokens
    /// of one file can then sit in another file's nodes (no `ranges`).
    user_macros: bool,
    /// Some file can make a user macro answer to a parser macro's name
    /// (`shadows_parser_macro`): a `println!` in a body may then be the
    /// user's macro, which the expander owns.
    shadowed: bool,
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
    /// Per map file, where its nodes sit (`span_shift::ranges_by_file`).
    /// Set at the full resolve when no macro or include can put a file's
    /// spans in another file's nodes; with macros or includes, the first
    /// patch probes the Ast (`span_shift::probe_extras`) and sets both
    /// this and `extras`. None walks the whole Ast for each edit.
    ranges: Option<Vec<FileRanges>>,
    /// Per map file, the probed extra nodes an edit in that file must
    /// also visit (`span_shift::ExtraNodes`); None until probed, and
    /// never when the resolve could prove ranges on its own.
    extras: Option<Vec<span_shift::ExtraNodes>>,
    /// Per map file, the fns whose name span is in it (`Front::fn_loc`
    /// indexes): an edit that adds lines renumbers only its own file's.
    fns_by_file: Vec<Vec<u32>>,
    /// True per slot an AST fn of this resolve holds, for the slot
    /// update's dead-slot rule. Slot assignment does not move while a
    /// base lives, so this is built once here, not per patch.
    live_slots: Vec<bool>,
}

/// The crate selection inputs a patch must see unchanged: anything that
/// steers discovery, cfg, crate identity, or what expansions show.
pub(super) fn inputs_fingerprint(parts: &dyn std::fmt::Debug) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    std::hash::Hash::hash(&format!("{parts:?}"), &mut h);
    std::hash::Hasher::finish(&h)
}

/// True when `text` may define a macro named like a parser macro
/// (`macro_rules! println`) or import one under such a name (`as vec`).
/// A text scan: a match in a comment or string only costs the patch for
/// bodies that call parser macros.
fn shadows_parser_macro(text: &str) -> bool {
    let ident_after = |rest: &str| -> String { rest.trim_start().chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect() };
    let word_before = |i: usize| i == 0 || !text.as_bytes()[i - 1].is_ascii_alphanumeric() && text.as_bytes()[i - 1] != b'_';
    let defines = text.match_indices("macro_rules").any(|(i, m)| {
        let rest = text[i + m.len()..].trim_start();
        rest.strip_prefix('!').is_some_and(|r| crate::expand::builtin::is_passthrough(&ident_after(r)))
    });
    let renames = text.match_indices("as").any(|(i, m)| {
        let rest = &text[i + m.len()..];
        word_before(i) && rest.starts_with(char::is_whitespace) && crate::expand::builtin::is_passthrough(&ident_after(rest))
    });
    defines || renames
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
        let shadowed = user_macros && texts.iter().any(|(_, t)| shadows_parser_macro(t));
        let includes = front.chunks.iter().any(|c| c.expand_deps.iter().any(|d| matches!(d, crate::expand::Dep::File { .. })));
        let ranges = (!user_macros && !includes).then(|| span_shift::ranges_by_file(&front.ast, n));
        let mut fns_by_file: Vec<Vec<u32>> = vec![Vec::new(); n];
        for (i, &(item, sub)) in front.fn_loc.iter().enumerate() {
            if item == usize::MAX || item >= front.ast.items.len() {
                continue;
            }
            let file = fn_def_at(&front.ast, item, sub).name_span.file;
            if let Some(v) = fns_by_file.get_mut(file.0 as usize) {
                v.push(i as u32);
            }
        }
        let mut live_slots = vec![false; front.slot_of.len()];
        for &s in front.fn_slot.iter().take(front.ast_fn_count) {
            if let Some(l) = live_slots.get_mut(s as usize) {
                *l = true;
            }
        }
        PatchBase {
            inputs,
            root_unspliced,
            spliced,
            needs,
            stamps,
            user_macros,
            shadowed,
            tables,
            local_names: None,
            std_ranges: std_out.0.to_vec(),
            std_routes: std_out.1.to_vec(),
            std_methods: std_out.2,
            fn_lines,
            body_hashes,
            arena_base: front.ast.exprs.len(),
            ranges,
            extras: None,
            fns_by_file,
            live_slots,
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
    /// Files read from disk to prove unchanged (a stat the patch could
    /// not trust), beyond the changed ones.
    pub reads: usize,
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
    /// Neither body holds a closure or a token collect's whole-Ast scans
    /// look for (`plain_body`).
    plain: bool,
    /// The old body's expression range (`FnDef::exprs`).
    old_exprs: (u32, u32),
}

/// A collected program kept for later requests (W-INCR3), one per mode
/// (`Front::kept`: check, build). It shares the front's merged Ast and
/// resolver tables (`Program::ast`, `Program::resolved`) until a body
/// patch detaches it; from then on every patch records its edits, until
/// `reuse_kept` moves its spans and takes it in place of a fresh collect
/// (when every edit allows it). Any other change to the Ast drops it.
pub(crate) struct KeptProgram {
    pub(crate) program: crate::check::collect::Program,
    /// The edits patches made since the program was detached, in order;
    /// None while the program shares the front's Ast.
    edits: Option<Vec<KeptEdit>>,
    bases: Vec<KeptBase>,
}

/// Keeps `program` for later requests, in its mode's slot.
pub(crate) fn keep(front: &mut Front, program: crate::check::collect::Program) {
    let slot = usize::from(program.gx.walk_instances);
    front.kept[slot] = Some(KeptProgram { program, edits: None, bases: Vec::new() });
}

/// One patch edit under a detached kept program.
#[derive(Clone)]
struct KeptEdit {
    edit: Edit,
    /// The fresh expansion contexts the Ast's span walk chose.
    ctxts: FxMap<u32, CtxtId>,
    /// The edited fn, in `Front::fn_loc` order (its `LocalDefId`).
    fn_index: usize,
    plain: bool,
    /// The old body's expression range (a template's picks key on it).
    old_exprs: (u32, u32),
}

/// One edited fn's discovery output as the kept program was built with
/// it, taken at the fn's first edit since (`GenReuse::out_copy`); None
/// when the cache held none.
type KeptBase = (usize, Option<crate::driver::gen_reuse::OutCopy>);

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
    let (edits, reads) = find_edits(front, inputs, root, request_start)?;
    let edits_in: Vec<KeptEdit> =
        edits.iter().map(|e| KeptEdit { edit: e.edit, ctxts: FxMap::default(), fn_index: e.fn_index, plain: e.plain, old_exprs: e.old_exprs }).collect();
    // Everything above only read; from here the front state changes, and
    // a failure must drop the base so no later request patches on it.
    // A kept program that shares this Ast lets go of it and of the
    // resolver tables, so the patch edits both in place; it records the
    // edits (see `KeptProgram`). With no edit it stays as it is.
    let mut kept: [Option<KeptProgram>; 2] = if edits.is_empty() { Default::default() } else { std::mem::take(&mut front.kept) };
    for slot in &mut kept {
        *slot = slot.take().filter(|k| k.edits.is_some() || Arc::ptr_eq(&k.program.ast, &front.ast));
        if let Some(k) = slot {
            k.program.ast = Arc::default();
            k.program.resolved = None;
            let edits = k.edits.get_or_insert_with(Vec::new);
            for e in &edits_in {
                if !edits.iter().any(|x| x.fn_index == e.fn_index) && !k.bases.iter().any(|b| b.0 == e.fn_index) {
                    let def = k.program.def_id(crate::def::LocalDefId(e.fn_index as u32));
                    k.bases.push((e.fn_index, caches.gen_reuse.out_copy(def)));
                }
            }
        }
    }
    let mut ctxts: Vec<FxMap<u32, CtxtId>> = Vec::new();
    let out = apply(front, caches, edits, reads, &mut ctxts);
    if out.is_err() {
        front.patch = None;
    } else {
        for (slot, k) in kept.into_iter().enumerate() {
            if let Some(mut k) = k {
                let new = edits_in.iter().zip(&ctxts).map(|(e, c)| KeptEdit { ctxts: c.clone(), ..e.clone() });
                k.edits.get_or_insert_with(Vec::new).extend(new);
                front.kept[slot] = Some(k);
            }
        }
    }
    out
}

/// The changed files and the body each edit sits in, with the number of
/// unchanged files read from disk because their stat was not trusted,
/// or why some edit is not a provable body edit. Reads only.
fn find_edits(front: &mut Front, inputs: u64, root: &str, request_start: SystemTime) -> Result<(Vec<BodyEdit>, usize), &'static str> {
    let base = front.patch.as_ref().ok_or("no base")?;
    if base.inputs != inputs {
        return Err("inputs");
    }
    // The tables are this base's own, or shared with the kept program only.
    let kept_tables = front.kept.iter().flatten().filter(|k| k.program.resolved.as_ref().is_some_and(|t| Arc::ptr_eq(t, &base.tables))).count();
    if front.env_hash.is_none() || front.chunks.len() != 1 || Arc::strong_count(&base.tables) != 1 + kept_tables {
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
    let mut reads = 0usize;
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
            reads += 1;
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
    // they stand when the union over files does. The new union folds
    // the edits over the base needs in place, no copy of the table.
    let base = front.patch.as_ref().ok_or("no base")?;
    let fold = |(a, p): (StdNeeds, bool), (n, q): (StdNeeds, bool)| {
        (StdNeeds { fns: a.fns || n.fns, methods: a.methods || n.methods, modules: a.modules | n.modules }, p || q)
    };
    let old_union = base.needs.iter().copied().fold((StdNeeds::default(), false), fold);
    let new_union = base
        .needs
        .iter()
        .enumerate()
        .map(|(k, &n)| edits.iter().find(|e| e.file.0 as usize == k).map_or(n, |e| e.needs))
        .fold((StdNeeds::default(), false), fold);
    if new_union != old_union {
        return Err("std needs");
    }
    let base = front.patch.as_mut().ok_or("no base")?;
    for (k, st) in fresh_stamps {
        base.stamps[k] = st;
    }
    Ok((edits, reads))
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
    if (old_calls || new_calls) && base.shadowed {
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
    let old_closures = ast.exprs[def.exprs.0 as usize..def.exprs.1 as usize].iter().any(|e| matches!(e, crate::ast::Expr::Closure { .. }));
    let new_closures = body_ast.exprs.iter().any(|e| matches!(e, crate::ast::Expr::Closure { .. }));
    let plain = !old_closures && !new_closures && plain_body(&old_body, &front.interner) && plain_body(&new_body, &front.interner);
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
        plain,
        old_exprs: def.exprs,
    })
}

/// True when a lexed body has no token that collect's whole-Ast scans
/// look for: `dyn` (a `dyn` type turns on the generic machinery) and
/// the names `ast_mentions` and `ast_uses_bound` scan for. Closure
/// expressions are checked on the nodes (`find_body_edit`).
fn plain_body(lexed: &lexer::Lexed, interner: &crate::intern::Interner) -> bool {
    const SCANNED: &[&str] = &["Cow", "Bound", "Included", "Excluded", "Unbounded", "RangeBounds", "start_bound", "end_bound"];
    lexed.tokens.iter().all(|t| match t.tok {
        Tok::Dyn => false,
        Tok::Ident(s) => !SCANNED.contains(&interner.get(s)),
        _ => true,
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
/// `ctxts` gets each edit's fresh expansion contexts, in edit order.
fn apply(front: &mut Front, caches: &mut Caches, mut edits: Vec<BodyEdit>, reads: usize, ctxts: &mut Vec<FxMap<u32, CtxtId>>) -> Result<Patched, &'static str> {
    let mut base = front.patch.take().ok_or("no base")?;
    let (mut spans, files) = (0usize, edits.len());
    let nodes_before = super::compile::ast_nodes(&front.ast);
    // A crate with user macros or includes got no file ranges at the
    // resolve, so its span walks would visit the whole Ast per edit.
    // Probe once, on the first patch: the nodes that can hold another
    // file's spans (or a context) are few, and the rest walk by file.
    if base.ranges.is_none() && !edits.is_empty() {
        let n = front.map.file_count();
        let ast = Arc::make_mut(&mut front.ast);
        base.extras = Some(span_shift::probe_extras(ast, n));
        base.ranges = Some(span_shift::ranges_by_file(ast, n));
    }
    let no_extras = span_shift::ExtraNodes::default();
    for e in &edits {
        // The old body's nodes stay in the arenas, unreachable; blank them,
        // because some passes scan whole arenas (closures, `dyn`, `Cow`).
        let ranges = base.ranges.as_ref().and_then(|r| r.get(e.file.0 as usize));
        let extras = base.extras.as_ref().and_then(|x| x.get(e.file.0 as usize)).unwrap_or(&no_extras);
        span_shift::blank_nodes_extras(Arc::make_mut(&mut front.ast), e.file, e.old_body, ranges, extras);
        // Spans next: the new body is lexed at the new positions.
        let mut memo = FxMap::default();
        spans += span_shift::shift_ast_extras(Arc::make_mut(&mut front.ast), e.edit, ranges, extras, &mut memo);
        ctxts.push(memo);
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
        let _ = Arc::make_mut(&mut front.ast).append_chunk(std::mem::take(&mut e.body_ast), stmt_base);
        let def = fn_def_at_mut(Arc::make_mut(&mut front.ast), e.item, e.sub);
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
        // Under a probed plan, probe just the appended nodes: the first
        // probe never saw them, and the body's path rewrite may have
        // given a node a span from another file.
        if base.extras.is_some() {
            let ast = &front.ast;
            let only = FileRanges {
                exprs: vec![before.0..ast.exprs.len()],
                pats: vec![before.1..ast.pats.len()],
                tys: vec![before.2..ast.tys.len()],
                blocks: vec![before.3..ast.blocks.len()],
                items: Vec::new(),
                stmt_items: vec![before.4..ast.stmt_items.len()],
            };
            let n = front.map.file_count();
            let probed = span_shift::probe_extras_in(Arc::make_mut(&mut front.ast), n, &only);
            for (x, p) in base.extras.as_mut().unwrap().iter_mut().zip(probed) {
                x.exprs.extend(p.exprs);
                x.pats.extend(p.pats);
                x.tys.extend(p.tys);
                x.blocks.extend(p.blocks);
                x.items.extend(p.items);
                x.stmt_items.extend(p.stmt_items);
            }
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
    // moves every fn after it in that file, and no fn in any other.
    for e in &edits {
        let after = (e.edit.b as i64 + e.edit.d) as u32;
        if let Some(fns) = base.fns_by_file.get(e.file.0 as usize) {
            for &j in fns {
                let (item, sub) = front.fn_loc[j as usize];
                let span = fn_def_at(&front.ast, item, sub).name_span;
                if span.lo >= after {
                    base.fn_lines[j as usize] = front.map.line_col(span).0;
                }
            }
        }
    }
    let edited: Vec<usize> = edits.iter().map(|e| e.fn_index).collect();
    let changed = slot_update(front, caches, &base.body_hashes, &edited, &base.live_slots);
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
        reads,
    };
    front.patch = Some(base);
    Ok(out)
}

/// Takes the kept program in place of a fresh collect, with the number
/// of its spans moved, or says why not (the `kept=` of `lust-visits:`).
/// The program holds when it still shares the front's Ast, or when this
/// request's patch detached it and every edit allows it: the edited fn
/// is a plain fn (not a template, so no template check reads its body);
/// without user generics, both bodies hold nothing collect's whole-Ast
/// scans look for (`BodyEdit::plain`); and when collect runs instance
/// discovery over plain bodies, the new body's discovery output equals
/// the one the program was built with (`KeptBase`). Collect would then build the same tables, up to
/// spans, which move here with the edits. `tables` are this request's
/// resolver tables, as collect would attach them.
pub(super) fn reuse_kept(
    front: &mut Front,
    caches: &mut Caches,
    tables: Option<&Arc<ResolvedTables>>,
    walk_instances: bool,
) -> Result<(crate::check::collect::Program, usize, Vec<crate::diag::Diag>), &'static str> {
    use crate::check::generics::FnClass;
    use crate::def::LocalDefId;
    // A build's program holds the generic instances a check's lacks.
    let k = front.kept[usize::from(walk_instances)].take().ok_or(if front.kept.iter().any(Option::is_some) { "mode" } else { "none" })?;
    let bases = k.bases;
    let mut edits = match k.edits {
        Some(e) => e,
        None if Arc::ptr_eq(&k.program.ast, &front.ast) => Vec::new(),
        None => return Err("ast"),
    };
    let mut p = k.program;
    p.ast = front.ast.clone();
    p.resolved = tables.cloned();
    caches.gen_reuse.begin_kept();
    // Collect's whole-Ast scans only turn the generic flags on; once
    // `user_generics` is on they decide nothing.
    for e in &edits {
        if !e.plain && !p.gx.user_generics {
            return Err("body scan");
        }
        // A template checks again below, in a check only: a build's
        // instances replay its picks.
        let f = LocalDefId(e.fn_index as u32);
        match p.gx.fn_class.get(e.fn_index) {
            Some(FnClass::Plain) => {}
            Some(FnClass::Template)
                if !walk_instances
                    && e.plain
                    && !p.is_lang_method(f)
                    && !p.gx.opaques.contains_key(&crate::check::generics::opaque_def(p.def_id(f))) => {}
            _ => return Err("fn class"),
        }
    }
    let mut spans = 0;
    for e in &mut edits {
        let (edit, ctxts) = (e.edit, &mut e.ctxts);
        spans += crate::check::prog_shift::shift_program(&mut p, &mut |s| edit.span(s, ctxts));
    }
    // An edited template checks again as collect's template check does:
    // its old picks and closure call kinds go, the check records new ones.
    let mut template_errs = Vec::new();
    let mut seen: Vec<usize> = Vec::new();
    for e in &edits {
        if p.gx.fn_class.get(e.fn_index) != Some(&FnClass::Template) || seen.contains(&e.fn_index) {
            continue;
        }
        seen.push(e.fn_index);
        let f = LocalDefId(e.fn_index as u32);
        let ranges: Vec<(u32, u32)> = edits.iter().filter(|x| x.fn_index == e.fn_index).map(|x| x.old_exprs).collect();
        p.gx.trait_picks.retain(|x, _| !ranges.iter().any(|r| x.0 >= r.0 && x.0 < r.1));
        p.gx.template_closures.retain(|k, _| k.0 != f);
        p.gx.template_calls.retain(|k, _| k.0 != f);
        let counts = p.gx.mono_counts;
        template_errs.extend(crate::check::generics::check_template(&mut p, f, &mut caches.gen_reuse));
        p.gx.mono_counts = counts;
    }
    // Discovery checks every plain body when user generics exist; with
    // only the lang enum methods' generics, a build checks the bodies
    // that name one (not tracked here) and a check none.
    if p.gx.has_generics && !edits.is_empty() {
        if !p.gx.user_generics && walk_instances {
            return Err("lang generics");
        }
        if p.gx.user_generics {
            // As collect runs discovery: before the driver sets these.
            let (record_reads, unwind) = (p.record_reads, p.unwind);
            (p.record_reads, p.unwind) = (true, false);
            for (fn_index, base) in &bases {
                if p.gx.fn_class.get(*fn_index) != Some(&FnClass::Plain) {
                    continue;
                }
                let f = LocalDefId(*fn_index as u32);
                let (checked, discarded) = crate::check::check_fn(&p, f);
                if checked.closure_map_pending {
                    return Err("discovery");
                }
                let out = crate::check::generics::discovery_out(&p, &checked, &discarded);
                if !base.as_ref().is_some_and(|b| b.same(&p, &out, walk_instances)) {
                    return Err("discovery");
                }
                if discarded.is_empty() {
                    let (adt_tys, reqs, closures, vts) = &out;
                    caches.gen_reuse.store_discovered(&p, f, &checked.reads, adt_tys, reqs, closures, vts);
                }
                caches.gen_reuse.discovery_checked += 1;
                drop((checked, discarded));
                // Every body type enters the global store, as discovery's
                // replay does (lowering and codegen read it there).
                for t in out.0.iter().chain(out.3.iter().flat_map(|(a, b)| [a, b])) {
                    crate::check::generics::build_owned_ty(&mut p, t);
                }
            }
            (p.record_reads, p.unwind) = (record_reads, unwind);
        }
    }
    Ok((p, spans, template_errs))
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

pub(super) fn fn_def_at_mut(ast: &mut Ast, item: usize, sub: Option<usize>) -> &mut FnDef {
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
///
/// The dead-slot rule (the only part that walks per-fn state) runs for
/// the edited fns only. For any other fn it was settled by the last
/// request's slot update, and nothing since then can flip it: slot
/// assignment and the fn's own `slot_used` change only when that fn is
/// regenerated, instance slots only grow, and the compile tail's work
/// preparation re-evaluates the same rule for builds before it reuses
/// any C. The hash and ok scan stays: two word compares per fn, and
/// the ok flags are written by the tail, so no smaller exact set of
/// failed fns exists here.
fn slot_update(front: &mut Front, caches: &mut Caches, hashes: &[u64], edited: &[usize], live: &[bool]) -> Vec<usize> {
    let n = front.ast_fn_count;
    let mut changed = Vec::new();
    for (i, &hash) in hashes.iter().enumerate().take(n) {
        let slot = front.fn_slot[i] as usize;
        if edited.contains(&i)
            && caches.slot_used[slot]
                .iter()
                .any(|&u| !live.get(u as usize).copied().unwrap_or(false) && !front.inst_slot.get(u as usize).copied().unwrap_or(false))
        {
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
        run(session, root, Cmd::Check)
    }

    fn run(session: &mut Session, root: &Path, cmd: Cmd) -> (i32, String) {
        let req = Request {
            cmd,
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
    /// keeps the base for the fix. A no-op check reuses the last answer.
    /// A signature edit resolves in full.
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
            // A no-op check of the same request reuses that answer.
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "reuse");
            // A signature edit: a full resolve again.
            edit(&m1, "pub fn helper(x: i64) -> i64 {", "pub fn helper(x: i64, _k: u8) -> i64 {");
            edit(&m1, "a.add(helper(i));", "a.add(helper(i, 0));");
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "resolve");
            let _ = std::fs::remove_dir_all(&dir);
        }
        assert_eq!(per_size[0], per_size[1], "patch work (nodes, spans) for 3 and 12 modules");
    }

    /// A crate with a user macro got no per-file span ranges at the
    /// resolve, so each patch used to walk the whole Ast. The first
    /// patch now probes the Ast for the nodes that can hold another
    /// file's spans, and later patches walk one file plus those nodes:
    /// the same edit in a 3-module and a 12-module crate moves the
    /// same number of spans, and the answers match a cold session.
    #[test]
    fn body_edit_with_user_macros_still_walks_one_file() {
        let mut per_size = Vec::new();
        for n in [3usize, 12] {
            let dir = std::env::temp_dir().join(format!("lust-patch-macro-test-{}-{n}", std::process::id()));
            let root = write_crate(&dir, n);
            edit(&root, "mod m0;\n", "#[macro_export]\nmacro_rules! twice { ($e:expr) => { $e * 2 }; }\n\nmod m0;\n");
            edit(&root, "    println!(\"{t}\");\n", "    t += twice!(1);\n    println!(\"{t}\");\n");
            let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
            assert_eq!(check(&mut warm, &root).0, 0);
            let m1 = dir.join("m1.rs");
            // Two edits: the first probes, the second walks by the plan.
            edit(&m1, "        self.v += x;\n", "        let y = x + 1;\n        self.v += y - 1;\n");
            assert_eq!(check(&mut warm, &root).0, 0);
            assert_eq!(field(&warm.front.last_visits, "path"), "patch", "{}", warm.front.last_visits);
            edit(&m1, "        self.v += y - 1;\n", "        self.v += y - 2;\n        self.v += 1;\n");
            let (code, err) = check(&mut warm, &root);
            let v = warm.front.last_visits.clone();
            assert_eq!(field(&v, "path"), "patch", "{v}");
            assert_eq!((field(&v, "files"), field(&v, "checked")), ("1", "1"), "{v}");
            per_size.push((field(&v, "nodes").to_string(), field(&v, "spans").to_string()));
            let mut cold = Session::new(dir.join("obj-cold"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree");
            assert_eq!(code, 0);
            // An error after the edit reports at the moved position.
            edit(&m1, "    a.get()\n", "    a.get() + true\n");
            let (code, err) = check(&mut warm, &root);
            let mut cold = Session::new(dir.join("obj-cold2"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree on the error");
            assert_ne!(code, 0);
            let _ = std::fs::remove_dir_all(&dir);
        }
        assert_eq!(per_size[0], per_size[1], "patch work (nodes, spans) with macros for 3 and 12 modules: {per_size:?}");
    }

    /// A module with most kinds of span a collected program keeps: Adts
    /// with generic params, a trait and impls, a `dyn` signature, a
    /// nested fn (an item block), and a generic fn, all after `helper`.
    const RICH: &str = "pub fn helper(x: i64) -> i64 {
    x * 2
}

pub trait Shape {
    fn area(&self) -> i64;
}

pub struct Sq<T> {
    pub s: T,
}

impl Shape for Sq<i64> {
    fn area(&self) -> i64 {
        self.s * self.s
    }
}

pub fn total(s: &dyn Shape) -> i64 {
    s.area()
}

pub fn nested() -> i64 {
    fn inner(x: i64) -> i64 {
        x + 1
    }
    inner(2)
}

pub fn pick<T: Copy>(x: T) -> T {
    x
}

pub fn run() -> i64 {
    let q = Sq { s: 3 };
    total(&q) + nested() + pick(helper(1))
}
";

    /// The stdout of a binary just built. Another test thread's fork can
    /// hold it open for writing for a moment (ETXTBSY): retry then.
    fn run_bin(bin: &Path) -> Vec<u8> {
        for _ in 0..100 {
            match std::process::Command::new(bin).output() {
                Ok(o) => return o.stdout,
                Err(e) if e.kind() == std::io::ErrorKind::ExecutableFileBusy => std::thread::sleep(std::time::Duration::from_millis(20)),
                Err(e) => panic!("{}: {e}", bin.display()),
            }
        }
        panic!("{}: still busy", bin.display())
    }

    /// Every span of a program, sorted (contexts aside: their ids are
    /// per process, not per session).
    fn program_spans(p: &mut crate::check::collect::Program) -> Vec<(u32, u32, u32)> {
        let mut out = Vec::new();
        crate::check::prog_shift::shift_program(p, &mut |s| {
            out.push((s.file.0, s.lo, s.hi));
            s
        });
        out.sort_unstable();
        out
    }

    /// A body edit reuses the kept program instead of collecting, its
    /// collect work does not grow with the crate (3 and 12 modules), and
    /// the kept program's spans after the edit are those of a fresh
    /// collect of the edited text.
    #[test]
    fn kept_program_matches_a_fresh_collect() {
        let mut per_size = Vec::new();
        for n in [3usize, 12] {
            let dir = std::env::temp_dir().join(format!("lust-kept-test-{}-{n}", std::process::id()));
            let root = write_crate(&dir, n);
            for k in 0..n {
                std::fs::write(dir.join(format!("m{k}.rs")), RICH).unwrap();
            }
            let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
            assert_eq!(check(&mut warm, &root), (0, String::new()));
            let m1 = dir.join("m1.rs");
            // Adds a line in the first fn of the file: every later item moves.
            edit(&m1, "    x * 2\n", "    let y = x + 1;\n    (y - 1) * 2\n");
            assert_eq!(check(&mut warm, &root), (0, String::new()));
            let v = warm.front.last_visits.clone();
            assert_eq!((field(&v, "path"), field(&v, "kept"), field(&v, "collect")), ("patch", "reuse", "0"), "{v}");
            per_size.push((field(&v, "discovery").to_string(), field(&v, "checked").to_string()));
            let mut fresh = Session::new(dir.join("obj-fresh"), true, SessionKey::synthetic(&root, false));
            assert_eq!(check(&mut fresh, &root), (0, String::new()));
            let (a, b) = (warm.front.kept[0].as_mut().unwrap(), fresh.front.kept[0].as_mut().unwrap());
            assert_eq!(program_spans(&mut a.program), program_spans(&mut b.program), "kept and fresh program spans");
            // A build keeps its own program: after a check-only edit and a
            // check, the next build reuses it too and runs as cold does.
            let (code, err) = run(&mut warm, &root, Cmd::Build);
            assert_eq!(code, 0, "{err}");
            edit(&m1, "    (y - 1) * 2\n", "    (y - 2) * 2\n");
            assert_eq!(check(&mut warm, &root), (0, String::new()));
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
            assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
            let bin = root.with_extension("bin");
            let out = run_bin(&bin);
            let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
            assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
            assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
            // A generic fn's body: the kept program checks it again as a
            // template; an error there is collect's error, as cold.
            edit(&m1, "pub fn pick<T: Copy>(x: T) -> T {\n    x\n", "pub fn pick<T: Copy>(x: T) -> T {\n    let y = x;\n    y\n");
            assert_eq!(check(&mut warm, &root), (0, String::new()));
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
            edit(&m1, "    let y = x;\n    y\n", "    let y = x;\n    y + 1\n");
            let (code, err) = check(&mut warm, &root);
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
            let mut cold = Session::new(dir.join("obj-cold-t"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree on the template error");
            assert_ne!(code, 0);
            edit(&m1, "    let y = x;\n    y + 1\n", "    let y = x;\n    y\n");
            assert_eq!(check(&mut warm, &root), (0, String::new()));
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "the fix reuses it too: {}", warm.front.last_visits);
            // An error in the edited body: the warm answer is the cold one.
            edit(&m1, "    (y - 2) * 2\n", "    (y - 1) * true\n");
            let (code, err) = check(&mut warm, &root);
            assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
            let mut cold = Session::new(dir.join("obj-cold"), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree on the error");
            assert_ne!(code, 0);
            let _ = std::fs::remove_dir_all(&dir);
        }
        assert_eq!(per_size[0], per_size[1], "kept program work (discovery, checked) for 3 and 12 modules");
    }
}
