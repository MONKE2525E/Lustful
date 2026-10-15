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
// - the root file changed and carries a std splice its text no longer
//   ends with (the splice moves with an edit in the root text: its byte
//   ranges in the base, the resolver tables, and the Ast);
// - an edit is not strictly inside one top-level fn or method body, or
//   inside cfg-disabled code the expander dropped (`find_inactive_edit`);
// - the old or new body holds a `$`, an item keyword other than `fn`,
//   `static`, `const`, and `use`, a macro the expander owns, or a parser
//   macro while a user macro may take its name; or its items
//   (`stmt_items`) are not the old ones in the old blocks (`same_items`).
//   Attributes and the pure builtin macros (`PURE_MACROS`) patch when no
//   user or dependency macro can take a builtin's name: the new body
//   passes the cfg name check and expands alone, as the resolver checks
//   and expands its file; the expansion must read nothing outside the
//   body (no `Dep` but the cfg-disabled nodes it drops);
// - the fn returns `impl Trait` (its body is part of its item), or its
//   parameter patterns or signature expressions are not provably moved
//   ahead of the new body (`sig_nodes.rs`); a `const fn` patches, but
//   `const` values bake its body in, so when a const evaluation may run it
//   (`const_reach.rs`) the request then collects and walks reads as a cold
//   resolve of a const fn body edit does (`Patched::const_fn`);
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
    /// The crate's cfg environment and name, for expanding a body alone,
    /// when no user or dependency macro can take a builtin's name (no
    /// dependency crate, and no file `shadows_builtin`).
    expand: Option<(crate::resolve::cfg::CfgEnv, String)>,
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
    /// Per item index, its fns' raw body hashes from the item's last
    /// full rescan in a patch (which also proved no method of the item
    /// holds a body item): a later edit in the same impl rescans only
    /// the edited method and reuses these for the rest.
    item_scans: FxMap<usize, Vec<u64>>,
    /// The cfg-disabled nodes the expander dropped (`Dep::Dropped`), by
    /// file and start, with the spans of this text.
    dropped: Vec<Dropped>,
    /// What const evaluation may reach (`const_reach.rs`), built on the
    /// first const fn body edit and kept up to date by later patches.
    reach: Option<super::const_reach::ConstReach>,
}

/// One cfg-disabled node the last full resolve dropped (`Dep::Dropped`).
#[derive(Clone, Copy)]
struct Dropped {
    file: u32,
    lo: u32,
    hi: u32,
    item: bool,
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
    shadows(text, &|name| crate::expand::builtin::is_passthrough(name))
}

/// `shadows_parser_macro` for every builtin macro (parser and expander
/// owned), and for a macro whose name a macro supplies
/// (`macro_rules! $name`, read as an empty name).
fn shadows_builtin(text: &str) -> bool {
    use crate::expand::builtin::{is_passthrough, is_token_builtin};
    shadows(text, &|name| name.is_empty() || is_passthrough(name) || is_token_builtin(name))
}

/// True when `text` may define a macro whose name `named` takes, or
/// import one under such a name (`as name` that ends a use tree: then
/// `;`, `,`, or `}`). `as $name` is a cast in a macro, not an import.
fn shadows(text: &str, named: &dyn Fn(&str) -> bool) -> bool {
    let ident_after = |rest: &str| -> String { rest.trim_start().chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect() };
    let word_before = |i: usize| i == 0 || !text.as_bytes()[i - 1].is_ascii_alphanumeric() && text.as_bytes()[i - 1] != b'_';
    let defines = text.match_indices("macro_rules").any(|(i, m)| {
        let rest = text[i + m.len()..].trim_start();
        rest.strip_prefix('!').is_some_and(|r| named(&ident_after(r)))
    });
    let renames = text.match_indices("as").any(|(i, m)| {
        let rest = &text[i + m.len()..];
        if !word_before(i) || !rest.starts_with(char::is_whitespace) {
            return false;
        }
        let rest = rest.trim_start();
        let name = ident_after(rest);
        !name.is_empty() && rest[name.len()..].trim_start().starts_with([';', ',', '}']) && named(&name)
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
        expand: Option<(crate::resolve::cfg::CfgEnv, String)>,
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
        let expand = expand.filter(|_| !user_macros || !texts.iter().any(|(_, t)| shadows_builtin(t)));
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
        let mut dropped: Vec<Dropped> = front
            .chunks
            .iter()
            .flat_map(|c| &c.expand_deps)
            .filter_map(|d| match *d {
                crate::expand::Dep::Dropped { file, lo, hi, item } => Some(Dropped { file, lo, hi, item }),
                _ => None,
            })
            .collect();
        dropped.sort_unstable_by_key(|d| (d.file, d.lo));
        PatchBase {
            inputs,
            root_unspliced,
            spliced,
            needs,
            stamps,
            user_macros,
            shadowed,
            expand,
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
            item_scans: FxMap::default(),
            dropped,
            reach: None,
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
    /// Some edited body is a `const fn`'s that a const evaluation may
    /// run (see the module docs).
    pub const_fn: bool,
    /// Some edited const fn's result can reach const and static values
    /// only (`ConstReach::revaluable`): they must evaluate again.
    pub revalue: bool,
    /// The edited const fns (`Front::fn_loc` indexes).
    pub const_edits: Vec<usize>,
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

/// One edit proven to sit inside one fn body (`find_body_edit`), or
/// inside cfg-disabled code (`find_inactive_edit`, no `body`).
struct BodyEdit {
    file: FileId,
    text: String,
    edit: Edit,
    needs: (StdNeeds, bool),
    /// The new fn body; None when no Ast node changes.
    body: Option<NewBody>,
}

/// The fn body side of a `BodyEdit`.
struct NewBody {
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
    /// Neither body holds a closure or a token collect's whole-Ast scans
    /// look for (`plain_body`).
    plain: bool,
    /// The old body's expression range (`FnDef::exprs`).
    old_exprs: (u32, u32),
    /// The old body's items (`same_items`), where the new body's go.
    items: Vec<u32>,
    /// The signature nodes copied ahead of the new body (`sig_nodes.rs`).
    sig: Option<super::sig_nodes::SigNodes>,
    /// The nested fn whose own body the edit changed (`same_items`), in
    /// `Front::fn_loc` order.
    nested: Option<usize>,
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
    /// The edited fn, in `Front::fn_loc` order (its `LocalDefId`); None
    /// for an edit inside cfg-disabled code.
    fn_index: Option<usize>,
    plain: bool,
    /// The body's items (`stmt_items` indexes; see `reuse_kept`).
    items: Vec<u32>,
    /// The nested fn whose own body changed (`NewBody::nested`).
    nested: Option<usize>,
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
    let edits_in: Vec<KeptEdit> = edits
        .iter()
        .map(|e| KeptEdit {
            edit: e.edit,
            ctxts: FxMap::default(),
            fn_index: e.body.as_ref().map(|b| b.fn_index),
            plain: e.body.as_ref().is_none_or(|b| b.plain),
            items: e.body.as_ref().map_or_else(Vec::new, |b| b.items.clone()),
            nested: e.body.as_ref().and_then(|b| b.nested),
            old_exprs: e.body.as_ref().map_or((0, 0), |b| b.old_exprs),
        })
        .collect();
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
            // Each edited fn's discovery output as the program has it, the
            // nested fn whose body changed too (`reuse_kept` compares).
            for fn_index in edits_in.iter().flat_map(|e| e.fn_index.into_iter().chain(e.nested)) {
                if !edits.iter().any(|x| x.fn_index == Some(fn_index) || x.nested == Some(fn_index)) && !k.bases.iter().any(|b| b.0 == fn_index) {
                    let def = k.program.def_id(crate::def::LocalDefId(fn_index as u32));
                    k.bases.push((fn_index, caches.gen_reuse.out_copy(def)));
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
        // The std splice follows the root text in file 0. It stands while
        // the std needs do (checked below), so the new file text is the
        // new root text and the same splice.
        let text = match splice_of(front, base) {
            Some(splice) => format!("{root}{splice}"),
            None if base.spliced => return Err("spliced root"),
            None => root.to_string(),
        };
        changed.push((FileId(0), text));
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
        let old = front.map.text(file).ok_or("no text")?;
        let (p, s) = super::compile::common_ends(old.as_bytes(), text.as_bytes());
        let edit = Edit { file, a: p as u32, b: (old.len() - s) as u32, d: text.len() as i64 - old.len() as i64 };
        let body = match find_body_edit(front, &text, edit) {
            Ok(body) => Some(body),
            // No active fn body holds the edit: it may sit in code the
            // expander dropped.
            Err(why @ ("not in a fn body" | "no active item")) => {
                find_inactive_edit(front, &text, edit).map_err(|inactive| inactive.unwrap_or(why))?;
                None
            }
            Err(why) => return Err(why),
        };
        // The root's own needs: its text before the splice.
        let own = if file == FileId(0) { splice_of(front, front.patch.as_ref().ok_or("no base")?).map_or(text.len(), |sp| text.len() - sp.len()) } else { text.len() };
        edits.push(BodyEdit { file, needs: file_needs(&text[..own]), text, edit, body });
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

/// The std splice text after the root text in file 0, when the base
/// spliced one and the file still starts with the root text it read.
fn splice_of<'a>(front: &'a Front, base: &PatchBase) -> Option<&'a str> {
    if !base.spliced {
        return None;
    }
    front.map.text(FileId(0))?.strip_prefix(base.root_unspliced.as_str())
}

/// Proves that `edit` (the map's text of its file to `text`) sits
/// strictly inside one top-level fn or method body, and lexes, parses,
/// and rewrites the new body.
fn find_body_edit(front: &Front, text: &str, edit: Edit) -> Result<NewBody, &'static str> {
    let base = front.patch.as_ref().ok_or("no base")?;
    let file = edit.file;
    let old = front.map.text(file).ok_or("no text")?;
    let (a, b, d) = (edit.a as usize, edit.b as usize, edit.d);
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
        .ok_or_else(|| outside_fn_reason(ast, file, a, b))?;
    let def = fn_def_at(ast, item, sub);
    if def.ret.is_some_and(|t| matches!(ast.ty(t), TyExpr::ImplTrait { .. })) {
        return Err("impl Trait");
    }
    if !matches!(ast.items[item].kind, ItemKind::Fn(_) | ItemKind::Impl(_)) {
        return Err("not in a fn body");
    }
    let span = ast.blocks[def.body.ok_or("not in a fn body")?.0 as usize].span;
    // A fn's expression and pattern ranges (`FnDef::exprs`, closure
    // numbering reads them) start at its first parameter: parameter
    // patterns and expressions in the signature's types sit there, before
    // the body's nodes. They move ahead of the new body (`sig_nodes.rs`),
    // in the new body's own Ast from index 0, so the ranges keep the cold
    // shape.
    let mut body_ast = Ast::default();
    let sig = super::sig_nodes::copy(ast, def, span, &mut body_ast)?;
    let (lo, hi) = (span.lo as usize, span.hi as usize);
    let new_hi = (hi as i64 + d) as usize;
    let lex = |t: Option<&str>| t.and_then(|t| lexer::lex(t, file, lo as u32, &front.interner).ok()).ok_or("body lex");
    let (old_body, new_body) = (lex(old.get(lo..hi))?, lex(text.get(lo..new_hi))?);
    let (old_calls, old_pure) = body_tokens_ok(&old_body, lo, hi, &front.interner)?;
    let (new_calls, new_pure) = body_tokens_ok(&new_body, lo, new_hi, &front.interner)?;
    if (old_calls || new_calls) && base.shadowed || (old_pure || new_pure) && base.expand.is_none() {
        return Err("macro in body");
    }
    // Parse and rewrite the new body on its own: an error there (a
    // half-typed edit) gives up before any state changes, so the base
    // stands for the next request. Its pure builtin macros expand first,
    // and a static's init closure hoists into a hidden fn, as the
    // resolver's token passes do.
    let module = *base.tables.fn_module.get(fn_index).ok_or("state")?;
    let raw = lexer::Lexed { tokens: new_body.tokens.clone(), strings: new_body.strings.clone() };
    let hoisted = match &base.expand {
        Some((env, crate_name)) if new_pure => {
            let path = front.map.path(file);
            let shown = front.display_root.as_deref().and_then(|r| std::path::Path::new(path).strip_prefix(r).ok());
            let ctx = crate::expand::ExpandCtx {
                interner: &front.interner,
                known: &front.known,
                file_path: shown.map_or_else(|| path.to_string(), |rel| rel.to_string_lossy().to_string()),
                real_path: std::path::PathBuf::from(path),
                // No Cargo env on the patch path: a body that reads
                // one (`env!`, an include) records a non-`Dropped`
                // dep below and the patch gives up to a full resolve.
                cargo_env: Vec::new(),
                src: text,
                cfg: crate::resolve::worklist::expand_cfg(env),
                module_path: base.tables.modules[module.0 as usize].path.clone(),
                crate_name: Some(crate_name.clone()),
                client: &front.client,
            };
            // Unknown cfg names reject before expansion, as in the resolver.
            if crate::resolve::worklist::check_cfg_names(&raw, env, &front.interner).is_err() {
                return Err("body macro");
            }
            match crate::expand::expand_lexed_seeded_with_deps(raw, &ctx, &[]) {
                Ok((out, deps)) if deps.iter().all(|d| matches!(d, crate::expand::Dep::Dropped { .. })) => out,
                _ => return Err("body macro"),
            }
        }
        _ => crate::expand::lazy::hoist_static_closures(raw, &front.interner),
    };
    let toks = &hoisted.tokens[..hoisted.tokens.len() - 1];
    let (body, mut exprs, mut pats) =
        crate::parser::parse_body(toks, &hoisted.strings, &mut body_ast, &front.interner, &front.known).map_err(|_| "body parse")?;
    let (items, nested) = same_items(ast, old, text, span, &body_ast, (&old_body.tokens, &new_body.tokens), edit)?;
    let nested = match nested {
        Some(i) => Some(front.fn_loc.iter().position(|&l| l == (usize::MAX, Some(i as usize))).ok_or("body items")?),
        None => None,
    };
    let mut scratch = def.clone();
    scratch.body = Some(body);
    if let Some(sig) = &sig {
        (exprs.0, pats.0) = (0, 0);
        for p in &mut scratch.params {
            p.pat = p.pat.map(|q| sig.pat(q));
        }
    }
    let outer = match &ast.items[item].kind {
        ItemKind::Impl(imp) => Some(&imp.generics),
        _ => None,
    };
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
    let old_closures = ast.exprs[def.exprs.0 as usize..def.exprs.1 as usize].iter().any(|e| matches!(e, crate::ast::Expr::Closure { .. }));
    let new_closures = body_ast.exprs.iter().any(|e| matches!(e, crate::ast::Expr::Closure { .. }));
    let plain = !old_closures
        && !new_closures
        && plain_body(&old_body, &front.interner)
        && plain_body(&new_body, &front.interner)
        && plain_body(&hoisted, &front.interner);
    Ok(NewBody { fn_index, item, sub, old_body: (span.lo, span.hi), body_ast, body, exprs, pats, plain, old_exprs: def.exprs, items, sig, nested })
}

/// The items (`stmt_items` indexes, in parse order) of the old fn body at
/// `span`, when the new body (`body_ast`, parsed from `text`) holds the
/// same ones: as many, each with the same source text at its old place
/// moved by the edit, and no brace
/// token in the changed tokens of the body (`toks`: old and new), so each
/// item sits in the same block as before and sees the same items and
/// `use`s. Resolve and collect then make the same defs of them, with the
/// same indexes once `apply` puts each new item at its old index.
/// One exception, returned second: an edit strictly inside the body of a
/// nested fn that holds no item changes that fn's body only (its head
/// text stands, its end moves by the edit). Braces may change there: no
/// item sits in that body, and every other item still matches its text.
fn same_items(
    ast: &Ast,
    old: &str,
    text: &str,
    span: crate::diag::Span,
    body_ast: &Ast,
    toks: (&[lexer::Token], &[lexer::Token]),
    edit: Edit,
) -> Result<(Vec<u32>, Option<u32>), &'static str> {
    let inside = |s: crate::diag::Span| s.file == span.file && span.lo <= s.lo && s.hi <= span.hi;
    let olds: Vec<u32> = (0..ast.stmt_items.len() as u32).filter(|&i| inside(ast.stmt_items[i as usize].span)).collect();
    if olds.len() != body_ast.stmt_items.len() {
        return Err("body items");
    }
    if olds.is_empty() {
        return Ok((olds, None));
    }
    let fn_body = |it: &crate::ast::Item, a: &Ast| match &it.kind {
        ItemKind::Fn(f) => f.body.map(|b| a.blocks[b.0 as usize].span),
        _ => None,
    };
    let nested = olds.iter().position(|&i| fn_body(&ast.stmt_items[i as usize], ast).is_some_and(|b| b.lo < edit.a && edit.b < b.hi));
    if let Some(k) = nested {
        let b = fn_body(&ast.stmt_items[olds[k] as usize], ast).ok_or("body items")?;
        let holds = |s: crate::diag::Span| b.lo <= s.lo && s.hi <= b.hi;
        if olds.iter().enumerate().any(|(j, &i)| j != k && holds(ast.stmt_items[i as usize].span)) {
            return Err("body items");
        }
    } else {
        let (pre, post) = token_window(toks.0, toks.1, edit);
        let (ow, nw) = (&toks.0[pre..toks.0.len() - post], &toks.1[pre..toks.1.len() - post]);
        if ow.iter().chain(nw).any(|t| matches!(t.tok, Tok::LBrace | Tok::RBrace)) {
            return Err("body items");
        }
    }
    // Same text at the same place: span keys of the resolver tables
    // (`const_init_module`) move with the edit.
    let src = |t: &str, s: crate::diag::Span| t.get(s.lo as usize..s.hi as usize).map(str::to_owned);
    for (k, &i) in olds.iter().enumerate() {
        let (o, n) = (ast.stmt_items[i as usize].span, body_ast.stmt_items[k].span);
        if Some(k) == nested {
            // The head up to the body's brace stands (the edit is after it).
            let (b, nb) = (fn_body(&ast.stmt_items[i as usize], ast), fn_body(&body_ast.stmt_items[k], body_ast));
            let head = b.zip(nb).is_some_and(|(b, nb)| b.lo == nb.lo && src(old, crate::diag::Span { hi: b.lo, ..o }) == src(text, crate::diag::Span { hi: b.lo, ..n }));
            if edit.plain(o) != n || !head {
                return Err("body items");
            }
            continue;
        }
        if edit.plain(o) != n || src(old, o).is_none() || src(old, o) != src(text, n) {
            return Err("body items");
        }
    }
    let nested = nested.map(|k| olds[k]);
    Ok((olds, nested))
}

/// The changed tokens of one edit: how many tokens of `old` (lexed from
/// the old text) and `new` (the same range of the new text) lie wholly
/// before the edit at the same spans, and how many lie wholly after it at
/// the same spans moved by the edit. Those are the same text at the same
/// boundaries, so the same tokens; the rest of each is the window.
fn token_window(old: &[lexer::Token], new: &[lexer::Token], edit: Edit) -> (usize, usize) {
    let (a, b, d) = (edit.a, edit.b, edit.d);
    let span_eq = |x: &lexer::Token, y: &lexer::Token, shift: i64| {
        (x.span.lo as i64 + shift, x.span.hi as i64 + shift) == (y.span.lo as i64, y.span.hi as i64)
    };
    let pre = old.iter().zip(new).take_while(|(x, y)| x.span.hi <= a && span_eq(x, y, 0)).count();
    let post = old[pre..].iter().rev().zip(new[pre..].iter().rev()).take_while(|(x, y)| x.span.lo >= b && span_eq(x, y, d)).count();
    (pre, post)
}

/// Proves that `edit` (the map's text of its file to `text`) sits inside
/// a cfg-disabled node the expander dropped at the last full resolve
/// (`Dep::Dropped`), in a way a cold resolve of `text` answers the same
/// up to spans: the node lexes alone to the same tokens outside the
/// edit, the changed tokens sit in one brace group inside the node and
/// outside any macro call or attribute, they hold nothing the expander's
/// prescan, the module outline, or the cfg name check reads (`$`, `#`,
/// item keywords, `cfg`, `macro_rules`), and the new node passes the
/// expander's own grammar check (`parser::check_cfg_syntax`). The file's
/// text scans (`macro_rules`, parser macro shadowing) must stand too.
/// `Err(None)` when no dropped node holds the edit.
fn find_inactive_edit(front: &Front, text: &str, edit: Edit) -> Result<(), Option<&'static str>> {
    let base = front.patch.as_ref().ok_or(Some("no base"))?;
    let file = edit.file;
    let old = front.map.text(file).ok_or(Some("no text"))?;
    let (a, b, d) = (edit.a, edit.b, edit.d);
    let node = base.dropped.iter().find(|n| n.file == file.0 && n.lo < a && b < n.hi).ok_or(None)?;
    // The node sits in an item list (a module's, an impl's, a trait's),
    // in no active item's own text: an edit inside an active body would
    // move positions inside it, and only the patch's fns rehash their
    // text (`fn_text_hash`).
    let ast = &front.ast;
    let holds = |s: crate::diag::Span| s.file == file && s.lo <= node.lo && node.hi <= s.hi;
    let fn_holds = |f: &FnDef| holds(f.name_span) || f.body.is_some_and(|bl| holds(ast.blocks[bl.0 as usize].span));
    for it in ast.items.iter().filter(|it| holds(it.span)) {
        let inside = match &it.kind {
            ItemKind::Impl(imp) => imp.fns.iter().any(fn_holds) || imp.consts.iter().any(|c| holds(c.span)),
            ItemKind::Trait(tr) => tr.fns.iter().any(fn_holds) || tr.consts.iter().any(|c| holds(c.span)),
            _ => true,
        };
        if inside {
            return Err(Some("inactive in item"));
        }
    }
    let new_hi = (node.hi as i64 + d) as usize;
    let lex = |t: Option<&str>| t.and_then(|t| lexer::lex(t, file, node.lo, &front.interner).ok()).ok_or(Some("inactive lex"));
    let (old_toks, new_lexed) = (lex(old.get(node.lo as usize..node.hi as usize))?, lex(text.get(node.lo as usize..new_hi))?);
    let (ot, nt) = (&old_toks.tokens[..old_toks.tokens.len() - 1], &new_lexed.tokens[..new_lexed.tokens.len() - 1]);
    // Both end where the node ends, on a token that cannot run into the
    // text after it.
    let ends = |toks: &[lexer::Token], hi: usize| {
        toks.last().is_some_and(|t| {
            t.span.hi as usize == hi && matches!(t.tok, Tok::RBrace | Tok::Semi | Tok::RParen | Tok::RBracket | Tok::Comma)
        })
    };
    if !ends(ot, node.hi as usize) || !ends(nt, new_hi) {
        return Err(Some("inactive lex"));
    }
    let (pre, post) = token_window(ot, nt, edit);
    let (ow, nw) = (&ot[pre..ot.len() - post], &nt[pre..nt.len() - post]);
    // The groups around the window: open before it and closed after it,
    // in both versions (each version must balance).
    let closes = |toks: &[lexer::Token]| -> Option<Vec<usize>> {
        let (mut stack, mut close) = (Vec::new(), vec![usize::MAX; toks.len()]);
        for (i, t) in toks.iter().enumerate() {
            match t.tok {
                Tok::LBrace | Tok::LParen | Tok::LBracket => stack.push(i),
                Tok::RBrace | Tok::RParen | Tok::RBracket => close[stack.pop()?] = i,
                _ => {}
            }
        }
        stack.is_empty().then_some(close)
    };
    let (oc, nc) = (closes(ot).ok_or(Some("inactive lex"))?, closes(nt).ok_or(Some("inactive lex"))?);
    let (oend, nend) = (ot.len() - post, nt.len() - post);
    let chain: Vec<usize> =
        (0..pre).filter(|&i| oc[i] != usize::MAX && oc[i] >= oend && nc[i] >= nend && oc[i] - oend == nc[i] - nend).collect();
    let (macro_rules, cfg, union) = (front.interner.intern("macro_rules"), front.interner.intern("cfg"), front.interner.intern("union"));
    // Tokens the expander's prescan, the module outline, or the cfg name
    // check acts on: none may change.
    let read = |t: &lexer::Token| {
        matches!(
            t.tok,
            Tok::Pound
                | Tok::Dollar
                | Tok::DocStr(_)
                | Tok::Fn
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
        ) || matches!(t.tok, Tok::Ident(s) if s == macro_rules || s == cfg || s == union)
    };
    // A construct those passes read starts with one of those tokens: one
    // that starts just before the window (`#` + `[cfg_attr(..)]`, `cfg` +
    // `!(..)`, `macro_rules` + `! m {..}`) would take window tokens.
    if chain.is_empty() || ow.iter().chain(nw).any(read) || ot[pre.saturating_sub(4)..pre].iter().any(read) {
        return Err(Some("inactive tokens"));
    }
    // No group around the window is an attribute's (`#[`, `#![`) or a
    // macro definition's body (`macro_rules! m {`; the prescan defines
    // macros even in disabled code), and the window is in no `use` or
    // `extern` item of any group around it (the prescan reads the `use`
    // items of module lists).
    let before = |i: usize, k: usize| i.checked_sub(k).map(|j| ot[j].tok);
    if chain.iter().any(|&i| {
        matches!(before(i, 1), Some(Tok::Pound))
            || matches!((before(i, 2), before(i, 1)), (Some(Tok::Bang), Some(Tok::Ident(_))) | (Some(Tok::Pound), Some(Tok::Bang)))
    }) {
        return Err(Some("inactive macro"));
    }
    for (k, &g) in chain.iter().enumerate() {
        // This group's own tokens from its open up to the next group in
        // the chain (or the window): an item still open there holds it.
        let upto = chain.get(k + 1).copied().unwrap_or(pre);
        let mut i = g + 1;
        let mut open_item = false;
        while i < upto {
            match ot[i].tok {
                Tok::Semi => open_item = false,
                Tok::Use | Tok::Extern => open_item = true,
                _ => {}
            }
            i = if oc[i] != usize::MAX { oc[i] + 1 } else { i + 1 };
        }
        if open_item {
            return Err(Some("inactive tokens"));
        }
    }
    let hint = if node.item { crate::parser::CfgSyntaxHint::Item } else { crate::parser::CfgSyntaxHint::Node };
    crate::parser::check_cfg_syntax(nt, &new_lexed.strings, &front.interner, &front.known, hint).map_err(|_| Some("inactive syntax"))?;
    if old.contains("macro_rules") != text.contains("macro_rules")
        || shadows_parser_macro(old) != shadows_parser_macro(text)
        || shadows_builtin(old) != shadows_builtin(text)
    {
        return Err(Some("inactive text"));
    }
    Ok(())
}

/// Why an edit at `a..b` of `file` is in no top-level fn body: it sits
/// in some other item of the merged Ast (a nested fn, a trait method, a
/// const), or in no item at all (cfg-disabled code, or between items).
fn outside_fn_reason(ast: &Ast, file: FileId, a: usize, b: usize) -> &'static str {
    let inside = |sp: crate::diag::Span| sp.file == file && (sp.lo as usize) <= a && b <= sp.hi as usize;
    if ast.items.iter().any(|it| inside(it.span)) { "not in a fn body" } else { "no active item" }
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
/// `Eof`): one balanced brace group, no `$`, macro the expander owns but
/// `PURE_MACROS`, or item keyword but `fn`, `static`, `const`, `use`.
/// Returns whether it calls a parser macro (`println!` and kin) and
/// whether it needs the expander (a pure builtin or an attribute), or
/// why the body fails a check.
fn body_tokens_ok(lexed: &lexer::Lexed, lo: usize, hi: usize, interner: &crate::intern::Interner) -> Result<(bool, bool), &'static str> {
    let toks = &lexed.tokens;
    let n = toks.len().checked_sub(1).ok_or("body shape")?;
    if n < 2 || toks[n].tok != Tok::Eof || toks[0].tok != Tok::LBrace || toks[0].span.lo as usize != lo {
        return Err("body shape");
    }
    if toks[n - 1].tok != Tok::RBrace || toks[n - 1].span.hi as usize != hi {
        return Err("body shape");
    }
    let (macro_rules, union) = (interner.intern("macro_rules"), interner.intern("union"));
    let mut depth = 0usize;
    let (mut calls, mut pure) = (false, false);
    for (i, t) in toks[..n].iter().enumerate() {
        match t.tok {
            Tok::LBrace | Tok::LParen | Tok::LBracket => depth += 1,
            Tok::RBrace | Tok::RParen | Tok::RBracket => {
                depth = depth.checked_sub(1).ok_or("body shape")?;
                if depth == 0 && i != n - 1 {
                    return Err("body shape");
                }
            }
            // `fn`, `static`, `const`, and `use` items are compared after
            // the parse (`same_items`).
            Tok::Struct | Tok::Enum | Tok::Impl | Tok::Trait | Tok::Mod | Tok::Extern | Tok::Type => return Err("body item"),
            // Attributes go through the expander (cfg stripping).
            Tok::Pound | Tok::DocStr(_) => pure = true,
            Tok::Dollar => return Err("body attr"),
            Tok::Ident(s) if s == macro_rules || s == union => return Err("body item"),
            // A macro call: `name!`, never path-qualified.
            Tok::Bang if i > 0 => match toks[i - 1].tok {
                Tok::Ident(s) if i > 1 && toks[i - 2].tok == Tok::PathSep => return Err("body macro"),
                Tok::Ident(s) if crate::expand::builtin::is_passthrough(interner.get(s)) => calls = true,
                Tok::Ident(s) if PURE_MACROS.contains(&interner.get(s)) => pure = true,
                Tok::Ident(_) | Tok::SelfUpper | Tok::SelfLower | Tok::Crate | Tok::Super => return Err("body macro"),
                _ => {}
            },
            _ => {}
        }
    }
    // Anything else the expander acts on is a refused macro.
    if depth != 0 {
        return Err("body shape");
    }
    if !pure && crate::expand::needs_expansion(&toks[..n], interner) {
        return Err("body macro");
    }
    Ok((calls, pure))
}

/// Builtin macros the expander owns whose expansion reads only their
/// own tokens and the crate's cfg: a body that calls them expands alone
/// to what the resolver's expansion of its file gives (no position, path,
/// env, file, or item output). `cfg!` names also pass the cfg name check.
const PURE_MACROS: &[&str] =
    &["matches", "write", "writeln", "debug_assert", "debug_assert_eq", "debug_assert_ne", "unimplemented", "stringify", "concat", "cfg"];

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
        if let Some(body) = &e.body {
            span_shift::blank_nodes_extras(Arc::make_mut(&mut front.ast), e.file, body.old_body, ranges, extras);
        }
        // Spans next: the new body is lexed at the new positions.
        let mut memo = FxMap::default();
        spans += span_shift::shift_ast_extras(Arc::make_mut(&mut front.ast), e.edit, ranges, extras, &mut memo);
        ctxts.push(memo);
        let splice_len = if e.file == FileId(0) { splice_of(front, &base).map_or(0, str::len) } else { 0 };
        let tables = Arc::get_mut(&mut base.tables).ok_or("state")?;
        shift_table_spans(tables, e.edit);
        let lines = front.map.lines(e.file).splice(&e.text, e.edit.a as usize, e.edit.b as usize, (e.edit.b as i64 + e.edit.d) as usize);
        front.map.replace_text(e.file, e.text.clone(), lines);
        if e.file == FileId(0) {
            front.src.clone_from(&e.text);
            front.chunks[0].text.clone_from(&e.text);
            base.root_unspliced = e.text[..e.text.len() - splice_len].to_string();
        }
        // The splice after the root text moves with the edit: its byte
        // ranges in file 0 and the lang method range, wherever they sit
        // (the base, the resolver tables, the Ast).
        if base.spliced && e.file == FileId(0) {
            let mv = |x: u32| if x >= e.edit.b { (x as i64 + e.edit.d) as u32 } else { x };
            let ranges = |rs: &mut Vec<(u32, u32, ShippedCrate)>| rs.iter_mut().for_each(|r| (r.0, r.1) = (mv(r.0), mv(r.1)));
            ranges(&mut base.std_ranges);
            base.std_methods = (mv(base.std_methods.0), mv(base.std_methods.1));
            ranges(&mut tables.std_ranges);
            tables.std_splice_lo = tables.std_splice_lo.map(mv);
            let ast = Arc::make_mut(&mut front.ast);
            ranges(&mut ast.shipped);
            ast.lang_methods = (mv(ast.lang_methods.0), mv(ast.lang_methods.1));
        }
        base.needs[e.file.0 as usize] = e.needs;
        base.stamps[e.file.0 as usize] = None;
        for d in base.dropped.iter_mut().filter(|d| d.file == e.file.0) {
            let s = e.edit.plain(crate::diag::Span { file: e.file, lo: d.lo, hi: d.hi, ctxt: CtxtId::ROOT });
            (d.lo, d.hi) = (s.lo, s.hi);
        }
    }
    for e in edits.iter_mut() {
        let file = e.file;
        let Some(e) = e.body.as_mut() else { continue };
        let ast = &front.ast;
        let before = (ast.exprs.len(), ast.pats.len(), ast.tys.len(), ast.blocks.len(), ast.stmt_items.len());
        let stmt_base = before.4 as u32;
        let (_, new_items, _) = Arc::make_mut(&mut front.ast).append_chunk(std::mem::take(&mut e.body_ast), stmt_base);
        // Each body item takes its old index (`same_items`).
        if !e.items.is_empty() {
            let ast = Arc::make_mut(&mut front.ast);
            for blk in &mut ast.blocks[before.3..] {
                for s in &mut blk.stmts {
                    if let crate::ast::Stmt::Item(i) = s {
                        *i = *e.items.get((*i - stmt_base) as usize).ok_or("body items")?;
                    }
                }
            }
            for (&i, it) in e.items.iter().zip(new_items) {
                ast.stmt_items[i as usize] = it;
            }
        }
        if let Some(sig) = &e.sig {
            super::sig_nodes::relink(Arc::make_mut(&mut front.ast), e.item, e.sub, sig, (before.0 as u32, before.1 as u32));
        }
        let def = fn_def_at_mut(Arc::make_mut(&mut front.ast), e.item, e.sub);
        def.body = Some(BlockId(e.body.0 + before.3 as u32));
        def.exprs = (e.exprs.0 + before.0 as u32, e.exprs.1 + before.0 as u32);
        def.pats = (e.pats.0 + before.1 as u32, e.pats.1 + before.1 as u32);
        // The new body's nodes join the file's ranges for later edits.
        if let Some(r) = base.ranges.as_mut().and_then(|r| r.get_mut(file.0 as usize)) {
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
        let (hash, idents) = rescan_edited(front, &mut base, e)?;
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
    let edited: Vec<usize> = edits.iter().filter_map(|e| e.body.as_ref()).flat_map(|b| std::iter::once(b.fn_index).chain(b.nested)).collect();
    // A const fn edit is a plain body edit when no const evaluation can
    // run that fn (`const_reach.rs`).
    let is_const = |i: usize| {
        let (item, sub) = front.fn_loc[i];
        fn_def_at(&front.ast, item, sub).qual.is_const
    };
    let const_edits: Vec<usize> = edited.iter().copied().filter(|&i| is_const(i)).collect();
    match &mut base.reach {
        Some(r) => r.update(front, &edited),
        None if !const_edits.is_empty() => base.reach = Some(super::const_reach::ConstReach::build(front)),
        None => {}
    }
    // One that only const and static values can read keeps the program
    // after their values check again (`Patched::revalue`).
    let reached: Vec<usize> = match &base.reach {
        Some(r) => const_edits.iter().copied().filter(|&i| r.reaches(front, i)).collect(),
        None => Vec::new(),
    };
    let revalue = !reached.is_empty() && base.reach.as_ref().is_some_and(|r| r.revaluable(front, &reached));
    let changed = slot_update(front, caches, &base.body_hashes, &edited, &base.live_slots);
    let edits_len = edits.iter().filter(|e| e.body.is_some()).count();
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
        const_fn: !reached.is_empty() && !revalue,
        revalue,
        const_edits,
        files,
        nodes: super::compile::ast_nodes(&front.ast) - nodes_before,
        bodies: edits_len,
        spans,
        reads,
    };
    front.patch = Some(base);
    Ok(out)
}

/// Rescans the edited fn's item after its new body landed: the item
/// scan must stand (the edit changed no head). Returns the edited fn's
/// raw body hash and idents. The first edit in an impl whose bodies hold
/// no item scans every method and stores their hashes in the base; later
/// edits in that impl scan only the edited method, because a body hash
/// reads structure only (never spans), so unchanged methods keep theirs.
/// An item that holds body items rescans whole: its nested fns' hashes
/// fold in its content (`nested_fn_hashes`).
fn rescan_edited(front: &mut Front, base: &mut PatchBase, e: &NewBody) -> Result<(u64, Vec<Sym>), &'static str> {
    if let (Some(sub), Some(stored)) = (e.sub, base.item_scans.get(&e.item).cloned()) {
        let (hash, idents, inner) = super::ast_hash::scan_body(&front.ast, fn_def_at(&front.ast, e.item, e.sub));
        if inner.is_empty() {
            let mut hashes = stored;
            *hashes.get_mut(sub).ok_or("item scan")? = hash;
            let scan = super::ast_hash::scan_item_reuse(&front.ast, &front.ast.items[e.item], &hashes);
            if front.items.get(e.item) != Some(&scan) {
                return Err("item scan");
            }
            base.item_scans.insert(e.item, hashes);
            return Ok((hash, idents));
        }
    }
    let (scan, bodies, inner) = super::ast_hash::scan_item(&front.ast, &front.ast.items[e.item]);
    if front.items.get(e.item) != Some(&scan) {
        return Err("item scan");
    }
    nested_fn_hashes(front, base, &scan, &bodies, &inner)?;
    if inner.is_empty() {
        base.item_scans.insert(e.item, bodies.iter().map(|b| b.0).collect());
    } else {
        base.item_scans.remove(&e.item);
    }
    bodies.into_iter().nth(e.sub.unwrap_or(0)).ok_or("item scan")
}

/// The body hashes of the fns nested anywhere in one edited item
/// (`inner`, from `scan_item`), which fold in the item's content hash, as
/// the full scan computes them (`ast_hash::assemble`), and their lines.
fn nested_fn_hashes(
    front: &mut Front,
    base: &mut PatchBase,
    scan: &crate::scan::ItemScan,
    bodies: &[(u64, Vec<Sym>)],
    inner: &[u32],
) -> Result<(), &'static str> {
    if inner.is_empty() {
        return Ok(());
    }
    let content = super::ast_hash::item_content(scan, bodies);
    for &i in inner {
        let ItemKind::Fn(def) = &front.ast.stmt_items[i as usize].kind else { continue };
        let j = front.fn_loc.iter().position(|&l| l == (usize::MAX, Some(i as usize))).ok_or("state")?;
        let (hash, idents) = super::ast_hash::body_scan(&front.ast, def, None);
        let line = front.map.line_col(def.name_span).0;
        let h = fn_text_hash(&front.ast, &front.map, def, line, crate::scan::fold_outer(hash, content));
        base.fn_lines[j] = line;
        base.body_hashes[j] = h;
        let chunk = &mut front.chunks[0];
        chunk.scan.fns.get_mut(j).ok_or("state")?.body_hash = h;
        *chunk.scan.body_idents.get_mut(j).ok_or("state")? = idents;
    }
    Ok(())
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
        // Body items keep their indexes, text, and blocks (`same_items`),
        // so the program's statics, consts, item blocks, and nested fn
        // signatures stand. Closure and template tables key on Ast nodes,
        // which are new: a nested fn must be a plain fn with no closure.
        for &i in &e.items {
            if let Some(crate::check::collect::BodyItem::Fn(f)) = p.body_items.get(&i).copied() {
                let def = p.fn_def(f);
                let closure = p.ast.exprs[def.exprs.0 as usize..def.exprs.1 as usize].iter().any(|x| matches!(x, crate::ast::Expr::Closure { .. }));
                if closure || p.gx.fn_class.get(f.0 as usize) != Some(&FnClass::Plain) {
                    return Err("body items");
                }
            }
        }
        // A template checks again below, in a check only: a build's
        // instances replay its picks.
        let Some(fn_index) = e.fn_index else { continue };
        let f = LocalDefId(fn_index as u32);
        match p.gx.fn_class.get(fn_index) {
            Some(FnClass::Plain) => {}
            // A template with closures stands when its closures are the
            // registered ones (checked below, before its template check).
            Some(FnClass::Template)
                if !walk_instances
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
        let Some(fn_index) = e.fn_index else { continue };
        if p.gx.fn_class.get(fn_index) != Some(&FnClass::Template) || seen.contains(&fn_index) {
            continue;
        }
        seen.push(fn_index);
        let f = LocalDefId(fn_index as u32);
        if !crate::check::generics::template_closures_stand(&mut p, f) {
            return Err("closures");
        }
        let ranges: Vec<(u32, u32)> = edits.iter().filter(|x| x.fn_index == e.fn_index).map(|x| x.old_exprs).collect();
        p.gx.trait_picks.retain(|x, _| !ranges.iter().any(|r| x.0 >= r.0 && x.0 < r.1));
        p.gx.template_closures.retain(|k, _| k.0 != f);
        p.gx.template_calls.retain(|k, _| k.0 != f);
        // Collect's template check runs before mono: a coercion of a
        // type parameter to `dyn` then needs no concrete vtable.
        let (counts, mono_done) = (p.gx.mono_counts, std::mem::replace(&mut p.gx.mono_done, false));
        template_errs.extend(crate::check::generics::check_template(&mut p, f, &mut caches.gen_reuse));
        (p.gx.mono_counts, p.gx.mono_done) = (counts, mono_done);
    }
    // Discovery checks every plain body when user generics exist; with
    // only the lang enum methods' generics, a build checks the bodies
    // that name one (not tracked here) and a check none.
    if p.gx.has_generics && edits.iter().any(|e| e.fn_index.is_some()) {
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

    /// The second body edit in one impl rescans only the edited method
    /// and reuses the other methods' stored body hashes, one of which
    /// returns `impl Trait` (its body hash folds into the item scan).
    /// Every warm answer matches a cold session.
    #[test]
    fn second_edit_in_an_impl_rescans_one_method() {
        let dir = std::env::temp_dir().join(format!("lust-patch-impl-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(
            dir.join("m.rs"),
            "pub struct Acc {\n    pub v: i64,\n    pub xs: Vec<i64>,\n}\n\nimpl Acc {\n    pub fn add(&mut self, x: i64) {\n        self.v += x;\n    }\n    pub fn get(&self) -> i64 {\n        self.v\n    }\n    pub fn vals(&self) -> impl Iterator<Item = &i64> {\n        self.xs.iter()\n    }\n}\n\npub fn run() -> i64 {\n    let mut a = Acc { v: 0, xs: vec![1] };\n    a.add(3);\n    a.get() + a.vals().count() as i64\n}\n",
        )
        .unwrap();
        let root = dir.join("main.rs");
        std::fs::write(&root, "mod m;\n\nfn main() {\n    println!(\"{}\", m::run());\n}\n").unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let m = dir.join("m.rs");
        let mut cold_n = 0;
        for (old, new) in [
            ("        self.v += x;\n", "        let y = x + 1;\n        self.v += y - 1;\n"),
            ("        self.v\n", "        self.v + 0\n"),
            ("        self.v += y - 1;\n", "        self.v += y - 2;\n        self.v += 1;\n"),
            ("        self.v + 0\n", "        self.v + true\n"),
        ] {
            edit(&m, old, new);
            let (code, err) = check(&mut warm, &root);
            assert_eq!(field(&warm.front.last_visits, "path"), "patch", "{}", warm.front.last_visits);
            cold_n += 1;
            let mut cold = Session::new(dir.join(format!("obj-cold{cold_n}")), false, SessionKey::synthetic(&root, false));
            assert_eq!((code, err), check(&mut cold, &root), "warm and cold agree after editing {old:?}");
        }
        let _ = std::fs::remove_dir_all(&dir);
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

    /// Edits `file` of the crate at `root`, checks it warm, and asserts
    /// the warm answer is a cold session's; returns the warm
    /// `lust-visits:` line.
    fn warm_equals_cold(warm: &mut Session, root: &Path, file: &Path, old: &str, new: &str) -> String {
        edit(file, old, new);
        let got = check(warm, root);
        let dir = root.parent().unwrap().join(format!("obj-cold-{}", warm.front.last_visits.len()));
        let mut cold = Session::new(dir.clone(), false, SessionKey::synthetic(root, false));
        assert_eq!(got, check(&mut cold, root), "warm and cold agree after {new:?}: {}", warm.front.last_visits);
        let _ = std::fs::remove_dir_all(&dir);
        warm.front.last_visits.clone()
    }

    /// A body edit of a blanket impl method whose body coerces a type
    /// parameter to `dyn` checks the template again on the kept program
    /// as collect does (before mono, so no concrete vtable is asked for).
    #[test]
    fn kept_template_dyn_coercion_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-kept-dyn-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let root = dir.join("main.rs");
        let src = "use std::any::Any;\n\ntrait AnyValue: Any {\n    fn as_any(&self) -> &dyn Any;\n}\n\n\
                   impl<T: Any> AnyValue for T {\n    fn as_any(&self) -> &dyn Any {\n        self\n    }\n}\n\n\
                   fn main() {\n    println!(\"{}\", 5u8.as_any().is::<u8>());\n}\n";
        std::fs::write(&root, src).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root), (0, String::new()));
        let v = warm_equals_cold(&mut warm, &root, &root, "        self\n", "        let _e: u32 = 1;\n        self\n");
        assert_eq!((field(&v, "path"), field(&v, "kept")), ("patch", "reuse"), "{v}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module with cfg-disabled code the expander drops: a test module
    /// and a fn for another platform, around active fns.
    const INACTIVE: &str = "pub fn helper(x: i64) -> i64 {
    x * 2
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn doubles() {
        assert_eq!(helper(1), 2);
    }
}

#[cfg(not(unix))]
pub fn os_name() -> &'static str {
    \"other\"
}

pub fn run() -> i64 {
    let v: i64 = helper(3);
    v
}

pub trait Twice {
    fn twice(&self) -> i64 {
        #[cfg(test)]
        let _t = 1;
        2
    }
}
";

    /// An edit inside cfg-disabled code takes the body patch with no Ast
    /// node built (`find_inactive_edit`): edit, error, fix, undo, and
    /// another edit each give the cold answer. A grammar error in
    /// disabled code is the cold error (it resolves in full); a type error
    /// there is no error, as in rustc. Tokens the cold passes read (`cfg`,
    /// `#`), and disabled code inside an active body, resolve in full. A
    /// later active error shows its moved line.
    #[test]
    fn inactive_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-inactive-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, INACTIVE).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let path = |v: &str| (field(v, "path").to_string(), field(v, "nodes").to_string());
        let patch = || ("patch".to_string(), "0".to_string());
        let steps: &[(&str, &str, bool)] = &[
            // edit (adds lines), type error (no error in disabled code), fix
            ("        assert_eq!(helper(1), 2);\n", "        let y = 3;\n        assert_eq!(helper(1), y - 1);\n", true),
            ("let y = 3;", "let y: u32 = \"no\";", true),
            ("let y: u32 = \"no\";", "let y = 3;", true),
            // a grammar error: cold rejects; then the fix
            ("let y = 3;", "let y = ;", false),
            ("let y = ;", "let y = 3;", false),
            // undo, then another edit in the other disabled fn
            ("        let y = 3;\n        assert_eq!(helper(1), y - 1);\n", "        assert_eq!(helper(1), 2);\n", true),
            ("    \"other\"\n", "    let s = \"other\";\n    s\n", true),
            // tokens the cold passes read
            ("    let s = \"other\";\n", "    let s = if cfg!(windows) { \"w\" } else { \"other\" };\n", false),
            ("    let s = if cfg!(windows) { \"w\" } else { \"other\" };\n", "    let s = \"other\";\n", false),
        ];
        for &(old, new, fast) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            if fast {
                assert_eq!(path(&v), patch(), "{new:?}: {v}");
            }
        }
        // A disabled statement inside an active body (a trait default
        // method's): its positions would move under the patch.
        let v = warm_equals_cold(&mut warm, &root, &m1, "        let _t = 1;\n", "        let _t = 2;\n");
        assert_eq!((field(&v, "path"), field(&v, "why")), ("resolve", "inactive_in_item"), "{v}");
        // An active error after disabled code that grew: its line moves.
        warm_equals_cold(&mut warm, &root, &m1, "    #[test]\n", "    #[test]\n\n\n");
        let v = warm_equals_cold(&mut warm, &root, &m1, "    v\n}", "    v + true\n}");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module whose const fn bodies feed a const, an array length, and
    /// a static, read by an active fn.
    const CONSTS: &str = "pub const fn len() -> usize {
    4
}

pub const fn seed() -> i64 {
    3
}

pub const LEN: usize = len();
pub static TABLE: [i64; 2] = [seed(), seed() + 1];

pub fn run() -> i64 {
    let a: [u8; 4] = [0; LEN];
    a.len() as i64 + TABLE[1]
}
";

    /// A const fn body edit patches (no full resolve) and then collects
    /// and walks reads as a cold resolve does: a new value that breaks an
    /// array type is the cold error, the fix passes, and a build after a
    /// static's const fn edit prints the new value, as a cold build does.
    #[test]
    fn const_fn_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-constfn-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, CONSTS).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        for (old, new) in [("    4\n", "    5\n"), ("    5\n", "    4\n"), ("    3\n}\n\npub const LEN", "    let x = 7;\n    x\n}\n\npub const LEN")] {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Const fns that no const item reads (`unread`), one an array repeat
    /// length in a body reads (`local`), and one a `thread_local!` const
    /// initializer reads (`tls_init`).
    const UNREAD: &str = "use std::cell::Cell;

pub const fn unread(x: u32) -> u32 {
    x + 1
}

pub const fn local() -> usize {
    2
}

pub const fn tls_init() -> u32 {
    9
}

thread_local! {
    static T: Cell<u32> = const { Cell::new(tls_init()) };
}

pub fn run() -> i64 {
    let a = [0u8; local()];
    (unread(3) + T.with(|t| t.get())) as i64 + a.len() as i64
}
";

    /// A body edit of a const fn that no const evaluation can run
    /// (`const_reach.rs`) is a plain body edit: the kept program stands
    /// (no collect). Edit, error, fix, undo, and another edit each give
    /// the cold answer. A const fn a body's array length reads collects
    /// again; so does `unread` once an edit adds such a reader, and
    /// `tls_init`, which a stored check ran (a const overflow there is
    /// the cold error). A build prints what a cold build prints.
    #[test]
    fn unreached_const_fn_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-unread-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, UNREAD).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        // (old, new, expected kept=)
        let steps: &[(&str, &str, &str)] = &[
            ("    x + 1\n", "    let y = x;\n    y + 1\n", "reuse"),
            ("    y + 1\n", "    y + true\n", "reuse"),
            ("    y + true\n", "    y + 1\n", "reuse"),
            ("    let y = x;\n    y + 1\n", "    x + 1\n", "reuse"),
            ("    x + 1\n", "    x * 2 + 1\n", "reuse"),
            ("    2\n}\n\npub const fn tls_init", "    3\n}\n\npub const fn tls_init", "gen_state"),
            ("    9\n", "    let m: u32 = 4294967295;\n    m + 1\n", "gen_state"),
            // The failed reader stored no reads: it rechecks as any failed
            // body does, and collect runs for its discovery.
            ("    let m: u32 = 4294967295;\n    m + 1\n", "    10\n", "discovery"),
            ("    let a = [0u8; local()];\n", "    let a = [0u8; local()];\n    let _b: [u8; 7] = [0u8; unread(3) as usize];\n", "reuse"),
            ("    x * 2 + 1\n", "    x * 2 + 2\n", "gen_state"),
            ("    x * 2 + 2\n", "    x * 2 + 1\n", "gen_state"),
        ];
        for &(old, new, kept) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            assert_eq!(field(&v, "kept"), kept, "{new:?}: {v}");
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Fns whose signatures hold nodes before the body: parameter
    /// patterns, array lengths in parameter and return types, a method's
    /// tuple pattern.
    const SIGS: &str = "pub const N: usize = 2;

pub fn skip(_: &str) -> i64 {
    1
}

pub fn pair((a, b): (i64, i64), [c, _]: [i64; N]) -> i64 {
    a + b + c
}

pub fn first(xs: [u8; 4]) -> [u8; N] {
    [xs[0], xs[1]]
}

pub struct S;

impl S {
    pub fn get(&self, (x, _y): (i64, i64), _: u8) -> i64 {
        x
    }
}

pub fn run() -> i64 {
    skip(\"a\") + pair((1, 2), [3, 4]) + first([1, 2, 3, 4])[1] as i64 + S.get((5, 6), 7)
}
";

    /// A body edit of a fn whose signature holds patterns or array
    /// lengths takes the body patch, and the kept program stands. Edit,
    /// error, fix, undo, and another edit each give the cold answer
    /// (a name the pattern binds, used and then misspelled, too), and a
    /// build prints what a cold build prints.
    #[test]
    fn signature_nodes_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-sigs-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, SIGS).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str)] = &[
            ("    a + b + c\n", "    let d = a * b;\n    d + c\n"),
            ("    d + c\n", "    dd + c\n"),
            ("    dd + c\n", "    d + c + 1\n"),
            ("    let d = a * b;\n    d + c + 1\n", "    a + b + c\n"),
            ("    1\n}\n\npub fn pair", "    let _z: u8 = 3;\n    1\n}\n\npub fn pair"),
            ("    [xs[0], xs[1]]\n", "    [xs[1], xs[0]]\n"),
            ("    [xs[1], xs[0]]\n", "    [xs[1], xs[0], 1]\n"),
            ("    [xs[1], xs[0], 1]\n", "    [xs[1], xs[3]]\n"),
            ("        x\n", "        x + _y\n"),
            ("        x + _y\n", "        x + y\n"),
            ("        x + y\n", "        x * _y\n"),
        ];
        for &(old, new) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            assert_eq!(field(&v, "kept"), "reuse", "{new:?}: {v}");
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A fn with nested fns and a nested const, and a generic fn.
    const NESTED: &str = "pub fn outer(k: i64) -> i64 {
    const B: i64 = 3;
    fn twice(v: i64) -> i64 {
        v * 2
    }
    fn wrap(v: i64) -> Vec<i64> {
        vec![v]
    }
    twice(k) + wrap(B).len() as i64
}

pub fn id<T>(x: T) -> T {
    x
}

pub fn run() -> i64 {
    id(outer(4))
}
";

    /// An edit inside a nested fn's own body takes the body patch (braces
    /// may change there), and the kept program stands while the nested
    /// fn's discovery output does. Edit, error, fix, undo, and another
    /// edit each give the cold answer; a build prints what a cold build
    /// prints.
    #[test]
    fn nested_fn_body_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-nested-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, NESTED).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        // (old, new, expected kept=)
        let steps: &[(&str, &str, &str)] = &[
            ("        v * 2\n", "        let w = v + B;\n        w * 2\n", "reuse"),
            ("        w * 2\n", "        w * true\n", "reuse"),
            ("        w * true\n", "        if w > 0 { w * 2 } else { 0 }\n", "reuse"),
            ("        let w = v + B;\n        if w > 0 { w * 2 } else { 0 }\n", "        v * 2\n", "reuse"),
            ("        vec![v]\n", "        vec![v, v]\n", "reuse"),
            ("        vec![v, v]\n", "        let s: Vec<String> = id(Vec::new());\n        vec![v + s.len() as i64]\n", "discovery"),
            ("        v * 2\n", "        v * 4\n", "reuse"),
        ];
        for &(old, new, kept) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            assert_eq!(field(&v, "kept"), kept, "{new:?}: {v}");
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Const fns whose results reach only const and static values
    /// (`base` through `SCALE`, `pair` through `PAIRS`, `Num::new` through
    /// a `const` block in `NUMS`), a const that patterns match on, and one
    /// whose result reaches an array length (`width`).
    const VALUES: &str = "pub const fn base() -> i64 {
    3
}

pub const fn pair(a: i64) -> (i64, i64) {
    (a, a + 1)
}

pub const fn width() -> usize {
    2
}

pub struct Num(i64);

impl Num {
    pub const fn new(v: i64) -> Num {
        Num(v)
    }
}

pub const SCALE: i64 = base() * 2;
pub static PAIRS: [(i64, i64); 2] = [pair(1), pair(SCALE)];
pub static NUMS: [Num; 2] = [const { Num::new(4) }; 2];
const W: usize = width();

pub fn run() -> i64 {
    let a: [u8; W] = [0; W];
    let k = match PAIRS[1].0 {
        SCALE => 1,
        _ => 2,
    };
    SCALE + PAIRS[1].1 + k + a.len() as i64 + NUMS[1].0
}
";

    /// A body edit of a const fn whose result reaches only const and
    /// static values keeps the program when every value evaluates as
    /// before (kept=reuse). A new value, a const evaluation error, its
    /// fix, and the undo collect again (the collect error keeps the item
    /// state, so the fix patches); one that reaches an array length always
    /// does. Every answer is the cold one, and a build after a
    /// changed value prints what a cold build prints.
    #[test]
    fn revalued_const_fn_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-revalue-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, VALUES).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        // (old, new, expected kept=; "" for any)
        let steps: &[(&str, &str, &str)] = &[
            ("    3\n}\n\npub const fn pair", "    let b = 3;\n    b\n}\n\npub const fn pair", "reuse"),
            ("    (a, a + 1)\n", "    let n = a + 1;\n    (a, n)\n", "reuse"),
            ("    let n = a + 1;\n    (a, n)\n", "    (a, a + 2)\n", "gen_state"),
            ("    (a, a + 2)\n", "    (a, a + 1)\n", "gen_state"),
            // A collect error (const evaluation overflows) keeps the item
            // state: the fix patches too.
            ("    let b = 3;\n    b\n", "    let b: i64 = 9223372036854775807;\n    b + 1\n", "gen_state"),
            ("    let b: i64 = 9223372036854775807;\n    b + 1\n", "    let b = 4;\n    b\n", "gen_state"),
            ("    let b = 4;\n    b\n", "    let b = 4;\n    let _c = 1;\n    b\n", "reuse"),
            // A const block in a static's value evaluates with the value.
            ("        Num(v)\n", "        let w = v;\n        Num(w)\n", "reuse"),
            ("        let w = v;\n        Num(w)\n", "        Num(v + 1)\n", "gen_state"),
            ("    2\n}\n\npub struct Num", "    let w = 2;\n    w\n}\n\npub struct Num", "gen_state"),
        ];
        for &(old, new, kept) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            if !kept.is_empty() {
                assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
                assert_eq!(field(&v, "kept"), kept, "{new:?}: {v}");
            }
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A root file that carries a std splice (it calls a std method the
    /// splice defines, `and_then`) and holds fns of its own.
    const SPLICED_ROOT: &str = "use std::collections::HashMap;

mod m0;
mod m1;

fn count(words: &[&str]) -> usize {
    let mut m: HashMap<&str, usize> = HashMap::new();
    for w in words {
        *m.entry(w).or_insert(0) += 1;
    }
    m.len()
}

fn pick(o: Option<usize>) -> usize {
    o.and_then(|n| n.checked_add(1)).unwrap_or(0)
}

fn main() {
    let t = m0::run() + m1::run() + count(&[\"a\", \"b\", \"a\"]) as i64 + pick(Some(2)) as i64;
    println!(\"{t}\");
}
";

    /// An edit in a fn body of a root file that carries the std splice
    /// takes the body patch: the splice's ranges move with it. Edit,
    /// error, fix, undo, and another edit (one that adds lines, so every
    /// std line moves) each give the cold answer, and a build prints what
    /// a cold build prints.
    #[test]
    fn spliced_root_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-spliced-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        std::fs::write(&root, SPLICED_ROOT).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        assert!(warm.front.patch.as_ref().is_some_and(|b| b.spliced), "the root carries the std splice");
        let steps: &[(&str, &str)] = &[
            ("    m.len()\n", "    let n = m.len();\n    n\n"),
            ("    n\n}", "    n + true\n}"),
            ("    n + true\n}", "    n + 1\n}"),
            ("    let n = m.len();\n    n + 1\n", "    m.len()\n"),
            ("    println!", "    let _u = 1;\n    let _v = 2;\n    println!"),
            ("    m.len()\n", "    m.len() * 2\n"),
        ];
        for &(old, new) in steps {
            let v = warm_equals_cold(&mut warm, &root, &root, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
        }
        assert_eq!(field(&warm.front.last_visits, "kept"), "reuse", "{}", warm.front.last_visits);
        // The splice's positions are a fresh resolve's.
        let mut fresh = Session::new(dir.join("obj-fresh"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut fresh, &root).0, 0);
        let pos = |s: &Session| {
            let b = s.front.patch.as_ref().unwrap();
            (s.front.ast.shipped.clone(), s.front.ast.lang_methods, b.std_ranges.clone(), b.std_methods, b.tables.std_splice_lo, b.tables.std_ranges.clone())
        };
        assert!(pos(&warm) == pos(&fresh), "splice positions after the patches");
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Templates whose bodies hold closures.
    const TEMPLATE_CLOSURES: &str = "pub fn map_get<V: Copy>(m: &[(&str, V)], key: &str) -> Option<V> {
    m.iter().find(|(k, _)| *k == key).map(|e| e.1)
}

pub fn apply<F: Fn(i64) -> i64>(f: F, x: i64) -> i64 {
    let g = |y: i64| f(y) + 1;
    g(x)
}

pub trait Each<K> {
    fn each(&self, f: &mut dyn FnMut(&K));
}

impl Each<i64> for Vec<i64> {
    fn each(&self, f: &mut dyn FnMut(&i64)) {
        for x in self {
            f(x);
        }
    }
}

pub fn count_if<K>(m: &dyn Each<K>, mut keep: impl FnMut(&K) -> bool, mut on_hit: Option<&mut dyn FnMut(&K)>) -> i64 {
    let mut n = 0;
    m.each(&mut |k| {
        if keep(k) {
            n += 1;
            if let Some(h) = on_hit.as_mut() {
                h(k);
            }
        }
    });
    n
}

pub fn run() -> i64 {
    let v: Vec<i64> = vec![1, 2, 3];
    let mut seen = 0;
    let c = count_if(&v, |x| *x > 1, Some(&mut |_k: &i64| seen += 1));
    map_get(&[(\"a\", 1i64)], \"a\").unwrap_or(0) + apply(|v| v * 2, 3) + c + seen
}
";

    /// A body edit of a template with closures keeps the program while
    /// its closures are the registered ones (as many, same kinds and
    /// signatures); another closure, or one of another kind, collects
    /// again. Edit, error, fix, undo, and another edit each give the cold
    /// answer, and a build prints what a cold build prints.
    #[test]
    fn template_closure_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-tclos-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, TEMPLATE_CLOSURES).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        // (old, new, expected kept=; "" for any)
        let steps: &[(&str, &str, &str)] = &[
            ("    m.iter().find", "    let n = m.len();\n    let _ = n;\n    m.iter().find", "reuse"),
            ("*k == key", "*k == 1", ""),
            ("*k == 1", "k.len() == key.len() && *k == key", ""),
            ("k.len() == key.len() && *k == key", "*k == key", "reuse"),
            ("    let g = |y: i64| f(y) + 1;\n", "    let g = |y: i64| f(y) + 2;\n", "reuse"),
            ("    let g = |y: i64| f(y) + 2;\n    g(x)\n", "    let g = |y: i64| f(y) + 2;\n    let h = |z: i64| z;\n    h(g(x))\n", "closures"),
            ("    let h = |z: i64| z;\n    h(g(x))\n", "    g(x)\n", "closures"),
            ("    let mut n = 0;\n    m.each", "    let _z = 1;\n    let mut n = 0;\n    m.each", "reuse"),
            ("    let g = |y: i64| f(y) + 2;\n    g(x)\n", "    let mut n = 0;\n    let mut g = |y: i64| {\n        n += 1;\n        f(y) + n\n    };\n    g(x)\n", "closures"),
        ];
        for &(old, new, kept) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            if !kept.is_empty() {
                assert_eq!(field(&v, "kept"), kept, "{new:?}: {v}");
            }
        }
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module whose fns hold items: a `OnceLock` static, a `LazyLock`
    /// static (its init closure hoists into a hidden fn), and a const and
    /// a fn that reads it.
    const ITEMS: &str = "use std::sync::{LazyLock, OnceLock};

pub fn mode() -> u32 {
    static MODE: OnceLock<u32> = OnceLock::new();
    *MODE.get_or_init(|| 7)
}

pub fn lazy() -> u32 {
    static TABLE: LazyLock<Vec<u32>> = LazyLock::new(|| vec![1, 2, 3]);
    TABLE.len() as u32
}

pub fn nested() -> i64 {
    const K: i64 = 4;
    fn inner(x: i64) -> i64 {
        x + K
    }
    inner(2)
}

pub fn run() -> i64 {
    mode() as i64 + lazy() as i64 + nested()
}
";

    /// An edit around unchanged body items takes the body patch: edit,
    /// error, fix, undo, and another edit each give the cold answer, and a
    /// build prints what a cold build prints. An edit to an item, or one
    /// that moves braces around items, resolves in full.
    #[test]
    fn body_items_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-items-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, ITEMS).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str, bool)] = &[
            ("    *MODE.get_or_init(|| 7)\n", "    let m = *MODE.get_or_init(|| 7);\n    m + 1\n", true),
            ("    m + 1\n", "    m + true\n", true),
            ("    m + true\n", "    m + 1\n", true),
            ("    let m = *MODE.get_or_init(|| 7);\n    m + 1\n", "    *MODE.get_or_init(|| 7)\n", true),
            ("    inner(2)\n", "    inner(3) * K\n", true),
            ("    TABLE.len() as u32\n", "    let n = TABLE.len();\n    n as u32 + 1\n", true),
            // the item itself, or braces around it
            ("    const K: i64 = 4;\n", "    const K: i64 = 5;\n", false),
            ("    static MODE: OnceLock<u32> = OnceLock::new();\n    *MODE.get_or_init(|| 7)\n", "    {\n        static MODE: OnceLock<u32> = OnceLock::new();\n    }\n    7\n", false),
        ];
        for &(old, new, fast) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            if fast {
                assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            }
            // Plain nested fns with no closure: the kept program stands,
            // and its spans are a fresh collect's.
            if new.contains("inner(3)") || new.contains("let n = TABLE.len()") {
                assert_eq!(field(&v, "kept"), "reuse", "{new:?}: {v}");
                let mut fresh = Session::new(dir.join("obj-fresh"), true, SessionKey::synthetic(&root, false));
                assert_eq!(check(&mut fresh, &root).0, 0);
                let (a, b) = (warm.front.kept[0].as_mut().unwrap(), fresh.front.kept[0].as_mut().unwrap());
                assert_eq!(program_spans(&mut a.program), program_spans(&mut b.program), "kept and fresh program spans");
                let _ = std::fs::remove_dir_all(dir.join("obj-fresh"));
            }
        }
        warm_equals_cold(&mut warm, &root, &m1, "    {\n        static MODE: OnceLock<u32> = OnceLock::new();\n    }\n    7\n", "    static MODE: OnceLock<u32> = OnceLock::new();\n    *MODE.get_or_init(|| 7)\n");
        let v = warm_equals_cold(&mut warm, &root, &m1, "    inner(3) * K\n", "    inner(4) * K\n");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module whose fn bodies call pure builtin macros the expander owns.
    const MACROS: &str = "use std::fmt::Write;

#[derive(Clone, Copy)]
pub enum K {
    A,
    B(i64),
}

pub fn is_b(k: K) -> bool {
    matches!(k, K::B(_))
}

pub fn show(k: K) -> String {
    let mut s = String::new();
    write!(s, \"{}\", is_b(k) as i64).unwrap();
    s
}

pub fn run() -> i64 {
    debug_assert!(is_b(K::B(1)));
    show(K::A).len() as i64 + is_b(K::B(2)) as i64
}
";

    /// A body that calls pure builtin macros (`matches!`, `write!`,
    /// `debug_assert!`) takes the body patch: it expands alone. Edit,
    /// error, fix, undo, another edit, and a build all give the cold
    /// answer. A macro that reads a position (`line!`) resolves in full.
    #[test]
    fn pure_macro_edit_matches_cold() {
        let dir = std::env::temp_dir().join(format!("lust-macros-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, MACROS).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let steps: &[(&str, &str, bool)] = &[
            ("    matches!(k, K::B(_))\n", "    let b = matches!(k, K::B(x) if x > 0);\n    b\n", true),
            ("    b\n", "    b + 1\n", true),
            ("    b + 1\n", "    b\n", true),
            ("    let b = matches!(k, K::B(x) if x > 0);\n    b\n", "    matches!(k, K::B(_))\n", true),
            ("    write!(s, \"{}\", is_b(k) as i64).unwrap();\n", "    writeln!(s, \"{} {}\", is_b(k) as i64, 2).unwrap();\n", true),
            ("    debug_assert!(is_b(K::B(1)));\n", "    debug_assert_eq!(is_b(K::B(1)), true);\n", true),
            ("    debug_assert_eq!(is_b(K::B(1)), true);\n", "    debug_assert_eq!(is_b(K::B(1)), true, \"at {}\", line!());\n", false),
            ("    debug_assert_eq!(is_b(K::B(1)), true, \"at {}\", line!());\n", "    debug_assert_eq!(is_b(K::B(1)), true);\n", false),
        ];
        for &(old, new, fast) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            if fast {
                assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            }
        }
        let v = warm_equals_cold(&mut warm, &root, &m1, "    s\n}", "    let t = matches!(s.len(), 1 | 2);\n    if t { s } else { String::new() }\n}");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        // cfg! and a cfg'd statement expand with the crate cfg; an unknown
        // cfg name is the cold error.
        let steps: &[(&str, &str, bool)] = &[
            ("    let mut s = String::new();\n", "    let mut s = String::new();\n    if cfg!(windows) {\n        s.push('w');\n    }\n", true),
            ("        s.push('w');\n", "        s.push('v');\n", true),
            ("    let mut s = String::new();\n", "    let mut s = String::new();\n    #[cfg(test)]\n    let _t = 1;\n", true),
            ("    let _t = 1;\n", "    let _t = 2;\n", true),
            ("cfg!(windows)", "cfg!(lust_no_such_name)", false),
            ("cfg!(lust_no_such_name)", "cfg!(windows)", false),
        ];
        for &(old, new, fast) in steps {
            let v = warm_equals_cold(&mut warm, &root, &m1, old, new);
            if fast {
                assert_eq!(field(&v, "path"), "patch", "{new:?}: {v}");
            }
        }
        // A user macro of another name: bodies that call builtins patch.
        let dbl = "macro_rules! dbl {\n    ($e:expr) => {\n        $e * 2\n    };\n}\n\npub fn d() -> i64 {\n    dbl!(1)\n}\n\n";
        warm_equals_cold(&mut warm, &root, &m1, "pub fn is_b(", &format!("{dbl}pub fn is_b("));
        let v = warm_equals_cold(&mut warm, &root, &m1, "    matches!(k, K::B(_))\n", "    matches!(k, K::B(1))\n");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        // A user macro named like a builtin: the expander may pick it.
        let own = "macro_rules! matches {\n    ($($t:tt)*) => {\n        false\n    };\n}\n\n";
        warm_equals_cold(&mut warm, &root, &m1, "pub fn d()", &format!("{own}pub fn d()"));
        let v = warm_equals_cold(&mut warm, &root, &m1, "    matches!(k, K::B(1))\n", "    matches!(k, K::B(2))\n");
        assert_eq!(field(&v, "path"), "resolve", "{v}");
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A module with nested statics in two fns and a generic fn.
    const STATICS: &str = "use std::sync::atomic::{AtomicI64, Ordering};

pub fn bump() -> i64 {
    static N: AtomicI64 = AtomicI64::new(10);
    N.fetch_add(1, Ordering::Relaxed)
}

pub fn twice<T: Copy>(x: T) -> (T, T) {
    (x, x)
}

pub fn base() -> i64 {
    static B: AtomicI64 = AtomicI64::new(5);
    B.load(Ordering::Relaxed)
}

pub fn run() -> i64 {
    let (a, b) = twice(bump());
    a + b + base()
}
";

    /// A full resolve (a signature edit) in a crate whose fns hold statics
    /// keeps generic reuse while the statics keep their indexes: few
    /// bodies check. A new static before the others moves their indexes:
    /// collect runs again without reuse, and a build prints what a cold
    /// build prints.
    #[test]
    fn full_resolve_keeps_reuse_while_statics_stand() {
        let dir = std::env::temp_dir().join(format!("lust-statics-{}", std::process::id()));
        let root = write_crate(&dir, 2);
        let m1 = dir.join("m1.rs");
        std::fs::write(&m1, STATICS).unwrap();
        let mut warm = Session::new(dir.join("obj"), true, SessionKey::synthetic(&root, false));
        assert_eq!(check(&mut warm, &root).0, 0);
        let all: usize = field(&warm.front.last_visits, "checked").parse().unwrap();
        let v = warm_equals_cold(&mut warm, &root, &m1, "pub fn base() -> i64 {", "pub fn base() -> i64 {\n    let _k = 1;");
        assert_eq!(field(&v, "path"), "patch", "{v}");
        let v = warm_equals_cold(&mut warm, &root, &m1, "pub fn twice<T: Copy>(x: T) -> (T, T) {", "pub fn twice<T: Copy + Clone>(x: T) -> (T, T) {");
        assert_eq!(field(&v, "path"), "resolve", "{v}");
        let checked: usize = field(&v, "checked").parse().unwrap();
        assert!(checked < all, "a signature edit checks {checked} of {all} bodies: {v}");
        // A static before the others, in a new fn.
        warm_equals_cold(&mut warm, &root, &m1, "pub fn bump() -> i64 {", "pub fn first() -> i64 {\n    static F: AtomicI64 = AtomicI64::new(100);\n    F.load(Ordering::Relaxed)\n}\n\npub fn bump() -> i64 {");
        warm_equals_cold(&mut warm, &root, &m1, "    a + b + base()\n", "    a + b + base() + first()\n");
        assert_eq!(run(&mut warm, &root, Cmd::Build).0, 0);
        let bin = root.with_extension("bin");
        let out = run_bin(&bin);
        let mut cold = Session::new(dir.join("obj-cold-b"), false, SessionKey::synthetic(&root, false));
        assert_eq!(run(&mut cold, &root, Cmd::Build).0, 0);
        assert_eq!(out, run_bin(&bin), "warm and cold builds print the same");
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The shadow scans: a macro defined or imported under a builtin's
    /// name counts; prose and casts do not.
    #[test]
    fn shadow_scans() {
        use super::{shadows_builtin, shadows_parser_macro};
        assert!(shadows_parser_macro("use a::m as vec;"));
        assert!(shadows_parser_macro("macro_rules! println { () => {} }"));
        assert!(shadows_builtin("use a::{m as matches, n};"));
        assert!(shadows_builtin("macro_rules! write { () => {} }"));
        assert!(shadows_builtin("macro_rules! $name { () => {} }"));
        assert!(!shadows_builtin("($value as $repr);"));
        assert!(!shadows_builtin("// treated as line terminators."));
        assert!(!shadows_builtin("let x = y as u8;"));
        assert!(!shadows_builtin("macro_rules! dbl { () => {} }"));
    }
}
