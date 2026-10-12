// The compile pipeline, cold or incremental.
//
// A `Session` keeps everything an edit can reuse: the AST, per-function body hashes, generated C,
// glue, and object files. `lust daemon` keeps one session per file alive between requests; a plain
// `lust check` uses a fresh session once.
//
// Incremental rules, from cheapest to most expensive:
//   1. Only function bodies changed (same environment hash: all tokens outside bodies): re-parse,
//      re-check, and re-generate only those functions.
//   2. Only top-level functions were added, removed, or changed signature (all other items the
//      same): re-parse the file, but re-check and re-generate only the changed functions and the
//      bodies that mention their names.
//   3. Anything else (a type, an impl, a use changed): full rebuild.
use crate::ast::{Ast, ItemKind};
use crate::cgen::{self, FnOut, GlueSet};
use crate::collect::{self, FnId};
use crate::diag::{self, Diag, LineIndex};
use crate::intern::{FxMap, Interner, Known, Sym};
use crate::lexer::{self, Lexed};
use crate::scan;
use crate::{borrowck, check, ir, lower, parser};
use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

pub use crate::protocol::{Cmd, Request, Response};

/// Parsed program state. Owned separately from the caches so both can be borrowed at once.
struct Front {
    interner: Interner,
    known: Known,
    ast: Ast,
    /// `None` until the first successful parse.
    env_hash: Option<u64>,
    /// Top-level items of the last parse (to see which items an edit changed).
    items: Vec<scan::ItemScan>,
    /// Where each FnId's definition lives: item index, and index inside an impl block.
    fn_loc: Vec<(usize, Option<usize>)>,
    /// Each FnId's slot. A slot is a function's stable identity across edits (FnIds shift when
    /// functions are added); cached code, objects, and the C function table all use slots.
    fn_slot: Vec<u32>,
    slot_of: FxMap<(Sym, Sym), u32>,
    /// Body hash per slot, at the last parse.
    slot_hash: Vec<u64>,
    /// Lexed and scanned chunks from the last request, reused when their text is unchanged.
    chunks: Vec<Chunk>,
    /// The source and line index of the last request, to find what an edit changed.
    src: String,
    lines: LineIndex,
    /// The chunk-boundary mask (see `split_items`). Fixed for the session, so boundaries are too.
    split_mask: Option<u64>,
}

struct Chunk {
    /// Byte range of the chunk in the current source.
    start: usize,
    text: String,
    lexed: Lexed,
    /// The `start` the tokens were lexed at. Token spans are absolute, so they are only exact
    /// while this equals `start`.
    lexed_start: usize,
    scan: scan::ChunkScan,
    /// This chunk's items in `front.ast.items`, or None if it has not been parsed yet.
    items: Option<std::ops::Range<usize>>,
}

/// Per-slot results and build state.
struct Caches {
    /// The last check of this function passed.
    ok: Vec<bool>,
    out: Vec<FnOut>,
    has_out: Vec<bool>,
    glue: GlueSet,
    /// Slots per function unit. Fixed until the next full rebuild, so units stay stable.
    per_unit: usize,
    /// Slot capacity of `lust_fns` in libbase.so, and how many function units it has.
    table_cap: usize,
    base_units: usize,
    obj_dir: PathBuf,
    /// Units compiled into `obj_dir` with the current layout, and with which debug setting.
    objects: Option<bool>,
    /// A daemon session builds against libbase.so; a one-shot session links statically.
    persistent: bool,
    /// Units whose current code is in an overlay object, not in libbase.so.
    overlays: std::collections::BTreeSet<usize>,
}

pub struct Session {
    front: Front,
    caches: Caches,
}

impl Session {
    pub fn new(obj_dir: PathBuf, persistent: bool) -> Session {
        let interner = Interner::default();
        let known = Known::new(&interner);
        Session {
            front: Front {
                interner,
                known,
                ast: Ast::default(),
                env_hash: None,
                items: Vec::new(),
                fn_loc: Vec::new(),
                fn_slot: Vec::new(),
                slot_of: FxMap::default(),
                slot_hash: Vec::new(),
                chunks: Vec::new(),
                src: String::new(),
                lines: LineIndex::new(""),
                split_mask: None,
            },
            caches: Caches {
                ok: Vec::new(),
                out: Vec::new(),
                has_out: Vec::new(),
                glue: GlueSet::default(),
                per_unit: 16,
                table_cap: 0,
                base_units: 0,
                obj_dir,
                objects: None,
                persistent,
                overlays: Default::default(),
            },
        }
    }
    pub fn obj_dir(&self) -> &Path {
        &self.caches.obj_dir
    }
}

/// Wall time per stage.
struct Timer {
    stages: Vec<(&'static str, f64)>,
    last: Instant,
    start: Instant,
}

impl Timer {
    fn new() -> Timer {
        let now = Instant::now();
        Timer { stages: Vec::new(), last: now, start: now }
    }
    fn lap(&mut self, name: &'static str) {
        let now = Instant::now();
        self.stages.push((name, (now - self.last).as_secs_f64() * 1e3));
        self.last = now;
    }
    fn render(&self, out: &mut String) {
        for (name, ms) in &self.stages {
            let _ = writeln!(out, "  {name:<24} {ms:>9.2} ms");
        }
        let _ = writeln!(out, "  {:<24} {:>9.2} ms", "total", self.start.elapsed().as_secs_f64() * 1e3);
    }
}

/// Runs `f` for each item on all cores. Results keep the input order.
pub fn par_map<T: Sync, R: Send>(items: &[T], f: impl Fn(&T) -> R + Sync) -> Vec<R> {
    let cores = std::thread::available_parallelism().map_or(4, |n| n.get());
    let n = std::env::var("LUST_THREADS").ok().and_then(|v| v.parse().ok()).unwrap_or(cores).min(items.len().max(1));
    if n <= 1 {
        return items.iter().map(f).collect();
    }
    let next = AtomicUsize::new(0);
    // Batches amortize the atomic counter, but stay small enough to keep every thread busy.
    let batch = (items.len() / (n * 8)).clamp(1, 16);
    let chunks: Vec<Vec<(usize, R)>> = std::thread::scope(|s| {
        let handles: Vec<_> = (0..n)
            .map(|_| {
                s.spawn(|| {
                    let mut out = Vec::new();
                    loop {
                        let start = next.fetch_add(batch, Ordering::Relaxed);
                        if start >= items.len() {
                            break;
                        }
                        let end = (start + batch).min(items.len());
                        out.extend(items[start..end].iter().enumerate().map(|(k, item)| (start + k, f(item))));
                    }
                    out
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut all: Vec<Option<R>> = (0..items.len()).map(|_| None).collect();
    for chunk in chunks {
        for (i, r) in chunk {
            all[i] = Some(r);
        }
    }
    all.into_iter().map(|r| r.unwrap()).collect()
}

/// Splits source into chunks of whole top-level items, about `2 * cores` of them. Boundaries are
/// content-defined: the chunk is cut before an item when a hash of the item's header line hits a
/// mask. So editing or inserting an item only changes the chunk it is in, and every other chunk
/// keeps its exact text (and can be reused). A chunk only starts at a line that begins an item at
/// column 0, and never between an attribute and its item. `headers`, when given, are the
/// `item_headers` of the whole source (used on a session's first compile, where the region is
/// the whole source and the mask needed the same table).
fn split_items(src: &str, region: std::ops::Range<usize>, mask: u64, headers: Option<&[(usize, u64)]>) -> Vec<(usize, usize)> {
    let mut ranges = Vec::new();
    let mut chunk_start = region.start;
    let cut = |at: usize, h: u64, ranges: &mut Vec<(usize, usize)>, chunk_start: &mut usize| {
        // The multiply spreads FxHash's low bits.
        if (h.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 40) & mask == 0 {
            ranges.push((*chunk_start, region.start + at));
            *chunk_start = region.start + at;
        }
    };
    match headers {
        Some(headers) => {
            for &(at, h) in headers.iter().skip(1) {
                cut(at, h, &mut ranges, &mut chunk_start);
            }
        }
        None => {
            for (at, h) in item_headers(&src[region.clone()]).into_iter().skip(1) {
                cut(at, h, &mut ranges, &mut chunk_start);
            }
        }
    }
    ranges.push((chunk_start, region.end));
    ranges
}

/// The mask that makes `split_items` produce about `2 * cores` chunks for a source with
/// `item_count` top-level items.
fn split_mask(src_len: usize, item_count: usize, cores: usize) -> u64 {
    if src_len < 64 * 1024 {
        // Small files: one chunk (no item hash has all 24 masked bits zero in practice).
        return (1 << 24) - 1;
    }
    ((item_count / (cores * 2)).max(1).next_power_of_two() - 1) as u64
}

/// (offset of each top-level item's first line, hash of its header line), skipping attributes.
fn item_headers(src: &str) -> Vec<(usize, u64)> {
    let starts = ["fn ", "pub ", "struct ", "enum ", "impl ", "#[", "use "];
    let mut items = Vec::new();
    let mut prev_attr = false;
    let mut pending: Option<usize> = None;
    let mut pos = 0;
    for line in src.split_inclusive('\n') {
        let is_attr = line.starts_with("#[");
        if starts.iter().any(|s| line.starts_with(s)) && !prev_attr {
            pending = Some(pos);
        }
        if let Some(at) = pending
            && !is_attr
        {
            let mut h = crate::intern::FxHasher::default();
            std::hash::Hash::hash(line, &mut h);
            items.push((at, std::hash::Hasher::finish(&h)));
            pending = None;
        }
        if !line.trim().is_empty() {
            prev_attr = is_attr;
        }
        pos += line.len();
    }
    items
}

/// Lengths of the common prefix and common suffix of two strings (not overlapping).
fn common_ends(a: &[u8], b: &[u8]) -> (usize, usize) {
    // Compare in blocks first: slice equality is a fast memcmp.
    let n = a.len().min(b.len());
    let mut p = 0;
    while p + 4096 <= n && a[p..p + 4096] == b[p..p + 4096] {
        p += 4096;
    }
    while p < n && a[p] == b[p] {
        p += 1;
    }
    let max_s = n - p;
    let mut q = 0;
    while q + 4096 <= max_s && a[a.len() - q - 4096..a.len() - q] == b[b.len() - q - 4096..b.len() - q] {
        q += 4096;
    }
    while q < max_s && a[a.len() - q - 1] == b[b.len() - q - 1] {
        q += 1;
    }
    (p, q)
}

fn errors(diags: &mut [Diag], path: &str, src: &str, req: &Request) -> Response {
    let json = req.json;
    let text = diag::render(diags, path, src, json, req.max_errors);
    let mut r = Response { code: 1, ..Default::default() };
    if json {
        r.stdout = text;
    } else {
        r.stderr = text;
        let _ = writeln!(r.stderr, "error: could not compile `{path}` due to {} previous error(s)", diags.len());
    }
    r
}

/// After a parse that was not "bodies only": update item tables, assign slots by name, and pick the
/// functions to re-check. Returns their FnIds.
#[allow(clippy::too_many_arguments)]
fn slot_update(
    front: &mut Front,
    caches: &mut Caches,
    item_scans: Vec<scan::ItemScan>,
    env: u64,
    changed_names: Option<Vec<Sym>>,
    fn_at: &[(usize, usize)],
    cores: usize,
    scan_of: &dyn Fn(&Front, usize) -> (u64, u32),
    t: &mut Timer,
) -> Vec<usize> {
    let fn_count = fn_at.len();
    front.fn_loc = fn_locations(&front.ast);
    front.env_hash = Some(env);
    front.items = item_scans;
    if changed_names.is_none() {
        // Full rebuild: fresh slots in FnId order, and empty caches.
        front.slot_of.clear();
        caches.ok.clear();
        caches.out.clear();
        caches.has_out.clear();
        front.slot_hash.clear();
        caches.glue = GlueSet::default();
        caches.objects = None;
        caches.overlays.clear();
        // Cold builds gain nothing from many small units: each extra unit pays a tcc process
        // start and a header parse. Use about one unit per core. The daemon keeps small
        // units, so an edit recompiles little code.
        caches.per_unit =
            if caches.persistent { (fn_count / (cores * 4)).clamp(16, 256) } else { (fn_count / cores.max(1)).clamp(64, 512) };
    }
    // Assign slots by name. New functions get new slots; a removed function's slot is emptied.
    let keys = fn_keys(&front.ast, &front.fn_loc);
    let mut live = vec![false; front.slot_of.len()];
    front.fn_slot = keys
        .iter()
        .map(|k| {
            let next = front.slot_of.len() as u32;
            let slot = *front.slot_of.entry(*k).or_insert(next);
            if slot as usize >= live.len() {
                live.resize(slot as usize + 1, false);
            }
            live[slot as usize] = true;
            slot
        })
        .collect();
    let n_slots = front.slot_of.len();
    caches.ok.resize(n_slots, false);
    caches.has_out.resize(n_slots, false);
    caches.out.resize_with(n_slots, FnOut::default);
    front.slot_hash.resize(n_slots, 0);
    for slot in (0..n_slots).filter(|&s| !live[s]) {
        caches.out[slot] = FnOut::default();
        caches.has_out[slot] = true;
        caches.ok[slot] = true;
    }
    // Re-check a function if its body changed, or it is new, or its body mentions a changed
    // function's name (only possible in the "signatures" case).
    let names = changed_names.unwrap_or_default();
    let mut changed = Vec::new();
    for i in 0..fn_count {
        let slot = front.fn_slot[i] as usize;
        let (hash, _) = scan_of(front, i);
        let idents = &front.chunks[fn_at[i].0].scan.body_idents[fn_at[i].1];
        let mentions = idents.iter().any(|s| names.contains(s)) || keys[i].0 == Sym(u32::MAX) && names.contains(&keys[i].1);
        if front.slot_hash[slot] != hash || !caches.ok[slot] || mentions {
            front.slot_hash[slot] = hash;
            caches.has_out[slot] = false;
            changed.push(i);
        }
    }
    t.lap(if names.is_empty() { "parse (par)" } else { "parse changed chunks" });
    changed
}

/// Function names whose signature changed, or that were added or removed, if those are the only
/// changes between two item lists. None if anything else changed.
fn fn_only_changes(old: &[scan::ItemScan], new: &[scan::ItemScan]) -> Option<Vec<Sym>> {
    let others = |items: &[scan::ItemScan]| items.iter().filter(|i| i.fn_name.is_none()).map(|i| i.hash).collect::<Vec<_>>();
    if others(old) != others(new) {
        return None;
    }
    let fns = |items: &[scan::ItemScan]| items.iter().filter_map(|i| i.fn_name.map(|n| (n, i.hash))).collect::<FxMap<Sym, u64>>();
    let (a, b) = (fns(old), fns(new));
    let mut names: Vec<Sym> = a.iter().filter(|(n, h)| b.get(*n) != Some(*h)).map(|(n, _)| *n).collect();
    names.extend(b.keys().filter(|n| !a.contains_key(*n)));
    names.sort_unstable();
    names.dedup();
    Some(names)
}

/// A function's stable name: (impl type name, function name). Top-level functions use
/// `Sym(u32::MAX)` for the type.
fn fn_keys(ast: &Ast, fn_loc: &[(usize, Option<usize>)]) -> Vec<(Sym, Sym)> {
    fn_loc
        .iter()
        .map(|&(item, sub)| match (&ast.items[item].kind, sub) {
            (ItemKind::Fn(d), None) => (Sym(u32::MAX), d.name),
            (ItemKind::Impl(imp), Some(k)) => {
                let owner = match ast.ty(imp.self_ty) {
                    crate::ast::TyExpr::Path(segs) => segs[0].name,
                    _ => Sym(u32::MAX - 1),
                };
                (owner, imp.fns[k].name)
            }
            _ => unreachable!("fn_loc points at a function"),
        })
        .collect()
}

/// FnId order: top-level functions and impl methods, in item order. Same as `collect`.
fn fn_locations(ast: &Ast) -> Vec<(usize, Option<usize>)> {
    let mut out = Vec::new();
    for (i, item) in ast.items.iter().enumerate() {
        match &item.kind {
            ItemKind::Fn(_) => out.push((i, None)),
            ItemKind::Impl(imp) => out.extend((0..imp.fns.len()).map(|k| (i, Some(k)))),
            _ => {}
        }
    }
    out
}

/// Compiles one request, reusing whatever `session` holds.
pub fn compile(req: &Request, session: &mut Session) -> Response {
    let mut t = Timer::new();
    let path = req.file.to_string_lossy().to_string();
    let src = match std::fs::read_to_string(&req.file) {
        Ok(s) => s,
        Err(e) => return Response { stderr: format!("error: cannot read {path}: {e}\n"), code: 2, ..Default::default() },
    };
    let Session { front, caches } = session;
    t.lap("read");

    // Lex and scan in chunks of whole items, in parallel. Only the region an edit touched is
    // split and lexed again: chunks entirely before it are kept as they are, and chunks entirely
    // after it are kept with shifted offsets.
    let cores = std::thread::available_parallelism().map_or(4, |n| n.get());
    // On the first compile the mask needs the item header table, and so does the split below
    // (the region is then the whole source). Compute it once. It cost a full serial source
    // scan, about 2 ms on a 48k-line file (front-end probe, milestone 2).
    let mut fresh_headers: Option<Vec<(usize, u64)>> = None;
    let mask = match front.split_mask {
        Some(m) => m,
        None => {
            let headers = item_headers(&src);
            let m = split_mask(src.len(), headers.len(), cores);
            fresh_headers = Some(headers);
            front.split_mask = Some(m);
            m
        }
    };
    let old_len = front.src.len();
    let (prefix, suffix) = common_ends(front.src.as_bytes(), src.as_bytes());
    let delta = src.len() as i64 - old_len as i64;
    let mut kept_front = Vec::new();
    let mut kept_back = Vec::new();
    for c in std::mem::take(&mut front.chunks) {
        if c.start + c.text.len() <= prefix {
            kept_front.push(c);
        } else if c.start >= old_len - suffix && suffix > 0 {
            kept_back.push(c);
        }
    }
    let region_start = kept_front.last().map_or(0, |c| c.start + c.text.len());
    let region_end_old = kept_back.first().map_or(old_len, |c| c.start);
    let region_end = (region_end_old as i64 + delta) as usize;
    let lines = if old_len == 0 { LineIndex::new(&src) } else { front.lines.splice(&src, region_start, region_end_old, region_end) };
    let mut ranges: Vec<(usize, usize)> = kept_front.iter().map(|c| (c.start, c.start + c.text.len())).collect();
    let headers = if region_start == 0 && region_end == src.len() { fresh_headers.as_deref() } else { None };
    let middle = if region_start < region_end { split_items(&src, region_start..region_end, mask, headers) } else { Vec::new() };
    ranges.extend(middle.iter().copied());
    ranges.extend(kept_back.iter().map(|c| ((c.start as i64 + delta) as usize, (c.start as i64 + delta) as usize + c.text.len())));
    let mut reused: Vec<Option<Chunk>> =
        kept_front.into_iter().map(Some).chain(middle.iter().map(|_| None)).chain(kept_back.into_iter().map(Some)).collect();
    let need: Vec<usize> = (0..ranges.len()).filter(|&i| reused[i].is_none()).collect();
    let fresh = par_map(&need, |&i| {
        let (a, b) = ranges[i];
        lexer::lex(&src[a..b], a as u32, &front.interner).map(|l| {
            let sc = scan::scan(&l);
            (l, sc)
        })
    });
    if fresh.iter().any(|l| l.is_err()) {
        // Re-lex serially so the error never depends on the split.
        if let Err(d) = lexer::lex(&src, 0, &front.interner) {
            return errors(&mut [d], &path, &src, req);
        }
    }
    let mut fresh = need.iter().zip(fresh).map(|(&i, r)| (i, r.unwrap())).collect::<Vec<_>>().into_iter();
    let mut next_fresh = fresh.next();
    for (i, &(a, b)) in ranges.iter().enumerate() {
        let chunk = match reused[i].take() {
            Some(mut c) => {
                // Same text at a new position: shift the function offsets.
                let delta = a as i64 - c.start as i64;
                for f in &mut c.scan.fns {
                    f.fn_offset = (f.fn_offset as i64 + delta) as u32;
                }
                c.start = a;
                c
            }
            None => {
                let (_, (lexed, sc)) = next_fresh.take().unwrap();
                next_fresh = fresh.next();
                Chunk { start: a, text: src[a..b].to_string(), lexed, lexed_start: a, scan: sc, items: None }
            }
        };
        front.chunks.push(chunk);
    }
    let item_scans: Vec<scan::ItemScan> = front.chunks.iter().flat_map(|c| c.scan.items.iter().copied()).collect();
    let env = scan::env_hash(item_scans.iter());
    let fn_count = front.chunks.iter().map(|c| c.scan.fns.len()).sum::<usize>();
    // (chunk, index in chunk) for every function, in FnId order.
    let fn_at: Vec<(usize, usize)> =
        front.chunks.iter().enumerate().flat_map(|(c, ch)| (0..ch.scan.fns.len()).map(move |k| (c, k))).collect();
    let scan_of = |front: &Front, i: usize| -> (u64, u32) {
        let f = &front.chunks[fn_at[i].0].scan.fns[fn_at[i].1];
        (f.body_hash, lines.line_col(f.fn_offset).0)
    };
    t.lap(if need.len() == ranges.len() { "lex+scan (par)" } else { "lex+scan changed chunks" });
    front.src.clone_from(&src);
    front.lines = lines.clone();

    // Which rule applies (see the top of this file).
    let bodies_only = front.env_hash == Some(env) && front.fn_slot.len() == fn_count;
    let changed_names = if bodies_only || front.env_hash.is_none() { None } else { fn_only_changes(&front.items, &item_scans) };
    let mode = if bodies_only {
        "bodies"
    } else if changed_names.is_some() {
        "signatures"
    } else {
        "full"
    };

    let changed: Vec<usize> = if bodies_only {
        let changed: Vec<usize> = (0..fn_count)
            .filter(|&i| {
                let slot = front.fn_slot[i] as usize;
                front.slot_hash[slot] != scan_of(front, i).0 || !caches.ok[slot]
            })
            .collect();
        for &i in &changed {
            // A changed body is in a changed chunk, so its tokens are freshly lexed.
            let chunk = &front.chunks[fn_at[i].0];
            let f = &chunk.scan.fns[fn_at[i].1];
            let toks = &chunk.lexed.tokens[f.body.clone()];
            let slot = front.fn_slot[i] as usize;
            front.slot_hash[slot] = f.body_hash;
            caches.has_out[slot] = false;
            match parser::parse_body(toks, &chunk.lexed.strings, &mut front.ast, &front.interner, &front.known) {
                Ok((body, exprs, pats)) => {
                    let (item, sub) = front.fn_loc[i];
                    let def = match (&mut front.ast.items[item].kind, sub) {
                        (ItemKind::Fn(d), None) => d,
                        (ItemKind::Impl(imp), Some(k)) => &mut imp.fns[k],
                        _ => unreachable!("fn_loc out of date"),
                    };
                    def.body = body;
                    def.exprs = exprs;
                    def.pats = pats;
                }
                Err(d) => {
                    caches.ok[slot] = false;
                    return errors(&mut [d], &path, &src, req);
                }
            }
        }
        t.lap("parse changed bodies");
        changed
    } else if changed_names.is_some() {
        // Only top-level functions changed: parse just the chunks with new text, and splice their
        // items between the unchanged chunks' items.
        let todo: Vec<usize> = (0..front.chunks.len()).filter(|&i| front.chunks[i].items.is_none()).collect();
        let parsed = par_map(&todo, |&i| parser::parse(&front.chunks[i].lexed, &front.interner, &front.known));
        if let Some(Err(d)) = parsed.iter().find(|p| p.is_err()) {
            let d = d.clone();
            return errors(&mut [d], &path, &src, req);
        }
        let mut new_asts: FxMap<usize, Ast> = todo.iter().copied().zip(parsed.into_iter().map(|p| p.unwrap())).collect();
        let mut old_items: Vec<Option<crate::ast::Item>> = std::mem::take(&mut front.ast.items).into_iter().map(Some).collect();
        let mut items = Vec::with_capacity(old_items.len());
        for c in 0..front.chunks.len() {
            let start = items.len();
            match new_asts.remove(&c) {
                Some(ast) => items.extend(front.ast.append_chunk(ast)),
                None => items.extend(front.chunks[c].items.clone().unwrap().map(|k| old_items[k].take().unwrap())),
            }
            front.chunks[c].items = Some(start..items.len());
        }
        front.ast.items = items;
        slot_update(front, caches, item_scans, env, changed_names, &fn_at, cores, &scan_of, &mut t)
    } else {
        // Reused chunks that moved have stale token spans: lex them again before a full parse.
        let stale: Vec<usize> = (0..front.chunks.len()).filter(|&i| front.chunks[i].lexed_start != front.chunks[i].start).collect();
        let relexed = par_map(&stale, |&i| lexer::lex(&front.chunks[i].text, front.chunks[i].start as u32, &front.interner));
        for (&i, l) in stale.iter().zip(relexed) {
            front.chunks[i].lexed = l.expect("this text lexed before");
            front.chunks[i].lexed_start = front.chunks[i].start;
        }
        let parsed = par_map(&front.chunks, |c| parser::parse(&c.lexed, &front.interner, &front.known));
        let ast = if parsed.iter().all(|p| p.is_ok()) {
            let mut start = 0;
            for (c, p) in front.chunks.iter_mut().zip(&parsed) {
                let n = p.as_ref().unwrap().items.len();
                c.items = Some(start..start + n);
                start += n;
            }
            Ast::concat(parsed.into_iter().map(|p| p.unwrap()).collect())
        } else {
            // Re-parse serially for an exact error.
            let whole = lexer::lex(&src, 0, &front.interner).expect("lexed before");
            match parser::parse(&whole, &front.interner, &front.known) {
                Ok(a) => a,
                Err(d) => {
                    front.env_hash = None;
                    return errors(&mut [d], &path, &src, req);
                }
            }
        };
        front.ast = ast;
        slot_update(front, caches, item_scans, env, None, &fn_at, cores, &scan_of, &mut t)
    };

    let program = match collect::collect(&front.ast, &front.interner, &front.known) {
        Ok(p) => p,
        Err(mut ds) => {
            front.env_hash = None;
            return errors(&mut ds, &path, &src, req);
        }
    };
    if program.fns.len() != fn_count {
        // The scanner and the parser disagree (only possible with unusual syntax). Start over.
        front.env_hash = None;
        return Response { stderr: "error: internal: function count mismatch; run again\n".into(), code: 3, ..Default::default() };
    }
    t.lap("collect");

    // Front end for the functions that need it. A build also needs IR for functions with no C yet.
    let slot = |i: usize| front.fn_slot[i] as usize;
    let mut work = changed.clone();
    if req.cmd == Cmd::Build {
        work.extend((0..program.fns.len()).filter(|&i| !caches.has_out[slot(i)] && !changed.contains(&i)));
    }
    let results = par_map(&work, |&i| {
        let f = FnId(i as u32);
        let (checked, mut errs) = check::check_fn(&program, f);
        if !errs.is_empty() {
            return (None, errs);
        }
        let body = lower::lower(&program, f, checked);
        errs.extend(borrowck::borrowck(&program, &body));
        (Some(body), errs)
    });
    let mut diags: Vec<Diag> = Vec::new();
    for (k, &i) in work.iter().enumerate() {
        caches.ok[slot(i)] = results[k].1.is_empty();
        diags.extend(results[k].1.iter().cloned());
    }
    // A lust file is a bin crate, so check needs `main` too, as `rustc --emit=metadata`
    // does. `lust test` sets `harness`: it adds a generated `main` after this check.
    if !req.harness && program.main.is_none() {
        diags.push(Diag::new("L0130", diag::Span::default(), "no `main` function", "Add `fn main() { ... }`."));
    }
    t.lap(if mode == "full" { "check+borrowck (par)" } else { "check changed fns (par)" });
    // A one-shot (non-persistent) process exits right after this call. Freeing the IR and
    // program arenas, mostly built on worker threads, costs about 10 ms on a 31k-line crate,
    // so leak them on every return below and let the OS reclaim the memory at exit.
    let leak_at_exit = !caches.persistent;
    if !diags.is_empty() {
        let resp = errors(&mut diags, &path, &src, req);
        if leak_at_exit {
            std::mem::forget(results);
            std::mem::forget(program);
        }
        return resp;
    }
    let mut resp = Response::default();
    if req.cmd == Cmd::Check {
        if req.timings {
            let _ = writeln!(resp.stderr, "lust check {path}: ok ({} functions, {mode}: {} rechecked)", program.fns.len(), work.len());
            t.render(&mut resp.stderr);
        }
        if leak_at_exit {
            std::mem::forget(results);
            std::mem::forget(program);
        }
        return resp;
    }

    // Codegen for the work set.
    let bodies: Vec<(usize, ir::Body)> = work.iter().copied().zip(results).filter_map(|(i, r)| r.0.map(|b| (i, b))).collect();
    let outs = par_map(&bodies, |(i, b)| cgen::gen_fn(&program, b, &lines, scan_of(front, *i).1, &front.fn_slot));
    let n_slots = caches.out.len();
    let groups = cgen::group_fns(n_slots, caches.per_unit);
    let mut dirty_groups = vec![false; groups.len()];
    for ((i, _), out) in bodies.iter().zip(outs) {
        caches.out[slot(*i)] = out;
        caches.has_out[slot(*i)] = true;
        dirty_groups[slot(*i) / caches.per_unit] = true;
    }
    let glue_changed = caches.glue.add(&program, bodies.iter().flat_map(|(i, _)| caches.out[slot(*i)].glue.iter()));
    t.lap("codegen (par)");

    // Units: 0 = main (always rebuilt), 1 = glue, 2 = runtime, 3 = function table, 4.. = function
    // groups. A cold build links them all statically. The daemon links everything but main into
    // libbase.so once, then each edit compiles only "overlay" copies of the changed units and links
    // a small executable that loads libbase.so and swaps the new functions into `lust_fns`.
    const FIRST_FN_UNIT: usize = 4;
    const MAX_OVERLAYS: usize = 32;
    let fn_units: Vec<usize> = (0..groups.len()).map(|g| g + FIRST_FN_UNIT).collect();
    let dirty_fn_units: Vec<usize> = (0..groups.len()).filter(|&g| dirty_groups[g]).map(|g| g + FIRST_FN_UNIT).collect();
    // A fresh base: no base yet, or new slots outgrew its table or unit list.
    let fresh_base =
        caches.objects != Some(req.debug) || !caches.persistent || n_slots > caches.table_cap || groups.len() != caches.base_units;
    if fresh_base {
        caches.table_cap = n_slots * 2 + 64;
        caches.base_units = groups.len();
    }
    let rebuild_base = fresh_base || caches.overlays.len() + dirty_fn_units.len() > MAX_OVERLAYS;
    let dir = caches.obj_dir.clone();
    let base_obj = |u: usize| dir.join(format!("u{u}.o"));
    let overlay_obj = |u: usize| dir.join(format!("o{u}.o"));
    // (unit, overlay?) pairs to compile now.
    let mut todo: Vec<(usize, bool)> = Vec::new();
    if rebuild_base {
        // Everything not yet in the base goes in: all units on a fresh base, else the overlays.
        if fresh_base {
            todo.extend([(1, false), (2, false), (3, false)]);
            todo.extend(fn_units.iter().map(|&u| (u, false)));
        } else {
            let mut units: Vec<usize> = caches.overlays.iter().copied().chain(dirty_fn_units.iter().copied()).collect();
            units.sort_unstable();
            units.dedup();
            todo.extend(units.into_iter().map(|u| (u, false)));
            if glue_changed && !todo.contains(&(1, false)) {
                todo.push((1, false));
            }
        }
        caches.overlays.clear();
    } else {
        caches.overlays.extend(dirty_fn_units.iter().copied());
        todo.extend(dirty_fn_units.iter().map(|&u| (u, true)));
        if glue_changed {
            caches.overlays.insert(1);
            todo.push((1, true));
        }
    }
    let registered: Vec<usize> = caches.overlays.iter().copied().filter(|&u| u >= FIRST_FN_UNIT).collect();
    todo.push((0, false));
    let main_slot = front.fn_slot[program.main.unwrap().0 as usize];
    let mut slot_lines = vec![0u32; n_slots];
    for i in 0..fn_count {
        slot_lines[slot(i)] = scan_of(front, i).1;
    }
    // Hybrid glue: glue reached by 3 or more units stays in the shared glue unit, the rest is
    // static per unit. The set is frozen until the next fresh base (see cgen::GlueSet). The
    // glue unit's C is built below, only when unit 1 is in `todo`.
    if fresh_base || caches.glue.shared.is_none() {
        caches.glue.compute_shared(&caches.out, &groups, 3);
    }
    let gen_unit = |u: usize, overlay: bool| match u {
        0 => cgen::main_unit(main_slot, &path, &slot_lines, &registered),
        1 => cgen::glue_unit(&program, &caches.glue),
        2 => cgen::runtime_unit(),
        3 => cgen::table_unit(caches.table_cap, &fn_units),
        g => {
            let register = if overlay { format!("lust_overlay_u{g}") } else { format!("lust_register_u{g}") };
            cgen::fn_unit(&program, &caches.out, groups[g - FIRST_FN_UNIT].clone(), &caches.glue, &register)
        }
    };
    let units: Vec<(PathBuf, String)> =
        par_map(&todo, |&(u, overlay)| (if overlay { overlay_obj(u) } else { base_obj(u) }, gen_unit(u, overlay)));
    if let Some(p) = &req.emit_c {
        // Emitted C must be self-contained: write every base unit, not only the units
        // rebuilt for this (possibly warm, incremental) build.
        for u in [0, 1, 2, 3].into_iter().chain(fn_units.iter().copied()) {
            // The standalone main unit registers no overlays; `lust_base_init` covers all units.
            let c = if u == 0 { cgen::main_unit(main_slot, &path, &slot_lines, &[]) } else { gen_unit(u, false) };
            let _ = std::fs::write(format!("{}.u{u}.c", p.display()), c);
        }
    }
    t.lap("assemble C units (par)");
    // `lust run` of a small program (one function unit, fresh base): compile in memory and run
    // it there, with no object files, link, or exec. The runtime comes from a cached object.
    // libtcc compiles serially, so bigger programs keep the parallel file-based path below.
    // Any setup failure falls back to that path (user code has not run yet). A debug run also
    // keeps the file path, so a debugger sees a real binary.
    if let Some(run_args) = &req.run_args
        && fresh_base
        && groups.len() == 1
        && !req.debug
        && let Ok(runtime_obj) = crate::tcc::cached_runtime_object(&cgen::runtime_unit(), req.debug)
    {
        let mem_units: Vec<(PathBuf, String)> = units.iter().filter(|(o, _)| *o != base_obj(2)).cloned().collect();
        let mut argv = vec![req.out.to_string_lossy().into_owned()];
        argv.extend(run_args.iter().cloned());
        if let Ok(run) = crate::tcc::run_in_memory(&mem_units, &runtime_obj, &argv, caches.persistent, req.debug) {
            t.lap("tcc compile + run (memory)");
            resp.code = run.code;
            resp.ran = true;
            resp.stdout = run.stdout;
            if req.timings {
                let kb = mem_units.iter().map(|u| u.1.len()).sum::<usize>() / 1024;
                let _ =
                    writeln!(resp.stderr, "lust run {path}: exit {} ({} functions, {kb} KB of C, in memory)", run.code, program.fns.len());
                t.render(&mut resp.stderr);
            }
            resp.stderr.push_str(&run.stderr);
            if leak_at_exit {
                std::mem::forget(bodies);
                std::mem::forget(units);
                std::mem::forget(program);
            }
            return resp;
        }
    }
    if let Err(e) = std::fs::create_dir_all(&dir).map_err(|e| e.to_string()).and_then(|_| crate::tcc::compile_units(&units, req.debug)) {
        caches.objects = None;
        return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
    }
    caches.objects = Some(req.debug);
    t.lap("tcc compile");
    let all_base: Vec<PathBuf> = [1, 2, 3].into_iter().chain(fn_units.iter().copied()).map(base_obj).collect();
    let linked = if !caches.persistent {
        let mut objs = vec![base_obj(0)];
        objs.extend(all_base);
        crate::tcc::link(&objs, &req.out, req.debug)
    } else {
        let base = if rebuild_base { crate::tcc::link_shared(&all_base, &dir.join("libbase.so"), req.debug) } else { Ok(()) };
        if rebuild_base {
            t.lap("link libbase.so");
        }
        let mut objs = vec![base_obj(0)];
        objs.extend(caches.overlays.iter().map(|&u| overlay_obj(u)));
        base.and_then(|_| crate::tcc::link_with_base(&objs, &dir, &req.out, req.debug))
    };
    if let Err(e) = linked {
        caches.objects = None;
        return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
    }
    t.lap("link");
    if req.timings {
        let kb = units.iter().map(|u| u.1.len()).sum::<usize>() / 1024;
        let _ = writeln!(
            resp.stderr,
            "lust build {path}: ok ({} functions, {mode}: {} fn(s) generated, {} units compiled, {} overlays, {kb} KB of C)",
            program.fns.len(),
            bodies.len(),
            units.len(),
            caches.overlays.len(),
        );
        t.render(&mut resp.stderr);
    }
    if leak_at_exit {
        std::mem::forget(bodies);
        std::mem::forget(units);
        std::mem::forget(program);
    }
    resp
}
