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
    /// Bumped on every base rebuild. Each base is a new file (libbase-<n>.so), so an executable
    /// built earlier keeps loading the base it was linked with, even after a later rebuild.
    /// `base_gens` holds the generations still on disk, oldest first. Old generations are
    /// deleted only when no known output file references them any more (see `base_still_used`),
    /// so live binaries keep working and the cache grows only with binaries that still exist.
    base_gen: u64,
    base_gens: std::collections::VecDeque<u64>,
    /// (generation, output file) for every executable linked against a base in this session.
    base_users: Vec<(u64, PathBuf)>,
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
                base_gen: 0,
                base_gens: std::collections::VecDeque::new(),
                base_users: Vec::new(),
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

/// True if any known output file built against base generation `g` still exists and still
/// names `libbase-<g>.so` (an overwritten output names its newer base instead).
fn base_still_used(users: &[(u64, PathBuf)], g: u64) -> bool {
    let soname = format!("libbase-{g}.so");
    users
        .iter()
        .filter(|(u, _)| *u == g)
        .any(|(_, out)| std::fs::read(out).is_ok_and(|bytes| bytes.windows(soname.len()).any(|w| w == soname.as_bytes())))
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
/// column 0, is a proven top-level boundary (`boundaries`, from `BoundaryScan`), and never
/// between an attribute and its item. `headers`, when given, are the `item_headers` of the whole
/// source (used on a session's first compile, where the region is the whole source and the mask
/// needed the same table).
fn split_items(
    src: &str,
    region: std::ops::Range<usize>,
    mask: u64,
    headers: Option<&[(usize, u64)]>,
    boundaries: &[usize],
) -> Vec<(usize, usize)> {
    let mut ranges = Vec::new();
    let mut chunk_start = region.start;
    let cut = |at: usize, h: u64, ranges: &mut Vec<(usize, usize)>, chunk_start: &mut usize| {
        // The multiply spreads FxHash's low bits.
        if (h.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 40) & mask == 0 && boundaries.binary_search(&(region.start + at)).is_ok() {
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

/// A byte scanner that mirrors the lexer's states (strings, chars, comments) and tracks bracket
/// depth. It proves chunk boundaries: a line start is a top-level item boundary only if the
/// scanner is in the normal state there with all depths at zero. A deleted brace, an inserted
/// `/*` or `"`, or a column-0 method line inside an impl all fail this test, so chunks are only
/// split or reused where the split is still real in the new text.
#[derive(Clone, Copy, PartialEq, Eq)]
enum ScanState {
    Normal,
    Str,
    Char,
    LineComment,
    BlockComment(u32),
}

struct BoundaryScan {
    state: ScanState,
    brace: i64,
    paren: i64,
    bracket: i64,
}

impl BoundaryScan {
    fn new() -> BoundaryScan {
        BoundaryScan { state: ScanState::Normal, brace: 0, paren: 0, bracket: 0 }
    }
    fn clean(&self) -> bool {
        self.state == ScanState::Normal && self.brace == 0 && self.paren == 0 && self.bracket == 0
    }
    /// Feeds `b` (which starts at absolute offset `base`). Pushes every clean line start after a
    /// newline into `out`, when given.
    fn feed(&mut self, b: &[u8], base: usize, mut out: Option<&mut Vec<usize>>) {
        let mut i = 0;
        while i < b.len() {
            let c = b[i];
            match self.state {
                ScanState::Normal => {
                    match c {
                        b'\n' => {
                            i += 1;
                            if self.clean() {
                                if let Some(out) = out.as_deref_mut() {
                                    out.push(base + i);
                                }
                            }
                            continue;
                        }
                        b'/' if b.get(i + 1) == Some(&b'/') => {
                            self.state = ScanState::LineComment;
                            i += 2;
                            continue;
                        }
                        b'/' if b.get(i + 1) == Some(&b'*') => {
                            self.state = ScanState::BlockComment(1);
                            i += 2;
                            continue;
                        }
                        b'"' => self.state = ScanState::Str,
                        b'\'' => {
                            // A char literal, or a lifetime (same test as the lexer).
                            let is_char = match b.get(i + 1) {
                                Some(b'\\') => true,
                                Some(&n) => {
                                    let len = if n < 0x80 {
                                        1
                                    } else if n < 0xE0 {
                                        2
                                    } else if n < 0xF0 {
                                        3
                                    } else {
                                        4
                                    };
                                    b.get(i + 1 + len) == Some(&b'\'')
                                }
                                None => false,
                            };
                            if is_char {
                                self.state = ScanState::Char;
                            }
                        }
                        b'{' => self.brace += 1,
                        b'}' => self.brace -= 1,
                        b'(' => self.paren += 1,
                        b')' => self.paren -= 1,
                        b'[' => self.bracket += 1,
                        b']' => self.bracket -= 1,
                        _ => {}
                    }
                    i += 1;
                }
                ScanState::Str => match c {
                    b'\\' => i += 2,
                    b'"' => {
                        self.state = ScanState::Normal;
                        i += 1;
                    }
                    _ => i += 1,
                },
                ScanState::Char => match c {
                    b'\\' => i += 2,
                    b'\'' => {
                        self.state = ScanState::Normal;
                        i += 1;
                    }
                    _ => i += 1,
                },
                ScanState::LineComment => {
                    if c == b'\n' {
                        self.state = ScanState::Normal;
                        i += 1;
                        if self.clean() {
                            if let Some(out) = out.as_deref_mut() {
                                out.push(base + i);
                            }
                        }
                    } else {
                        i += 1;
                    }
                }
                ScanState::BlockComment(d) => {
                    if c == b'/' && b.get(i + 1) == Some(&b'*') {
                        self.state = ScanState::BlockComment(d + 1);
                        i += 2;
                    } else if c == b'*' && b.get(i + 1) == Some(&b'/') {
                        self.state = if d == 1 { ScanState::Normal } else { ScanState::BlockComment(d - 1) };
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
            }
        }
    }
}

/// True if lexing `text` from a clean top-level point ends in the normal state (not inside a
/// comment or string, all depths zero).
fn chunk_ends_clean(text: &str) -> bool {
    let mut scan = BoundaryScan::new();
    scan.feed(text.as_bytes(), 0, None);
    scan.clean()
}

/// True if a chunk may be reused in front of other text: it ends at a top-level item boundary
/// (token scan) and in a clean lex state. The lex test matters for a chunk that ends inside a
/// `//` comment with no trailing newline: its standalone tokens end there, but in the new text
/// the comment ends at the next newline and the bytes after it are code again. A chunk that
/// lexed without error can only end unclean inside a line comment, which a trailing newline
/// rules out, so the byte scan runs only for chunks without one.
fn chunk_end_ok(c: &Chunk) -> bool {
    c.scan.ends_at_boundary && (c.text.ends_with('\n') || chunk_ends_clean(&c.text))
}

/// Shifts every AST span at or after old offset `lo` by `delta` bytes. After an edit, the kept
/// suffix chunks keep their text at a new offset; their items in `front.ast` still carry old
/// spans. Spans the parser stored for an item lie within that item's chunk, so shifting by range
/// moves exactly the suffix items' spans. Runs before anything new is parsed in this compile, so
/// every span in the AST is still in old coordinates.
fn shift_ast_spans(front: &mut Front, lo: usize, delta: i64) {
    if delta == 0 {
        return;
    }
    let lo = lo as u32;
    let mut sh = |s: &mut diag::Span| {
        if s.start >= lo {
            s.start = (s.start as i64 + delta) as u32;
            s.end = (s.end as i64 + delta) as u32;
        }
    };
    let ast = &mut front.ast;
    for s in ast.expr_spans.iter_mut().chain(ast.pat_spans.iter_mut()).chain(ast.ty_spans.iter_mut()) {
        sh(s);
    }
    for b in &mut ast.blocks {
        sh(&mut b.span);
        for st in &mut b.stmts {
            if let crate::ast::Stmt::Let { span, .. } = st {
                sh(span);
            }
        }
    }
    for e in &mut ast.exprs {
        match e {
            crate::ast::Expr::MethodCall { name_span, .. } => sh(name_span),
            crate::ast::Expr::StructLit { fields, .. } => {
                for (_, s, _) in fields {
                    sh(s);
                }
            }
            _ => {}
        }
    }
    fn shift_fn(f: &mut crate::ast::FnDef, sh: &mut impl FnMut(&mut diag::Span)) {
        sh(&mut f.name_span);
        if let Some(sp) = &mut f.self_param {
            sh(&mut sp.span);
        }
        for p in &mut f.params {
            sh(&mut p.span);
        }
    }
    for item in &mut ast.items {
        match &mut item.kind {
            ItemKind::Fn(f) => shift_fn(f, &mut sh),
            ItemKind::Struct(s) => {
                sh(&mut s.name_span);
                for fd in &mut s.fields {
                    sh(&mut fd.span);
                }
                for (_, sp) in &mut s.derives {
                    sh(sp);
                }
            }
            ItemKind::Enum(e) => {
                sh(&mut e.name_span);
                for v in &mut e.variants {
                    sh(&mut v.span);
                    if let crate::ast::VariantFields::Struct(fs) = &mut v.fields {
                        for fd in fs {
                            sh(&mut fd.span);
                        }
                    }
                }
                for (_, sp) in &mut e.derives {
                    sh(sp);
                }
            }
            ItemKind::Impl(imp) => {
                for f in &mut imp.fns {
                    shift_fn(f, &mut sh);
                }
            }
            ItemKind::Use => {}
        }
    }
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
    // A chunk may be reused only if its edges are still top-level item boundaries in the new
    // text: `chunk_end_ok` proves the end edge (complete items, clean lex state). A chunk that
    // ended at the old end of file may end mid-item (a half-written `fn added`) or inside a
    // `//` comment, and then it must not be kept in front of other text. It may still be kept
    // when it reaches the new end of file, where a cold compile scans it the same way. Cut the
    // kept front list at the first chunk that fails the test.
    if let Some(i) = kept_front.iter().position(|c| !chunk_end_ok(c)) {
        let end = kept_front[i].start + kept_front[i].text.len();
        if end < src.len() {
            kept_front.truncate(i);
        }
    }
    // The same test between kept back chunks: if a non-final back chunk does not end at an item
    // boundary, the next back chunk does not start at one. Drop everything up to it.
    while let Some(i) = (0..kept_back.len().saturating_sub(1)).find(|&i| !chunk_end_ok(&kept_back[i])) {
        kept_back.drain(..=i);
    }
    let region_start = kept_front.last().map_or(0, |c| c.start + c.text.len());
    // Prove the changed region's split points, and that the first kept back chunk still starts
    // at a top-level boundary. If the region does not end clean (an inserted `/*` or `"`, a
    // deleted brace), or does not end at a line start (its last token could merge with the back
    // chunk's first token), the back chunk starts inside a comment, string, item, or token:
    // drop it into the region and keep scanning.
    let mut boundaries: Vec<usize> = vec![region_start];
    let mut bscan = BoundaryScan::new();
    let mut scanned_to = region_start;
    let (region_end_old, region_end) = loop {
        let end_old = kept_back.first().map_or(old_len, |c| c.start);
        let end = (end_old as i64 + delta) as usize;
        if end > scanned_to {
            bscan.feed(&src.as_bytes()[scanned_to..end], scanned_to, Some(&mut boundaries));
            scanned_to = end;
        }
        let at_line_start = end == region_start || src.as_bytes()[end - 1] == b'\n';
        if (bscan.clean() && at_line_start) || kept_back.is_empty() {
            break (end_old, end);
        }
        kept_back.remove(0);
    };
    let lines = if old_len == 0 { LineIndex::new(&src) } else { front.lines.splice(&src, region_start, region_end_old, region_end) };
    let mut ranges: Vec<(usize, usize)> = kept_front.iter().map(|c| (c.start, c.start + c.text.len())).collect();
    let headers = if region_start == 0 && region_end == src.len() { fresh_headers.as_deref() } else { None };
    let middle =
        if region_start < region_end { split_items(&src, region_start..region_end, mask, headers, &boundaries) } else { Vec::new() };
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
        // A chunk cut a comment or string the scanner did not see, or the text is bad: lex the
        // whole file. Its error is the answer; if it lexes, compile as one chunk. Never panic.
        match lexer::lex(&src, 0, &front.interner) {
            Err(mut d) => return errors(std::slice::from_mut(&mut d), &path, &src, req),
            Ok(whole) => {
                let sc = scan::scan(&whole);
                front.chunks = vec![Chunk { start: 0, text: src.clone(), lexed: whole, lexed_start: 0, scan: sc, items: None }];
            }
        }
    } else {
        let mut fresh = need.iter().zip(fresh).map(|(&i, r)| (i, r.unwrap())).collect::<Vec<_>>().into_iter();
        let mut next_fresh = fresh.next();
        for (i, &(a, b)) in ranges.iter().enumerate() {
            let chunk = match reused[i].take() {
                Some(mut c) => {
                    // Same text at a new position, and the edges are proven boundaries, so the
                    // tokens are the same: shift their spans and the function offsets.
                    let delta = a as i64 - c.start as i64;
                    if delta != 0 {
                        for f in &mut c.scan.fns {
                            f.fn_offset = (f.fn_offset as i64 + delta) as u32;
                        }
                        for t in &mut c.lexed.tokens {
                            t.span.start = (t.span.start as i64 + delta) as u32;
                            t.span.end = (t.span.end as i64 + delta) as u32;
                        }
                        c.lexed_start = a;
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
    }
    // The kept suffix moved by `delta`: put its AST spans (still in old coordinates, nothing new
    // parsed yet) at their new positions.
    if old_len > 0 {
        shift_ast_spans(front, region_end_old, delta);
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
        // Reused chunks carry shifted token spans (see chunk assembly), so every chunk is ready.
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
            let whole = match lexer::lex(&src, 0, &front.interner) {
                Ok(w) => w,
                Err(mut d) => {
                    front.env_hash = None;
                    return errors(std::slice::from_mut(&mut d), &path, &src, req.json);
                }
            };
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
        if rebuild_base {
            caches.base_gen += 1;
            caches.base_gens.push_back(caches.base_gen);
        }
        let name = format!("base-{}", caches.base_gen);
        let base = if rebuild_base { crate::tcc::link_shared(&all_base, &dir.join(format!("lib{name}.so")), req.debug) } else { Ok(()) };
        if rebuild_base {
            t.lap("link libbase.so");
        }
        let mut objs = vec![base_obj(0)];
        objs.extend(caches.overlays.iter().map(|&u| overlay_obj(u)));
        base.and_then(|_| crate::tcc::link_with_base(&objs, &dir, &name, &req.out, req.debug))
    };
    if let Err(e) = linked {
        caches.objects = None;
        return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
    }
    // Reference-counted cleanup: record this build as a user of the current base, then delete
    // old generations past a small grace count while no known output file still references
    // them. A binary the user kept keeps its base; one that was overwritten or deleted does
    // not. A running program keeps its mapped copy after unlink.
    if caches.persistent && caches.base_gen > 0 {
        caches.base_users.push((caches.base_gen, req.out.clone()));
    }
    const KEEP_BASES: usize = 4;
    let excess: Vec<u64> = caches.base_gens.iter().take(caches.base_gens.len().saturating_sub(KEEP_BASES)).copied().collect();
    for g in excess {
        if !base_still_used(&caches.base_users, g) {
            caches.base_gens.retain(|&x| x != g);
            caches.base_users.retain(|(u, _)| *u != g);
            let _ = std::fs::remove_file(dir.join(format!("libbase-{g}.so")));
        }
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
