// The compile pipeline, cold or incremental. State that an edit can reuse lives in
// `Session` (session.rs).
//
// Incremental rules, from cheapest to most expensive:
//   1. Only function bodies changed (same environment hash: all tokens outside bodies): re-parse,
//      re-check, and re-generate only those functions.
//   2. Only top-level functions were added, removed, or changed signature (all other items the
//      same): re-parse the file, but re-check and re-generate only the changed functions and the
//      bodies that mention their names. A changed function always rechecks: its body is checked
//      against its own signature, which the body hash does not cover. A mention-only candidate
//      (own signature unchanged, body unchanged) whose recorded reads all still match the new
//      program (`Program::reads_dirty`, the section 8.3 step 5 dirty walk for Binding and
//      MethodSet nodes first) is reused without a recheck: per-name binding reads, method-set
//      probes, and failed lookups are precise where name mentions are not. Candidates with no
//      stored reads always recheck.
//   3. Anything else (a type, an impl, a use changed): full rebuild.
use super::session::{Caches, Chunk, Front, Session};
use super::{Cmd, Request, Response};
use crate::ast::{Ast, ItemKind};
use crate::cgen::{self, FnOut, GlueSet};
use crate::check::collect::{self, LocalDefId};
use crate::def::{self, CrateIds, DiskDefId, StableCrateHash};
use crate::diag::{self, Diag, FileId, LineIndex, SourceMap};
use crate::expand;
use crate::intern::{FxMap, Interner, Sym};
use crate::lexer;
use crate::scan;
use crate::{borrowck, check, ir, lower, parser};
use std::fmt::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

/// The session's one source file in its source map. A crate is one file today, so every
/// span the lexer makes in this pipeline names it (docs/ARCH.md section 9.2, S1).
const ROOT_FILE: FileId = FileId(0);

/// Runs macro expansion over one lexed chunk or file (for W-RESOLVE: this
/// is the spot that moves into the 6.1 outline worklist). Expansion is a
/// no-op for files with no macro definitions or non-parser macro calls,
/// so macro-free files keep the current path bit for bit.
fn expand_tokens(front: &Front, lexed: lexer::Lexed, file: &std::path::Path, src: &str, test: bool) -> Result<lexer::Lexed, Diag> {
    let ctx = expand::ExpandCtx::for_file(&front.interner, &front.known, file, src, test);
    expand::expand_lexed(lexed, &ctx)
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

/// True when `LUST_STATS` is set to a value other than "" or "0". Stats go
/// to stderr as one `lust-stats:` line per compile; the scale gate
/// (scripts/scale-gate.py) parses them. Off by default: user output does
/// not change.
fn stats_on() -> bool {
    matches!(std::env::var("LUST_STATS"), Ok(v) if !v.is_empty() && v != "0")
}

/// One compile's scale-gate counters (docs/ARCH.md section 9.3 scale
/// gate), rendered as a single line. `c_bytes` counts C text emitted
/// this compile (units actually generated), `dirty_units` the fn units
/// whose objects were (re)compiled or served as overlays, and
/// `unit_cache_hits` the units whose object came from the disk unit
/// cache instead of tcc. Instance count is the live slot count: today
/// one instance per fn (mono instances join with generics).
#[derive(Default)]
struct Stats {
    mode: &'static str,
    fns: usize,
    rechecked: usize,
    reused: usize,
    invalidated: usize,
    c_bytes: usize,
    dirty_units: usize,
    units_compiled: usize,
    unit_cache_hits: usize,
    table_rebuilt: bool,
    instances: usize,
}

impl Stats {
    fn render(&self, out: &mut String) {
        let _ = writeln!(
            out,
            "lust-stats: mode={} fns={} rechecked={} reused={} invalidated={} c_bytes={} dirty_units={} units_compiled={} unit_cache_hits={} table_rebuilt={} instances={}",
            self.mode,
            self.fns,
            self.rechecked,
            self.reused,
            self.invalidated,
            self.c_bytes,
            self.dirty_units,
            self.units_compiled,
            self.unit_cache_hits,
            self.table_rebuilt as u8,
            self.instances,
        );
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

/// True when a chunk's expansion reads token positions (`line!`,
/// `column!`, `file!`, `stringify!`, `dbg!`): its expanded tokens are
/// only valid at the position they were expanded at, so a kept chunk
/// that moved must be lexed and expanded again. The text scan is
/// deliberately loose (a name inside a longer identifier also hits);
/// a false hit costs one relex, a miss would serve a stale `line!`.
fn chunk_pos_sensitive(c: &Chunk) -> bool {
    ["line!", "column!", "file!", "stringify!", "dbg!"].iter().any(|n| c.text.contains(n))
}

/// True when a chunk's expansion reads files outside the source
/// (`include!` and kin): such a chunk is never reused, because the
/// included file can change while the source text stays the same.
fn chunk_reads_files(c: &Chunk) -> bool {
    c.text.contains("include")
}

/// Shifts every AST span in file `file` at or after old offset `lo` by `delta` bytes.
/// The caller passes the old start of the common suffix: every byte from there on is the
/// same text at a new offset, so every span there moves by `delta`. This threshold matters
/// inside the changed region too: in bodies-only mode an unchanged function after the edit
/// point in the same chunk keeps its old AST, and its spans must move or its diagnostic
/// and panic columns are off by the edit size. Spans in changed text belong to bodies or
/// items that this compile re-parses before use, so shifting their dead nodes is harmless.
/// Runs before anything new is parsed in this compile, so every span in the AST is still
/// in old coordinates.
fn shift_ast_spans(front: &mut Front, file: FileId, lo: usize, delta: i64) {
    if delta == 0 {
        return;
    }
    let lo = lo as u32;
    let mut sh = |s: &mut diag::Span| {
        if s.file == file && s.lo >= lo {
            *s = s.shifted(delta);
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
    for item in ast.items.iter_mut().chain(ast.stmt_items.iter_mut()) {
        sh(&mut item.span);
        match &mut item.kind {
            ItemKind::Fn(f) => shift_fn(f, &mut sh),
            ItemKind::Struct(s) => {
                sh(&mut s.name_span);
                match &mut s.fields {
                    crate::ast::VariantFields::Struct(fs) | crate::ast::VariantFields::Tuple(fs) => {
                        for fd in fs {
                            sh(&mut fd.span);
                        }
                    }
                    crate::ast::VariantFields::Unit => {}
                }
                for (_, sp) in &mut s.derives {
                    sh(sp);
                }
            }
            ItemKind::Enum(e) => {
                sh(&mut e.name_span);
                for v in &mut e.variants {
                    sh(&mut v.span);
                    if let crate::ast::VariantFields::Struct(fs) | crate::ast::VariantFields::Tuple(fs) = &mut v.fields {
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
            _ => {}
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

fn errors(diags: &mut [Diag], map: &SourceMap, src: &str, req: &Request) -> Response {
    let json = req.json;
    let text = diag::render(diags, map, src, json, req.max_errors);
    let mut r = Response { code: 1, ..Default::default() };
    if json {
        r.stdout = text;
    } else {
        r.stderr = text;
        let path = map.path(ROOT_FILE);
        let _ = writeln!(r.stderr, "error: could not compile `{path}` due to {} previous error(s)", diags.len());
    }
    r
}

/// After a parse that was not "bodies only": update item tables, assign slots by
/// stable def hash, and pick the functions to re-check. Returns (changed,
/// mention_only): changed local ids as indexes, plus the subset that changed
/// only by mentioning a changed name (body hash equal, last check passed, own
/// signature item unchanged). Mention-only functions are the candidates the
/// read-set dirty walk can reuse after collect. The one failure is a def hash
/// collision (src/def.rs): an internal error the caller turns into a code 3 response.
#[allow(clippy::too_many_arguments)]
fn slot_update(
    front: &mut Front,
    caches: &mut Caches,
    item_scans: Vec<scan::ItemScan>,
    env: u64,
    changed_names: Option<Vec<Sym>>,
    fn_at: &[(usize, usize)],
    cores: usize,
    crate_ids: CrateIds,
    scan_of: &dyn Fn(&Front, usize) -> (u64, u32),
    t: &mut Timer,
) -> Result<(Vec<usize>, Vec<usize>), String> {
    let fn_count = fn_at.len();
    front.fn_loc = fn_locations(&front.ast);
    front.env_hash = Some(env);
    front.items = item_scans;
    if changed_names.is_none() {
        // Full rebuild: fresh caches, but slots stay append-only (section
        // 4.2): existing fns keep the slots the manifest gave them, a
        // seeded manifest from a previous daemon included, so slot
        // numbers are stable across restarts and load orders. Only when
        // dead slots outnumber live fns by a wide margin does a full
        // rebuild compact: it renumbers in def order and the stored
        // manifest is rewritten (the base rebuild of 4.2, in slot form).
        if front.slot_of.len() > fn_count * 2 + 64 {
            front.slot_of.clear();
            front.slot_paths.clear();
            front.slot_manifest_stored = 0;
        }
        caches.ok.clear();
        caches.out.clear();
        caches.has_out.clear();
        caches.slot_reads.clear();
        caches.slot_used.clear();
        caches.slot_fp.clear();
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
    // Assign slots by stable identity, append-only. New functions get new slots;
    // a removed function's slot is emptied. A known hash with a different path
    // text is a hash collision: stop with an internal error (section 1.7). The
    // same path twice is a duplicate definition, which `collect` reports.
    let keys = fn_keys(&front.ast, &front.fn_loc, &front.interner, crate_ids.stable);
    let mut live = vec![false; front.slot_of.len()];
    let mut fn_slot = Vec::with_capacity(keys.len());
    for k in &keys {
        if let Err(c) = def::insert_path(&mut front.slot_paths, k.disk, &k.path) {
            return Err(c.to_string());
        }
        let slot = match front.slot_of.get(&k.disk) {
            Some(&slot) => slot,
            None => {
                let slot = front.slot_of.len() as u32;
                front.slot_of.insert(k.disk, slot);
                slot
            }
        };
        if slot as usize >= live.len() {
            live.resize(slot as usize + 1, false);
        }
        live[slot as usize] = true;
        fn_slot.push(slot);
    }
    front.fn_slot = fn_slot;
    let n_slots = front.slot_of.len();
    caches.ok.resize(n_slots, false);
    caches.has_out.resize(n_slots, false);
    caches.out.resize_with(n_slots, FnOut::default);
    caches.slot_reads.resize_with(n_slots, || None);
    caches.slot_used.resize_with(n_slots, Vec::new);
    caches.slot_fp.resize(n_slots, 0);
    front.slot_hash.resize(n_slots, 0);
    for slot in (0..n_slots).filter(|&s| !live[s]) {
        caches.out[slot] = FnOut::default();
        caches.has_out[slot] = true;
        caches.ok[slot] = true;
        caches.slot_reads[slot] = None;
        caches.slot_used[slot].clear();
        caches.slot_fp[slot] = 0;
    }
    // Re-check a function if its body changed, or it is new, or its body mentions a changed
    // function's name (only possible in the "signatures" case). A function in the last
    // group only (same body hash, last check passed, and its own signature unchanged) is a
    // reuse candidate for the read-set dirty walk after collect; its `has_out` is cleared
    // only if the walk keeps it changed, which the caller does when it stays in the work
    // set (see the walk in `compile`). A function whose own signature item changed is
    // never a candidate: its body is checked against that signature (parameter names and
    // types bind the locals, the return type coerces the tail), and the body hash does
    // not cover the signature tokens, so no recorded read set can prove the old result
    // stands. It rechecks like a body change.
    let names = changed_names.unwrap_or_default();
    let mut changed = Vec::new();
    let mut mention_only = Vec::new();
    for i in 0..fn_count {
        let slot = front.fn_slot[i] as usize;
        let (hash, _) = scan_of(front, i);
        let idents = &front.chunks[fn_at[i].0].scan.body_idents[fn_at[i].1];
        let own_sig_changed = keys[i].free && names.contains(&keys[i].name);
        let mentions = own_sig_changed || idents.iter().any(|s| names.contains(s));
        let body_same = front.slot_hash[slot] == hash;
        if !body_same || !caches.ok[slot] || mentions {
            if body_same && caches.ok[slot] && mentions && !own_sig_changed {
                mention_only.push(i);
            } else {
                // Same rule as the bodies-only path: `slot_hash` advances
                // below before the check runs, so clear the passing mark
                // now. An early return between here and the check loop
                // (a collect error, say) then leaves the function dirty,
                // never unchanged-and-passing with an unchecked body.
                caches.ok[slot] = false;
                caches.has_out[slot] = false;
                caches.slot_reads[slot] = None;
            }
            front.slot_hash[slot] = hash;
            changed.push(i);
        }
    }
    t.lap(if names.is_empty() { "parse (par)" } else { "parse changed chunks" });
    Ok((changed, mention_only))
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

/// One function's slot key: its stable disk identity, the canonical path text
/// (for collision checks), and the two facts the changed-name scan needs.
struct FnKey {
    disk: DiskDefId,
    path: String,
    /// A top-level function (not an impl method).
    free: bool,
    name: Sym,
}

/// The slot key of every function, in LocalDefId order. Identity comes from
/// name strings through src/def.rs (free fn: its name; method: its impl's path
/// plus its name), never from `Sym` values, so keys are the same in every
/// session. An impl whose self type is not a plain path gets a placeholder
/// header; `collect` rejects it later, so its slots are never used. The hashes
/// computed here must equal the ones `collect` stores in `Program::fn_defs`;
/// a test below checks both against one source.
fn fn_keys(ast: &Ast, fn_loc: &[(usize, Option<usize>)], interner: &Interner, stable: StableCrateHash) -> Vec<FnKey> {
    // Each impl item's path, impls with the same header counted in file order.
    let mut ordinals: FxMap<String, u32> = FxMap::default();
    let mut impl_paths: Vec<Option<(def::DefPathHash, String)>> = Vec::with_capacity(ast.items.len());
    for item in &ast.items {
        let path = match &item.kind {
            ItemKind::Impl(imp) => {
                let header = match ast.ty(imp.self_ty) {
                    crate::ast::TyExpr::Path(segs) if !segs.is_empty() => interner.get(segs[0].name).to_string(),
                    _ => "<error>".to_string(),
                };
                let ordinal = ordinals.get(&header).copied().unwrap_or(0);
                ordinals.insert(header.clone(), ordinal + 1);
                Some(def::impl_path(stable, &[], &header, ordinal))
            }
            _ => None,
        };
        impl_paths.push(path);
    }
    let key = |hash, path, free, name| FnKey { disk: DiskDefId { krate: stable, hash }, path, free, name };
    fn_loc
        .iter()
        .map(|&(item, sub)| match (&ast.items[item].kind, sub) {
            (ItemKind::Fn(d), None) => {
                let (hash, path) = def::free_fn_path(stable, &[], interner.get(d.name));
                key(hash, path, true, d.name)
            }
            (ItemKind::Impl(imp), Some(k)) => {
                let (ihash, itext) = impl_paths[item].as_ref().unwrap();
                let (hash, path) = def::method_path(*ihash, itext, interner.get(imp.fns[k].name));
                key(hash, path, false, imp.fns[k].name)
            }
            _ => unreachable!("fn_loc points at a function"),
        })
        .collect()
}

/// LocalDefId order: top-level functions and impl methods, in item order. Same as `collect`.
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

/// Compiles one request, reusing whatever `session` holds. The session
/// serves one `SessionKey`: a request for another key is a routing bug and
/// gets an internal error, never this session's state.

/// Splices the checked source std fns after `src` (see the call site in
/// `compile`). Returns the shipped byte ranges and the std fn routes.
fn splice_std(
    src: &mut String,
    std_cache: &mut Option<Result<std::sync::Arc<crate::stdload::StdLoad>, String>>,
) -> Result<(Vec<(u32, u32, crate::ty::lang::ShippedCrate)>, Vec<&'static crate::ty::lang::StdFnDef>), Response> {
    let load = std_cache.get_or_insert_with(|| crate::stdload::load_std().map(std::sync::Arc::new)).clone();
    let load = match load {
        Ok(l) => l,
        Err(e) => return Err(Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() }),
    };
    let mut ranges = Vec::new();
    if !src.ends_with('\n') {
        src.push('\n');
    }
    for (krate, text) in &load.splices {
        let lo = src.len() as u32;
        src.push_str(text);
        if !src.ends_with('\n') {
            src.push('\n');
        }
        ranges.push((lo, src.len() as u32, *krate));
    }
    Ok((ranges, load.fns.clone()))
}

/// The resolver front end (W-RESOLVE): Cargo graph selection, the
/// outline worklist, and the session setup the shared tail consumes.
/// Every request is a full rebuild in this path for now: correctness
/// first, and the daemon fuzzer's fresh-session guard compares answers,
/// not speed. Returns the tail tuple (map, changed, mention-only,
/// fn count, mode, fn lines, body hashes, tables).
#[allow(clippy::too_many_arguments)]
fn resolved_setup(
    req: &Request,
    front: &mut Front,
    caches: &mut Caches,
    std_cache: &mut Option<Result<std::sync::Arc<crate::stdload::StdLoad>, String>>,
    user_src: &str,
    crate_ids_default: CrateIds,
    std_ranges: &mut Vec<(u32, u32, crate::ty::lang::ShippedCrate)>,
    std_routes: &mut Vec<&'static crate::ty::lang::StdFnDef>,
    t: &mut Timer,
) -> Result<(SourceMap, Vec<usize>, Vec<usize>, usize, &'static str, Vec<u32>, Vec<u64>, Option<crate::resolve::imports::ResolvedTables>), Response> {
    use crate::resolve::cargo::{self, GraphRequest};
    use crate::resolve::cfg::CfgEnv;
    use crate::resolve::worklist::{self, CrateInput};
    front.resolved_crate = true;
    let key = &req.session;
    let code2 = |msg: String| Response { stderr: format!("error: {msg}\n"), code: 2, ..Default::default() };
    // Crate selection: through the Cargo graph when a manifest names the
    // crate, else the synthetic one-file package of the session key.
    let (root_path, mut root_text, crate_ids, env, externs, crate_name) = if let Some(manifest) = &key.krate.manifest_path {
        let greq = GraphRequest {
            manifest_path: manifest.clone(),
            package: None,
            features: key.features.clone(),
            default_features: key.default_features,
            all_features: key.all_features,
            target_triple: key.target_triple.clone(),
        };
        let graph = cargo::load_graph(&greq).map_err(code2)?;
        t.lap("cargo graph");
        let pre_env = CfgEnv::new(&key.target_triple, &key.features, key.krate.test, key.profile);
        let unit =
            cargo::select_unit(&graph, &greq, &key.krate.target_kind, &key.krate.target_name, &pre_env, &front.interner, key.krate.test)
                .map_err(code2)?;
        let root_text = std::fs::read_to_string(&unit.target.src_path)
            .map_err(|e| code2(format!("cannot read {}: {e}", unit.target.src_path.display())))?;
        // Edition and lint gates for the selected unit (section 1.1),
        // rendered against the crate root file.
        let mut gate_map = SourceMap::default();
        gate_map.add_file_with_text(&unit.target.src_path.to_string_lossy(), &root_text);
        for check in [cargo::check_edition(&unit), cargo::check_lints(&graph, &unit)] {
            if let Err(mut d) = check {
                return Err(errors(std::slice::from_mut(&mut d), &gate_map, &root_text, req));
            }
        }
        let env = CfgEnv::new(&key.target_triple, &unit.features, key.krate.test, key.profile);
        let ids = CrateIds {
            local: def::LOCAL_CRATE,
            stable: def::stable_crate_hash(&unit.package_id, &key.krate.target_kind, &unit.target.name, key.krate.test),
        };
        (unit.target.src_path.clone(), root_text, ids, env, unit.externs.clone(), unit.package.name.replace('-', "_"))
    } else {
        let stem = key.krate.root.file_stem().and_then(|s| s.to_str()).unwrap_or("main").to_string();
        let env = CfgEnv::new(&key.target_triple, &key.features, key.krate.test, key.profile);
        (key.krate.root.clone(), user_src.to_string(), crate_ids_default, env, Vec::new(), stem)
    };
    // Std splice, in the root file text, exactly as the single-file path
    // (user spans do not move). A second resolve runs when only a
    // non-root file mentions a source std fn.
    let mut spliced = false;
    if crate::ty::lang::needs_std_load(&root_text) {
        let (ranges, routes) = splice_std(&mut root_text, std_cache)?;
        *std_ranges = ranges;
        *std_routes = routes;
        spliced = true;
        t.lap("std load+splice");
    }
    let resolved = loop {
        let input = CrateInput {
            root_path: root_path.clone(),
            root_text: root_text.clone(),
            env: env.clone(),
            crate_ids,
            crate_name: crate_name.clone(),
            externs: externs.clone(),
        };
        match worklist::resolve_crate(&input, &front.interner, &front.known) {
            Ok(r) => {
                if r.needs_std && !spliced {
                    let (ranges, routes) = splice_std(&mut root_text, std_cache)?;
                    *std_ranges = ranges;
                    *std_routes = routes;
                    spliced = true;
                    t.lap("std load+splice");
                    continue;
                }
                break r;
            }
            Err(e) => {
                if e.needs_std && !spliced {
                    let (ranges, routes) = splice_std(&mut root_text, std_cache)?;
                    *std_ranges = ranges;
                    *std_routes = routes;
                    spliced = true;
                    continue;
                }
                let mut diags = e.diags;
                return Err(errors(&mut diags, &e.map, &e.all_text, req));
            }
        }
    };
    t.lap("resolve (worklist)");
    let worklist::ResolvedCrate { ast, map, tables, fn_lines, body_hashes, .. } = resolved;
    let fn_count = fn_lines.len();
    front.ast = ast;
    front.map = map.clone();
    front.src.clone_from(&root_text);
    front.resolved_crate_ids = Some(crate_ids);
    // One synthetic chunk: the tail's slot update reads body idents and
    // item scans from chunks; the worklist's per-fn hashes ride in
    // through `scan_of` below, so the chunk scan carries shape only.
    let lexed = match lexer::lex(&root_text, ROOT_FILE, 0, &front.interner) {
        Ok(l) => l,
        Err(mut d) => return Err(errors(std::slice::from_mut(&mut d), &map, &root_text, req)),
    };
    let item_scans: Vec<scan::ItemScan> = front
        .ast
        .items
        .iter()
        .enumerate()
        .map(|(i, item)| scan::ItemScan {
            hash: (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1,
            fn_name: match &item.kind {
                ItemKind::Fn(f) => Some(f.name),
                _ => None,
            },
        })
        .collect();
    let n_items = item_scans.len();
    front.chunks = vec![Chunk {
        start: 0,
        text: root_text,
        lexed,
        lexed_start: 0,
        scan: scan::ChunkScan {
            fns: (0..fn_count).map(|_| scan::FnScan { body_hash: 1, fn_offset: 0, body: 0..0 }).collect(),
            items: item_scans.clone(),
            body_idents: vec![Vec::new(); fn_count],
            ends_at_boundary: true,
        },
        items: Some(0..n_items),
    }];
    let env = scan::env_hash(item_scans.iter());
    let fn_at: Vec<(usize, usize)> = (0..fn_count).map(|i| (0, i)).collect();
    let cores = std::thread::available_parallelism().map_or(4, |n| n.get());
    let lines = fn_lines.clone();
    let hashes = body_hashes.clone();
    let scan_of = |_: &Front, i: usize| (hashes[i], lines[i]);
    let (changed, mention_only) = match slot_update(front, caches, item_scans, env, None, &fn_at, cores, crate_ids, &scan_of, t) {
        Ok(c) => c,
        Err(e) => {
            front.env_hash = None;
            return Err(Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() });
        }
    };
    Ok((map, changed, mention_only, fn_count, "full", fn_lines, body_hashes, Some(tables)))
}

pub fn compile(req: &Request, session: &mut Session) -> Response {
    let mut t = Timer::new();
    if req.session != session.key {
        return Response {
            stderr: format!(
                "error: internal: request routed to the wrong session\n  request: {}\n  session: {}\n",
                req.session.describe(),
                session.key.describe()
            ),
            code: 3,
            ..Default::default()
        };
    }
    // Lust builds for the host target today. A named non-host triple is a
    // clear error, not a host binary under a foreign name.
    let triple = &req.session.target_triple;
    if !triple.is_empty() && triple != crate::protocol::host_triple() {
        return Response {
            stderr: format!(
                "error: unsupported target `{triple}`: lust builds for the host target `{}` today\n",
                crate::protocol::host_triple()
            ),
            code: 2,
            ..Default::default()
        };
    }
    let path = req.file.to_string_lossy().to_string();
    let mut src = match std::fs::read_to_string(&req.file) {
        Ok(s) => s,
        Err(e) => return Response { stderr: format!("error: cannot read {path}: {e}\n"), code: 2, ..Default::default() },
    };
    // The crate identity for stable defs comes from the session's key (its
    // package and target identity, `Session::crate_ids`). For a single-file
    // program that is the synthetic one-file bin crate, as before.
    let crate_ids = session.crate_ids();
    // Open the disk cache once per session and seed slot assignment from
    // the stored manifest, so a restarted daemon gives every fn the slot
    // it had before, in any load or discovery order (sections 4.2, 8.4).
    if !session.cache_tried {
        session.cache_tried = true;
        session.disk_cache = crate::driver::cache::Cache::open(&req.file);
        if session.front.slot_of.is_empty()
            && let Some(cache) = &session.disk_cache
            && let Some(manifest) = cache.load_slot_manifest(&session.key)
        {
            session.front.slot_manifest_stored = manifest.len();
            session.front.slot_of = manifest;
        }
    }
    let session_key = session.key.clone();
    let Session { front, caches, std_cache, disk_cache, .. } = session;
    t.lap("read");

    // Resolver routing (W-RESOLVE): a manifest-selected crate, or a root
    // file that mentions modules, imports, cfg, or const/static/type
    // items, compiles through the outline worklist (full rebuild per
    // request for now). Routing is sticky per session (see Front).
    let use_resolver = front.resolved_crate
        || req.session.krate.manifest_path.is_some()
        || crate::resolve::worklist::needs_resolve(&src, &front.interner);

    // Source std (S5): if this file can mention a source std fn, load the
    // checked shipped library (once per session) and splice its fns after
    // the user text. User spans do not move. `std_ranges` records which
    // byte ranges of the combined source belong to which shipped crate;
    // intrinsic privilege keys on them after collect. A file that cannot
    // mention a source std fn pays one byte scan and nothing else.
    let mut std_ranges: Vec<(u32, u32, crate::ty::lang::ShippedCrate)> = Vec::new();
    let mut std_routes: Vec<&'static crate::ty::lang::StdFnDef> = Vec::new();
    if !use_resolver && crate::ty::lang::needs_std_load(&src) {
        match splice_std(&mut src, std_cache) {
            Ok((ranges, routes)) => {
                std_ranges = ranges;
                std_routes = routes;
            }
            Err(resp) => return resp,
        }
        t.lap("std load+splice");
    }

    // Both front ends produce the same locals for the shared tail.
    let (map, mut changed, mention_only, fn_count, mode, fn_lines_all, body_hashes_all, resolved_tables) = if use_resolver {
        match resolved_setup(req, front, caches, std_cache, &src, crate_ids, &mut std_ranges, &mut std_routes, &mut t) {
            Ok(x) => x,
            Err(resp) => return resp,
        }
    } else {
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
            // A file with macro definitions lexes as one chunk for now:
            // expansion is per chunk, and a def must be in the chunk that
            // uses it until the 6.1 worklist owns crate-level expansion.
            let m = if src.contains("macro_rules") { (1 << 24) - 1 } else { split_mask(src.len(), headers.len(), cores) };
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
    // A kept chunk holds expanded tokens, and expansion can read more
    // than the chunk text: token positions and included files. A chunk
    // that reads included files is never kept. A position-sensitive
    // back chunk that moved is not kept either; front chunks sit at
    // their old offsets, where their positions still hold. Keep the
    // lists a prefix and a suffix, as the boundary proof below needs.
    if let Some(i) = kept_front.iter().position(chunk_reads_files) {
        kept_front.truncate(i);
    }
    if let Some(i) = kept_back.iter().rposition(|c| chunk_reads_files(c) || (delta != 0 && chunk_pos_sensitive(c))) {
        kept_back.drain(..=i);
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
    // The source map for this request: the session's one file under the request's path,
    // its line index spliced from the last request's index when there is one.
    let mut map = front.map.clone();
    if map.is_empty() {
        map.add_file(&path, &src);
    } else {
        let lines =
            if old_len == 0 { LineIndex::new(&src) } else { map.lines(ROOT_FILE).splice(&src, region_start, region_end_old, region_end) };
        map.set_file(ROOT_FILE, &path, lines);
    }
    let mut ranges: Vec<(usize, usize)> = kept_front.iter().map(|c| (c.start, c.start + c.text.len())).collect();
    let headers = if region_start == 0 && region_end == src.len() { fresh_headers.as_deref() } else { None };
    let middle =
        if region_start < region_end { split_items(&src, region_start..region_end, mask, headers, &boundaries) } else { Vec::new() };
    ranges.extend(middle.iter().copied());
    ranges.extend(kept_back.iter().map(|c| ((c.start as i64 + delta) as usize, (c.start as i64 + delta) as usize + c.text.len())));
    let mut reused: Vec<Option<Chunk>> =
        kept_front.into_iter().map(Some).chain(middle.iter().map(|_| None)).chain(kept_back.into_iter().map(Some)).collect();
    let need: Vec<usize> = (0..ranges.len()).filter(|&i| reused[i].is_none()).collect();
    let test_mode = req.harness || req.session.krate.test;
    let fresh = par_map(&need, |&i| {
        let (a, b) = ranges[i];
        lexer::lex(&src[a..b], ROOT_FILE, a as u32, &front.interner).and_then(|l| expand_tokens(front, l, &req.file, &src, test_mode)).map(
            |l| {
                let sc = scan::scan(&l);
                (l, sc)
            },
        )
    });
    // A macro error in a chunk is the answer, not a lexing fallback.
    if let Some(Err(d)) = fresh.iter().find(|l| matches!(l, Err(d) if d.code.starts_with("L08"))) {
        let mut d = d.clone();
        return errors(std::slice::from_mut(&mut d), &map, &src, req);
    }
    if fresh.iter().any(|l| l.is_err()) {
        // A chunk cut a comment or string the scanner did not see, or the text is bad: lex the
        // whole file. Its error is the answer; if it lexes, compile as one chunk. Never panic.
        match lexer::lex(&src, ROOT_FILE, 0, &front.interner).and_then(|l| expand_tokens(front, l, &req.file, &src, test_mode)) {
            Err(mut d) => return errors(std::slice::from_mut(&mut d), &map, &src, req),
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
                            t.span = t.span.shifted(delta);
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
    // The common suffix moved by `delta`: put its AST spans (still in old coordinates, nothing
    // new parsed yet) at their new positions. The threshold is the suffix start, not the first
    // kept chunk: unchanged items between the edit and that chunk keep their old AST.
    if old_len > 0 {
        shift_ast_spans(front, ROOT_FILE, old_len - suffix, delta);
    }
    let item_scans: Vec<scan::ItemScan> = front.chunks.iter().flat_map(|c| c.scan.items.iter().copied()).collect();
    let env = scan::env_hash(item_scans.iter());
    let fn_count = front.chunks.iter().map(|c| c.scan.fns.len()).sum::<usize>();
    // (chunk, index in chunk) for every function, in LocalDefId order.
    let fn_at: Vec<(usize, usize)> =
        front.chunks.iter().enumerate().flat_map(|(c, ch)| (0..ch.scan.fns.len()).map(move |k| (c, k))).collect();
    let scan_of = |front: &Front, i: usize| -> (u64, u32) {
        let f = &front.chunks[fn_at[i].0].scan.fns[fn_at[i].1];
        (f.body_hash, map.line_col_at(ROOT_FILE, f.fn_offset).0)
    };
    t.lap(if need.len() == ranges.len() { "lex+scan (par)" } else { "lex+scan changed chunks" });
    front.src.clone_from(&src);
    front.map = map.clone();

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

    let (changed, mention_only): (Vec<usize>, Vec<usize>) = if bodies_only {
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
            // The hash now names a body that has not been checked yet, so
            // the old passing mark must go with it: if a later body in
            // this loop fails to parse, the early return below must not
            // leave this function looking unchanged and passing (fuzz
            // seed 29, iter 562). The check loop rewrites `ok` for every
            // changed function it reaches.
            caches.ok[slot] = false;
            caches.has_out[slot] = false;
            if let Some(r) = caches.slot_reads.get_mut(slot) {
                *r = None;
            }
            match parser::parse_body(toks, &chunk.lexed.strings, &mut front.ast, &front.interner, &front.known) {
                Ok((body, exprs, pats)) => {
                    let (item, sub) = front.fn_loc[i];
                    let def = match (&mut front.ast.items[item].kind, sub) {
                        (ItemKind::Fn(d), None) => d,
                        (ItemKind::Impl(imp), Some(k)) => &mut imp.fns[k],
                        _ => unreachable!("fn_loc out of date"),
                    };
                    def.body = Some(body);
                    def.exprs = exprs;
                    def.pats = pats;
                }
                Err(d) => {
                    caches.ok[slot] = false;
                    return errors(&mut [d], &map, &src, req);
                }
            }
        }
        t.lap("parse changed bodies");
        (changed, Vec::new())
    } else if changed_names.is_some() {
        // Only top-level functions changed: parse just the chunks with new text, and splice their
        // items between the unchanged chunks' items.
        let todo: Vec<usize> = (0..front.chunks.len()).filter(|&i| front.chunks[i].items.is_none()).collect();
        let parsed = par_map(&todo, |&i| parser::parse(&front.chunks[i].lexed, &front.interner, &front.known));
        if let Some(Err(d)) = parsed.iter().find(|p| p.is_err()) {
            let d = d.clone();
            return errors(&mut [d], &map, &src, req);
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
        match slot_update(front, caches, item_scans, env, changed_names, &fn_at, cores, crate_ids, &scan_of, &mut t) {
            Ok(c) => c,
            Err(e) => {
                front.env_hash = None;
                return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
            }
        }
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
            let whole =
                match lexer::lex(&src, ROOT_FILE, 0, &front.interner).and_then(|l| expand_tokens(front, l, &req.file, &src, test_mode)) {
                    Ok(w) => w,
                    Err(mut d) => {
                        front.env_hash = None;
                        return errors(std::slice::from_mut(&mut d), &map, &src, req);
                    }
                };
            match parser::parse(&whole, &front.interner, &front.known) {
                Ok(a) => a,
                Err(d) => {
                    front.env_hash = None;
                    return errors(&mut [d], &map, &src, req);
                }
            }
        };
        front.ast = ast;
        match slot_update(front, caches, item_scans, env, None, &fn_at, cores, crate_ids, &scan_of, &mut t) {
            Ok(c) => c,
            Err(e) => {
                front.env_hash = None;
                return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
            }
        }
    };

    let fn_lines_all: Vec<u32> = (0..fn_count).map(|i| scan_of(front, i).1).collect();
    let body_hashes_all: Vec<u64> = (0..fn_count).map(|i| scan_of(front, i).0).collect();
    (map, changed, mention_only, fn_count, mode, fn_lines_all, body_hashes_all, None)
    };
    let scan_of = |front: &Front, i: usize| {
        let _ = front;
        (body_hashes_all[i], fn_lines_all[i])
    };

    // Persist slot assignment when it grew (or was compacted): the next
    // daemon seeds from this file even if this compile later fails,
    // because the assignment itself is already in use by cached C.
    if front.slot_of.len() != front.slot_manifest_stored {
        if let Some(cache) = disk_cache {
            cache.store_slot_manifest(&session_key, &front.slot_of);
        }
        front.slot_manifest_stored = front.slot_of.len();
    }

    // The resolver path computes crate identity from the Cargo graph;
    // the single-file path keeps the session key's identity.
    let crate_ids = if let Some(ids) = front.resolved_crate_ids.take() { ids } else { crate_ids };
    let mut program = match collect::collect(&front.ast, &front.interner, &front.known, crate_ids) {
        Ok(p) => p,
        Err(mut ds) => {
            front.env_hash = None;
            return errors(&mut ds, &map, &src, req);
        }
    };
    if let Some(tables) = resolved_tables {
        program.resolved = Some(Box::new(tables));
    }
    // Route the spliced source std fns: resolve each registry row's
    // mangled name to the local fn the splice defined. A missing fn is
    // a broken std build (the loader found it standalone), so it is an
    // installation error, not a user diagnostic.
    if !std_ranges.is_empty() {
        program.shipped_ranges = std_ranges;
        for def in std_routes {
            let mangled = front.interner.intern(def.mangled);
            match program.fn_names.get(&mangled) {
                Some(&f) => {
                    let path: Vec<Sym> = def.path.iter().map(|s| front.interner.intern(s)).collect();
                    program.std_fns.push((path, f));
                }
                None => {
                    front.env_hash = None;
                    return Response {
                        stderr: format!("error: lust std load failed: spliced std fn `{}` is missing after collect\n", def.path.join("::")),
                        code: 3,
                        ..Default::default()
                    };
                }
            }
        }
    }
    if program.fns.len() != fn_count {
        // The scanner and the parser disagree (only possible with unusual syntax). Start over.
        front.env_hash = None;
        return Response { stderr: "error: internal: function count mismatch; run again\n".into(), code: 3, ..Default::default() };
    }
    t.lap("collect");

    // Read-set dirty walk (section 8.3 step 5, Binding nodes first): a
    // mention-only candidate from a signature-only edit whose recorded
    // reads all still match this program keeps its last passing result
    // (check state and C). Candidates with no stored reads, or with any
    // dirty read (a changed binding answer, a moved method candidate, a
    // failed lookup that now resolves), stay in the work set and lose
    // their stored C, exactly as before this walk existed.
    let mut reads_reused = 0usize;
    let mut reads_invalidated = 0usize;
    if mode == "signatures" && !mention_only.is_empty() {
        let slot_at = |i: usize| front.fn_slot[i] as usize;
        // Clone the candidate read sets out of the caches so the walk can
        // borrow the program while results land back in the caches.
        let candidates: Vec<(usize, Option<crate::driver::graph::Reads>)> =
            mention_only.iter().map(|&i| (i, caches.slot_reads.get(slot_at(i)).cloned().flatten())).collect();
        let mut reused: Vec<usize> = Vec::new();
        for (i, reads) in candidates {
            match reads {
                Some(r) if { let d = program.reads_dirty(&r); reads_invalidated += d; d == 0 } => reused.push(i),
                Some(_) => {
                    let s = slot_at(i);
                    caches.has_out[s] = false;
                    caches.slot_reads[s] = None;
                }
                None => {
                    let s = slot_at(i);
                    caches.has_out[s] = false;
                }
            }
        }
        if !reused.is_empty() {
            reads_reused = reused.len();
            changed.retain(|i| !reused.contains(i));
        }
        t.lap("reads dirty walk");
    }

    // Front end for the functions that need it. A build also needs IR for functions with no C yet.
    let slot = |i: usize| front.fn_slot[i] as usize;
    let mut work = changed.clone();
    if req.cmd == Cmd::Build {
        work.extend((0..program.fns.len()).filter(|&i| !caches.has_out[slot(i)] && !changed.contains(&i)));
    }
    let results = par_map(&work, |&i| {
        let f = LocalDefId(i as u32);
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
        // Store the read set with the result (section 8.2 rule 2): the
        // next signature-only edit replays it in the dirty walk above.
        // Only passing functions get one; a failing function always
        // rechecks (its `ok` is false), so it needs no read set. The
        // stored set gains a `Sig` read of the function itself: body
        // checking reads its own signature (parameter types bind the
        // locals, the return type coerces the tail) through the compat
        // `FnInfo` path, which records nothing, so this entry is the only
        // record of that read. `slot_update` already keeps a fn whose
        // own signature item changed out of the reuse candidates; the
        // read keeps the walk itself honest about the same edge.
        if results[k].1.is_empty()
            && let Some(body) = &results[k].0
            && caches.slot_reads.get(slot(i)).is_some()
        {
            let mut stored = body.reads.clone();
            let _ = program.sig_of(&mut stored, program.def_id(LocalDefId(i as u32)));
            caches.slot_reads[slot(i)] = Some(stored);
        }
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
        let resp = errors(&mut diags, &map, &src, req);
        if leak_at_exit {
            std::mem::forget(results);
            std::mem::forget(program);
        }
        return resp;
    }
    let mut resp = Response::default();
    if req.cmd == Cmd::Check {
        if stats_on() {
            Stats {
                mode,
                fns: program.fns.len(),
                rechecked: work.len(),
                reused: reads_reused,
                invalidated: reads_invalidated,
                instances: front.fn_slot.len(),
                ..Default::default()
            }
            .render(&mut resp.stderr);
        }
        if req.timings {
            let _ = writeln!(
                resp.stderr,
                "lust check {path}: ok ({} functions, {mode}: {} rechecked, {} reused by reads)",
                program.fns.len(),
                work.len(),
                reads_reused
            );
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
    let outs = par_map(&bodies, |(i, b)| cgen::gen_fn(&program, b, &map, scan_of(front, *i).1, &front.fn_slot));
    let n_slots = caches.out.len();
    let groups = cgen::group_fns(n_slots, caches.per_unit);
    let mut dirty_groups = vec![false; groups.len()];
    for ((i, body), out) in bodies.iter().zip(outs) {
        // Stable instance fingerprint: hash the emitted code (see
        // `Caches::slot_fp` for why not the scan body hash).
        if let Some(fp) = caches.slot_fp.get_mut(slot(*i)) {
            let mut h = crate::intern::FxHasher::default();
            std::hash::Hash::hash(&out.code, &mut h);
            *fp = std::hash::Hasher::finish(&h);
        }
        caches.out[slot(*i)] = out;
        caches.has_out[slot(*i)] = true;
        dirty_groups[slot(*i) / caches.per_unit] = true;
        // The slots this fn's C references: itself (its register store)
        // plus every `Fn` call target (printed as `lust_fns[slot]`).
        // The unit's used-slots hash is built from these (section 4.2).
        if let Some(used) = caches.slot_used.get_mut(slot(*i)) {
            used.clear();
            used.push(slot(*i) as u32);
            for block in &body.blocks {
                if let ir::Terminator::Call { target: ir::CallTarget::Fn(f), .. } = &block.term {
                    used.push(front.fn_slot[f.0 as usize]);
                }
            }
        }
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
    // A fresh base: no base yet under this debug setting, or a one-shot
    // (static) build. Growth no longer forces one (section 4.2): when
    // slots outgrow the table capacity or a new fn unit appears, only
    // the table unit (whose C is the capacity plus the unit list; its
    // identity is `graph::table_unit_key`) rebuilds and the base
    // relinks over the existing unit objects. Unrelated units keep
    // their objects, in the session and in the disk unit cache.
    let fresh_base = caches.objects != Some(req.debug) || !caches.persistent;
    let cap_grown = n_slots > caches.table_cap;
    if fresh_base || cap_grown {
        caches.table_cap = n_slots * 2 + 64;
    }
    if fresh_base {
        caches.base_units = groups.len();
    }
    let table_dirty = cap_grown || groups.len() != caches.base_units;
    let rebuild_base = fresh_base || table_dirty || caches.overlays.len() + dirty_fn_units.len() > MAX_OVERLAYS;
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
            if table_dirty && !todo.contains(&(3, false)) {
                todo.push((3, false));
            }
            // The relinked base now registers every current unit.
            caches.base_units = groups.len();
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
        0 => cgen::main_unit(main_slot, map.path(ROOT_FILE), &slot_lines, &registered),
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
            let c = if u == 0 { cgen::main_unit(main_slot, map.path(ROOT_FILE), &slot_lines, &[]) } else { gen_unit(u, false) };
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
    // Per-unit object identity (section 4.2): each fn unit keys on its
    // instances' fingerprints (today: stable per-fn C fingerprints, one
    // instance per fn) plus its used-slots hash; the table unit keys on
    // the full slot
    // manifest. The disk object cache folds the C text in as well (see
    // cache.rs), so a hit is exactly as sound as recompiling. Adding one
    // reachable fn changes no unrelated unit's key: its object is copied
    // from disk and tcc never sees it.
    let manifest = crate::driver::graph::SlotManifest::from_disk_slots(&front.slot_of);
    let unit_key_of = |u: usize| -> crate::driver::graph::UnitKey {
        use crate::driver::graph::{Fingerprint, used_slots_hash};
        match u {
            3 => crate::driver::graph::table_unit_key(&manifest),
            g if g >= FIRST_FN_UNIT => {
                let range = &groups[g - FIRST_FN_UNIT];
                let instances: Vec<Fingerprint> =
                    range.clone().map(|s| Fingerprint(caches.slot_fp.get(s).copied().unwrap_or(0))).collect();
                let mut pairs: Vec<(crate::driver::graph::InstanceKeyHash, u32)> = Vec::new();
                for s in range.clone() {
                    if let Some(used) = caches.slot_used.get(s) {
                        for &used_slot in used {
                            if let Some(k) = manifest.key_at(used_slot) {
                                pairs.push((k, used_slot));
                            }
                        }
                    }
                }
                crate::driver::graph::unit_key(&instances, used_slots_hash(&pairs))
            }
            _ => crate::driver::graph::UnitKey(0),
        }
    };
    let mut unit_hits = 0usize;
    let mut misses: Vec<(PathBuf, String, crate::driver::graph::UnitKey)> = Vec::new();
    if let Err(e) = std::fs::create_dir_all(&dir) {
        caches.objects = None;
        return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
    }
    for ((obj, c), &(u, _)) in units.iter().zip(todo.iter()) {
        let key = unit_key_of(u);
        if disk_cache.as_ref().is_some_and(|cache| cache.unit_object(key, c, req.debug, obj)) {
            unit_hits += 1;
        } else {
            misses.push((obj.clone(), c.clone(), key));
        }
    }
    let miss_units: Vec<(PathBuf, String)> = misses.iter().map(|(o, c, _)| (o.clone(), c.clone())).collect();
    if let Err(e) = crate::tcc::compile_units(&miss_units, req.debug) {
        caches.objects = None;
        return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
    }
    if let Some(cache) = disk_cache {
        for (obj, c, key) in &misses {
            cache.store_unit_object(*key, c, req.debug, obj);
        }
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
    if stats_on() {
        Stats {
            mode,
            fns: program.fns.len(),
            rechecked: work.len(),
            reused: reads_reused,
            invalidated: reads_invalidated,
            c_bytes: units.iter().map(|u| u.1.len()).sum(),
            dirty_units: dirty_fn_units.len(),
            units_compiled: miss_units.len(),
            unit_cache_hits: unit_hits,
            table_rebuilt: todo.iter().any(|&(u, _)| u == 3),
            instances: front.fn_slot.len(),
        }
        .render(&mut resp.stderr);
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Known;

    /// The driver's slot keys and `collect`'s stored def ids are computed in two
    /// places from the same source. They must agree for every function, methods
    /// in repeated impl blocks included, or slots and defs would name different
    /// functions. The reverse map (`local_def`) must round-trip too.
    #[test]
    fn slot_keys_match_collect_def_ids() {
        let src = "\
struct Foo { x: i64 }
fn helper() -> i64 { 1 }
impl Foo { fn get(&self) -> i64 { self.x } }
fn main() { println!(\"{}\", helper()); }
impl Foo { fn set(&mut self, v: i64) { self.x = v; } }
";
        let interner = Interner::default();
        let known = Known::new(&interner);
        let lexed = lexer::lex(src, ROOT_FILE, 0, &interner).unwrap();
        let ast = parser::parse(&lexed, &interner, &known).unwrap();
        let ids = CrateIds { local: def::LOCAL_CRATE, stable: def::synthetic_crate_hash("test.rs", false) };
        let program = collect::collect(&ast, &interner, &known, ids).unwrap();
        let keys = fn_keys(&ast, &fn_locations(&ast), &interner, ids.stable);
        assert_eq!(keys.len(), program.fns.len());
        assert_eq!(program.krate, def::LOCAL_CRATE);
        for (i, k) in keys.iter().enumerate() {
            let local = LocalDefId(i as u32);
            assert_eq!(k.disk, program.disk_id(local), "fn {i}");
            assert_eq!(program.def_id(local).krate, program.krate, "fn {i}");
            assert_eq!(program.local_def(k.disk.hash), Some(local), "fn {i}");
        }
        assert_eq!(program.main.map(|m| program.def_id(m)), keys.get(2).map(|k| crate::def::DefId { krate: ids.local, hash: k.disk.hash }));
    }

    fn req_for(key: crate::protocol::SessionKey) -> Request {
        Request {
            cmd: Cmd::Check,
            file: key.krate.root.clone(),
            session: key,
            out: PathBuf::from("/tmp/out"),
            json: false,
            timings: false,
            debug: false,
            emit_c: None,
            max_errors: 20,
            run_args: None,
            harness: false,
        }
    }

    /// Routing guard: a request for another crate selection never compiles in
    /// this session (code 3 before any file read), and a non-host target is a
    /// clear code 2, not a host build under a foreign name.
    #[test]
    fn compile_refuses_a_misrouted_request() {
        let dir = PathBuf::from("/tmp/lust-route-test");
        let a = crate::protocol::SessionKey::synthetic(std::path::Path::new("/tmp/nope/a.rs"), false);
        let mut b = crate::protocol::SessionKey::synthetic(std::path::Path::new("/tmp/nope/a.rs"), false);
        b.features = vec!["alpha".into()];
        let mut s = Session::new(dir.clone(), false, a.clone());
        let r = compile(&req_for(b), &mut s);
        assert_eq!(r.code, 3);
        assert!(r.stderr.contains("wrong session"), "{}", r.stderr);
        let mut foreign = a;
        foreign.target_triple = "wasm32-wasip1".into();
        let req = req_for(foreign.clone());
        let mut s = Session::new(dir, false, foreign);
        let r = compile(&req, &mut s);
        assert_eq!(r.code, 2);
        assert!(r.stderr.contains("unsupported target"), "{}", r.stderr);
    }
}
