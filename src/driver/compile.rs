// The compile pipeline, cold or incremental. State that an edit can reuse lives in
// `Session` (session.rs).
//
// Incremental rules, from cheapest to most expensive:
//   1. Only function bodies changed (same environment hash: all tokens outside bodies): re-parse,
//      re-check, and re-generate only those functions. One exception: a changed const fn body can
//      move const and static values, array lengths, and discriminants that unchanged bodies baked
//      in, so then every unchanged passing body joins the read-set dirty walk (rule 2's mechanism)
//      and the glue unit (which holds the statics) rebuilds.
//   2. Only top-level functions were added, removed, or changed signature (all other items the
//      same): re-parse the file, but re-check and re-generate only the changed functions and the
//      bodies that mention their names. A changed function always rechecks: its body is checked
//      against its own signature, which the body hash does not cover. A mention-only candidate
//      (own signature unchanged, body unchanged) whose recorded reads all still match the new
//      program (`Program::reads_dirty`, the section 8.3 step 5 dirty walk) is reused without a
//      recheck: per-name binding reads, method-set probes, and failed lookups are precise where
//      name mentions are not. Candidates with no stored reads always recheck.
//   3. Anything else (a type, an impl, a use changed): full mode. Every unchanged passing body
//      is a dirty-walk candidate; only bodies whose recorded reads changed recheck. The caches
//      clear instead when reuse is not provable (first compile, Adt sequence change, or slot
//      compaction; see `slot_update`).
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
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Instant;

/// The session's one source file in its source map. A crate is one file today, so every
/// span the lexer makes in this pipeline names it (docs/ARCH.md section 9.2, S1).
const ROOT_FILE: FileId = FileId(0);

/// Runs macro expansion over one lexed chunk or file (for W-RESOLVE: this
/// is the spot that moves into the 6.1 outline worklist). Expansion is a
/// no-op for files with no macro definitions or non-parser macro calls,
/// so macro-free files keep the current path bit for bit.
fn expand_tokens(
    front: &Front,
    lexed: lexer::Lexed,
    file: &std::path::Path,
    src: &str,
    test: bool,
) -> Result<(lexer::Lexed, Vec<expand::Dep>), Diag> {
    let ctx = expand::ExpandCtx::for_file(&front.interner, &front.known, file, src, test);
    expand::expand_lexed_with_deps(lexed, &ctx)
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
    /// Records sub-stage times measured inside a stage that just
    /// finished (the worklist phases), in place of one `lap` for the
    /// whole stage.
    fn lap_parts(&mut self, parts: Vec<(&'static str, f64)>) {
        self.stages.extend(parts);
        self.last = Instant::now();
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
    reemitted: usize,
}

impl Stats {
    fn render(&self, out: &mut String) {
        let _ = writeln!(
            out,
            "lust-stats: mode={} fns={} rechecked={} reused={} invalidated={} c_bytes={} dirty_units={} units_compiled={} unit_cache_hits={} table_rebuilt={} instances={} reemitted={}",
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
            self.reemitted,
        );
    }
}

/// Unique temp file sequence for base-dir writes in this process. Several
/// sessions here share one base dir (the warm session and guard workers,
/// on several threads in one daemon), so a pid alone does not make a
/// temp name unique.
fn base_tmp_seq() -> u64 {
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// True if `out` exists and still names `soname` (an overwritten output names its newer base instead).
fn output_names_base(out: &Path, soname: &str) -> bool {
    std::fs::read(out).is_ok_and(|bytes| bytes.windows(soname.len()).any(|w| w == soname.as_bytes()))
}

/// True if any known output file built against base file `soname` still exists and still names it.
fn base_still_used(users: &[(String, PathBuf)], soname: &str) -> bool {
    users.iter().filter(|(u, _)| u == soname).any(|(_, out)| output_names_base(out, soname))
}

/// The persistent directory for this session's base libraries. Executables
/// load a base by absolute rpath, so the base must sit somewhere stable:
/// the disk cache dir's `bases/` subdir first (per source tree, next to
/// other lust state), then the user cache dir, and as a last resort the
/// session object dir (old behavior; those bases die with the daemon's
/// temp dir, like any file in temp space). The disk cache being off
/// (`LUST_NO_CACHE`) does not apply here: a base is a run-time part of a
/// built executable, not a cache entry. Resolved once per session.
fn resolve_base_dir(caches: &mut Caches, src_file: &Path) -> PathBuf {
    if let Some(dir) = &caches.base_dir {
        return dir.clone();
    }
    let mut candidates = vec![crate::driver::cache::cache_dir(src_file).join("bases")];
    if let Some(xdg) = std::env::var_os("XDG_CACHE_HOME").filter(|v| !v.is_empty()) {
        candidates.push(PathBuf::from(xdg).join("lust").join("bases"));
    } else if let Some(home) = std::env::var_os("HOME").filter(|v| !v.is_empty()) {
        candidates.push(PathBuf::from(home).join(".cache").join("lust").join("bases"));
    }
    let dir = candidates.into_iter().find(|d| std::fs::create_dir_all(d).is_ok()).unwrap_or_else(|| caches.obj_dir.clone());
    caches.base_dir = Some(dir.clone());
    dir
}

/// Moves a freshly linked base temp file to its final name. If the final
/// file already exists (same content name, or a concurrent build won
/// the rename race), the temp copy is dropped.
fn install_base(tmp: &Path, dest: &Path) -> Result<(), String> {
    if dest.exists() {
        let _ = std::fs::remove_file(tmp);
        return Ok(());
    }
    match std::fs::rename(tmp, dest) {
        Ok(()) => Ok(()),
        Err(_) if dest.exists() => {
            let _ = std::fs::remove_file(tmp);
            Ok(())
        }
        Err(e) => Err(format!("cannot move the base library to {}: {e}", dest.display())),
    }
}

/// Records one executable's use of a base in `<base_dir>/manifest`
/// (`soname <TAB> output` per line), so a later daemon can tell which
/// base files a kept executable still needs after this daemon is gone.
fn record_base_user(base_dir: &Path, soname: &str, out: &Path) {
    use std::io::Write as _;
    let line = format!("{soname}\t{}\n", out.to_string_lossy());
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(base_dir.join("manifest")) {
        let _ = f.write_all(line.as_bytes());
    }
}

/// The pid in a base file name (`libbase-<pid>-<hash>.so`): the process
/// that built it. Base files are also unique per session instance (the
/// session's object dir is mixed into the hash), so one session never
/// links against, and must never delete, another live session's file.
fn base_owner_pid(soname: &str) -> Option<u32> {
    let rest = soname.strip_prefix("libbase-")?;
    let pid = rest.split('-').next()?;
    if !pid.is_empty() && pid.bytes().all(|b| b.is_ascii_digit()) { pid.parse().ok() } else { None }
}

/// Deletes base files in `base_dir` that the manifest proves dead: every
/// recorded output for the base is gone or now names a different base.
/// A base whose owning process is still alive is never deleted: it may
/// be a live session's current base, which the owner will load on its
/// next link even if the last executable was overwritten since.
/// `exiting_pid` names a live-but-exiting owner (this daemon at
/// shutdown) whose files count as ownerless. Files with no manifest
/// entry are kept (an entry is appended right after its executable
/// links, so an unrecorded file may be in use by a concurrent build).
/// Also deletes half-written rebuild temp files
/// (`libbase-tmp-<pid>-*.so`) whose pid is gone. The manifest is
/// rewritten with only the kept, deduplicated entries. Called on a
/// session's first base build and on daemon exit.
pub fn sweep_bases(base_dir: &Path, exiting_pid: u32) {
    // Half-written temp bases from crashed builds. /proc presence is
    // the liveness probe (Linux hosts only; elsewhere the file stays).
    if let Ok(rd) = std::fs::read_dir(base_dir) {
        for e in rd.flatten() {
            let name = e.file_name().to_string_lossy().into_owned();
            if let Some(rest) = name.strip_prefix("libbase-tmp-")
                && let Some(pid) = rest.split('-').next()
                && pid.parse::<u32>().is_ok()
                && pid != std::process::id().to_string()
                && !Path::new(&format!("/proc/{pid}")).exists()
            {
                let _ = std::fs::remove_file(e.path());
            }
        }
    }
    let manifest = base_dir.join("manifest");
    let Ok(text) = std::fs::read_to_string(&manifest) else { return };
    // (soname, outputs) in first-seen order, outputs deduplicated.
    let mut entries: Vec<(String, Vec<PathBuf>)> = Vec::new();
    for line in text.lines() {
        let Some((soname, out)) = line.split_once('\t') else { continue };
        if soname.is_empty() || out.is_empty() {
            continue;
        }
        match entries.iter_mut().find(|(s, _)| s == soname) {
            Some((_, outs)) => {
                let p = PathBuf::from(out);
                if !outs.contains(&p) {
                    outs.push(p);
                }
            }
            None => entries.push((soname.to_string(), vec![PathBuf::from(out)])),
        }
    }
    let owner_alive = |soname: &str| match base_owner_pid(soname) {
        Some(pid) if pid == exiting_pid => false,
        Some(pid) => pid == std::process::id() || Path::new(&format!("/proc/{pid}")).exists(),
        None => false,
    };
    let mut kept = String::new();
    for (soname, outs) in &entries {
        if owner_alive(soname) || outs.iter().any(|o| output_names_base(o, soname)) {
            for o in outs {
                kept.push_str(&format!("{soname}\t{}\n", o.to_string_lossy()));
            }
        } else {
            let _ = std::fs::remove_file(base_dir.join(soname));
        }
    }
    let tmp = base_dir.join(format!("manifest.tmp{}-{}", std::process::id(), base_tmp_seq()));
    if std::fs::write(&tmp, kept).is_ok() && std::fs::rename(&tmp, &manifest).is_err() {
        let _ = std::fs::remove_file(&tmp);
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

/// FxHash of one source file's current text in the map: the guard
/// under which cached IR spans stay valid (`ir_cache::CachedBody`).
fn file_text_hash(map: &SourceMap, file: FileId) -> u64 {
    let mut h = crate::intern::FxHasher::default();
    std::hash::Hash::hash(map.text(file).unwrap_or(""), &mut h);
    std::hash::Hasher::finish(&h)
}

/// The Adt and top-level static indices `collect` will assign for
/// one Ast under the session `DefOrder`, predicted with the same
/// hash and rank rules collect uses, plus whether this Ast has a
/// shape whose derived indices can shift on growth (generic
/// parameters anywhere, or a nested static). The slot update
/// compares the prediction with the last parse's indices: cached
/// output carries session-local indices (CTy in glue and type
/// sets, static indices in IR), so it is reusable only when every
/// old def keeps its index.
fn predicted_def_ids(
    ast: &Ast,
    interner: &Interner,
    stable: StableCrateHash,
    order: &collect::DefOrder,
) -> (FxMap<crate::def::DefPathHash, u32>, FxMap<crate::def::DefPathHash, u32>, bool) {
    let mut adt_hashes: Vec<crate::def::DefPathHash> = Vec::new();
    let mut static_hashes: Vec<crate::def::DefPathHash> = Vec::new();
    let mut counts: FxMap<Sym, u32> = FxMap::default();
    let mut fragile = false;
    let has_params = |g: &crate::ast::Generics| !g.params.is_empty();
    for item in &ast.items {
        match &item.kind {
            ItemKind::Struct(s) => {
                fragile |= has_params(&s.generics);
                let disamb = *counts.entry(s.name).and_modify(|c| *c += 1).or_insert(0);
                adt_hashes.push(def::item_hash(stable, &[], def::DefKind::Adt, interner.get(s.name), disamb));
            }
            ItemKind::Enum(e) => {
                fragile |= has_params(&e.generics);
                let disamb = *counts.entry(e.name).and_modify(|c| *c += 1).or_insert(0);
                adt_hashes.push(def::item_hash(stable, &[], def::DefKind::Adt, interner.get(e.name), disamb));
            }
            ItemKind::Union(u) => {
                // Collect numbers no Adt for a union today, but the
                // old sequence hash counted it as an Adt-shaped def:
                // keep it in the map so a union edit still guards.
                fragile |= has_params(&u.generics);
                let disamb = *counts.entry(u.name).and_modify(|c| *c += 1).or_insert(0);
                adt_hashes.push(def::item_hash(stable, &[], def::DefKind::Adt, interner.get(u.name), disamb));
            }
            ItemKind::Static(s) => {
                static_hashes.push(def::item_hash(stable, &[], def::DefKind::Static, interner.get(s.name), 0));
            }
            ItemKind::Fn(f) => fragile |= has_params(&f.generics),
            ItemKind::Impl(imp) => {
                fragile |= has_params(&imp.generics) || imp.fns.iter().any(|f| has_params(&f.generics));
            }
            ItemKind::Trait(t) => fragile |= has_params(&t.generics),
            _ => {}
        }
    }
    for item in &ast.stmt_items {
        match &item.kind {
            ItemKind::Static(_) => fragile = true,
            ItemKind::Fn(f) => fragile |= has_params(&f.generics),
            _ => {}
        }
    }
    let to_map = |hashes: &[crate::def::DefPathHash], ranks: Vec<u32>| -> FxMap<crate::def::DefPathHash, u32> {
        hashes.iter().copied().zip(ranks).collect()
    };
    let adts = to_map(&adt_hashes, collect::stable_ranks_preview(&order.adts, &adt_hashes));
    let statics = to_map(&static_hashes, collect::stable_ranks_preview(&order.statics, &static_hashes));
    (adts, statics, fragile)
}

/// True when every def in `prev` is present in `new` at the same index.
fn ids_kept(prev: &FxMap<crate::def::DefPathHash, u32>, new: &FxMap<crate::def::DefPathHash, u32>) -> bool {
    prev.iter().all(|(h, id)| new.get(h) == Some(id))
}

/// True when a disk-loaded `order` names none of this parse's defs:
/// a stale file for a different def set. The file's stable crate
/// hash already matched at decode, so zero overlap means the
/// crate's types were replaced wholesale; the caller drops the
/// order and numbers fresh. An empty order or an empty parse is
/// never stale (nothing to distrust, or nothing to number yet).
fn def_order_stale(
    order: &collect::DefOrder,
    adt_ids: &FxMap<crate::def::DefPathHash, u32>,
    static_ids: &FxMap<crate::def::DefPathHash, u32>,
) -> bool {
    let loaded_any = !order.adts.is_empty() || !order.statics.is_empty();
    let current_any = !adt_ids.is_empty() || !static_ids.is_empty();
    let overlap = order.adts.iter().any(|h| adt_ids.contains_key(h)) || order.statics.iter().any(|h| static_ids.contains_key(h));
    loaded_any && current_any && !overlap
}

/// True when the non-fn item hash sequence differs between two item
/// lists (a type, impl, const, or structure edit happened).
fn nonfn_items_changed(old: &[scan::ItemScan], new: &[scan::ItemScan]) -> bool {
    let others = |items: &[scan::ItemScan]| items.iter().filter(|i| i.fn_name.is_none()).map(|i| i.hash).collect::<Vec<_>>();
    others(old) != others(new)
}

/// After a parse that was not "bodies only": update item tables, assign slots by
/// stable def hash, and pick the functions to re-check. Returns (changed,
/// mention_only, const_fn_changed): changed local ids as indexes, plus the subset the read-set
/// dirty walk may still reuse after collect (body hash equal, last check
/// passed, own signature item unchanged), plus whether a const fn's body or
/// signature changed. A const fn change can move const and static values,
/// array lengths, and discriminants that other items baked in, so every
/// unchanged passing body becomes a walk candidate then, as in full mode;
/// the caller also rebuilds the glue unit (it holds the statics). In signatures mode the candidates
/// are the bodies that mention a changed name; in full mode every unchanged
/// passing body is a candidate and the walk decides from its recorded reads
/// (Binding, MethodSet, ImplSet, Sig, Layout; Sig fingerprints hash named
/// Adt layouts deeply, so type and impl edits dirty through them). Full
/// mode falls back to clearing every cache when reuse is not provable: the
/// first compile, an Adt or static index change (cached C and glue carry
/// session-local indices), or slot compaction (cached C carries slot
/// numbers). The one failure is a def hash collision (src/def.rs): an
/// internal error the caller turns into a code 3 response.
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
) -> Result<(Vec<usize>, Vec<usize>, bool), String> {
    let fn_count = fn_at.len();
    front.fn_loc = fn_locations(&front.ast);
    let had_env = front.env_hash.is_some();
    // Cached output stays reusable in full mode when every Adt and
    // static of the last parse keeps its session-local index in
    // this parse (pure additions append at the end of the session
    // order), except that growth in a fragile program (generics,
    // nested statics) can shift derived indices the maps do not
    // name, so growth there still clears.
    let (mut adt_ids, mut static_ids, mut fragile) = predicted_def_ids(&front.ast, &front.interner, crate_ids.stable, &front.def_order);
    // A def order loaded from disk is trusted only when it names at
    // least one def of this parse (`def_order_stale`).
    if front.def_order_loaded {
        front.def_order_loaded = false;
        if def_order_stale(&front.def_order, &adt_ids, &static_ids) {
            front.def_order = collect::DefOrder::default();
            front.def_order_stored = 0;
            (adt_ids, static_ids, fragile) = predicted_def_ids(&front.ast, &front.interner, crate_ids.stable, &front.def_order);
        }
    }
    let grew = adt_ids.len() > front.prev_adt_ids.len() || static_ids.len() > front.prev_static_ids.len();
    let ids_stable = had_env
        && ids_kept(&front.prev_adt_ids, &adt_ids)
        && ids_kept(&front.prev_static_ids, &static_ids)
        && !(grew && (fragile || front.prev_order_fragile));
    front.prev_adt_ids = adt_ids;
    front.prev_static_ids = static_ids;
    front.prev_order_fragile = fragile;
    let nonfn_changed = had_env && nonfn_items_changed(&front.items, &item_scans);
    front.env_hash = Some(env);
    front.items = item_scans;
    let compact = front.slot_of.len() > fn_count * 2 + 64;
    // Full mode may keep the caches (and let the dirty walk pick the
    // work set) only when Adt and static ids are stable. Slot
    // compaction renumbers, but per-slot state remaps by stable
    // identity below and C re-emits from cached IR in the tail, so
    // it preserves too.
    let full_walk = changed_names.is_none() && ids_stable;
    // Per-slot state taken out for a compaction remap, keyed back in
    // by stable identity after assignment.
    struct SlotVecs {
        ok: Vec<bool>,
        out: Vec<FnOut>,
        has_out: Vec<bool>,
        reads: Vec<Option<crate::driver::graph::Reads>>,
        used: Vec<Vec<u32>>,
        fp: Vec<u64>,
        ir: Vec<Option<super::ir_cache::CachedBody>>,
        hash: Vec<u64>,
        head: Vec<u64>,
    }
    let mut remap: Option<(FxMap<DiskDefId, u32>, SlotVecs)> = None;
    if full_walk && compact {
        let old = SlotVecs {
            ok: std::mem::take(&mut caches.ok),
            out: std::mem::take(&mut caches.out),
            has_out: std::mem::take(&mut caches.has_out),
            reads: std::mem::take(&mut caches.slot_reads),
            used: std::mem::take(&mut caches.slot_used),
            fp: std::mem::take(&mut caches.slot_fp),
            ir: std::mem::take(&mut caches.slot_ir),
            hash: std::mem::take(&mut front.slot_hash),
            head: std::mem::take(&mut front.slot_head),
        };
        remap = Some((front.slot_of.clone(), old));
        front.slot_of.clear();
        front.slot_paths.clear();
        front.slot_manifest_stored = 0;
        // The base relinks under the new numbers; renumbered C is
        // re-emitted from cached IR in the tail (or rechecked when no
        // IR is cached), never reused as-is.
        caches.objects = None;
        caches.overlays.clear();
    }
    if changed_names.is_none() && !full_walk {
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
        caches.slot_ir.clear();
        front.slot_hash.clear();
        front.slot_head.clear();
        caches.glue = GlueSet::default();
        caches.objects = None;
        caches.overlays.clear();
        // Cold builds gain nothing from many small units: each extra unit pays a tcc process
        // start and a header parse. Use about one unit per core. The daemon keeps small
        // units, so an edit recompiles little code.
        caches.per_unit =
            if caches.persistent { (fn_count / (cores * 4)).clamp(16, 256) } else { (fn_count / cores.max(1)).clamp(64, 512) };
    }
    if full_walk && nonfn_changed {
        // A type or impl edit can change the C type definitions and
        // glue that every unit header carries, even in units whose fns
        // the walk will reuse. Force a fresh base: all units reassemble
        // from the preserved per-fn C, and the per-unit disk cache
        // (whose key includes the C text) serves every unit whose text
        // did not in fact change, so tcc still sees only the units
        // whose types moved.
        caches.objects = None;
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
    caches.slot_ir.resize_with(n_slots, || None);
    front.slot_hash.resize(n_slots, 0);
    front.slot_head.resize(n_slots, 0);
    // Compaction remap: move each live fn's per-slot state from its
    // old slot to its new one, by stable identity.
    if let Some((old_map, mut old)) = remap {
        for (i, k) in keys.iter().enumerate() {
            let Some(&old_slot) = old_map.get(&k.disk) else { continue };
            let old_slot = old_slot as usize;
            let new_slot = front.fn_slot[i] as usize;
            if old_slot >= old.ok.len() {
                continue;
            }
            caches.ok[new_slot] = old.ok[old_slot];
            caches.has_out[new_slot] = old.has_out[old_slot];
            caches.out[new_slot] = std::mem::take(&mut old.out[old_slot]);
            caches.slot_reads[new_slot] = old.reads[old_slot].take();
            caches.slot_used[new_slot] = std::mem::take(&mut old.used[old_slot]);
            caches.slot_fp[new_slot] = old.fp[old_slot];
            caches.slot_ir[new_slot] = old.ir[old_slot].take();
            front.slot_hash[new_slot] = old.hash[old_slot];
            front.slot_head[new_slot] = old.head[old_slot];
        }
    }
    // Every fn's head hash at this parse (see `Front::slot_head`), and
    // whether it is a const fn (its body feeds const evaluation, so a
    // body edit can move values other items baked in).
    let head_ast = &front.ast;
    let (heads, is_const): (Vec<u64>, Vec<bool>) = par_map(&front.fn_loc, |&(item, sub)| {
        let f = match (item != usize::MAX, sub) {
            (false, Some(k)) => match &head_ast.stmt_items[k].kind {
                ItemKind::Fn(d) => d,
                _ => unreachable!("fn_loc out of date"),
            },
            _ => match (&head_ast.items[item].kind, sub) {
                (ItemKind::Fn(d), None) => d,
                (ItemKind::Impl(imp), Some(k)) => &imp.fns[k],
                _ => unreachable!("fn_loc out of date"),
            },
        };
        (super::ast_hash::fn_head_hash(head_ast, f), f.qual.is_const)
    })
    .into_iter()
    .unzip();
    for slot in (0..n_slots).filter(|&s| !live[s]) {
        caches.out[slot] = FnOut::default();
        caches.has_out[slot] = true;
        caches.ok[slot] = true;
        caches.slot_reads[slot] = None;
        caches.slot_used[slot].clear();
        caches.slot_fp[slot] = 0;
        caches.slot_ir[slot] = None;
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
    // A const fn whose body hash or signature item changed: its old
    // results may sit inside const and static values, array lengths,
    // and discriminants across the crate. Collect re-evaluates those
    // items, and their new values ride in `Sig` and `Layout`
    // fingerprints; making every unchanged passing body a candidate
    // lets the dirty walk find the readers. (A brand-new const fn also
    // sets this: one needless walk, no wrong reuse.)
    // The token scan and the Ast can disagree on the fn count for
    // unusual shapes (an impl inside a body, which collect rejects
    // with its own diagnostic): pair scan index i with Ast index i
    // only where both lists have an entry, and never index past
    // either list. `collect` runs next and gives the real answer;
    // the tail's count guard catches any remaining disagreement.
    // On disagreement the const-fn question answers "may have
    // changed", so no body is reused on a guess.
    let paired = fn_count.min(front.fn_loc.len());
    let const_fn_changed = fn_count != front.fn_loc.len()
        || (0..paired).any(|i| {
            is_const[i]
                && (front.slot_hash.get(front.fn_slot[i] as usize).copied().unwrap_or(0) != scan_of(front, i).0
                    || (keys[i].free && names.contains(&keys[i].name)))
        });
    let mut changed = Vec::new();
    let mut mention_only = Vec::new();
    for i in 0..paired {
        let slot = front.fn_slot[i] as usize;
        let (hash, _) = scan_of(front, i);
        let idents = &front.chunks[fn_at[i].0].scan.body_idents[fn_at[i].1];
        let own_sig_changed = keys[i].free && names.contains(&keys[i].name);
        let mentions = own_sig_changed || idents.iter().any(|s| names.contains(s));
        let body_same = front.slot_hash[slot] == hash;
        // A changed head (parameter names, patterns, types) always
        // rechecks the fn itself: no read set covers the bindings its
        // own head creates. The stored hash advances with the body
        // hash below, before the check runs, under the same rule.
        let head_same = front.slot_head[slot] == heads[i];
        if (full_walk || const_fn_changed) && body_same && head_same && caches.ok[slot] {
            // Full-mode (or const-fn-edit) candidate: the body is unchanged and passed
            // before, so only its recorded reads can dirty it. It
            // stays in `changed` (the walk in `compile` removes the
            // clean ones) and keeps its passing mark and C until the
            // walk decides, exactly like a mention-only candidate.
            mention_only.push(i);
            changed.push(i);
            continue;
        }
        if !body_same || !head_same || !caches.ok[slot] || mentions {
            if body_same && head_same && caches.ok[slot] && mentions && !own_sig_changed {
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
            front.slot_head[slot] = heads[i];
            changed.push(i);
        }
    }
    t.lap(if names.is_empty() { "parse (par)" } else { "parse changed chunks" });
    Ok((changed, mention_only, const_fn_changed))
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
    par_map(fn_loc, |&(item, sub)| match (item != usize::MAX, sub) {
        (false, Some(k)) => {
            let d = match &ast.stmt_items[k].kind {
                ItemKind::Fn(d) => d,
                _ => unreachable!("fn_loc points at a function"),
            };
            let seg = format!("#nested{k}");
            let (hash, path) = def::free_fn_path(stable, &[seg.as_str()], interner.get(d.name));
            key(hash, path, true, d.name)
        }
        _ => match (&ast.items[item].kind, sub) {
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
        },
    })
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
    // Nested fns follow, in stmt item order, marked with a usize::MAX item
    // index and the stmt item index as the sub index (collect's order).
    for (i, item) in ast.stmt_items.iter().enumerate() {
        if matches!(item.kind, ItemKind::Fn(_)) {
            out.push((usize::MAX, Some(i)));
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
/// The worklist reruns per request (per-file caches inside it are
/// W-DRIVER phase 2 step B), but checking and codegen are incremental:
/// the merged Ast is scanned structurally (`ast_hash`), the same
/// bodies/signatures/full mode split as the single-file path picks
/// the slot update, and the shared tail's read-set dirty walk reuses
/// every body whose recorded reads still match. Returns the tail
/// tuple (map, changed, mention-only, const-fn-changed, fn count,
/// mode, fn lines, body hashes, tables).
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
) -> Result<(SourceMap, Vec<usize>, Vec<usize>, bool, usize, &'static str, Vec<u32>, Vec<u64>, Option<crate::resolve::imports::ResolvedTables>), Response> {
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
        (unit.target.src_path.clone(), root_text, ids, env, unit.deps.clone(), unit.package.name.replace('-', "_"))
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
            deps: externs.clone(),
        };
        match worklist::resolve_crate_cached(&input, &front.interner, &front.known, &mut front.resolve_cache) {
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
    let worklist::ResolvedCrate {
        ast, map, tables, fn_lines, body_hashes: _, structure_hash, expand_deps, timings: resolve_timings, scans, ..
    } =
        resolved;
    t.lap_parts(resolve_timings);
    let fn_count = fn_lines.len();
    // Dropping the previous merged Ast walks every node string and
    // Vec; at crate scale that is milliseconds on the request path.
    // A large old Ast drops on a side thread.
    let old_ast = std::mem::replace(&mut front.ast, ast);
    if old_ast.exprs.len() > 20_000 {
        std::thread::spawn(move || drop(old_ast));
    }
    front.map = map.clone();
    front.src.clone_from(&root_text);
    front.resolved_crate_ids = Some(crate_ids);
    // Structural scan of the merged Ast, assembled by the worklist
    // from per-file chunk scans (real per-item hashes without
    // bodies, per-fn body hashes, and body identifier sets). The
    // worklist's module/import structure hash rides in as one extra
    // non-fn item scan at the end: flattening dropped the `mod` and
    // `use` items from the Ast, so without it an import-only edit
    // would look like a body-only edit (or no edit at all).
    if scans.bodies.len() != fn_count {
        // The worklist and the Ast scan disagree on the fn list: an
        // internal error, never a guess at reuse.
        front.env_hash = None;
        return Err(Response { stderr: "error: internal: resolver function count mismatch; run again\n".into(), code: 3, ..Default::default() });
    }
    let body_hashes: Vec<u64> = scans.bodies.iter().map(|b| b.0).collect();
    let mut item_scans = scans.items;
    item_scans.push(scan::ItemScan { hash: structure_hash, fn_name: None });
    t.lap("ast scan");
    // One synthetic chunk: the tail's slot update reads body idents
    // from chunk scans; per-fn hashes and lines ride in through
    // `scan_of` below.
    let lexed = match lexer::lex(&root_text, ROOT_FILE, 0, &front.interner) {
        Ok(l) => l,
        Err(mut d) => return Err(errors(std::slice::from_mut(&mut d), &map, &root_text, req)),
    };
    let n_items = front.ast.items.len();
    front.chunks = vec![Chunk {
        start: 0,
        text: root_text,
        lexed,
        lexed_start: 0,
        scan: scan::ChunkScan {
            fns: body_hashes.iter().map(|&body_hash| scan::FnScan { body_hash, nested: false, fn_offset: 0, body: 0..0 }).collect(),
            items: item_scans.clone(),
            body_idents: scans.bodies.into_iter().map(|b| b.1).collect(),
            ends_at_boundary: true,
        },
        items: Some(0..n_items),
        expand_deps,
    }];
    let env = scan::env_hash(item_scans.iter());
    // The same mode split as the single-file path. Bodies mode goes
    // through `slot_update` with no changed names to name: a changed
    // body hash (or a fn whose last check failed) is exactly its
    // recheck rule, and the Ast is already freshly parsed here.
    let bodies_only = front.env_hash == Some(env) && front.fn_slot.len() == fn_count;
    let changed_names = if bodies_only {
        Some(Vec::new())
    } else if front.env_hash.is_none() {
        None
    } else {
        fn_only_changes(&front.items, &item_scans)
    };
    let mode = if bodies_only {
        "bodies"
    } else if changed_names.is_some() {
        "signatures"
    } else {
        "full"
    };
    let fn_at: Vec<(usize, usize)> = (0..fn_count).map(|i| (0, i)).collect();
    let cores = std::thread::available_parallelism().map_or(4, |n| n.get());
    let lines = fn_lines.clone();
    let hashes = body_hashes.clone();
    let scan_of = |_: &Front, i: usize| (hashes[i], lines[i]);
    let (changed, mention_only, const_fn_changed) =
        match slot_update(front, caches, item_scans, env, changed_names, &fn_at, cores, crate_ids, &scan_of, t) {
            Ok(c) => c,
            Err(e) => {
                front.env_hash = None;
                return Err(Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() });
            }
        };
    Ok((map, changed, mention_only, const_fn_changed, fn_count, mode, fn_lines, body_hashes, Some(tables)))
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
        if session.front.def_order.adts.is_empty()
            && session.front.def_order.statics.is_empty()
            && let Some(cache) = &session.disk_cache
            && let Some(order) = cache.load_def_order(&session.key, crate_ids.stable)
        {
            session.front.def_order_stored = order.adts.len() + order.statics.len();
            session.front.def_order = order;
            session.front.def_order_loaded = true;
        }
    }
    let session_key = session.key.clone();
    let Session { front, caches, std_cache, disk_cache, .. } = session;
    t.lap("read");

    // Resolver routing (W-RESOLVE): a manifest-selected crate, or a root
    // file that mentions modules, imports, cfg, or const/static/type
    // items, compiles through the outline worklist. Routing follows the current text, never just the
    // session's past: a fresh session routes by these same two facts, so
    // a warm session that stayed on the worklist after an edit removed
    // the trigger would answer through a different front end than a cold
    // compile for the same bytes (the two front ends order expansion and
    // parse errors differently; fuzz realish seed 107, iter 585). When
    // the route falls back, drop the resolver-built front state (merged
    // AST, synthetic chunk, spliced source): the chunk path must never
    // reuse it, and with `env_hash` cleared the request rebuilds in full
    // mode, which resets the caches in `slot_update`.
    let wants_resolver =
        req.session.krate.manifest_path.is_some() || crate::resolve::worklist::needs_resolve(&src, &front.interner);
    if front.resolved_crate && !wants_resolver {
        front.ast = Ast::default();
        front.env_hash = None;
        front.prev_adt_ids.clear();
        front.prev_static_ids.clear();
        front.prev_order_fragile = false;
        front.items.clear();
        front.fn_loc.clear();
        front.fn_slot.clear();
        front.slot_hash.clear();
        front.slot_head.clear();
        front.chunks.clear();
        front.src.clear();
        front.map = SourceMap::default();
        front.resolved_crate = false;
        front.resolved_crate_ids = None;
    }
    let use_resolver = front.resolved_crate || wants_resolver;

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
    let (map, mut changed, mention_only, const_fn_changed, fn_count, mode, fn_lines_all, body_hashes_all, resolved_tables) = if use_resolver {
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
    // A chunk whose expansion read a file or env value that has since
    // changed expands differently now, so no chunk is reused this
    // request (expansion is per chunk, but a changed include can hold
    // macro definitions other chunks used; dropping all is the simple
    // sound rule). Added for W-MACRO (docs/ARCH.md section 6.4).
    // Same for a chunk whose expansion baked in a position (`line!`):
    // reused at a different start line its baked values are wrong.
    let line_of = |text: &str, at: usize| text.as_bytes()[..at.min(text.len())].iter().filter(|&&b| b == b'\n').count();
    let pos_stale = front.chunks.iter().any(|c| {
        if !c.expand_deps.contains(&expand::Dep::Position) {
            return false;
        }
        if c.start + c.text.len() <= prefix {
            false
        } else if c.start >= old_len - suffix && suffix > 0 {
            line_of(&front.src, c.start) != line_of(&src, (c.start as i64 + delta) as usize)
        } else {
            false
        }
    });
    let deps_stale = pos_stale || front.chunks.iter().any(|c| expand::deps_stale(&c.expand_deps));
    let mut kept_front = Vec::new();
    let mut kept_back = Vec::new();
    for c in std::mem::take(&mut front.chunks) {
        if deps_stale {
            continue;
        }
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
            |(l, deps)| {
                let sc = scan::scan(&l);
                (l, sc, deps)
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
            Ok((whole, deps)) => {
                let sc = scan::scan(&whole);
                front.chunks =
                    vec![Chunk { start: 0, text: src.clone(), lexed: whole, lexed_start: 0, scan: sc, items: None, expand_deps: deps }];
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
                    let (_, (lexed, sc, deps)) = next_fresh.take().unwrap();
                    next_fresh = fresh.next();
                    Chunk { start: a, text: src[a..b].to_string(), lexed, lexed_start: a, scan: sc, items: None, expand_deps: deps }
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
    let fn_at: Vec<(usize, usize)> = {
        // Collect's LocalDefId order: top-level fns first, then nested.
        let mut tops: Vec<(usize, usize)> = Vec::new();
        let mut nested: Vec<(usize, usize)> = Vec::new();
        for (c, ch) in front.chunks.iter().enumerate() {
            for k in 0..ch.scan.fns.len() {
                if ch.scan.fns[k].nested {
                    nested.push((c, k));
                } else {
                    tops.push((c, k));
                }
            }
        }
        tops.extend(nested);
        tops
    };
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

    let (changed, mention_only, const_fn_changed): (Vec<usize>, Vec<usize>, bool) = if bodies_only {
        let mut changed: Vec<usize> = (0..fn_count)
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
                    let def = match (item != usize::MAX, sub) {
                        (false, Some(k)) => match &mut front.ast.stmt_items[k].kind {
                            ItemKind::Fn(d) => d,
                            _ => unreachable!("fn_loc out of date"),
                        },
                        _ => match (&mut front.ast.items[item].kind, sub) {
                            (ItemKind::Fn(d), None) => d,
                            (ItemKind::Impl(imp), Some(k)) => &mut imp.fns[k],
                            _ => unreachable!("fn_loc out of date"),
                        },
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
        // A changed const fn body can move const and static values,
        // array lengths, and discriminants that unchanged bodies baked
        // in. Make every unchanged passing body a dirty-walk candidate,
        // as `slot_update` does in the other modes: the walk replays
        // their recorded reads against the re-collected program, whose
        // `Sig` fingerprints fold the new values.
        let const_fn_changed = changed.iter().any(|&i| {
            let (item, sub) = front.fn_loc[i];
            let def = match (item != usize::MAX, sub) {
                (false, Some(k)) => match &front.ast.stmt_items[k].kind {
                    ItemKind::Fn(d) => d,
                    _ => unreachable!("fn_loc out of date"),
                },
                _ => match (&front.ast.items[item].kind, sub) {
                    (ItemKind::Fn(d), None) => d,
                    (ItemKind::Impl(imp), Some(k)) => &imp.fns[k],
                    _ => unreachable!("fn_loc out of date"),
                },
            };
            def.qual.is_const
        });
        let mut mention_only = Vec::new();
        if const_fn_changed {
            for i in 0..fn_count {
                if !changed.contains(&i) && caches.ok[front.fn_slot[i] as usize] {
                    mention_only.push(i);
                    changed.push(i);
                }
            }
        }
        (changed, mention_only, const_fn_changed)
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
                    Ok((w, _deps)) => w,
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
    (map, changed, mention_only, const_fn_changed, fn_count, mode, fn_lines_all, body_hashes_all, None)
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
    let mut program = match collect::collect_with_order(&front.ast, &front.interner, &front.known, crate_ids, req.cmd == Cmd::Build, &mut front.def_order) {
        Ok(p) => p,
        Err(mut ds) => {
            front.env_hash = None;
            return errors(&mut ds, &map, &src, req);
        }
    };
    // Persist the def order when collect grew it, like the slot
    // manifest above: the next daemon must number defs as this
    // one did or the disk objects' indices move under it.
    front.def_order_loaded = false;
    if front.def_order.adts.len() + front.def_order.statics.len() != front.def_order_stored {
        if let Some(cache) = disk_cache {
            cache.store_def_order(&session_key, &front.def_order, crate_ids.stable);
        }
        front.def_order_stored = front.def_order.adts.len() + front.def_order.statics.len();
    }
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
    if program.fns.len() < fn_count {
        // The scanner and the parser disagree (only possible with unusual syntax). Start over.
        front.env_hash = None;
        return Response { stderr: "error: internal: function count mismatch; run again\n".into(), code: 3, ..Default::default() };
    }
    // Mono instance slots (docs/ARCH.md section 4.2; W-TRAITS-CORE
    // through W-DRIVER): collect appends materialized instances
    // after the AST fns. They get append-only slots keyed by their
    // instance disk identity, exactly like AST fns in slot_update;
    // templates and trait-method stubs are emptied like dead slots
    // so only plain fns and instances are checked and generated.
    // A generic program always runs its whole concrete work set:
    // instance discovery is a whole-program walk, and the
    // incremental reuse paths key on AST fns only.
    if program.gx.has_generics {
        for i in fn_count..program.fns.len() {
            let disk = program.disk_id(LocalDefId(i as u32));
            if let Err(c) = def::insert_path(&mut front.slot_paths, disk, &format!("instance#{}", disk.hash.0)) {
                front.env_hash = None;
                return Response { stderr: format!("error: {c}\n"), code: 3, ..Default::default() };
            }
            let slot = match front.slot_of.get(&disk) {
                Some(&slot) => slot,
                None => {
                    let slot = front.slot_of.len() as u32;
                    front.slot_of.insert(disk, slot);
                    slot
                }
            };
            front.fn_slot.push(slot);
        }
        let n_slots = front.slot_of.len();
        caches.ok.resize(n_slots, false);
        caches.has_out.resize(n_slots, false);
        caches.out.resize_with(n_slots, FnOut::default);
        caches.slot_reads.resize_with(n_slots, || None);
        caches.slot_used.resize_with(n_slots, Vec::new);
        caches.slot_fp.resize(n_slots, 0);
        caches.slot_ir.resize_with(n_slots, || None);
        front.slot_hash.resize(n_slots, 0);
        for i in 0..program.fns.len() {
            if !matches!(
                program.gx.fn_class.get(i),
                Some(crate::check::generics::FnClass::Plain | crate::check::generics::FnClass::Instance) | None
            ) {
                let s = front.fn_slot[i] as usize;
                caches.out[s] = FnOut::default();
                caches.has_out[s] = true;
                caches.ok[s] = true;
                caches.slot_reads[s] = None;
                caches.slot_used[s].clear();
            }
        }
    }
    t.lap("collect");
    // A full-mode edit or a const fn edit can move what derived glue
    // was generated from. Record that now, for whatever build comes
    // next: this request may be check-only, and the build request
    // after it sees an unchanged file in bodies mode. The build that
    // refreshes the glue clears the flag (see the glue step below).
    if mode == "full" || const_fn_changed {
        caches.glue_stale = true;
    }

    // Read-set dirty walk (section 8.3 step 5): a candidate whose
    // recorded reads all still match this program keeps its last
    // passing result (check state and C). Candidates come from
    // signature-only edits (bodies that mention a changed name) and
    // from full-mode edits (every unchanged passing body; deep `Sig`
    // fingerprints carry type and impl edits into the reads that used
    // them). Candidates with no stored reads, or with any dirty read
    // (a changed binding answer, a moved method candidate, a failed
    // lookup that now resolves, a changed layout), stay in the work
    // set and lose their stored C, exactly as before this walk existed.
    let mut reads_reused = 0usize;
    let mut reads_invalidated = 0usize;
    if !mention_only.is_empty() {
        let slot_at = |i: usize| front.fn_slot[i] as usize;
        // Clone the candidate read sets out of the caches so the walk can
        // borrow the program while results land back in the caches.
        let candidates: Vec<(usize, Option<crate::driver::graph::Reads>)> =
            mention_only.iter().map(|&i| (i, caches.slot_reads.get(slot_at(i)).cloned().flatten())).collect();
        let mut reused: Vec<usize> = Vec::new();
        for (i, reads) in candidates {
            match reads {
                Some(r)
                    if {
                        let d = program.reads_dirty(&r);
                        reads_invalidated += d;
                        d == 0
                    } =>
                {
                    reused.push(i)
                }
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

    // Slot-moved C re-emit (section 4.2): a reused fn whose own slot
    // or a used slot moved since its C was emitted (a compaction
    // renumber) re-emits C from its cached IR, with no recheck. The
    // rebuilt body must reproduce the cached IR fingerprint, and its
    // file text must stand (spans); anything else falls back to a
    // recheck through the ordinary work set.
    let slot = |i: usize| front.fn_slot[i] as usize;
    let mut reemit: Vec<(usize, ir::Body)> = Vec::new();
    let mut reemit_failed: Vec<usize> = Vec::new();
    if req.cmd == Cmd::Build && !program.gx.has_generics {
        let mut file_hashes: FxMap<FileId, u64> = FxMap::default();
        for i in 0..program.fns.len() {
            if changed.contains(&i) {
                continue;
            }
            let s = slot(i);
            if !caches.has_out[s] {
                continue;
            }
            let Some(Some(cached)) = caches.slot_ir.get(s) else { continue };
            let moved = cached.slot_at_gen != s as u32
                || cached.used_at_gen.iter().any(|(disk, at_gen)| front.slot_of.get(disk) != Some(at_gen));
            if !moved {
                continue;
            }
            let file = program.fn_info(LocalDefId(i as u32)).def.name_span.file;
            let fh = *file_hashes.entry(file).or_insert_with(|| file_text_hash(&map, file));
            let rebuilt = if fh == cached.file_hash {
                super::ir_cache::rebuild(&program, cached, LocalDefId(i as u32))
            } else {
                None
            };
            match rebuilt {
                Some(body) if super::ir_cache::ir_fingerprint(&program, &body, &map, scan_of(front, i).1) == cached.ir_fp => {
                    reemit.push((i, body))
                }
                _ => reemit_failed.push(i),
            }
        }
        if !reemit.is_empty() || !reemit_failed.is_empty() {
            t.lap("ir re-emit rebuild");
        }
    }
    let reemitted = reemit.len();

    // Front end for the functions that need it. A build also needs IR for functions with no C yet.
    let mut work = changed.clone();
    work.extend(reemit_failed.iter().copied());
    if req.cmd == Cmd::Build {
        work.extend((0..program.fns.len()).filter(|&i| !caches.has_out[slot(i)] && !changed.contains(&i)));
    }
    if program.gx.has_generics {
        // The whole concrete set, every compile (see the instance
        // slot block above).
        work = (0..program.fns.len())
            .filter(|&i| {
                matches!(
                    program.gx.fn_class.get(i),
                    Some(crate::check::generics::FnClass::Plain | crate::check::generics::FnClass::Instance) | None
                )
            })
            .collect();
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

    // Codegen for the work set, plus any slot-moved re-emits rebuilt
    // from cached IR above.
    let mut bodies: Vec<(usize, ir::Body)> = work.iter().copied().zip(results).filter_map(|(i, r)| r.0.map(|b| (i, b))).collect();
    bodies.extend(reemit);
    // An instance's lines and body span are its template's.
    let line_base_of = |front: &Front, i: usize| -> u32 {
        let scan_i = program.gx.instances.get(&LocalDefId(i as u32)).and_then(|info| info.template_local).map_or(i, |t| t.0 as usize);
        if scan_i < fn_count { scan_of(front, scan_i).1 } else { 0 }
    };
    let outs = par_map(&bodies, |(i, b)| cgen::gen_fn(&program, b, &map, line_base_of(front, *i), &front.fn_slot));
    let n_slots = caches.out.len();
    let groups = cgen::group_fns(n_slots, caches.per_unit);
    let mut dirty_groups = vec![false; groups.len()];
    let mut file_hashes: FxMap<FileId, u64> = FxMap::default();
    for ((i, body), out) in bodies.iter().zip(outs) {
        let s = slot(*i);
        // Instance fingerprint: the lowered IR (see `Caches::slot_fp`),
        // never the emitted C (which prints slot numbers; those ride
        // in the used-slots hash instead).
        let base_line = line_base_of(front, *i);
        let fp = super::ir_cache::ir_fingerprint(&program, body, &map, base_line);
        if let Some(x) = caches.slot_fp.get_mut(s) {
            *x = fp;
        }
        caches.out[s] = out;
        caches.has_out[s] = true;
        dirty_groups[s / caches.per_unit] = true;
        // The slots this fn's C references: itself (its register store)
        // plus every direct call target and fn-pointer value (printed
        // as `lust_fns[slot]` / `lust_tramps[slot]`). The unit's
        // used-slots hash is built from these (section 4.2); the disk
        // pairs are the next renumber's re-emit trigger.
        let targets = super::ir_cache::used_disk_targets(&program, body);
        let mut used_slots = vec![s as u32];
        let mut used_pairs: Vec<(DiskDefId, u32)> = Vec::with_capacity(targets.len());
        for d in &targets {
            if let Some(l) = program.local_def(d.hash).filter(|l| program.disk_id(*l) == *d) {
                let ts = front.fn_slot[l.0 as usize];
                used_slots.push(ts);
                used_pairs.push((*d, ts));
            }
        }
        if let Some(used) = caches.slot_used.get_mut(s) {
            *used = used_slots;
        }
        let file = program.fn_info(LocalDefId(*i as u32)).def.name_span.file;
        let fh = *file_hashes.entry(file).or_insert_with(|| file_text_hash(&map, file));
        if let Some(slot_ir) = caches.slot_ir.get_mut(s) {
            *slot_ir = Some(super::ir_cache::cache_body(&program, body, fh, s as u32, used_pairs, fp));
        }
    }
    // Derived glue (Debug, Clone, Eq, Drop) is keyed by Adt id but
    // generated from field and variant types, and the glue unit also
    // holds the statics. Regenerate every live glue definition and
    // compare text when a compile since the last build saw a
    // full-mode or const fn edit (`glue_stale`, set above), or this
    // build will reassemble a fresh base anyway (`objects` mismatch:
    // first build, a carried-over non-fn change, an error reset). A
    // changed definition forces a fresh base so fn units that carry
    // static copies reassemble too. The statics compare against the
    // fingerprint last built into the glue unit, so a value edit
    // consumed by an earlier check request still rebuilds it here.
    let statics_fp = crate::driver::graph::statics_fingerprint(&program);
    let statics_changed = caches.statics_fp != statics_fp;
    caches.statics_fp = statics_fp;
    let glue_changed = if caches.glue_stale || caches.objects != Some(req.debug) {
        caches.glue_stale = false;
        let (shared_changed, regenerated) =
            caches.glue.refresh(&program, &front.fn_slot, caches.out.iter().flat_map(|o| o.glue.iter()));
        if regenerated {
            caches.objects = None;
        }
        shared_changed || regenerated || statics_changed
    } else {
        caches.glue.add(&program, &front.fn_slot, bodies.iter().flat_map(|(i, _)| caches.out[slot(*i)].glue.iter())) || statics_changed
    };
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
    // Instance slots take their template's line: cgen stores an
    // instance's panic lines relative to it (see `line_base_of`).
    let mut slot_lines = vec![0u32; n_slots];
    for i in 0..front.fn_slot.len().min(program.fns.len()) {
        slot_lines[slot(i)] = line_base_of(front, i);
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
    // instances' IR fingerprints (one instance per fn today) plus its
    // used-slots hash; the table unit keys on the full slot manifest.
    // The disk object cache keys on that alone for keyed units (see
    // cache.rs): C text is a function of the IR and the used slots,
    // so a hit is exactly as sound as recompiling, and a slot change
    // misses and re-emits. Adding one reachable fn changes no
    // unrelated unit's key: its object is copied from disk and tcc
    // never sees it.
    let manifest = crate::driver::graph::SlotManifest::from_disk_slots(&front.slot_of);
    // The stable hash of one C type for unit keys: Adts by def plus
    // layout fingerprint (the unit header prints their definitions),
    // everything else structural.
    fn cty_fp(p: &collect::Program, c: &cgen::CTy) -> u64 {
        fn inner(h: &mut crate::intern::FxHasher, p: &collect::Program, c: &cgen::CTy) {
            use std::hash::Hash;
            match c {
                cgen::CTy::Unit => 0u8.hash(h),
                cgen::CTy::Bool => 1u8.hash(h),
                cgen::CTy::Char => 2u8.hash(h),
                cgen::CTy::Int(i) => (3u8, i.name()).hash(h),
                cgen::CTy::Str => 4u8.hash(h),
                cgen::CTy::String => 5u8.hash(h),
                cgen::CTy::Vec(x) => {
                    6u8.hash(h);
                    inner(h, p, x);
                }
                cgen::CTy::Option(x) => {
                    7u8.hash(h);
                    inner(h, p, x);
                }
                cgen::CTy::Ref(x) => {
                    8u8.hash(h);
                    inner(h, p, x);
                }
                cgen::CTy::Adt(a) => {
                    9u8.hash(h);
                    crate::driver::graph::layout_fingerprint(p, p.def_of_adt(*a)).0.hash(h);
                }
                cgen::CTy::Args => 10u8.hash(h),
                cgen::CTy::Chars => 11u8.hash(h),
                cgen::CTy::Tuple(ts) => {
                    12u8.hash(h);
                    (ts.len() as u64).hash(h);
                    for t in ts {
                        inner(h, p, t);
                    }
                }
                cgen::CTy::Array(x, n) => {
                    (13u8, n).hash(h);
                    inner(h, p, x);
                }
                cgen::CTy::Slice(x) => {
                    14u8.hash(h);
                    inner(h, p, x);
                }
                cgen::CTy::Float(f) => (15u8, f.name()).hash(h),
                cgen::CTy::FnPtr(inputs, out) => {
                    16u8.hash(h);
                    (inputs.len() as u64).hash(h);
                    for t in inputs {
                        inner(h, p, t);
                    }
                    inner(h, p, out);
                }
                cgen::CTy::Result(a, b) => {
                    17u8.hash(h);
                    inner(h, p, a);
                    inner(h, p, b);
                }
            }
        }
        let mut h = crate::intern::FxHasher::default();
        inner(&mut h, p, c);
        std::hash::Hasher::finish(&h)
    }
    let unit_key_of = |u: usize| -> crate::driver::graph::UnitKey {
        use crate::driver::graph::{Fingerprint, used_slots_hash};
        match u {
            3 => crate::driver::graph::table_unit_key(&manifest, caches.table_cap, fn_units.len()),
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
                let base = crate::driver::graph::unit_key(&instances, used_slots_hash(&pairs));
                // Glue placement and header types are unit C inputs
                // the instance fingerprints do not cover: which glue
                // this unit carries statically (versus the shared
                // glue unit), and the layouts of the C types its
                // header declares. Fold both into the key.
                let mut extra: Vec<(u64, u64, bool)> = Vec::new();
                for s in range.clone() {
                    let Some(out) = caches.out.get(s) else { continue };
                    for (g, c) in &out.glue {
                        let shared = caches.glue.shared.as_ref().is_none_or(|set| set.contains(&(g.clone(), c.clone())));
                        let mut gh = crate::intern::FxHasher::default();
                        std::hash::Hash::hash(&std::mem::discriminant(g), &mut gh);
                        extra.push((std::hash::Hasher::finish(&gh), cty_fp(&program, c), shared));
                    }
                    for c in &out.types {
                        extra.push((u64::MAX, cty_fp(&program, c), false));
                    }
                }
                extra.sort_unstable();
                extra.dedup();
                let mut h = crate::intern::FxHasher::default();
                std::hash::Hash::hash(&"cunit-glue-v1", &mut h);
                std::hash::Hash::hash(&base.0, &mut h);
                for e in extra {
                    std::hash::Hash::hash(&e, &mut h);
                }
                crate::driver::graph::UnitKey(std::hash::Hasher::finish(&h))
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
    for ((obj, c), &(u, overlay)) in units.iter().zip(todo.iter()) {
        // An overlay copy of a unit differs from its base copy only
        // in the register symbol name, which no fingerprint above
        // sees: key the two forms apart, or a base object could serve
        // an overlay link (unresolved `lust_overlay_u<N>`).
        let key = if overlay {
            let mut h = crate::intern::FxHasher::default();
            std::hash::Hash::hash(&"cunit-overlay-v1", &mut h);
            std::hash::Hash::hash(&unit_key_of(u).0, &mut h);
            crate::driver::graph::UnitKey(std::hash::Hasher::finish(&h))
        } else {
            unit_key_of(u)
        };
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
        // The base library lives in a persistent dir under a content name
        // (see `resolve_base_dir`): the executable loads it by absolute
        // rpath at run time, so it must survive this daemon and its
        // per-daemon temp dir (`dir`, deleted on daemon exit). A content
        // name also means two sessions or daemons can never overwrite
        // each other's base under a running executable.
        let base_dir = resolve_base_dir(caches, &req.file);
        if !caches.base_swept {
            sweep_bases(&base_dir, 0);
            caches.base_swept = true;
        }
        let base = if rebuild_base {
            caches.base_gen += 1;
            let tmp = base_dir.join(format!("libbase-tmp-{}-{}-{}.so", std::process::id(), caches.base_gen, base_tmp_seq()));
            let built = std::fs::create_dir_all(&base_dir)
                .map_err(|e| format!("cannot create {}: {e}", base_dir.display()))
                .and_then(|_| crate::tcc::link_shared(&all_base, &tmp, req.debug))
                .and_then(|_| {
                    let bytes = std::fs::read(&tmp).map_err(|e| format!("cannot read {}: {e}", tmp.display()))?;
                    // The object dir in the hash makes the name unique to this
                    // session instance, and the pid names the owning process:
                    // see `base_owner_pid`.
                    let (a, b) = crate::driver::cache::hash128(&[&bytes, caches.obj_dir.to_string_lossy().as_bytes()], 41);
                    caches.base_name = format!("base-{}-{a:016x}{b:016x}", std::process::id());
                    let soname = format!("lib{}.so", caches.base_name);
                    install_base(&tmp, &base_dir.join(&soname))?;
                    if !caches.base_files.contains(&soname) {
                        caches.base_files.push_back(soname);
                    }
                    Ok(())
                });
            if built.is_err() {
                let _ = std::fs::remove_file(&tmp);
            }
            t.lap("link libbase.so");
            built
        } else if !caches.base_name.is_empty() && !base_dir.join(format!("lib{}.so", caches.base_name)).exists() {
            // The base file vanished under a live session. The bases dir
            // is in `.lust-cache`, state outside tools may delete as a
            // cache (the edit fuzzer rewrites the crate tree every edit).
            // The base objects still live in the session object dir, so
            // relink the same base under the same name.
            let dest = base_dir.join(format!("lib{}.so", caches.base_name));
            let tmp = base_dir.join(format!("libbase-tmp-{}-relink-{}.so", std::process::id(), base_tmp_seq()));
            let built = std::fs::create_dir_all(&base_dir)
                .map_err(|e| format!("cannot create {}: {e}", base_dir.display()))
                .and_then(|_| crate::tcc::link_shared(&all_base, &tmp, req.debug))
                .and_then(|_| install_base(&tmp, &dest));
            if built.is_err() {
                let _ = std::fs::remove_file(&tmp);
            }
            t.lap("link libbase.so");
            built
        } else {
            Ok(())
        };
        let name = caches.base_name.clone();
        let mut objs = vec![base_obj(0)];
        objs.extend(caches.overlays.iter().map(|&u| overlay_obj(u)));
        base.and_then(|_| crate::tcc::link_with_base(&objs, &base_dir, &name, &req.out, req.debug))
    };
    if let Err(e) = linked {
        caches.objects = None;
        return Response { stderr: format!("error: {e}\n"), code: 3, ..Default::default() };
    }
    // Reference-counted cleanup: record this build as a user of the current base (in memory
    // and in the base dir manifest, for after this daemon exits), then delete old bases past
    // a small grace count while no known output file still references them. A binary the user
    // kept keeps its base; one that was overwritten or deleted does not. A running program
    // keeps its mapped copy after unlink.
    if caches.persistent && !caches.base_name.is_empty() {
        let soname = format!("lib{}.so", caches.base_name);
        if let Some(base_dir) = caches.base_dir.clone() {
            record_base_user(&base_dir, &soname, &req.out);
        }
        caches.base_users.push((soname, req.out.clone()));
    }
    const KEEP_BASES: usize = 4;
    let excess: Vec<String> = caches.base_files.iter().take(caches.base_files.len().saturating_sub(KEEP_BASES)).cloned().collect();
    for soname in excess {
        if !base_still_used(&caches.base_users, &soname) {
            caches.base_files.retain(|x| x != &soname);
            caches.base_users.retain(|(u, _)| u != &soname);
            if let Some(base_dir) = &caches.base_dir {
                let _ = std::fs::remove_file(base_dir.join(&soname));
            }
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
            reemitted,
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

    /// The base sweep never deletes a live owner's base (it may be a live
    /// session's current base, found by fuzz seed 7 multi when a guard
    /// session's first-build sweep deleted the warm session's base), but
    /// deletes a dead owner's, and an exiting owner's when told.
    #[test]
    fn sweep_bases_keeps_live_owners() {
        let dir = std::env::temp_dir().join(format!("lust-basesweep-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let mine = format!("libbase-{}-aaaa.so", std::process::id());
        let dead = "libbase-4000000003-bbbb.so";
        for f in [&mine, &dead.to_string()] {
            std::fs::write(dir.join(f), b"x").unwrap();
        }
        let gone = dir.join("gone.bin");
        std::fs::write(dir.join("manifest"), format!("{mine}\t{}\n{dead}\t{}\n", gone.display(), gone.display())).unwrap();
        sweep_bases(&dir, 0);
        assert!(dir.join(&mine).exists(), "live owner's base kept");
        assert!(!dir.join(dead).exists(), "dead owner's unreferenced base swept");
        sweep_bases(&dir, std::process::id());
        assert!(!dir.join(&mine).exists(), "exiting owner's unreferenced base swept");
        let _ = std::fs::remove_dir_all(&dir);
    }

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

    /// Adt and static indices are stable under reordering and
    /// addition: a fresh order numbers by def hash (not item
    /// order), and a session order keeps every old index when a
    /// new def arrives whose hash sorts before the old ones. The
    /// driver's predicted indices match collect's assignment.
    #[test]
    fn adt_and_static_indices_are_stable() {
        let interner = Interner::default();
        let known = Known::new(&interner);
        let ids = CrateIds { local: def::LOCAL_CRATE, stable: def::synthetic_crate_hash("test.rs", false) };
        // Collects one source and returns its Adt and static indices
        // by name (Program borrows the Ast, so it stays inside).
        let collect_src = |src: &str, order: &mut collect::DefOrder| {
            let lexed = lexer::lex(src, ROOT_FILE, 0, &interner).unwrap();
            let ast = parser::parse(&lexed, &interner, &known).unwrap();
            let (adts, statics, _) = predicted_def_ids(&ast, &interner, ids.stable, order);
            let program = collect::collect_with_order(&ast, &interner, &known, ids, true, order).unwrap();
            for (hash, &id) in &adts {
                let def = crate::def::DefId { krate: ids.local, hash: *hash };
                assert_eq!(program.adt_by_def(def).map(|a| a.0), Some(id), "predicted Adt index");
            }
            for (hash, &idx) in &statics {
                let def = crate::def::DefId { krate: ids.local, hash: *hash };
                assert_eq!(program.static_by_def(def), Some(idx), "predicted static index");
            }
            let by_name = |names: &[&str]| -> Vec<u32> { names.iter().map(|n| program.type_names.get(&interner.intern(n)).map_or(u32::MAX, |a| a.0)).collect() };
            let statics_by_name =
                |names: &[&str]| -> Vec<u32> { names.iter().map(|n| program.static_names.get(&interner.intern(n)).copied().unwrap_or(u32::MAX)).collect() };
            (by_name(&["Alpha", "Mid", "Zed"]), statics_by_name(&["SA", "SM", "SZ"]))
        };

        // Item order does not decide indices in a fresh session.
        let (a, _) = collect_src("struct Zed { x: i64 }\nstruct Alpha { x: i64 }\nfn main() {}\n", &mut collect::DefOrder::default());
        let (b, _) = collect_src("struct Alpha { x: i64 }\nstruct Zed { x: i64 }\nfn main() {}\n", &mut collect::DefOrder::default());
        assert_eq!(a[0], b[0], "Alpha index is order-independent");
        assert_eq!(a[2], b[2], "Zed index is order-independent");

        // One session: adding defs (in any item position) and
        // reordering files keeps every old index.
        let mut order = collect::DefOrder::default();
        let (a1, s1) = collect_src(
            "struct Zed { x: i64 }\nstruct Mid { x: i64 }\nstatic SZ: i64 = 1;\nstatic SM: i64 = 2;\nfn main() {}\n",
            &mut order,
        );
        let (a2, s2) = collect_src(
            "struct Alpha { x: i64 }\nstruct Mid { x: i64 }\nstruct Zed { x: i64 }\nstatic SA: i64 = 3;\nstatic SM: i64 = 2;\nstatic SZ: i64 = 1;\nfn main() {}\n",
            &mut order,
        );
        assert_eq!(a1[1], a2[1], "Mid keeps its index");
        assert_eq!(a1[2], a2[2], "Zed keeps its index");
        assert_eq!(s1[1], s2[1], "SM keeps its index");
        assert_eq!(s1[2], s2[2], "SZ keeps its index");
    }

    /// A disk-loaded def order is stale only when it names none of
    /// the current defs; any overlap (the same crate, edited) keeps
    /// it, and empty sides never count as stale.
    #[test]
    fn loaded_def_order_stale_only_without_overlap() {
        use crate::def::DefPathHash as H;
        let ids = |hs: &[u64]| -> FxMap<H, u32> { hs.iter().enumerate().map(|(i, h)| (H(*h), i as u32)).collect() };
        let mut order = collect::DefOrder::default();
        assert!(!def_order_stale(&order, &ids(&[1]), &ids(&[])), "empty order");
        order.adts = vec![H(10), H(20)];
        order.statics = vec![H(30)];
        assert!(def_order_stale(&order, &ids(&[1, 2]), &ids(&[3])), "no overlap");
        assert!(!def_order_stale(&order, &ids(&[20, 2]), &ids(&[3])), "Adt overlap");
        assert!(!def_order_stale(&order, &ids(&[1]), &ids(&[30])), "static overlap");
        assert!(!def_order_stale(&order, &ids(&[]), &ids(&[])), "empty parse");
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

    /// Resolver routing follows the current text: after a `static` item
    /// routes one compile through the worklist, deleting it must route
    /// the next compile through the chunk path again, exactly as a fresh
    /// session would, and the answers must match. Sticky routing made a
    /// warm session answer through the other front end for the same
    /// bytes (fuzz realish seed 107, iter 585).
    #[test]
    fn resolver_routing_unsticks_when_trigger_goes() {
        let dir = std::env::temp_dir().join(format!("lust-unstick-test-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        let file = dir.join("route.rs");
        let key = crate::protocol::SessionKey::synthetic(&file, false);
        let req = req_for(key.clone());
        let mut s = Session::new(dir.join("obj"), false, key.clone());
        std::fs::write(&file, "static S: i64 = 1;\nfn main() { println!(\"{}\", S); }\n").unwrap();
        let r = compile(&req, &mut s);
        assert_eq!(r.code, 0, "primer: {}", r.stderr);
        assert!(s.front.resolved_crate, "the static item routes through the resolver");
        std::fs::write(&file, "fn main() { println!(\"{}\", xformat!(\"{}\", 1)); }\n").unwrap();
        let warm = compile(&req, &mut s);
        assert!(!s.front.resolved_crate, "routing falls back when the trigger is gone");
        let mut fresh = Session::new(dir.join("obj2"), false, key);
        let cold = compile(&req, &mut fresh);
        assert_eq!(warm.code, 1);
        assert_eq!(warm.code, cold.code);
        assert_eq!(warm.stderr, cold.stderr);
        assert!(warm.stderr.contains("L0802"), "{}", warm.stderr);
        let _ = std::fs::remove_dir_all(&dir);
    }
}
