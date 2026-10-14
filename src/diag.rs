// Diagnostics: every error has a stable code, a message, a source span, and a fix hint for agents.
//
// Human text and `--json` output come from the same `Diag` values. The JSON form is versioned
// (`"schema":1`): one object per line, with the primary span, labeled secondary spans, optional
// concrete edits, and the hash of the exact bytes that were checked. Output is bounded: exact
// duplicates are suppressed and at most `max_errors` diagnostics are shown, followed by an
// explicit truncation record. Truncation never changes the exit status.
use crate::def::DefId;
use std::fmt::Write;

/// The version of the JSON diagnostic schema.
pub const SCHEMA: u32 = 1;
/// Default cap on shown diagnostics (`--max-errors` overrides it; 0 means no cap).
/// The wire protocol carries the value, so this constant documents the default only.
#[allow(dead_code)]
pub const DEFAULT_MAX_ERRORS: usize = 20;

/// One source file in a session's source map. Session-local: a `FileId` must never enter a
/// disk cache key (disk forms use the path; see docs/ARCH.md sections 1.2 and 8.4). Ids are
/// assigned at crate load in sorted canonical path order, then append-only. Today a crate
/// is one file, so every span in it has `FileId(0)`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileId(pub u32);

impl FileId {
    /// Not a source file: a span in it names a line of Rust 1.99's own std
    /// source, for a panic rustc reports inside std (no `#[track_caller]`).
    /// Only literal-text `Panic` terminators carry one (`Span::std_site`);
    /// cgen's `loc` and the IR cache read it before any source map lookup.
    pub const STD_SITE: FileId = FileId(u32::MAX);
}

/// The expansion context of a span: which macro expansion (if any) produced its tokens.
/// `CtxtId(0)` is the root context (ordinary source). `CtxtId(n)` for n > 0 names entry
/// n - 1 of the source map's expansion table. Session-local, like `FileId`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct CtxtId(pub u32);

impl CtxtId {
    /// The root context: tokens that come from no macro expansion.
    pub const ROOT: CtxtId = CtxtId(0);
}

/// A byte range in one source file, plus the expansion context of its tokens.
/// `lo` and `hi` are byte offsets in `file`. Four u32 fields, so `Span` stays small and
/// `Copy`. The default span (file 0, bytes 0..0, root context) is the dummy span for
/// synthetic nodes and for diagnostics that name no source position.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub lo: u32,
    pub hi: u32,
    pub ctxt: CtxtId,
}

impl Span {
    /// A root-context span over bytes `lo..hi` in `file`. The lexer is the main caller.
    pub fn new(file: FileId, lo: u32, hi: u32) -> Span {
        Span { file, lo, hi, ctxt: CtxtId::ROOT }
    }
    /// The smallest span that covers both spans. Both spans must be in the same file. The
    /// result keeps the left span's context: name resolution reads the contexts of the
    /// spans that were combined, never of this cover span (docs/ARCH.md section 6.3).
    ///
    /// Spans from different expansion contexts (a macro argument and the
    /// macro's own tokens) are not ranges of one text: the cover is taken
    /// over their call sites instead, in the root context, which is where
    /// rustc reports a panic in such an expression.
    pub fn to(self, other: Span) -> Span {
        if self.ctxt != other.ctxt {
            let (a, b) = (call_site_span(self), call_site_span(other));
            if a.file == b.file && a.ctxt == b.ctxt {
                return Span { file: a.file, lo: a.lo.min(b.lo), hi: a.hi.max(b.hi), ctxt: a.ctxt };
            }
            return self;
        }
        debug_assert_eq!(self.file, other.file, "Span::to across files");
        Span { file: self.file, lo: self.lo.min(other.lo), hi: self.hi.max(other.hi), ctxt: self.ctxt }
    }
    /// A `FileId::STD_SITE` span: `file` indexes `lust_std_files` in
    /// runtime/panic.c, at 1-based `line` and `col` of that std file.
    pub fn std_site(file: u32, line: u32, col: u32) -> Span {
        Span { file: FileId::STD_SITE, lo: file, hi: (line << 12) | col.min(0xFFF), ctxt: CtxtId::ROOT }
    }
    /// This span moved by `delta` bytes within the same file. The driver uses it when an
    /// edit shifts the kept suffix of a file; file and context do not change.
    pub fn shifted(self, delta: i64) -> Span {
        Span { lo: (self.lo as i64 + delta) as u32, hi: (self.hi as i64 + delta) as u32, ..self }
    }
}

/// A secondary span with a short label (for example, where a borrow starts).
#[derive(Clone, Debug)]
pub struct Label {
    pub span: Span,
    pub text: String,
}

/// One concrete source edit in the same file. `auto` means a tool may apply it without asking.
#[derive(Clone, Debug)]
pub struct Edit {
    pub start: u32,
    pub end: u32,
    pub replacement: String,
    pub auto: bool,
}

#[derive(Clone, Debug)]
pub struct Diag {
    pub code: &'static str,
    pub severity: &'static str,
    pub message: String,
    pub span: Span,
    pub fix: String,
    pub labels: Vec<Label>,
    pub edits: Vec<Edit>,
}

impl Diag {
    pub fn new(code: &'static str, span: Span, message: impl Into<String>, fix: impl Into<String>) -> Diag {
        Diag { code, severity: "error", message: message.into(), span, fix: fix.into(), labels: Vec::new(), edits: Vec::new() }
    }
    /// Adds a labeled secondary span.
    pub fn with_label(mut self, span: Span, text: impl Into<String>) -> Diag {
        self.labels.push(Label { span, text: text.into() });
        self
    }
    /// Adds a concrete edit for this diagnostic.
    #[allow(dead_code)]
    pub fn with_edit(mut self, edit: Edit) -> Diag {
        self.edits.push(edit);
        self
    }
}

/// Error for a Rust syntax form whose AST shape exists (docs/ARCH.md S3b) but whose
/// parser, checker, and codegen land with a later feature package. `code` is the stable
/// Appendix A code for the form's area; `what` names the form in one short phrase.
pub fn not_yet(code: &'static str, span: Span, what: &str) -> Diag {
    Diag::new(code, span, format!("{what} is not supported yet"), "Rewrite this part with the supported subset (see README).")
}

/// Error for a Rust feature that lust will support later but this prototype does not.
pub fn unsupported(span: Span, what: &str) -> Diag {
    Diag::new(
        "L9001",
        span,
        format!("{what} is not supported by the lust prototype yet"),
        "Rewrite this part with the supported subset (see README).",
    )
}

/// Stable hash of the checked source bytes (FNV-1a, 64 bit), as `fnv1a64:<16 hex digits>`.
pub fn source_hash(src: &str) -> String {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in src.as_bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    format!("fnv1a64:{h:016x}")
}

/// Maps byte offsets to 1-based line and column numbers.
#[derive(Clone)]
pub struct LineIndex {
    starts: Vec<u32>,
    /// Each char whose display width differs from its byte length (a
    /// tab, most non-ASCII chars): its byte offset and width minus bytes.
    /// Empty for an ASCII file with no tab. Panic locations count columns
    /// as rustc does, in display width (`display_col`).
    wide: Vec<(u32, i32)>,
}

/// Appends the `LineIndex::wide` entries of `text`, which starts at byte `base`.
fn wide_chars(text: &str, base: usize, out: &mut Vec<(u32, i32)>) {
    if text.is_ascii() && !text.as_bytes().contains(&b'\t') {
        return;
    }
    for (i, ch) in text.char_indices() {
        if ch == '\t' || !ch.is_ascii() {
            let d = crate::colwidth::char_width(ch) as i32 - ch.len_utf8() as i32;
            if d != 0 {
                out.push(((base + i) as u32, d));
            }
        }
    }
}

impl LineIndex {
    pub fn new(src: &str) -> LineIndex {
        // `match_indices` with a char pattern uses memchr, which is much faster than a byte loop.
        let mut starts = Vec::with_capacity(src.len() / 32);
        starts.push(0);
        starts.extend(src.match_indices('\n').map(|(i, _)| i as u32 + 1));
        let mut wide = Vec::new();
        wide_chars(src, 0, &mut wide);
        LineIndex { starts, wide }
    }
    /// The index after an edit replaced `old[a..old_b]` with `new[a..new_b]`: line starts before
    /// the edit are kept, starts inside it are recomputed, and starts after it are shifted.
    pub fn splice(&self, new: &str, a: usize, old_b: usize, new_b: usize) -> LineIndex {
        let delta = new_b as i64 - old_b as i64;
        let keep = self.starts.partition_point(|&s| s as usize <= a);
        let mut starts = Vec::with_capacity(self.starts.len() + 16);
        starts.extend_from_slice(&self.starts[..keep]);
        starts.extend(new[a..new_b].match_indices('\n').map(|(i, _)| (a + i) as u32 + 1));
        let after = self.starts.partition_point(|&s| s as usize <= old_b);
        starts.extend(self.starts[after..].iter().map(|&s| (s as i64 + delta) as u32));
        let keep = self.wide.partition_point(|&(o, _)| (o as usize) < a);
        let mut wide = self.wide[..keep].to_vec();
        wide_chars(&new[a..new_b], a, &mut wide);
        let after = self.wide.partition_point(|&(o, _)| (o as usize) < old_b);
        wide.extend(self.wide[after..].iter().map(|&(o, d)| ((o as i64 + delta) as u32, d)));
        LineIndex { starts, wide }
    }

    pub fn line_col(&self, offset: u32) -> (u32, u32) {
        let line = self.starts.partition_point(|&s| s <= offset) - 1;
        (line as u32 + 1, offset - self.starts[line] + 1)
    }
    /// 1-based line and display column of byte `offset`: rustc's
    /// `col_display + 1`, where a tab counts 4 and each char its width.
    pub fn line_display_col(&self, offset: u32) -> (u32, u32) {
        let (line, col) = self.line_col(offset);
        let start = self.starts[line as usize - 1];
        let lo = self.wide.partition_point(|&(o, _)| o < start);
        let hi = self.wide.partition_point(|&(o, _)| o < offset);
        let extra: i32 = self.wide[lo..hi].iter().map(|&(_, d)| d).sum();
        (line, (col as i32 + extra).max(1) as u32)
    }
}

/// One macro expansion: the macro def that ran, the call site that produced a
/// context, and the context the call itself was in. The chain of these records
/// (through `parent` and each `call_span`) maps an expanded span back to
/// ordinary source. No expansion exists until macro support lands; the record
/// shape is fixed now so `Span` does not change again. `macro_def` is the
/// macro's `DefId` (docs/ARCH.md section 6.3); until W-MACRO creates macro
/// defs, records carry `DefId::PLACEHOLDER`.
#[allow(dead_code)] // `macro_def` and `parent` are first read by macro expansion and its diagnostics.
#[derive(Clone)]
pub struct Expansion {
    pub macro_def: DefId,
    pub call_span: Span,
    pub parent: CtxtId,
}

/// Process-wide expansion table. Macro expansion runs inside the lexer and
/// chunk paths, which have no handle on the session's `SourceMap`, so the
/// expander registers every expansion here and gets a globally unique
/// `CtxtId`. A `SourceMap`'s own table (built by `add_expansion`) takes
/// precedence for ids it holds; today only tests build one. Entries are
/// append-only for the life of the process, so a daemon keeps them across
/// requests: spans in reused chunks stay valid.
static GLOBAL_EXPANSIONS: std::sync::Mutex<Vec<Expansion>> = std::sync::Mutex::new(Vec::new());

/// Records one expansion in the process-wide table and returns the context
/// id for its tokens. The macro expander is the caller.
pub fn register_expansion(exp: Expansion) -> CtxtId {
    let mut table = GLOBAL_EXPANSIONS.lock().unwrap();
    table.push(exp);
    CtxtId(table.len() as u32)
}

/// What one expansion's tokens may see of the locals around the macro's
/// definition point (ARCH 6.3). A macro defined inside a body reads
/// locals that were bound before its definition, in the context its
/// definition was written in; a macro defined at item level reads no
/// body locals at all. Parallel to the process-wide expansion table.
#[derive(Clone, Copy)]
pub struct HygieneMark {
    pub def_span: Span,
    pub local_def: bool,
}

static HYGIENE_MARKS: std::sync::Mutex<Vec<Option<HygieneMark>>> = std::sync::Mutex::new(Vec::new());

/// Records the hygiene mark for one expansion context. The expander
/// calls this right after `register_expansion` for the same context.
pub fn register_hygiene(ctxt: CtxtId, mark: HygieneMark) {
    let mut table = HYGIENE_MARKS.lock().unwrap();
    let idx = (ctxt.0 as usize).saturating_sub(1);
    if table.len() <= idx {
        table.resize(idx + 1, None);
    }
    table[idx] = Some(mark);
}

/// Contexts whose string literals came out of a macro expansion at the
/// point a format macro reads them (`println!(concat!("{x}", ""))`).
/// Rust forbids captured variables in such format strings; the expander
/// stamps the produced literal with a context recorded here and the
/// parser's format reader checks it. Parallel to `HYGIENE_MARKS`.
static NO_CAPTURE_MARKS: std::sync::Mutex<Vec<bool>> = std::sync::Mutex::new(Vec::new());

/// Records `ctxt` as a no-capture format string context. The expander
/// calls this right after `register_expansion` for the same context.
pub fn mark_no_capture(ctxt: CtxtId) {
    let mut table = NO_CAPTURE_MARKS.lock().unwrap();
    let idx = (ctxt.0 as usize).saturating_sub(1);
    if table.len() <= idx {
        table.resize(idx + 1, false);
    }
    table[idx] = true;
}

/// True when `ctxt` was recorded by `mark_no_capture`.
pub fn is_no_capture(ctxt: CtxtId) -> bool {
    if ctxt == CtxtId::ROOT {
        return false;
    }
    NO_CAPTURE_MARKS.lock().unwrap().get((ctxt.0 - 1) as usize).copied().unwrap_or(false)
}

fn hygiene_mark(ctxt: CtxtId) -> Option<HygieneMark> {
    if ctxt == CtxtId::ROOT {
        return None;
    }
    HYGIENE_MARKS.lock().unwrap().get((ctxt.0 - 1) as usize).copied().flatten()
}

/// True when an identifier used under `use_ctxt` may bind the local
/// bound at `binding` (whose span carries the binding's own context):
/// same context always, and for a macro defined in a body, bindings
/// from its definition context that were bound before the definition.
pub fn ctxt_can_see_local(use_ctxt: CtxtId, binding: Span) -> bool {
    if binding.ctxt == use_ctxt {
        return true;
    }
    let mut cur = use_ctxt;
    while let Some(mark) = hygiene_mark(cur) {
        if !mark.local_def {
            return false;
        }
        if binding.ctxt == mark.def_span.ctxt {
            return binding.file == mark.def_span.file && binding.lo < mark.def_span.lo;
        }
        cur = mark.def_span.ctxt;
    }
    false
}

/// The ordinary-source span an expanded span reports at, through the
/// process-wide table only. `line!`, `file!`, and `column!` read their
/// call site through this during expansion (ARCH 6.4).
pub fn call_site_span(span: Span) -> Span {
    let mut span = span;
    while span.ctxt != CtxtId::ROOT {
        match global_expansion(span.ctxt) {
            Some(e) => span = e.call_span,
            None => break,
        }
    }
    span
}

/// The expansion record for a context id from the process-wide table, if any.
fn global_expansion(ctxt: CtxtId) -> Option<Expansion> {
    if ctxt == CtxtId::ROOT {
        return None;
    }
    GLOBAL_EXPANSIONS.lock().unwrap().get((ctxt.0 - 1) as usize).cloned()
}

/// One file known to a source map: its path (as diagnostics print it) and its line index.
/// Multi-file crates also keep each file's text in the map, so a diagnostic
/// snippet reads the file its span names (docs/ARCH.md section 1.2). The
/// one-file driver path keeps text out of the map and passes it to `render`.
#[derive(Clone)]
struct SourceFile {
    path: String,
    lines: LineIndex,
    text: Option<String>,
}

/// The session's source map: every file's path and line index, plus the expansion table
/// that `CtxtId`s index into. Owned by the compile session. A stage that needs a path or a
/// line for a span asks the map. Today a crate has one file, so the map holds one entry.
#[derive(Clone, Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
    expansions: Vec<Expansion>,
}

impl SourceMap {
    /// Adds a file and returns its id. Files are append-only: an id, once given, names the
    /// same file for the rest of the session.
    pub fn add_file(&mut self, path: &str, src: &str) -> FileId {
        let id = FileId(self.files.len() as u32);
        self.files.push(SourceFile { path: path.to_string(), lines: LineIndex::new(src), text: None });
        id
    }
    /// Adds a file and keeps its text in the map (multi-file crates).
    pub fn add_file_with_text(&mut self, path: &str, src: &str) -> FileId {
        let id = FileId(self.files.len() as u32);
        self.files.push(SourceFile { path: path.to_string(), lines: LineIndex::new(src), text: Some(src.to_string()) });
        id
    }
    /// The number of files in the map.
    pub fn file_count(&self) -> usize {
        self.files.len()
    }
    /// The text of `file`, when the map keeps it (multi-file crates).
    pub fn text(&self, file: FileId) -> Option<&str> {
        self.files.get(file.0 as usize).and_then(|f| f.text.as_deref())
    }
    /// Replaces a file's path and line index. The driver uses this for the session's one
    /// file on each request: the path comes from the request, and the index is spliced
    /// from the last request's index, so it arrives ready-made.
    pub fn set_file(&mut self, file: FileId, path: &str, lines: LineIndex) {
        self.files[file.0 as usize] = SourceFile { path: path.to_string(), lines, text: None };
    }
    /// True when no file has been added yet (a fresh session).
    pub fn is_empty(&self) -> bool {
        self.files.is_empty()
    }
    /// The path diagnostics print for `file`.
    pub fn path(&self, file: FileId) -> &str {
        &self.files[file.0 as usize].path
    }
    /// The line index of `file` (the driver splices it on an edit; see `LineIndex::splice`).
    pub fn lines(&self, file: FileId) -> &LineIndex {
        &self.files[file.0 as usize].lines
    }
    /// 1-based line and column of a span's first byte.
    pub fn line_col(&self, span: Span) -> (u32, u32) {
        self.lines(span.file).line_col(span.lo)
    }
    /// 1-based line and display column of a span's first byte (panic
    /// locations; see `LineIndex::line_display_col`).
    pub fn line_display_col(&self, span: Span) -> (u32, u32) {
        self.lines(span.file).line_display_col(span.lo)
    }
    /// 1-based line and column of byte `offset` in `file`.
    pub fn line_col_at(&self, file: FileId, offset: u32) -> (u32, u32) {
        self.lines(file).line_col(offset)
    }
    /// The ordinary-source span an expanded span reports at: follow expansion call sites
    /// out to the root context. Diagnostics and panic locations use the call site
    /// (docs/ARCH.md section 6.3). With no expansions this is the span itself.
    pub fn call_site(&self, span: Span) -> Span {
        let mut span = span;
        while span.ctxt != CtxtId::ROOT {
            // A record in this map's own table wins; expansion contexts the
            // expander registered live in the process-wide table instead.
            let exp = match self.expansions.get((span.ctxt.0 - 1) as usize) {
                Some(e) => Some(e.clone()),
                None => global_expansion(span.ctxt),
            };
            match exp {
                Some(e) => span = e.call_span,
                // An unknown context cannot be followed further; report the
                // span as written rather than failing the diagnostic.
                None => break,
            }
        }
        span
    }
    /// Records one expansion in this map's own table and returns the context
    /// id for its tokens. Do not mix with `register_expansion` in one
    /// session: both number contexts from 1, and this table wins lookups.
    #[allow(dead_code)] // The expander uses the process-wide table today; the worklist driver (ARCH 6.1) will own this one.
    pub fn add_expansion(&mut self, exp: Expansion) -> CtxtId {
        self.expansions.push(exp);
        CtxtId(self.expansions.len() as u32)
    }
}

/// A span as a JSON object: byte range plus 1-based line and column of both ends.
fn span_json(map: &SourceMap, span: Span) -> String {
    let (line, col) = map.line_col(span);
    let (end_line, end_col) = map.line_col_at(span.file, span.hi);
    format!(
        "{{\"start\":{},\"end\":{},\"line\":{},\"col\":{},\"end_line\":{},\"end_col\":{}}}",
        span.lo, span.hi, line, col, end_line, end_col
    )
}

/// Appends the source line for `span` and a caret line under it, with an optional note.
/// `src` is the text of `span`'s file (today the map's one file; see `render`).
fn push_snippet(out: &mut String, src: &str, map: &SourceMap, span: Span, note: Option<&str>) {
    let (line, col) = map.line_col(span);
    let text = src.lines().nth(line as usize - 1).unwrap_or("");
    let width = (span.hi.saturating_sub(span.lo)).max(1) as usize;
    let width = width.min(text.len().saturating_sub(col as usize - 1).max(1));
    let _ = writeln!(out, "   | {text}");
    match note {
        Some(n) => {
            let _ = writeln!(out, "   | {}{} {n}", " ".repeat(col as usize - 1), "^".repeat(width));
        }
        None => {
            let _ = writeln!(out, "   | {}{}", " ".repeat(col as usize - 1), "^".repeat(width));
        }
    }
}

/// Renders diagnostics, sorted by position, as human text or JSON lines.
///
/// Paths and line numbers come from `map`; an expanded span reports at its call site.
/// `src` is the text of the map's first file (today a crate has one file): snippets and
/// the source hash read it.
///
/// At most `max_errors` distinct diagnostics are shown (0 means no cap). Repeated diagnostics
/// with the same code and span (cascade duplicates of one root error) are suppressed. When
/// anything is suppressed or omitted, an explicit truncation record is emitted last.
pub fn render(diags: &mut [Diag], map: &SourceMap, src: &str, json: bool, max_errors: usize) -> String {
    diags.sort_by(|a, b| (a.span.file, a.span.lo, a.span.hi, a.code).cmp(&(b.span.file, b.span.lo, b.span.hi, b.code)));
    let mut uniq: Vec<&Diag> = Vec::with_capacity(diags.len());
    for d in diags.iter() {
        match uniq.last() {
            Some(prev) if prev.code == d.code && prev.span == d.span => {}
            _ => uniq.push(d),
        }
    }
    let total = uniq.len();
    let duplicates = diags.len() - total;
    let shown = if max_errors == 0 { total } else { total.min(max_errors) };
    let omitted = total - shown;
    let hash = source_hash(src);
    let mut out = String::new();
    for d in uniq.iter().take(shown) {
        let span = map.call_site(d.span);
        let path = map.path(span.file);
        let (line, col) = map.line_col(span);
        if json {
            let mut labels = String::new();
            for (i, l) in d.labels.iter().enumerate() {
                if i > 0 {
                    labels.push(',');
                }
                let ls = map.call_site(l.span);
                let (ll, lc) = map.line_col(ls);
                let (el, ec) = map.line_col_at(ls.file, ls.hi);
                let _ = write!(
                    labels,
                    "{{\"start\":{},\"end\":{},\"line\":{},\"col\":{},\"end_line\":{},\"end_col\":{},\"label\":{}}}",
                    ls.lo,
                    ls.hi,
                    ll,
                    lc,
                    el,
                    ec,
                    json_str(&l.text)
                );
            }
            let mut edits = String::new();
            for (i, e) in d.edits.iter().enumerate() {
                if i > 0 {
                    edits.push(',');
                }
                let _ = write!(
                    edits,
                    "{{\"start\":{},\"end\":{},\"replacement\":{},\"auto\":{}}}",
                    e.start,
                    e.end,
                    json_str(&e.replacement),
                    e.auto
                );
            }
            let _ = writeln!(
                out,
                "{{\"schema\":{},\"kind\":\"diagnostic\",\"code\":\"{}\",\"severity\":\"{}\",\"message\":{},\"file\":{},\"source_hash\":{},\"span\":{},\"labels\":[{}],\"fix\":{},\"edits\":[{}]}}",
                SCHEMA,
                d.code,
                d.severity,
                json_str(&d.message),
                json_str(path),
                json_str(&hash),
                span_json(map, span),
                labels,
                json_str(&d.fix),
                edits
            );
        } else {
            let _ = writeln!(out, "error[{}]: {}", d.code, d.message);
            let _ = writeln!(out, "  --> {path}:{line}:{col}");
            push_snippet(&mut out, map.text(span.file).unwrap_or(src), map, span, None);
            for l in &d.labels {
                let ls = map.call_site(l.span);
                let (ll, lc) = map.line_col(ls);
                let lpath = map.path(ls.file);
                let _ = writeln!(out, "  ::: {lpath}:{ll}:{lc}");
                push_snippet(&mut out, map.text(ls.file).unwrap_or(src), map, ls, Some(&l.text));
            }
            let _ = writeln!(out, "   = fix: {}\n", d.fix);
        }
    }
    if omitted > 0 || duplicates > 0 {
        if json {
            // The record names one file: the first diagnostic's (the one file, today).
            let first_path = uniq.first().map_or("", |d| map.path(map.call_site(d.span).file));
            let _ = writeln!(
                out,
                "{{\"schema\":{},\"kind\":\"truncated\",\"file\":{},\"source_hash\":{},\"shown\":{},\"total\":{},\"omitted\":{},\"duplicates_suppressed\":{},\"max_errors\":{}}}",
                SCHEMA,
                json_str(first_path),
                json_str(&hash),
                shown,
                total,
                omitted,
                duplicates,
                max_errors
            );
        } else {
            if omitted > 0 {
                let _ = writeln!(out, "... and {omitted} more error(s) not shown (use --max-errors to show more; 0 means no cap)");
            }
            if duplicates > 0 {
                let _ = writeln!(out, "... and {duplicates} duplicate error(s) suppressed");
            }
        }
    }
    out
}

/// A string as a quoted, escaped JSON string.
pub(crate) fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Spans name a file and a context; shifting moves bytes only; `to` covers both spans.
    #[test]
    fn span_fields_and_shift() {
        let s = Span::new(FileId(3), 10, 20);
        assert_eq!((s.file, s.lo, s.hi, s.ctxt), (FileId(3), 10, 20, CtxtId::ROOT));
        let moved = s.shifted(-4);
        assert_eq!((moved.file, moved.lo, moved.hi, moved.ctxt), (FileId(3), 6, 16, CtxtId::ROOT));
        let cover = Span::new(FileId(3), 15, 30).to(s);
        assert_eq!((cover.file, cover.lo, cover.hi), (FileId(3), 10, 30));
        assert_eq!(std::mem::size_of::<Span>(), 16);
    }

    /// Two files keep separate paths and line indexes. An expanded span reports at the
    /// outermost call site through the expansion chain.
    #[test]
    fn map_files_and_call_site() {
        let mut map = SourceMap::default();
        let a = map.add_file("a.rs", "aa\nbb\ncc\n");
        let b = map.add_file("b.rs", "x\nyyy\n");
        assert_eq!((a, b), (FileId(0), FileId(1)));
        assert_eq!(map.path(b), "b.rs");
        assert_eq!(map.line_col(Span::new(a, 4, 5)), (2, 2));
        assert_eq!(map.line_col(Span::new(b, 3, 4)), (2, 2));

        let outer_call = Span::new(a, 0, 2);
        let c1 = map.add_expansion(Expansion { macro_def: DefId::PLACEHOLDER, call_span: outer_call, parent: CtxtId::ROOT });
        let inner_call = Span { file: b, lo: 2, hi: 3, ctxt: c1 };
        let c2 = map.add_expansion(Expansion { macro_def: DefId::PLACEHOLDER, call_span: inner_call, parent: c1 });
        assert_eq!((c1, c2), (CtxtId(1), CtxtId(2)));
        let inner = Span { file: b, lo: 4, hi: 5, ctxt: c2 };
        assert_eq!(map.call_site(inner), outer_call);
        assert_eq!(map.call_site(outer_call), outer_call);
    }

    /// JSON diagnostics take `file` and line numbers from the span's file in the map.
    #[test]
    fn render_json_uses_span_file() {
        let mut map = SourceMap::default();
        map.add_file("a.rs", "aa\n");
        let b = map.add_file("b.rs", "x\nyyy\n");
        let mut ds = [Diag::new("L0001", Span::new(b, 3, 4), "bad", "Fix it.")];
        let out = render(&mut ds, &map, "aa\n", true, 20);
        assert!(out.contains(r#""file":"b.rs""#), "{out}");
        assert!(out.contains(r#""span":{"start":3,"end":4,"line":2,"col":2,"end_line":2,"end_col":3}"#), "{out}");
    }
}
