// Diagnostics: every error has a stable code, a message, a source span, and a fix hint for agents.
//
// Human text and `--json` output come from the same `Diag` values. The JSON form is versioned
// (`"schema":1`): one object per line, with the primary span, labeled secondary spans, optional
// concrete edits, and the hash of the exact bytes that were checked. Output is bounded: exact
// duplicates are suppressed and at most `max_errors` diagnostics are shown, followed by an
// explicit truncation record. Truncation never changes the exit status.
use std::fmt::Write;

/// The version of the JSON diagnostic schema.
pub const SCHEMA: u32 = 1;
/// Default cap on shown diagnostics (`--max-errors` overrides it; 0 means no cap).
/// The wire protocol carries the value, so this constant documents the default only.
#[allow(dead_code)]
pub const DEFAULT_MAX_ERRORS: usize = 20;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(start: u32, end: u32) -> Span {
        Span { start, end }
    }
    pub fn to(self, other: Span) -> Span {
        Span { start: self.start.min(other.start), end: self.end.max(other.end) }
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
}

impl LineIndex {
    pub fn new(src: &str) -> LineIndex {
        // `match_indices` with a char pattern uses memchr, which is much faster than a byte loop.
        let mut starts = Vec::with_capacity(src.len() / 32);
        starts.push(0);
        starts.extend(src.match_indices('\n').map(|(i, _)| i as u32 + 1));
        LineIndex { starts }
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
        LineIndex { starts }
    }

    pub fn line_col(&self, offset: u32) -> (u32, u32) {
        let line = self.starts.partition_point(|&s| s <= offset) - 1;
        (line as u32 + 1, offset - self.starts[line] + 1)
    }
}

/// A span as a JSON object: byte range plus 1-based line and column of both ends.
fn span_json(index: &LineIndex, span: Span) -> String {
    let (line, col) = index.line_col(span.start);
    let (end_line, end_col) = index.line_col(span.end);
    format!(
        "{{\"start\":{},\"end\":{},\"line\":{},\"col\":{},\"end_line\":{},\"end_col\":{}}}",
        span.start, span.end, line, col, end_line, end_col
    )
}

/// Appends the source line for `span` and a caret line under it, with an optional note.
fn push_snippet(out: &mut String, src: &str, index: &LineIndex, span: Span, note: Option<&str>) {
    let (line, col) = index.line_col(span.start);
    let text = src.lines().nth(line as usize - 1).unwrap_or("");
    let width = (span.end.saturating_sub(span.start)).max(1) as usize;
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
/// At most `max_errors` distinct diagnostics are shown (0 means no cap). Repeated diagnostics
/// with the same code and span (cascade duplicates of one root error) are suppressed. When
/// anything is suppressed or omitted, an explicit truncation record is emitted last.
pub fn render(diags: &mut [Diag], path: &str, src: &str, json: bool, max_errors: usize) -> String {
    diags.sort_by(|a, b| (a.span.start, a.span.end, a.code).cmp(&(b.span.start, b.span.end, b.code)));
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
    let index = LineIndex::new(src);
    let hash = source_hash(src);
    let mut out = String::new();
    for d in uniq.iter().take(shown) {
        let (line, col) = index.line_col(d.span.start);
        if json {
            let mut labels = String::new();
            for (i, l) in d.labels.iter().enumerate() {
                if i > 0 {
                    labels.push(',');
                }
                let (ll, lc) = index.line_col(l.span.start);
                let (el, ec) = index.line_col(l.span.end);
                let _ = write!(
                    labels,
                    "{{\"start\":{},\"end\":{},\"line\":{},\"col\":{},\"end_line\":{},\"end_col\":{},\"label\":{}}}",
                    l.span.start,
                    l.span.end,
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
                span_json(&index, d.span),
                labels,
                json_str(&d.fix),
                edits
            );
        } else {
            let _ = writeln!(out, "error[{}]: {}", d.code, d.message);
            let _ = writeln!(out, "  --> {path}:{line}:{col}");
            push_snippet(&mut out, src, &index, d.span, None);
            for l in &d.labels {
                let (ll, lc) = index.line_col(l.span.start);
                let _ = writeln!(out, "  ::: {path}:{ll}:{lc}");
                push_snippet(&mut out, src, &index, l.span, Some(&l.text));
            }
            let _ = writeln!(out, "   = fix: {}\n", d.fix);
        }
    }
    if omitted > 0 || duplicates > 0 {
        if json {
            let _ = writeln!(
                out,
                "{{\"schema\":{},\"kind\":\"truncated\",\"file\":{},\"source_hash\":{},\"shown\":{},\"total\":{},\"omitted\":{},\"duplicates_suppressed\":{},\"max_errors\":{}}}",
                SCHEMA,
                json_str(path),
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
