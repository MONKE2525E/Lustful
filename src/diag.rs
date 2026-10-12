// Diagnostics: every error has a stable code, a message, a source span, and a fix hint for agents.
use std::fmt::Write;

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

#[derive(Clone, Debug)]
pub struct Diag {
    pub code: &'static str,
    pub message: String,
    pub span: Span,
    pub fix: String,
}

impl Diag {
    pub fn new(code: &'static str, span: Span, message: impl Into<String>, fix: impl Into<String>) -> Diag {
        Diag { code, message: message.into(), span, fix: fix.into() }
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

/// Renders diagnostics, sorted by position, as human text or JSON lines.
pub fn render(diags: &mut [Diag], path: &str, src: &str, json: bool) -> String {
    diags.sort_by_key(|d| (d.span.start, d.code));
    let index = LineIndex::new(src);
    let mut out = String::new();
    for d in diags.iter() {
        let (line, col) = index.line_col(d.span.start);
        if json {
            let _ = writeln!(
                out,
                "{{\"code\":\"{}\",\"severity\":\"error\",\"message\":{},\"at\":\"{}:{}:{}\",\"fix\":{}}}",
                d.code,
                json_str(&d.message),
                path,
                line,
                col,
                json_str(&d.fix)
            );
        } else {
            let text = src.lines().nth(line as usize - 1).unwrap_or("");
            let width = (d.span.end.saturating_sub(d.span.start)).max(1) as usize;
            let width = width.min(text.len().saturating_sub(col as usize - 1).max(1));
            let _ = writeln!(out, "error[{}]: {}", d.code, d.message);
            let _ = writeln!(out, "  --> {path}:{line}:{col}");
            let _ = writeln!(out, "   | {text}");
            let _ = writeln!(out, "   | {}{}", " ".repeat(col as usize - 1), "^".repeat(width));
            let _ = writeln!(out, "   = fix: {}\n", d.fix);
        }
    }
    out
}

fn json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}
