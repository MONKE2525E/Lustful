// Codegen for panic=unwind (docs/ARCH.md section 7.2): explicit
// propagation. After every call and every statement that can unwind,
// a frame checks for a new exception on its thread (one global load
// when no thread has one) and jumps to its cleanup ladder; the
// ladder drops the live locals and its last block gives the exception
// back and returns. A statement in a cleanup block that ends with a
// new exception aborts. The runtime half is in runtime/panic.c.
use super::*;

/// What a statement or call does when it ends with a new exception.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Unw {
    /// Take the exception into the frame and run the cleanup from block `n`.
    Goto(u32),
    /// The statement is cleanup itself: a new exception aborts.
    Abort,
}

impl Unw {
    /// The C check that follows a call or statement.
    pub(super) fn check(self) -> String {
        match self {
            Unw::Goto(b) => format!("LUST_UNW({b});"),
            Unw::Abort => "LUST_UNW_ABORT();".into(),
        }
    }
}

impl FnGen<'_, '_> {
    /// `catch_unwind(f)` (lowered with no cleanup successor, lower/unwind.rs):
    /// calls `f`; under panic=unwind a panic in it comes back here and
    /// becomes `Err(payload)`, with `f`'s value dropped as `call_once`
    /// drops it. Under panic=abort a panic never returns, so it is `Ok`.
    pub(super) fn catch_unwind_call(&mut self, ops: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        let callee = self.callee_of(&ops[0]);
        let once = !matches!(callee, sync::Callee::Closure(_, false));
        let (env, env_ty) = self.operand(&ops[0], loc, post);
        collect_types(&env_ty, &mut self.sig_types);
        let ret = self.callee_ret(&callee);
        let res = CTy::Result(Box::new(ret), Box::new(CTy::BoxDyn));
        collect_types(&res, &mut self.sig_types);
        let ev = self.tmp();
        let _ = writeln!(self.out, "    {} {ev} = {env};", ctype(&env_ty));
        let mut call = String::new();
        let v = self.callee_call_c(&mut call, &callee, &ev, &[]);
        self.out.push_str(&call);
        let caught = self.tmp();
        if self.p.unwind {
            let _ = writeln!(self.out, "    lust_dyn {caught}p; int {caught} = lust_unw_pending && lust_unw_mine(); if ({caught}) {caught}p = lust_unw_catch();");
        }
        if !once && needs_drop_c(self.p, &env_ty) {
            self.want(Glue::Drop, &env_ty);
            let _ = writeln!(self.out, "    drop_{}(&{ev});", mangle(&env_ty));
        }
        let r = self.tmp();
        let ok = self.make_variant(&res, 0, &[v]);
        if self.p.unwind {
            let err = self.make_variant(&res, 1, &[format!("{caught}p")]);
            let _ = writeln!(self.out, "    {} {r} = {caught} ? {err} : {ok};", ctype(&res));
        } else {
            let _ = writeln!(self.out, "    {} {r} = {ok};", ctype(&res));
        }
        r
    }
}

/// The blocks of `body` that are cleanup: every block reachable from a
/// call's unwind successor or a statement's cleanup entry. Lowering
/// builds them as ladders that only reach each other.
pub(super) fn cleanup_blocks(body: &Body) -> Vec<bool> {
    let mut seen = vec![false; body.blocks.len()];
    let mut stack: Vec<usize> = body.stmt_unwind.iter().map(|&(_, _, u)| u.0 as usize).collect();
    for b in &body.blocks {
        if let Terminator::Call { unwind: Some(u), .. } = b.term {
            stack.push(u.0 as usize);
        }
    }
    while let Some(b) = stack.pop() {
        if std::mem::replace(&mut seen[b], true) {
            continue;
        }
        stack.extend(succ(&body.blocks[b].term).into_iter().map(|s| s.0 as usize));
    }
    seen
}

/// Calls that can panic or run user code, by name prefix. A runtime
/// helper that panics returns a safe placeholder in unwind mode, so
/// only its statement-level callers need the check right after it.
const CHECKED_PREFIXES: &[&str] = &["lust_", "drop_", "clone_", "eq_", "cmp_", "dbg_", "disp_", "default_"];

/// Wraps every call statement `name(..);` in `text` whose name has a
/// checked prefix as `{ name(..); <check> }`, so the code after a
/// panicking call in the same C statement block does not run. Calls
/// inside expressions are left alone: the statement's own check
/// follows them. String and char literals are skipped.
pub(super) fn wrap_calls(text: &str, check: &str) -> String {
    let b = text.as_bytes();
    let mut out = String::with_capacity(text.len() + 64);
    let (mut i, mut copied) = (0, 0);
    while i < b.len() {
        match b[i] {
            b'"' | b'\'' => i = skip_lit(b, i),
            c if is_ident(c) && (i == 0 || !is_ident(b[i - 1])) => {
                let start = i;
                while i < b.len() && is_ident(b[i]) {
                    i += 1;
                }
                let name = &text[start..i];
                if !CHECKED_PREFIXES.iter().any(|p| name.starts_with(p)) || name.starts_with("lust_unw_") || !stmt_start(b, start) {
                    continue;
                }
                let mut j = i;
                while j < b.len() && b[j] == b' ' {
                    j += 1;
                }
                if j >= b.len() || b[j] != b'(' {
                    continue;
                }
                let Some(close) = match_paren(b, j) else { continue };
                let mut k = close + 1;
                while k < b.len() && b[k] == b' ' {
                    k += 1;
                }
                if k >= b.len() || b[k] != b';' {
                    continue;
                }
                out.push_str(&text[copied..start]);
                out.push_str("{ ");
                out.push_str(&text[start..=k]);
                out.push(' ');
                out.push_str(check);
                out.push_str(" }");
                copied = k + 1;
                i = k + 1;
            }
            _ => i += 1,
        }
    }
    out.push_str(&text[copied..]);
    out
}

fn is_ident(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

/// The index after the string or char literal that starts at `i`.
fn skip_lit(b: &[u8], i: usize) -> usize {
    let q = b[i];
    let mut j = i + 1;
    while j < b.len() && b[j] != q {
        j += if b[j] == b'\\' { 2 } else { 1 };
    }
    j + 1
}

/// The index of the `)` that closes the `(` at `open`.
fn match_paren(b: &[u8], open: usize) -> Option<usize> {
    let mut depth = 0usize;
    let mut j = open;
    while j < b.len() {
        match b[j] {
            b'"' | b'\'' => {
                j = skip_lit(b, j);
                continue;
            }
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(j);
                }
            }
            _ => {}
        }
        j += 1;
    }
    None
}

/// Whether the token at `at` starts a C statement: after `;`, `{`,
/// `}`, `else`, the condition of `if`/`for`/`while`, or the start.
fn stmt_start(b: &[u8], at: usize) -> bool {
    let mut j = at;
    while j > 0 && b[j - 1].is_ascii_whitespace() {
        j -= 1;
    }
    if j == 0 {
        return true;
    }
    match b[j - 1] {
        b';' | b'{' | b'}' => true,
        b'e' => j >= 4 && &b[j - 4..j] == b"else" && (j == 4 || !is_ident(b[j - 5])),
        b')' => {
            // Back to the matching `(`, then the keyword before it.
            let mut depth = 0usize;
            let mut k = j - 1;
            loop {
                match b[k] {
                    b')' => depth += 1,
                    b'(' => {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    _ => {}
                }
                if k == 0 {
                    return false;
                }
                k -= 1;
            }
            while k > 0 && b[k - 1] == b' ' {
                k -= 1;
            }
            let end = k;
            while k > 0 && is_ident(b[k - 1]) {
                k -= 1;
            }
            matches!(&b[k..end], b"if" | b"for" | b"while")
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::wrap_calls;

    #[test]
    fn wraps_statement_calls_only() {
        let c = "X;";
        assert_eq!(wrap_calls("  lust_bounds(a, b, 3u);\n", c), "  { lust_bounds(a, b, 3u); X; }\n");
        assert_eq!(wrap_calls("  if (x) lust_panic_cstr(\"a (b\", 1u); y = 2;\n", c), "  if (x) { lust_panic_cstr(\"a (b\", 1u); X; } y = 2;\n");
        assert_eq!(wrap_calls("  t = lust_add_i32(a, b, 1u);\n", c), "  t = lust_add_i32(a, b, 1u);\n");
        assert_eq!(wrap_calls("  (void)lust_x(a);\n", c), "  (void)lust_x(a);\n");
        assert_eq!(wrap_calls("  else drop_S(&p);", c), "  else { drop_S(&p); X; }");
        assert_eq!(wrap_calls("  lust_unw_take(&ex);", c), "  lust_unw_take(&ex);");
        assert_eq!(wrap_calls("  for (i = 0; i < n; i++) drop_T(&v[i]);", c), "  for (i = 0; i < n; i++) { drop_T(&v[i]); X; }");
    }
}
