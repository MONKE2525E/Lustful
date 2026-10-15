// The `str` split family in body checking (W-STD-B): `split`, `rsplit`,
// `split_terminator`, `rsplit_terminator`, `splitn`, `rsplitn`,
// `split_inclusive`, `split_whitespace`, `split_ascii_whitespace`,
// `lines`, `split_once`, and `rsplit_once`, over the patterns std's
// `Pattern` impls cover: `char`, `&str` (also `&&str` and `&String`),
// char arrays and slices, and `FnMut(char) -> bool` closures. The
// iterators are `IterKind::StrSplit` (ty/iter.rs); the runtime runs std's
// searchers and `SplitInternal` (runtime/core.c `lust_split_step`).
use super::*;
use crate::ty::iter::{self as it, SplitMode};

/// True when a split pattern type is a string needle (`&str`, `&&str`,
/// `&String`), whose searcher is not double-ended.
pub fn str_needle(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Ref(_, _, inner) => match tys.kind(inner) {
            TyKind::Str => true,
            TyKind::Ref(_, _, x) => tys.kind(x) == TyKind::Str,
            _ => tys.is_string_ty(inner),
        },
        _ => false,
    }
}

/// True for the pattern types lust runs (std's `Pattern` impls but the
/// fn-item and fn-pointer predicates).
fn pattern_ok(tys: &impl TyIntern, t: Ty) -> bool {
    match tys.kind(t) {
        TyKind::Char | TyKind::Closure(..) => true,
        TyKind::Array(e, _) => e == CHAR,
        TyKind::Ref(_, _, inner) => {
            str_needle(tys, t) || matches!(tys.kind(inner), TyKind::Array(e, _) | TyKind::Slice(e) if e == CHAR)
        }
        _ => false,
    }
}

impl<'p> Ctx<'p> {
    /// The split family on a `str` or `String` receiver; None for other
    /// methods and receivers.
    pub(super) fn str_split_method(&mut self, e: ExprId, base: Ty, derefs: u8, name: Sym, name_span: Span, args: &[ExprId]) -> Option<Ty> {
        let base = self.deep(base);
        if self.kind(base) != TyKind::Str && !self.tys.is_string_ty(base) {
            return None;
        }
        use SplitMode as M;
        // (mode, takes a count, takes a pattern, `Some(back)` for the
        // `_once` forms)
        let (mode, count, pat, once) = match self.p.interner.get(name) {
            "split" => (M::Split, false, true, None),
            "rsplit" => (M::RSplit, false, true, None),
            "split_terminator" => (M::SplitTerminator, false, true, None),
            "rsplit_terminator" => (M::RSplitTerminator, false, true, None),
            "splitn" => (M::SplitN, true, true, None),
            "rsplitn" => (M::RSplitN, true, true, None),
            "split_inclusive" => (M::SplitInclusive, false, true, None),
            "split_whitespace" => (M::SplitWhitespace, false, false, None),
            "split_ascii_whitespace" => (M::SplitAsciiWhitespace, false, false, None),
            "lines" => (M::Lines, false, false, None),
            "split_once" => (M::Split, false, true, Some(false)),
            "rsplit_once" => (M::Split, false, true, Some(true)),
            _ => return None,
        };
        let n = usize::from(count) + usize::from(pat);
        if args.len() != n {
            self.err("L0105", name_span, format!("this method takes {n} argument(s) but {} were given", args.len()), "Pass exactly the declared arguments.");
            for &a in args {
                self.expr(a, None);
            }
            return Some(ERROR);
        }
        if count {
            self.check_args(&[USIZE], &args[..1], name_span);
        }
        let p = match args.last().filter(|_| pat) {
            Some(&a) => {
                // A closure is checked against `FnMut(char) -> bool` (as the
                // adapters' closures are), so `|c| ..` needs no annotation;
                // a closure value must have that signature too.
                let closure_expr = matches!(self.p.ast.expr(a), Expr::Closure { .. });
                let t = if closure_expr {
                    let f = self.fn_mut_param(&[CHAR], BOOL, name_span);
                    self.check_args(&[f], &[a], name_span);
                    f
                } else {
                    self.expr(a, None)
                };
                let t = self.deep(t);
                if let TyKind::Closure(..) = self.kind(t)
                    && !closure_expr
                {
                    let f = self.fn_mut_param(&[CHAR], BOOL, name_span);
                    if !self.unify(f, t) {
                        self.mismatch(self.span(a), f, t);
                        return Some(ERROR);
                    }
                }
                if !pattern_ok(&self.tys, t) {
                    if self.kind(t) != TyKind::Error {
                        let tn = self.tn(t);
                        self.err(
                            "L0612",
                            self.span(a),
                            format!("`{tn}` is not a str pattern lust takes"),
                            "Pass a char, a `&str`, a char array or slice, or a closure `|c: char| -> bool`.",
                        );
                    }
                    return Some(ERROR);
                }
                t
            }
            None => CHAR,
        };
        let b = match once {
            Some(false) => Builtin::StrSplitOnce,
            Some(true) => Builtin::StrRSplitOnce,
            None => Builtin::StrSplit,
        };
        self.set_res(e, Res::BuiltinMethod { b, derefs, autoref: Autoref::Ref });
        Some(match once {
            Some(_) => {
                let ts = self.tys.intern_tys(&[REF_STR, REF_STR]);
                let pair = self.tys.intern(TyKind::Tuple(ts));
                self.tys.mk_option(pair)
            }
            None => it::mk_split(&mut self.tys, p, mode),
        })
    }
}
