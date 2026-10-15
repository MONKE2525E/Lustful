// The str split family in codegen (W-STD-B): one runtime step per
// `next`/`next_back` (runtime/core.c `lust_split_step`) and
// `split_once`/`rsplit_once`, with the pattern described by a `lust_pat`
// built from its type: a char, a string needle (`&str`, `&&str`,
// `&String`), a char set (an array, a reference to one, or a slice), or
// a closure, called through a small adapter (`void *env, uint32_t c`).
use super::*;
use crate::ty::iter::{self as it, SplitMode};

impl FnGen<'_, '_> {
    /// One split builtin as the runtime runs it, or None for every other
    /// builtin. `StrSplit` itself is expanded in lower/iter.rs.
    pub(super) fn split_builtin(&mut self, b: Builtin, ops: &[Operand], dest: &CTy, loc: &str, post: &mut Vec<String>) -> Option<String> {
        use Builtin as B;
        if !matches!(b, B::StrSplitNext | B::StrSplitNextBack | B::StrSplitUpper | B::StrSplitOnce | B::StrRSplitOnce) {
            return None;
        }
        let mut vals = Vec::new();
        let mut tys = Vec::new();
        for o in ops {
            let (v, t) = self.operand(o, loc, post);
            vals.push(v);
            tys.push(t);
        }
        collect_types(dest, &mut self.sig_types);
        let dc = ctype(dest);
        let t = self.tmp();
        match b {
            B::StrSplitNext | B::StrSplitNextBack => {
                let (p, mode) = self.split_parts(&ops[0]);
                let s = &vals[0];
                let pat = self.split_pat(p, mode, &format!("(&({s})->f7)"));
                let back = u8::from(b == B::StrSplitNextBack);
                let _ = writeln!(
                    self.out,
                    "    lust_str {t}_s; lust_pat {t}_p = {pat}; int {t}_k = lust_split_step((lust_split*)({s}), &{t}_p, {}, {back}, &{t}_s);",
                    mode as u8
                );
                let some = self.make_variant(dest, 1, &[format!("{t}_s")]);
                let none = self.make_variant(dest, 0, &[]);
                let _ = writeln!(self.out, "    {dc} {t} = {t}_k ? {some} : {none};");
                Some(t)
            }
            B::StrSplitUpper => Some(format!("lust_split_upper((const lust_split*)({}))", vals[0])),
            _ => {
                // (`&str` or `&String`, pattern by value).
                let hay = match &tys[0] {
                    CTy::Ref(x) if **x == CTy::String => format!("lust_string_as_str({})", vals[0]),
                    _ => vals[0].clone(),
                };
                let p = self.op_lust_ty(&ops[1]);
                let _ = writeln!(self.out, "    {} {t}_v = {};", ctype(&tys[1]), vals[1]);
                let pat = self.split_pat(p, SplitMode::Split, &format!("(&{t}_v)"));
                let back = u8::from(b == B::StrRSplitOnce);
                let _ = writeln!(
                    self.out,
                    "    lust_str {t}_a, {t}_b; lust_pat {t}_p = {pat}; int {t}_k = lust_str_split_once({hay}, &{t}_p, {back}, &{t}_a, &{t}_b);"
                );
                if needs_drop_c(self.p, &tys[1]) {
                    self.want(Glue::Drop, &tys[1]);
                    let _ = writeln!(self.out, "    drop_{}(&{t}_v);", mangle(&tys[1]));
                }
                let pair = CTy::Tuple(vec![CTy::Ref(Box::new(CTy::Str)), CTy::Ref(Box::new(CTy::Str))]);
                collect_types(&pair, &mut self.sig_types);
                let some = self.make_variant(dest, 1, &[format!("(({}){{ {t}_a, {t}_b }})", ctype(&pair))]);
                let none = self.make_variant(dest, 0, &[]);
                let _ = writeln!(self.out, "    {dc} {t} = {t}_k ? {some} : {none};");
                Some(t)
            }
        }
    }

    /// The type of an operand: a constant's, or its place's (the local's
    /// type through its derefs).
    fn op_lust_ty(&self, o: &Operand) -> Ty {
        let pl = match o {
            Operand::Move(pl) | Operand::Copy(pl) => pl,
            Operand::Const(Const::Str(_)) => return REF_STR,
            Operand::Const(Const::Char(_)) => return CHAR,
            Operand::Const(_) => return ERROR,
        };
        let mut t = self.body.locals[pl.local as usize].ty;
        for pr in &pl.proj {
            t = match (self.body.tys.kind(t), pr) {
                (TyKind::Ref(_, _, i), Proj::Deref) => i,
                _ => return ERROR,
            };
        }
        t
    }

    /// The pattern type and mode of a `&mut StrSplit<P, M>` operand.
    fn split_parts(&self, o: &Operand) -> (Ty, SplitMode) {
        let mut t = self.op_lust_ty(o);
        while let TyKind::Ref(_, _, i) = self.body.tys.kind(t) {
            t = i;
        }
        match it::iter_parts(&self.body.tys, t) {
            Some((it::IterKind::StrSplit, a)) => (a[0], it::split_mode(&self.body.tys, a[1]).unwrap_or(SplitMode::Split)),
            _ => (CHAR, SplitMode::Split),
        }
    }

    /// A `lust_pat` initializer for pattern type `p` stored at the C
    /// pointer `ptr` (the whitespace and line modes ignore it).
    fn split_pat(&mut self, p: Ty, mode: SplitMode, ptr: &str) -> String {
        let n_of = |this: &Self, c: ConstId| match this.body.tys.const_kind(c) {
            ConstKind::Int(n) => n as u64,
            _ => 0,
        };
        match mode {
            SplitMode::SplitWhitespace => return "((lust_pat){ .kind = LUST_PAT_SPACE })".into(),
            SplitMode::SplitAsciiWhitespace => return "((lust_pat){ .kind = LUST_PAT_ASCII_SPACE })".into(),
            SplitMode::Lines => return "((lust_pat){ .kind = LUST_PAT_CHAR, .ch = 10 })".into(),
            _ => {}
        }
        match self.body.tys.kind(p) {
            TyKind::Char => format!("((lust_pat){{ .kind = LUST_PAT_CHAR, .ch = *{ptr} }})"),
            TyKind::Array(_, c) => format!("((lust_pat){{ .kind = LUST_PAT_SET, .set = ({ptr})->v, .n = {} }})", n_of(self, c)),
            TyKind::Closure(def, _) => {
                let f = self.p.gx.closures[&def].body_fn;
                let a = self.split_adapter(f);
                format!("((lust_pat){{ .kind = LUST_PAT_PRED, .pred = {a}, .env = (void*){ptr} }})")
            }
            TyKind::Ref(_, _, inner) => match self.body.tys.kind(inner) {
                TyKind::Str => format!("((lust_pat){{ .kind = LUST_PAT_STR, .needle = *{ptr} }})"),
                TyKind::Ref(..) => format!("((lust_pat){{ .kind = LUST_PAT_STR, .needle = **{ptr} }})"),
                TyKind::Array(_, c) => format!("((lust_pat){{ .kind = LUST_PAT_SET, .set = (*{ptr})->v, .n = {} }})", n_of(self, c)),
                TyKind::Slice(_) => format!("((lust_pat){{ .kind = LUST_PAT_SET, .set = (*{ptr}).ptr, .n = (*{ptr}).len }})"),
                _ => format!("((lust_pat){{ .kind = LUST_PAT_STR, .needle = lust_string_as_str(*{ptr}) }})"),
            },
            _ => "((lust_pat){ .kind = LUST_PAT_CHAR })".into(),
        }
    }

    /// The `uint8_t f(void *env, uint32_t c)` adapter that calls a
    /// predicate closure's body (its env is the stored closure).
    fn split_adapter(&mut self, f: LocalDefId) -> String {
        let name = format!("lust_splitp_{}_{}", self.slots[self.body.fn_id.0 as usize], self.adapters);
        self.adapters += 1;
        let mut body = String::new();
        let (r, _) = self.closure_call_c(&mut body, f, "env", &["c".to_string()]);
        let _ = writeln!(self.prelude, "static uint8_t {name}(void *env, uint32_t c) {{\n{body}  return {r};\n}}");
        name
    }
}
