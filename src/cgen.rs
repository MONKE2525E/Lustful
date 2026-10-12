// C backend. Each function is generated on its own (in parallel). Type helpers ("glue": drop, clone,
// eq, debug) are requested by structural type and generated once, after all functions.
use crate::ast::{BinOp, UnOp};
use crate::check::Builtin;
use crate::collect::*;
use crate::diag::{LineIndex, Span};
use crate::ir::*;
use crate::types::*;
use std::collections::{HashMap, HashSet};
use std::fmt::Write;

/// A body-independent type, so glue can be shared across functions.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CTy {
    Unit,
    Bool,
    Char,
    Int(IntTy),
    Str,
    String,
    Vec(Box<CTy>),
    Option(Box<CTy>),
    Ref(Box<CTy>),
    Adt(AdtId),
    Args,
    Chars,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Glue {
    Drop,
    Clone,
    Eq,
    Debug,
}

pub fn cty(tys: &impl TyIntern, t: Ty) -> CTy {
    match tys.kind(t) {
        TyKind::Unit | TyKind::Never | TyKind::Error | TyKind::Var(..) => CTy::Unit,
        TyKind::Bool => CTy::Bool,
        TyKind::Char => CTy::Char,
        TyKind::Int(i) => CTy::Int(i),
        TyKind::Str => CTy::Str,
        TyKind::String => CTy::String,
        TyKind::Vec(e) => CTy::Vec(Box::new(cty(tys, e))),
        TyKind::Option(e) => CTy::Option(Box::new(cty(tys, e))),
        TyKind::Chars => CTy::Chars,
        TyKind::Ref(_, e) => CTy::Ref(Box::new(cty(tys, e))),
        TyKind::Adt(a) => CTy::Adt(a),
        TyKind::Args => CTy::Args,
    }
}

fn int_c(i: IntTy) -> &'static str {
    match i {
        IntTy::I8 => "int8_t",
        IntTy::I16 => "int16_t",
        IntTy::I32 => "int32_t",
        IntTy::I64 | IntTy::Isize => "int64_t",
        IntTy::U8 => "uint8_t",
        IntTy::U16 => "uint16_t",
        IntTy::U32 => "uint32_t",
        IntTy::U64 | IntTy::Usize => "uint64_t",
    }
}

/// Suffix of the runtime's checked-math helpers for this type.
fn int_fn(i: IntTy) -> &'static str {
    match i {
        IntTy::I8 => "i8",
        IntTy::I16 => "i16",
        IntTy::I32 => "i32",
        IntTy::I64 | IntTy::Isize => "i64",
        IntTy::U8 => "u8",
        IntTy::U16 => "u16",
        IntTy::U32 => "u32",
        IntTy::U64 | IntTy::Usize => "u64",
    }
}

pub fn ctype(t: &CTy) -> String {
    match t {
        CTy::Unit | CTy::Bool => "uint8_t".into(),
        CTy::Char => "uint32_t".into(),
        CTy::Int(i) => int_c(*i).into(),
        CTy::Str => "lust_str".into(),
        CTy::String => "lust_String".into(),
        CTy::Vec(_) => "lust_Vec".into(),
        CTy::Ref(inner) if **inner == CTy::Str => "lust_str".into(),
        CTy::Ref(inner) => format!("{}*", ctype(inner)),
        CTy::Adt(a) => format!("A{}", a.0),
        CTy::Option(_) => format!("O_{}", mangle(t)),
        CTy::Args => "lust_Args".into(),
        CTy::Chars => "lust_Chars".into(),
    }
}

fn mangle(t: &CTy) -> String {
    match t {
        CTy::Unit => "u".into(),
        CTy::Bool => "b".into(),
        CTy::Char => "c".into(),
        CTy::Int(i) => i.name().into(),
        CTy::Str => "str".into(),
        CTy::String => "S".into(),
        CTy::Vec(e) => format!("V_{}_", mangle(e)),
        CTy::Ref(e) => format!("R_{}_", mangle(e)),
        CTy::Adt(a) => format!("A{}", a.0),
        CTy::Option(e) => format!("O_{}_", mangle(e)),
        CTy::Args => "Args".into(),
        CTy::Chars => "Chars".into(),
    }
}

/// Adds the named C types (structs, enums, Options) that `t` uses, including inside Vec and refs.
/// A `lust_str` expression for a `&str` or `&String` receiver.
fn str_of(v: &str, t: &CTy) -> String {
    match t {
        CTy::Ref(inner) if **inner == CTy::String => format!("lust_string_as_str({v})"),
        _ => v.to_string(),
    }
}

fn collect_types(t: &CTy, out: &mut HashSet<CTy>) {
    match t {
        CTy::Adt(_) => {
            out.insert(t.clone());
        }
        CTy::Option(e) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::Vec(e) | CTy::Ref(e) => collect_types(e, out),
        _ => {}
    }
}

/// Named types that `t` holds by value, so their C definitions must come first.
fn by_value_deps(t: &CTy, out: &mut Vec<CTy>) {
    match t {
        CTy::Adt(_) | CTy::Option(_) => out.push(t.clone()),
        _ => {}
    }
}

fn is_copy_c(p: &Program, t: &CTy) -> bool {
    match t {
        CTy::Unit | CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Ref(_) | CTy::Args | CTy::Chars => true,
        CTy::Option(e) => is_copy_c(p, e),
        CTy::Adt(a) => p.adt(*a).derives.copy,
        _ => false,
    }
}

fn needs_drop_c(p: &Program, t: &CTy) -> bool {
    match t {
        CTy::String | CTy::Vec(_) => true,
        CTy::Option(e) => needs_drop_c(p, e),
        CTy::Adt(a) => p.adt(*a).variants.iter().any(|v| v.fields.iter().any(|f| needs_drop(p, &p.tys, f.ty))),
        _ => false,
    }
}

fn c_string_lit(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() + 2);
    s.push('"');
    for &b in bytes {
        match b {
            b'"' => s.push_str("\\\""),
            b'\\' => s.push_str("\\\\"),
            b'?' => s.push_str("\\077"),
            0x20..=0x7e => s.push(b as char),
            _ => {
                let _ = write!(s, "\\{:03o}", b);
            }
        }
    }
    s.push('"');
    s
}

/// The generated code for one function, plus the glue it needs.
#[derive(Default)]
pub struct FnOut {
    pub code: String,
    pub glue: HashSet<(Glue, CTy)>,
    /// Named C types (structs, enums, Options) this function's code needs declared.
    pub types: HashSet<CTy>,
}

struct FnGen<'b, 'p, 'a> {
    p: &'p Program<'a>,
    body: &'b Body<'p>,
    out: String,
    glue: HashSet<(Glue, CTy)>,
    local_cty: Vec<CTy>,
    local_drop: Vec<bool>,
    lines: &'b LineIndex,
    /// Types in the signatures of called functions, needed for the call casts.
    sig_types: HashSet<CTy>,
    /// Line of the function's `fn` keyword. Locations are stored relative to it, so the C for
    /// an unchanged function stays valid when code above it moves.
    base_line: u32,
    /// FnId to table slot. Slots are stable across edits; FnIds are not.
    slots: &'b [u32],
    tmp: u32,
}

/// `(RET (*)(PARAMS))`, the cast that calls function `f` through the table.
fn fn_ptr_cast(p: &Program, f: FnId) -> String {
    let info = p.fn_info(f);
    let params: Vec<String> = info.params.iter().map(|&t| ctype(&cty(&p.tys, t))).collect();
    let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    format!("({} (*)({}))", ctype(&cty(&p.tys, info.ret)), params)
}

/// The C signature of function `f`, defined under the C name `f<slot>`.
fn fn_sig(p: &Program, f: FnId, slot: u32) -> String {
    let info = p.fn_info(f);
    let params: Vec<String> = info.params.iter().enumerate().map(|(i, &t)| format!("{} p{}", ctype(&cty(&p.tys, t)), i + 1)).collect();
    let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    format!("{} f{slot}({})", ctype(&cty(&p.tys, info.ret)), params)
}

/// Generates C for one function body. `base_line` is the line of its `fn` keyword; `slots` maps
/// every FnId to its slot in `lust_fns`.
pub fn gen_fn(p: &Program, body: &Body, lines: &LineIndex, base_line: u32, slots: &[u32]) -> FnOut {
    let local_cty: Vec<CTy> = body.locals.iter().map(|l| cty(&body.tys, l.ty)).collect();
    let local_drop = local_cty.iter().map(|t| needs_drop_c(p, t)).collect();
    let mut g = FnGen {
        p,
        body,
        out: String::new(),
        glue: HashSet::new(),
        local_cty,
        local_drop,
        lines,
        sig_types: HashSet::new(),
        base_line,
        slots,
        tmp: 0,
    };
    g.function();
    let mut types = std::mem::take(&mut g.sig_types);
    for t in &g.local_cty {
        collect_types(t, &mut types);
    }
    for (_, t) in &g.glue {
        collect_types(t, &mut types);
    }
    FnOut { code: g.out, glue: g.glue, types }
}

impl FnGen<'_, '_, '_> {
    /// A packed source location, relative to the function's first line. See `lust_loc`.
    fn loc(&self, span: Span) -> String {
        let (l, c) = self.lines.line_col(span.start);
        let rel = l.saturating_sub(self.base_line).min(0xFFFFF) as u64;
        let slot = self.slots[self.body.fn_id.0 as usize] as u64;
        format!("{}u", (slot << 32) | (rel << 12) | c.min(0xFFF) as u64)
    }
    fn tmp(&mut self) -> String {
        self.tmp += 1;
        format!("t{}", self.tmp)
    }
    fn want(&mut self, g: Glue, t: &CTy) {
        self.glue.insert((g, t.clone()));
    }

    fn function(&mut self) {
        let p = self.p;
        let fid = self.body.fn_id;
        let slot = self.slots[fid.0 as usize];
        let _ = writeln!(self.out, "/* {} */\nstatic {} {{", p.name(p.fn_info(fid).name), fn_sig(p, fid, slot));
        // Locals grouped by C type. No initializers: the borrow checker proves every read is
        // after a write. Drop flags start at 0, except for parameters, which own their values.
        let mut by_type: Vec<(String, Vec<String>)> = Vec::new();
        let mut flags = Vec::new();
        for (i, t) in self.local_cty.iter().enumerate() {
            let is_param = i >= 1 && i <= self.body.arg_count;
            let decl = if is_param { format!("l{i} = p{i}") } else { format!("l{i}") };
            let ct = ctype(t);
            match by_type.iter_mut().find(|(c, _)| *c == ct) {
                Some((_, v)) => v.push(decl),
                None => by_type.push((ct, vec![decl])),
            }
            if self.local_drop[i] {
                flags.push(format!("d{i} = {}", is_param as u8));
            }
        }
        for (ct, names) in &by_type {
            // In C, `T* a, b` makes only `a` a pointer, so every declarator gets its own stars.
            let base = ct.trim_end_matches('*');
            let stars = &ct[base.len()..];
            let decls: Vec<String> = names.iter().map(|n| format!("{stars}{n}")).collect();
            let _ = writeln!(self.out, "  {base} {};", decls.join(", "));
        }
        if !flags.is_empty() {
            let _ = writeln!(self.out, "  uint8_t {};", flags.join(", "));
        }
        let n = self.body.blocks.len();
        let mut reachable = vec![false; n];
        let mut stack = vec![0usize];
        while let Some(b) = stack.pop() {
            if std::mem::replace(&mut reachable[b], true) {
                continue;
            }
            stack.extend(succ(&self.body.blocks[b].term).into_iter().map(|s| s.0 as usize));
        }
        let order: Vec<usize> = (0..n).filter(|&b| reachable[b]).collect();
        for (k, &bi) in order.iter().enumerate() {
            let _ = writeln!(self.out, "bb{bi}:;");
            let block = self.body.block(Bb(bi as u32));
            for s in &block.stmts {
                self.stmt(&s.kind, s.span);
            }
            let next = order.get(k + 1).copied();
            if let Terminator::Goto(t) = &block.term
                && Some(t.0 as usize) == next
            {
                continue;
            }
            self.term(&block.term, block.term_span);
        }
        self.out.push_str("}\n\n");
    }

    // ---------- Places and operands ----------

    fn place(&mut self, pl: &Place, loc: &str) -> (String, CTy) {
        let mut e = format!("l{}", pl.local);
        let mut t = self.local_cty[pl.local as usize].clone();
        let mut variant: Option<u32> = None;
        for pr in &pl.proj {
            match (pr, t.clone()) {
                (Proj::Deref, CTy::Ref(inner)) => {
                    if *inner == CTy::Str {
                        // A `str` place is represented by its fat `&str` value.
                        t = CTy::Str;
                    } else {
                        e = format!("(*{e})");
                        t = *inner;
                    }
                }
                (Proj::Field(i), CTy::Adt(a)) => {
                    let v = variant.take();
                    e = match v {
                        Some(v) => format!("{e}.u.v{v}.f{i}"),
                        None => format!("{e}.f{i}"),
                    };
                    let fty = self.p.adt(a).variants[v.unwrap_or(0) as usize].fields[*i as usize].ty;
                    t = cty(&self.p.tys, fty);
                }
                (Proj::Downcast(_), CTy::Option(_)) => {}
                (Proj::Field(_), CTy::Option(inner)) => {
                    e = format!("{e}.v");
                    t = *inner;
                }
                (Proj::Downcast(v), _) => variant = Some(*v),
                (Proj::Index(l), CTy::Vec(el)) => {
                    e = format!("(({}*){e}.ptr)[lust_bounds(l{l}, {e}.len, {loc})]", ctype(&el));
                    t = *el;
                }
                _ => panic!("bad projection in codegen"),
            }
        }
        (e, t)
    }

    fn operand(&mut self, o: &Operand, loc: &str, post: &mut Vec<String>) -> (String, CTy) {
        match o {
            Operand::Copy(pl) => self.place(pl, loc),
            Operand::Move(pl) => {
                let (e, t) = self.place(pl, loc);
                if self.local_drop[pl.local as usize] {
                    if pl.proj.is_empty() {
                        // Moving the whole local: it owns nothing now.
                        post.push(format!("d{} = 0;", pl.local));
                    } else if pl.proj.iter().all(|x| matches!(x, Proj::Field(_) | Proj::Downcast(_))) {
                        // Moving one field out (a partial move, or an enum payload). Zero the
                        // field so the local's later drop skips it (a zero `String` or `Vec`
                        // drops as a no-op) but still drops every other field.
                        post.push(format!("{e} = ({}){{0}};", ctype(&t)));
                    }
                }
                (e, t)
            }
            Operand::Const(c) => match c {
                Const::Int(v, it) => {
                    let lit = if *v < (1 << 31) { v.to_string() } else { format!("(({}){}ULL)", int_c(*it), v) };
                    (lit, CTy::Int(*it))
                }
                Const::Bool(b) => ((*b as u8).to_string(), CTy::Bool),
                Const::Char(c) => (format!("((uint32_t){})", *c as u32), CTy::Char),
                Const::Str(i) => {
                    let s = &self.p.ast.strings[*i as usize];
                    (format!("((lust_str){{(uint8_t*){}, {}}})", c_string_lit(s.as_bytes()), s.len()), CTy::Ref(Box::new(CTy::Str)))
                }
                Const::Unit => ("0".into(), CTy::Unit),
            },
        }
    }

    // ---------- Statements ----------

    fn stmt(&mut self, s: &StmtKind, span: Span) {
        let loc = self.loc(span);
        match s {
            StmtKind::Assign(dest, rv) => {
                // Rvalues may emit helper statements with temporaries, so open a C block lazily.
                let mark = self.out.len();
                self.out.push_str("  {\n");
                let body_start = self.out.len();
                let mut post = Vec::new();
                let value = self.rvalue(rv, &loc, &mut post);
                let (d, dt) = self.place(dest, &loc);
                let drop = needs_drop_c(self.p, &dt);
                if drop && dest.proj.is_empty() && !rvalue_mentions(rv, dest.local) {
                    // The old value is dropped before the new one is written. Safe because the
                    // rvalue does not read the destination.
                    self.want(Glue::Drop, &dt);
                    let (m, l) = (mangle(&dt), dest.local);
                    if self.out.len() == body_start {
                        self.out.truncate(mark);
                        let _ = write!(self.out, "  if (d{l}) drop_{m}(&{d}); {d} = {value}; d{l} = 1;");
                        for p in &post {
                            let _ = write!(self.out, " {p}");
                        }
                        self.out.push('\n');
                        return;
                    }
                    let _ = writeln!(self.out, "    if (d{l}) drop_{m}(&{d});\n    {d} = {value};\n    d{l} = 1;");
                    for p in &post {
                        let _ = writeln!(self.out, "    {p}");
                    }
                    self.out.push_str("  }\n");
                    return;
                }
                if drop {
                    let t = self.tmp();
                    let _ = writeln!(self.out, "    {} {t} = {value};", ctype(&dt));
                    for p in &post {
                        let _ = writeln!(self.out, "    {p}");
                    }
                    self.want(Glue::Drop, &dt);
                    let m = mangle(&dt);
                    if dest.proj.is_empty() {
                        let l = dest.local;
                        let _ = writeln!(self.out, "    if (d{l}) drop_{m}(&{d});\n    {d} = {t};\n    d{l} = 1;");
                    } else {
                        let _ = writeln!(self.out, "    drop_{m}(&{d});\n    {d} = {t};");
                    }
                } else {
                    if dt == CTy::Str {
                        panic!("unsized assignment");
                    }
                    if self.out.len() == body_start && post.is_empty() {
                        // No helper statements: a plain assignment needs no block.
                        self.out.truncate(mark);
                        let _ = writeln!(self.out, "  {d} = {value};");
                        return;
                    }
                    let _ = writeln!(self.out, "    {d} = {value};");
                    for p in &post {
                        let _ = writeln!(self.out, "    {p}");
                    }
                }
                self.out.push_str("  }\n");
            }
            StmtKind::Drop(l) => {
                let t = self.local_cty[*l as usize].clone();
                if self.local_drop[*l as usize] {
                    self.want(Glue::Drop, &t);
                    let _ = writeln!(self.out, "  if (d{l}) {{ d{l} = 0; drop_{}(&l{l}); }}", mangle(&t));
                }
            }
            StmtKind::StorageDead(_) | StmtKind::FakeRead(_) => {}
            StmtKind::Print { stderr, newline, parts } => {
                self.out.push_str("  {\n");
                let mut post = Vec::new();
                let s = self.format(parts, &loc, &mut post);
                if *newline {
                    let _ = writeln!(self.out, "    lust_string_push_bytes(&{s}, \"\\n\", 1);");
                }
                let f = if *stderr { "1" } else { "0" };
                let _ = writeln!(self.out, "    lust_write({f}, &{s});");
                self.out.push_str("  }\n");
            }
        }
    }

    fn term(&mut self, t: &Terminator, span: Span) {
        let loc = self.loc(span);
        let mut post = Vec::new();
        match t {
            Terminator::Goto(b) => {
                let _ = writeln!(self.out, "  goto bb{};", b.0);
            }
            Terminator::If(o, a, b) => {
                let (c, _) = self.operand(o, &loc, &mut post);
                let _ = writeln!(self.out, "  if ({c}) goto bb{}; else goto bb{};", a.0, b.0);
            }
            Terminator::Switch(o, cases, other) => {
                let (c, _) = self.operand(o, &loc, &mut post);
                let _ = write!(self.out, "  switch ({c}) {{");
                for (v, b) in cases {
                    let _ = write!(self.out, " case {v}: goto bb{};", b.0);
                }
                let _ = writeln!(self.out, " default: goto bb{}; }}", other.0);
            }
            Terminator::Return => self.out.push_str("  return l0;\n"),
            Terminator::Unreachable => self.out.push_str("  abort();\n"),
            Terminator::Panic(parts) => {
                self.out.push_str("  {\n");
                let s = self.format(parts, &loc, &mut post);
                let _ = writeln!(self.out, "    lust_panic(&{s}, {loc});\n  }}");
            }
        }
    }

    // ---------- Rvalues ----------

    fn rvalue(&mut self, rv: &Rvalue, loc: &str, post: &mut Vec<String>) -> String {
        match rv {
            Rvalue::Use(o) => self.operand(o, loc, post).0,
            Rvalue::Ref(_, pl) => {
                let (e, t) = self.place(pl, loc);
                if t == CTy::Str { e } else { format!("(&{e})") }
            }
            Rvalue::Bin(op, a, b) => {
                let (a, at) = self.operand(a, loc, post);
                let (b, bt) = self.operand(b, loc, post);
                self.bin(*op, &a, &at, &b, &bt, loc)
            }
            Rvalue::Un(op, a) => {
                let (a, at) = self.operand(a, loc, post);
                match (op, &at) {
                    (UnOp::Neg, CTy::Int(i)) => format!("lust_neg_{}({a}, {loc})", int_fn(*i)),
                    (UnOp::Not, CTy::Bool) => format!("(!{a})"),
                    (UnOp::Not, CTy::Int(i)) => format!("(({})~{a})", int_c(*i)),
                    _ => panic!("bad unary op"),
                }
            }
            Rvalue::Cast(o, to) => {
                let (a, _) = self.operand(o, loc, post);
                let to = cty(&self.body.tys, *to);
                format!("(({}){a})", ctype(&to))
            }
            Rvalue::Opt(ty, op) => {
                let ct = ctype(&cty(&self.body.tys, *ty));
                match op {
                    Some(o) => {
                        let (v, _) = self.operand(o, loc, post);
                        format!("(({ct}){{ .tag = 1, .v = {v} }})")
                    }
                    None => format!("(({ct}){{ .tag = 0 }})"),
                }
            }
            Rvalue::Aggregate(a, v, ops) => {
                let adt = self.p.adt(*a);
                let vals: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                if adt.is_enum {
                    if fields.is_empty() {
                        format!("((A{}){{ .tag = {v} }})", a.0)
                    } else {
                        format!("((A{}){{ .tag = {v}, .u = {{ .v{v} = {{ {} }} }} }})", a.0, fields.join(", "))
                    }
                } else if fields.is_empty() {
                    format!("((A{}){{0}})", a.0)
                } else {
                    format!("((A{}){{ {} }})", a.0, fields.join(", "))
                }
            }
            Rvalue::VecLit(elem, ops) => {
                let et = ctype(&cty(&self.body.tys, *elem));
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_Vec {t} = lust_vec_with_capacity({}, sizeof({et}));", ops.len());
                for (i, o) in ops.iter().enumerate() {
                    let (v, _) = self.operand(o, loc, post);
                    let _ = writeln!(self.out, "    (({et}*){t}.ptr)[{i}] = {v};");
                }
                let _ = writeln!(self.out, "    {t}.len = {};", ops.len());
                t
            }
            Rvalue::VecRepeat(elem, x, n) => {
                let ec = cty(&self.body.tys, *elem);
                let et = ctype(&ec);
                let (xv, _) = self.operand(x, loc, post);
                let (nv, _) = self.operand(n, loc, post);
                let (t, xt, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {et} {xt} = {xv};\n    uint64_t {i}_n = {nv};");
                let _ = writeln!(self.out, "    lust_Vec {t} = lust_vec_with_capacity({i}_n, sizeof({et}));");
                let clone = if is_copy_c(self.p, &ec) {
                    xt.to_string()
                } else {
                    self.want(Glue::Clone, &ec);
                    format!("clone_{}(&{xt})", mangle(&ec))
                };
                // Clone n-1 times, then move the original into the last slot (as Rust does).
                let _ = writeln!(self.out, "    for (uint64_t {i} = 0; {i} + 1 < {i}_n; {i}++) (({et}*){t}.ptr)[{i}] = {clone};");
                let _ = write!(self.out, "    if ({i}_n) (({et}*){t}.ptr)[{i}_n - 1] = {xt};");
                if needs_drop_c(self.p, &ec) {
                    self.want(Glue::Drop, &ec);
                    let _ = write!(self.out, " else drop_{}(&{xt});", mangle(&ec));
                }
                let _ = writeln!(self.out, "\n    {t}.len = {i}_n;");
                t
            }
            Rvalue::Call(f, ops) => {
                // Every call goes through `lust_fns`, so a changed function can be swapped in
                // without relinking its callers.
                let info = self.p.fn_info(*f);
                for &t in info.params.iter().chain(std::iter::once(&info.ret)) {
                    let ct = cty(&self.p.tys, t);
                    collect_types(&ct, &mut self.sig_types);
                }
                let args: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                format!("({}lust_fns[{}])({})", fn_ptr_cast(self.p, *f), self.slots[f.0 as usize], args.join(", "))
            }
            Rvalue::Builtin(b, ops) => self.builtin(*b, ops, loc, post),
            Rvalue::Eq { a, b, ty, ne } => {
                let (a, _) = self.operand(a, loc, post);
                let (b, _) = self.operand(b, loc, post);
                let t = cty(&self.body.tys, *ty);
                let e = self.eq_expr(&t, &a, &b);
                if *ne { format!("(!{e})") } else { e }
            }
            Rvalue::StrCmp(op, a, b) => {
                let (a, _) = self.operand(a, loc, post);
                let (b, _) = self.operand(b, loc, post);
                match op {
                    BinOp::Eq => format!("lust_str_eq({a}, {b})"),
                    BinOp::Ne => format!("(!lust_str_eq({a}, {b}))"),
                    _ => format!("(lust_str_cmp({a}, {b}) {} 0)", op.symbol()),
                }
            }
            Rvalue::StringAdd(a, b) => {
                let (a, _) = self.operand(a, loc, post);
                let (b, _) = self.operand(b, loc, post);
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_String {t} = {a};\n    lust_string_push_str(&{t}, {b});");
                t
            }
            Rvalue::Format(parts) => self.format(parts, loc, post),
            Rvalue::Discriminant(pl) => {
                let (e, _) = self.place(pl, loc);
                format!("{e}.tag")
            }
        }
    }

    fn bin(&mut self, op: BinOp, a: &str, at: &CTy, b: &str, bt: &CTy, loc: &str) -> String {
        use BinOp::*;
        if op.is_cmp() {
            return format!("({a} {} {b})", op.symbol());
        }
        match at {
            CTy::Bool => format!("((uint8_t)({a} {} {b}))", op.symbol()),
            CTy::Int(i) => {
                let (c, f) = (int_c(*i), int_fn(*i));
                match op {
                    Add => format!("lust_add_{f}({a}, {b}, {loc})"),
                    Sub => format!("lust_sub_{f}({a}, {b}, {loc})"),
                    Mul => format!("lust_mul_{f}({a}, {b}, {loc})"),
                    Div => format!("lust_div_{f}({a}, {b}, {loc})"),
                    Rem => format!("lust_rem_{f}({a}, {b}, {loc})"),
                    BitAnd | BitOr | BitXor => format!("(({c})({a} {} {b}))", op.symbol()),
                    Shl | Shr => {
                        let amount = match bt {
                            CTy::Int(bi) if bi.signed() => format!("(uint64_t)(int64_t)({b})"),
                            _ => format!("(uint64_t)({b})"),
                        };
                        let dir = if op == Shl { "left" } else { "right" };
                        let sh = format!("lust_shift_amount({amount}, {}, \"{dir}\", {loc})", i.bits());
                        if op == Shl { format!("(({c})((uint64_t)({a}) << {sh}))") } else { format!("(({c})({a} >> {sh}))") }
                    }
                    _ => unreachable!(),
                }
            }
            _ => panic!("bad binary operand type"),
        }
    }

    /// `a` and `b` are pointers to values of type `t`.
    fn eq_expr(&mut self, t: &CTy, a: &str, b: &str) -> String {
        match t {
            CTy::Unit => "1".into(),
            CTy::Bool | CTy::Char | CTy::Int(_) => format!("(*{a} == *{b})"),
            _ => {
                self.want(Glue::Eq, t);
                format!("eq_{}({a}, {b})", mangle(t))
            }
        }
    }

    fn builtin(&mut self, b: Builtin, ops: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        use Builtin as B;
        let mut vals = Vec::new();
        let mut tys = Vec::new();
        for o in ops {
            let (v, t) = self.operand(o, loc, post);
            vals.push(v);
            tys.push(t);
        }
        let int_of = |t: &CTy| match t {
            CTy::Int(i) => *i,
            _ => IntTy::I64,
        };
        match b {
            B::StringNew => "lust_string_new()".into(),
            B::StringFrom => format!("lust_string_from({})", vals[0]),
            B::StringWithCapacity => format!("lust_string_with_capacity({})", vals[0]),
            B::VecNew | B::VecWithCapacity => unreachable!("lowered to VecLit"),
            B::EnvArgs => "((lust_Args){ (uint64_t)lust_argc })".into(),
            B::ArgsCount => format!("{}.n", vals[0]),
            B::StrLen => format!("{}.len", vals[0]),
            B::StrIsEmpty => format!("({}.len == 0)", vals[0]),
            B::StrToString => format!("lust_string_from({})", vals[0]),
            B::StringLen | B::VecLen => format!("({})->len", vals[0]),
            B::StringIsEmpty | B::VecIsEmpty => format!("(({})->len == 0)", vals[0]),
            B::StringPushStr => {
                let _ = writeln!(self.out, "    lust_string_push_str({}, {});", vals[0], vals[1]);
                "0".into()
            }
            B::StringPush => {
                let _ = writeln!(self.out, "    lust_string_push_char({}, {});", vals[0], vals[1]);
                "0".into()
            }
            B::StringAsStr => format!("lust_string_as_str({})", vals[0]),
            B::VecPush => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                // The value must be read before `lust_vec_push_slot` can reallocate the
                // buffer: `v.push(v[0])` in one C assignment could read the freed buffer.
                let t = self.tmp();
                let _ = writeln!(self.out, "    {et} {t} = {};", vals[1]);
                let _ = writeln!(self.out, "    *({et}*)lust_vec_push_slot({}, sizeof({et})) = {t};", vals[0]);
                "0".into()
            }
            B::Clone => {
                let CTy::Ref(inner) = &tys[0] else { unreachable!() };
                if is_copy_c(self.p, inner) || **inner == CTy::Str {
                    format!("(*{})", vals[0])
                } else {
                    self.want(Glue::Clone, inner);
                    format!("clone_{}({})", mangle(inner), vals[0])
                }
            }
            B::ToString => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_String {t} = lust_string_new();");
                let ty = tys[0].clone();
                let CTy::Ref(inner) = ty else { unreachable!() };
                self.fmt_value(&t, &vals[0], &inner, false);
                t
            }
            B::WrappingAdd | B::WrappingSub | B::WrappingMul => {
                let c = int_c(int_of(&tys[0]));
                let op = match b {
                    B::WrappingAdd => "+",
                    B::WrappingSub => "-",
                    _ => "*",
                };
                format!("(({c})((uint64_t)({}) {op} (uint64_t)({})))", vals[0], vals[1])
            }
            B::Abs => format!("lust_abs_{}({}, {loc})", int_fn(int_of(&tys[0])), vals[0]),
            B::Pow => format!("lust_pow_{}({}, {}, {loc})", int_fn(int_of(&tys[0])), vals[0], vals[1]),
            B::Min => format!("({0} < {1} ? {0} : {1})", vals[0], vals[1]),
            B::Max => format!("({0} > {1} ? {0} : {1})", vals[0], vals[1]),
            B::OptIsSome => format!("(({})->tag == 1)", vals[0]),
            B::OptIsNone => format!("(({})->tag == 0)", vals[0]),
            B::OptUnwrap | B::OptExpect => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t} = {};", ctype(&tys[0]), vals[0]);
                if b == B::OptUnwrap {
                    let _ =
                        writeln!(self.out, "    if (!{t}.tag) lust_panic_cstr(\"called `Option::unwrap()` on a `None` value\", {loc});");
                } else {
                    let _ = writeln!(self.out, "    if (!{t}.tag) lust_panic_str({}, {loc});", vals[1]);
                }
                format!("{t}.v")
            }
            B::OptUnwrapOr => {
                let CTy::Option(inner) = &tys[0] else { unreachable!() };
                let (t, d) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {} {t} = {};\n    {} {d} = {};", ctype(&tys[0]), vals[0], ctype(inner), vals[1]);
                if needs_drop_c(self.p, inner) {
                    // The unused default is dropped, as in Rust.
                    self.want(Glue::Drop, inner);
                    let _ = writeln!(self.out, "    if ({t}.tag) drop_{}(&{d});", mangle(inner));
                }
                format!("({t}.tag ? {t}.v : {d})")
            }
            B::VecPop | B::VecGet | B::VecFirst | B::VecLast => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (opt, r) =
                    if b == B::VecPop { (CTy::Option(e.clone()), "") } else { (CTy::Option(Box::new(CTy::Ref(e.clone()))), "&") };
                let ot = ctype(&opt);
                let t = self.tmp();
                let v = &vals[0];
                let (cond, idx) = match b {
                    B::VecPop => (format!("{v}->len > 0"), format!("--{v}->len")),
                    B::VecGet => (format!("{} < {v}->len", vals[1]), vals[1].clone()),
                    B::VecFirst => (format!("{v}->len > 0"), "0".into()),
                    _ => (format!("{v}->len > 0"), format!("{v}->len - 1")),
                };
                let _ = writeln!(
                    self.out,
                    "    {ot} {t}; {t}.tag = 0;\n    if ({cond}) {{ {t}.tag = 1; {t}.v = {r}(({et}*){v}->ptr)[{idx}]; }}"
                );
                t
            }
            B::VecContains => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (t, i) = (self.tmp(), self.tmp());
                let elem = format!("(&(({et}*){}->ptr)[{i}])", vals[0]);
                let eq = self.eq_expr(e, &elem, &vals[1]);
                let _ = writeln!(
                    self.out,
                    "    uint8_t {t} = 0;\n    for (uint64_t {i} = 0; {i} < {}->len; {i}++) if ({eq}) {{ {t} = 1; break; }}",
                    vals[0]
                );
                t
            }
            B::VecSwap => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let (et, t) = (ctype(e), self.tmp());
                let (vv, a, bb) = (&vals[0], &vals[1], &vals[2]);
                let _ = writeln!(
                    self.out,
                    "    lust_bounds({a}, {vv}->len, {loc}); lust_bounds({bb}, {vv}->len, {loc});\n    {et} {t} = (({et}*){vv}->ptr)[{a}]; (({et}*){vv}->ptr)[{a}] = (({et}*){vv}->ptr)[{bb}]; (({et}*){vv}->ptr)[{bb}] = {t};"
                );
                "0".into()
            }
            B::VecClear | B::VecTruncate => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let n = if b == B::VecClear { "0".to_string() } else { vals[1].clone() };
                let vv = &vals[0];
                if needs_drop_c(self.p, e) {
                    self.want(Glue::Drop, e);
                    let i = self.tmp();
                    let _ = writeln!(
                        self.out,
                        "    for (uint64_t {i} = {n}; {i} < {vv}->len; {i}++) drop_{}(&(({}*){vv}->ptr)[{i}]);",
                        mangle(e),
                        ctype(e)
                    );
                }
                let _ = writeln!(self.out, "    if ({n} < {vv}->len) {vv}->len = {n};");
                "0".into()
            }
            B::VecInsert => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let et = ctype(e);
                let (vv, i, x) = (&vals[0], &vals[1], &vals[2]);
                let _ = writeln!(self.out, "    lust_vec_insert_at({vv}, {i}, sizeof({et}), {loc});\n    (({et}*){vv}->ptr)[{i}] = {x};");
                "0".into()
            }
            B::VecRemove => {
                let CTy::Ref(v) = &tys[0] else { unreachable!() };
                let CTy::Vec(e) = &**v else { unreachable!() };
                let (et, t) = (ctype(e), self.tmp());
                let (vv, i) = (&vals[0], &vals[1]);
                let _ = writeln!(
                    self.out,
                    "    lust_vec_check_remove({vv}, {i}, {loc});\n    {et} {t} = (({et}*){vv}->ptr)[{i}];\n    lust_vec_remove_at({vv}, {i}, sizeof({et}));"
                );
                t
            }
            B::StrContains | B::StrStartsWith | B::StrEndsWith => {
                let a = str_of(&vals[0], &tys[0]);
                let f = match b {
                    B::StrContains => "lust_str_contains",
                    B::StrStartsWith => "lust_str_starts_with",
                    _ => "lust_str_ends_with",
                };
                format!("{f}({a}, {})", vals[1])
            }
            B::StrTrim => format!("lust_str_trim({})", str_of(&vals[0], &tys[0])),
            B::StrToUppercase => format!("lust_str_ascii_case({}, 1)", str_of(&vals[0], &tys[0])),
            B::StrToLowercase => format!("lust_str_ascii_case({}, 0)", str_of(&vals[0], &tys[0])),
            B::StrChars => format!("lust_chars({})", str_of(&vals[0], &tys[0])),
            B::CharsNext => {
                let t = self.tmp();
                let it = &vals[0];
                let ot = ctype(&CTy::Option(Box::new(CTy::Char)));
                let _ = writeln!(
                    self.out,
                    "    {ot} {t}; {t}.tag = {it}->pos < {it}->s.len;\n    if ({t}.tag) {t}.v = lust_utf8_next({it}->s.ptr, &{it}->pos);"
                );
                t
            }
            B::CharsCount => format!("lust_chars_count({})", vals[0]),
            B::CharIsDigit => format!("(*{0} >= '0' && *{0} <= '9')", vals[0]),
            B::CharIsAlphabetic => format!("((*{0} | 32) >= 'a' && (*{0} | 32) <= 'z')", vals[0]),
            B::CharIsAlphanumeric => format!("((*{0} >= '0' && *{0} <= '9') || ((*{0} | 32) >= 'a' && (*{0} | 32) <= 'z'))", vals[0]),
            B::CharIsWhitespace => format!("(*{0} == ' ' || *{0} == '\\t' || *{0} == '\\n' || *{0} == '\\r' || *{0} == 12)", vals[0]),
            B::CharIsUppercase => format!("(*{0} >= 'A' && *{0} <= 'Z')", vals[0]),
            B::CharIsLowercase => format!("(*{0} >= 'a' && *{0} <= 'z')", vals[0]),
            B::CharToUppercase => format!("((*{0} >= 'a' && *{0} <= 'z') ? *{0} - 32 : *{0})", vals[0]),
            B::CharToLowercase => format!("((*{0} >= 'A' && *{0} <= 'Z') ? *{0} + 32 : *{0})", vals[0]),
            B::CharToDigit => {
                let ot = ctype(&CTy::Option(Box::new(CTy::Int(IntTy::U32))));
                let t = self.tmp();
                let _ = writeln!(
                    self.out,
                    "    {ot} {t}; {t}.tag = 0;\n    {{ uint32_t d = lust_digit({}, {}, {loc}); if (d != 0xFFFFFFFFu) {{ {t}.tag = 1; {t}.v = d; }} }}",
                    vals[0], vals[1]
                );
                t
            }
        }
    }

    // ---------- Formatting ----------

    fn format(&mut self, parts: &[FmtPart], loc: &str, post: &mut Vec<String>) -> String {
        let s = self.tmp();
        let _ = writeln!(self.out, "    lust_String {s} = lust_string_new();");
        for part in parts {
            match part {
                FmtPart::Lit(text) => {
                    if !text.is_empty() {
                        let _ = writeln!(self.out, "    lust_string_push_bytes(&{s}, {}, {});", c_string_lit(text.as_bytes()), text.len());
                    }
                }
                FmtPart::Arg { value, ty, debug } => {
                    let (v, _) = self.operand(value, loc, post);
                    let t = cty(&self.body.tys, *ty);
                    self.fmt_value(&s, &v, &t, *debug);
                }
            }
        }
        s
    }

    /// Appends `*ptr` (of type `t`) to the String `out`, with Display or Debug formatting.
    fn fmt_value(&mut self, out: &str, ptr: &str, t: &CTy, debug: bool) {
        let mut e = if *t == CTy::Str { ptr.to_string() } else { format!("(*{ptr})") };
        let mut t = t.clone();
        while let CTy::Ref(inner) = t.clone() {
            if *inner == CTy::Str {
                break;
            }
            e = format!("(*{e})");
            t = *inner;
        }
        let line = match (&t, debug) {
            (CTy::Int(i), _) if i.signed() => format!("lust_fmt_i64(&{out}, (int64_t){e});"),
            (CTy::Int(_), _) => format!("lust_fmt_u64(&{out}, (uint64_t){e});"),
            (CTy::Bool, _) => format!("lust_fmt_bool(&{out}, {e});"),
            (CTy::Char, false) => format!("lust_string_push_char(&{out}, {e});"),
            (CTy::Char, true) => format!("lust_fmt_char_debug(&{out}, {e});"),
            (CTy::String, false) => format!("lust_string_push_str(&{out}, lust_string_as_str(&{e}));"),
            (CTy::String, true) => format!("lust_fmt_str_debug(&{out}, lust_string_as_str(&{e}));"),
            (CTy::Ref(_), false) | (CTy::Str, false) => format!("lust_string_push_str(&{out}, {e});"),
            (CTy::Ref(_), true) | (CTy::Str, true) => format!("lust_fmt_str_debug(&{out}, {e});"),
            (CTy::Unit, _) => format!("lust_string_push_bytes(&{out}, \"()\", 2);"),
            (CTy::Args, _) => format!("lust_string_push_bytes(&{out}, \"Args\", 4);"),
            _ => {
                self.want(Glue::Debug, &t);
                format!("dbg_{}(&{out}, &{e});", mangle(&t))
            }
        };
        let _ = writeln!(self.out, "    {line}");
    }
}

// ---------- Compilation units ----------
//
// Unit 0 holds the globals, the function line table, and `main`. Unit 1 holds the shared glue
// (see `GlueSet`); other glue is static in the function units. The other units hold functions, in
// fixed groups of FnIds. Grouping depends only on the function count, so an edit that keeps the
// program's shape recompiles only the units it touches (plus unit 0).

/// Function groups for units 2 and up.
pub fn group_fns(n: usize, per_unit: usize) -> Vec<std::ops::Range<usize>> {
    (0..n).step_by(per_unit.max(1)).map(|a| a..(a + per_unit).min(n)).collect()
}

/// All glue needed by a set of functions, closed over field types.
//
// Glue placement is hybrid. `shared` holds the keys that live once in the glue unit (unit 1):
// glue that many function units reach (see `compute_shared`). Every other key is emitted as a
// static copy in each function unit that reaches it, so an edit that needs new glue does not
// rebuild the glue unit. `shared` is None until the first `compute_shared`; before that, all
// glue lives in the glue unit, as before.
#[derive(Default)]
pub struct GlueSet {
    pub protos: HashMap<(Glue, CTy), String>,
    defs: String,
    /// Each key's definition on its own, so units can carry static copies of just what they reach.
    def_map: HashMap<(Glue, CTy), String>,
    /// The glue keys each key's definition calls.
    deps: HashMap<(Glue, CTy), Vec<(Glue, CTy)>>,
    /// Keys that live in the shared glue unit. Frozen until the next `compute_shared`.
    pub shared: Option<HashSet<(Glue, CTy)>>,
}

impl GlueSet {
    /// Adds glue for `keys` and everything it needs. Returns true when the shared glue unit's
    /// content changed, so the caller must recompile it. New glue that no unit shared at freeze
    /// time is not in `shared`, so it returns false for that: the new glue is static in the
    /// function units that reach it.
    pub fn add<'k>(&mut self, p: &Program, keys: impl Iterator<Item = &'k (Glue, CTy)>) -> bool {
        let mut pending: Vec<(Glue, CTy)> = keys.filter(|k| !self.protos.contains_key(k)).cloned().collect();
        let mut shared_changed = false;
        while let Some(g) = pending.pop() {
            if self.protos.contains_key(&g) {
                continue;
            }
            let mut more = Vec::new();
            let mut proto = String::new();
            let mut def = String::new();
            glue_def(p, &g.0, &g.1, &mut proto, &mut def, &mut more);
            self.defs.push_str(&def);
            self.def_map.insert(g.clone(), def);
            self.deps.insert(g.clone(), more.clone());
            shared_changed |= self.shared.as_ref().is_none_or(|s| s.contains(&g));
            self.protos.insert(g, proto);
            pending.extend(more);
        }
        shared_changed
    }

    /// The glue keys a set of direct needs reaches, deps included.
    fn closure<'a>(&'a self, roots: impl Iterator<Item = &'a (Glue, CTy)>) -> HashSet<&'a (Glue, CTy)> {
        let mut seen = HashSet::new();
        let mut stack: Vec<&(Glue, CTy)> = roots.collect();
        while let Some(k) = stack.pop() {
            if seen.insert(k) {
                if let Some(deps) = self.deps.get(k) {
                    stack.extend(deps.iter());
                }
            }
        }
        seen
    }

    /// Picks the shared set: keys reached by at least `k` function units (`fns` is indexed by
    /// slot, `groups` are the units). The set is closed over deps, so the shared glue unit's
    /// definitions only call each other. Call this only on a fresh base, then keep it frozen:
    /// a key that turned shared later would need the base glue unit rebuilt.
    pub fn compute_shared(&mut self, fns: &[FnOut], groups: &[std::ops::Range<usize>], k: usize) {
        let mut count: HashMap<&(Glue, CTy), usize> = HashMap::new();
        for range in groups {
            for key in self.closure(fns[range.clone()].iter().flat_map(|f| f.glue.iter())) {
                *count.entry(key).or_default() += 1;
            }
        }
        let mut shared: HashSet<(Glue, CTy)> = count.into_iter().filter(|&(_, n)| n >= k).map(|(key, _)| key.clone()).collect();
        // Close over deps (the count already implies this, but keep the glue unit self-contained).
        let mut stack: Vec<(Glue, CTy)> = shared.iter().cloned().collect();
        while let Some(key) = stack.pop() {
            if let Some(deps) = self.deps.get(&key) {
                for dep in deps {
                    if shared.insert(dep.clone()) {
                        stack.push(dep.clone());
                    }
                }
            }
        }
        self.shared = Some(shared);
    }

    fn is_shared(&self, k: &(Glue, CTy)) -> bool {
        self.shared.as_ref().is_some_and(|s| s.contains(k))
    }
}

fn unit_header() -> String {
    let mut c = String::with_capacity(64 * 1024);
    c.push_str(runtime_decls());
    c.push('\n');
    c
}

/// The runtime without function bodies: `LUST_BODY(...)` regions are cut out once, so units do
/// not make tcc tokenize code that would expand to nothing.
fn runtime_decls() -> &'static str {
    static DECLS: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    DECLS.get_or_init(|| {
        let src = include_str!("runtime.c");
        let mut out = String::with_capacity(src.len() / 2);
        let mut rest = src;
        // Skip the macro's own definition lines, which mention LUST_BODY without a body.
        while let Some(i) = rest.find("LUST_BODY(") {
            let line_start = rest[..i].rfind('\n').map_or(0, |n| n + 1);
            if rest[line_start..].starts_with("#define LUST_BODY") {
                let end = rest[i..].find('\n').map_or(rest.len(), |n| i + n);
                out.push_str(&rest[..end]);
                rest = &rest[end..];
                continue;
            }
            out.push_str(&rest[..i]);
            // Find the matching close paren of LUST_BODY( ... ).
            let mut depth = 0;
            let mut end = i;
            for (k, ch) in rest[i..].char_indices() {
                match ch {
                    '(' => depth += 1,
                    ')' => {
                        depth -= 1;
                        if depth == 0 {
                            end = i + k + 1;
                            break;
                        }
                    }
                    _ => {}
                }
            }
            out.push(';');
            rest = &rest[end..];
        }
        out.push_str(rest);
        // Units do not include <stdint.h> or <stddef.h>: tcc spends about 1 ms per unit parsing
        // the system headers behind them. The compiler's predefined types define the same names
        // (tcc and gcc both predefine them; on macOS arm64 tcc's __INT64_TYPE__ is long long,
        // which matches Apple's int64_t). The runtime unit keeps the real includes.
        out.replacen(
            "#include <stdint.h>\n#include <stddef.h>\n",
            "typedef signed char int8_t; typedef unsigned char uint8_t; typedef short int16_t; typedef unsigned short uint16_t;\ntypedef int int32_t; typedef unsigned int uint32_t;\n#ifdef __INT64_TYPE__\ntypedef __INT64_TYPE__ int64_t; typedef unsigned __INT64_TYPE__ uint64_t;\n#else\ntypedef long long int64_t; typedef unsigned long long uint64_t;\n#endif\n#ifdef __SIZE_TYPE__\ntypedef __SIZE_TYPE__ size_t; typedef __PTRDIFF_TYPE__ ptrdiff_t; typedef __UINTPTR_TYPE__ uintptr_t; typedef __INTPTR_TYPE__ intptr_t;\n#else\ntypedef unsigned long size_t; typedef long ptrdiff_t; typedef unsigned long uintptr_t; typedef long intptr_t;\n#endif\n#define INT64_MIN (-9223372036854775807LL-1)\n#ifndef NULL\n#define NULL ((void*)0)\n#endif\n",
            1,
        )
    })
}

/// The unit with the runtime's function definitions. It only changes when lust itself does.
pub fn runtime_unit() -> String {
    format!("#define LUST_IMPL 1\n{}", include_str!("runtime.c"))
}

/// Unit 0: the line table (by slot), globals, overlay registration, and `main`. Rebuilt on every
/// build.
pub fn main_unit(main_slot: u32, file: &str, slot_lines: &[u32], overlays: &[usize]) -> String {
    let mut c = unit_header();
    let lines: Vec<String> = slot_lines.iter().map(|l| l.to_string()).collect();
    let _ = writeln!(c, "static const uint32_t lines[{}] = {{{}}};", lines.len().max(1), lines.join(","));
    for u in overlays {
        let _ = writeln!(c, "void lust_overlay_u{u}(void);");
    }
    let _ = writeln!(
        c,
        "int main(int argc, char **argv) {{\n  (void)argv;\n  lust_argc = argc;\n  lust_file = {};\n  lust_fn_line = lines;\n  lust_base_init();",
        c_string_lit(file.as_bytes())
    );
    for u in overlays {
        let _ = writeln!(c, "  lust_overlay_u{u}();");
    }
    let _ = writeln!(c, "  ((void (*)(void))lust_fns[{main_slot}])();\n  lust_flush();\n  return 0;\n}}");
    c
}

/// The function table (with room for `capacity` slots), and `lust_base_init`, which registers
/// every base function unit.
pub fn table_unit(capacity: usize, fn_units: &[usize]) -> String {
    let mut c = unit_header();
    let _ = writeln!(c, "lust_fnptr lust_fns[{}];", capacity.max(1));
    for u in fn_units {
        let _ = writeln!(c, "void lust_register_u{u}(void);");
    }
    c.push_str("void lust_base_init(void) {\n");
    for u in fn_units {
        let _ = writeln!(c, "  lust_register_u{u}();");
    }
    c.push_str("}\n");
    c
}

/// The shared glue unit. With a frozen shared set it holds only those keys; the rest of the
/// glue is static in the function units (see `GlueSet`).
pub fn glue_unit(p: &Program, g: &GlueSet) -> String {
    let mut c = unit_header();
    let mut types = HashSet::new();
    if let Some(shared) = &g.shared {
        for k in shared {
            collect_types(&k.1, &mut types);
        }
        type_decls(p, &mut c, &types);
        let mut keys: Vec<&(Glue, CTy)> = shared.iter().collect();
        keys.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
        for k in &keys {
            c.push_str(&g.protos[*k]);
        }
        for k in &keys {
            c.push_str(&g.def_map[*k]);
        }
        return c;
    }
    for k in g.protos.keys() {
        collect_types(&k.1, &mut types);
    }
    type_decls(p, &mut c, &types);
    let mut protos: Vec<&String> = g.protos.values().collect();
    protos.sort();
    for proto in protos {
        c.push_str(proto);
    }
    c.push_str(&g.defs);
    c
}

/// The unit for the slots in `range` (`fns` is indexed by slot; empty slots have no code). Its
/// functions are static; the function `register` stores them in `lust_fns`.
pub fn fn_unit(p: &Program, fns: &[FnOut], range: std::ops::Range<usize>, g: &GlueSet, register: &str) -> String {
    let mut c = unit_header();
    let mut types = HashSet::new();
    let mut seen: HashSet<&(Glue, CTy)> = HashSet::new();
    for f in &fns[range.clone()] {
        types.extend(f.types.iter().cloned());
        seen.extend(f.glue.iter());
    }
    // With a frozen shared set, glue that is not shared is static in this unit: walk its deps
    // too, and stop at shared keys (their deps live in the glue unit). Shared keys still need
    // their prototype, and every reached key needs its C type declared.
    let hybrid = g.shared.is_some();
    if hybrid {
        let mut stack: Vec<&(Glue, CTy)> = seen.iter().copied().collect();
        while let Some(k) = stack.pop() {
            collect_types(&k.1, &mut types);
            if !g.is_shared(k) {
                if let Some(deps) = g.deps.get(k) {
                    for dep in deps {
                        if seen.insert(dep) {
                            stack.push(dep);
                        }
                    }
                }
            }
        }
    }
    type_decls(p, &mut c, &types);
    let mut keys: Vec<&(Glue, CTy)> = seen.iter().copied().collect();
    keys.sort_by(|a, b| g.protos[*a].cmp(&g.protos[*b]));
    for k in &keys {
        if hybrid && !g.is_shared(k) {
            c.push_str("static ");
        }
        c.push_str(&g.protos[*k]);
    }
    if hybrid {
        for k in keys.iter().filter(|k| !g.is_shared(k)) {
            c.push_str("static ");
            c.push_str(&g.def_map[*k]);
        }
    }
    for f in &fns[range.clone()] {
        c.push_str(&f.code);
    }
    let _ = writeln!(c, "void {register}(void) {{");
    for i in range.filter(|&i| !fns[i].code.is_empty()) {
        let _ = writeln!(c, "  lust_fns[{i}] = (lust_fnptr)f{i};");
    }
    c.push_str("}\n");
    c
}

/// Declares the given types, plus every type they contain (by value or inside a Vec).
fn type_decls(p: &Program, out: &mut String, roots: &HashSet<CTy>) {
    // Close over field types.
    let mut wanted: HashSet<CTy> = HashSet::new();
    let mut stack: Vec<CTy> = roots.iter().cloned().collect();
    while let Some(t) = stack.pop() {
        if !wanted.insert(t.clone()) {
            continue;
        }
        let mut inner = HashSet::new();
        match &t {
            CTy::Adt(a) => p.adt(*a).variants.iter().flat_map(|v| &v.fields).for_each(|f| collect_types(&cty(&p.tys, f.ty), &mut inner)),
            CTy::Option(e) => collect_types(e, &mut inner),
            _ => {}
        }
        stack.extend(inner);
    }
    let mut list: Vec<CTy> = wanted.into_iter().collect();
    list.sort_by_cached_key(mangle);
    for t in &list {
        if let CTy::Adt(a) = t {
            let _ = writeln!(out, "typedef struct A{0} A{0};", a.0);
        }
    }
    // Each definition comes after the types it holds by value.
    fn emit(p: &Program, t: &CTy, emitted: &mut HashSet<CTy>, out: &mut String) {
        if !emitted.insert(t.clone()) {
            return;
        }
        let mut deps = Vec::new();
        match t {
            CTy::Adt(a) => p.adt(*a).variants.iter().flat_map(|v| &v.fields).for_each(|f| by_value_deps(&cty(&p.tys, f.ty), &mut deps)),
            CTy::Option(e) => by_value_deps(e, &mut deps),
            _ => {}
        }
        for d in &deps {
            emit(p, d, emitted, out);
        }
        match t {
            CTy::Option(e) => {
                let _ = writeln!(out, "typedef struct {0} {{ uint32_t tag; {1} v; }} {0};", ctype(t), ctype(e));
            }
            CTy::Adt(a) => {
                let adt = p.adt(*a);
                let a = a.0;
                let _ = writeln!(out, "/* {} */", p.name(adt.name));
                let fields = |v: &Variant| -> String {
                    v.fields.iter().enumerate().map(|(i, f)| format!("{} f{i}; ", ctype(&cty(&p.tys, f.ty)))).collect()
                };
                if adt.is_enum {
                    let _ = write!(out, "struct A{a} {{ uint32_t tag; ");
                    if adt.variants.iter().any(|v| !v.fields.is_empty()) {
                        out.push_str("union { ");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            if !v.fields.is_empty() {
                                let _ = write!(out, "struct {{ {}}} v{vi}; ", fields(v));
                            }
                        }
                        out.push_str("} u; ");
                    }
                    out.push_str("};\n");
                } else {
                    let f = fields(&adt.variants[0]);
                    let f = if f.is_empty() { "uint8_t unused; ".to_string() } else { f };
                    let _ = writeln!(out, "struct A{a} {{ {f}}};");
                }
            }
            _ => {}
        }
    }
    let mut emitted = HashSet::new();
    for t in &list {
        emit(p, t, &mut emitted, out);
    }
    out.push('\n');
}

fn glue_def(p: &Program, g: &Glue, t: &CTy, protos: &mut String, defs: &mut String, more: &mut Vec<(Glue, CTy)>) {
    let m = mangle(t);
    let ct = ctype(t);
    let mut need = |g: Glue, t: &CTy| more.push((g, t.clone()));
    let mut body = String::new();
    match g {
        Glue::Drop => {
            let _ = writeln!(protos, "void drop_{m}({ct} *p);");
            match t {
                CTy::String => body.push_str("  lust_string_drop(p);\n"),
                CTy::Vec(e) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < p->len; i++) drop_{}(&(({}*)p->ptr)[i]);", mangle(e), ctype(e));
                    }
                    body.push_str("  free(p->ptr);\n");
                }
                CTy::Option(e) => {
                    need(Glue::Drop, e);
                    let _ = writeln!(body, "  if (p->tag) drop_{}(&p->v);", mangle(e));
                }
                CTy::Adt(a) => {
                    let adt = p.adt(*a);
                    if adt.is_enum {
                        body.push_str("  switch (p->tag) {\n");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            for (fi, f) in v.fields.iter().enumerate() {
                                let ft = cty(&p.tys, f.ty);
                                if needs_drop_c(p, &ft) {
                                    need(Glue::Drop, &ft);
                                    let _ = write!(body, " drop_{}(&p->u.v{vi}.f{fi});", mangle(&ft));
                                }
                            }
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n");
                    } else {
                        for (fi, f) in adt.variants[0].fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            if needs_drop_c(p, &ft) {
                                need(Glue::Drop, &ft);
                                let _ = writeln!(body, "  drop_{}(&p->f{fi});", mangle(&ft));
                            }
                        }
                    }
                }
                _ => {}
            }
            let _ = writeln!(defs, "void drop_{m}({ct} *p) {{\n{body}}}\n");
        }
        Glue::Clone => {
            let _ = writeln!(protos, "{ct} clone_{m}({ct} *p);");
            let clone_of = |t: &CTy, e: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                if is_copy_c(p, t) {
                    e.to_string()
                } else {
                    need(Glue::Clone, t);
                    format!("clone_{}(&{e})", mangle(t))
                }
            };
            match t {
                CTy::String => body.push_str("  return lust_string_clone(p);\n"),
                CTy::Option(e) => {
                    let c = clone_of(e, "p->v", &mut need);
                    let _ = writeln!(body, "  {ct} r = *p;\n  if (p->tag) r.v = {c};\n  return r;");
                }
                CTy::Vec(e) => {
                    let et = ctype(e);
                    let _ = writeln!(body, "  lust_Vec r = lust_vec_with_capacity(p->len, sizeof({et}));");
                    let c = clone_of(e, &format!("(({et}*)p->ptr)[i]"), &mut need);
                    let _ =
                        writeln!(body, "  for (uint64_t i = 0; i < p->len; i++) (({et}*)r.ptr)[i] = {c};\n  r.len = p->len;\n  return r;");
                }
                CTy::Adt(a) => {
                    let adt = p.adt(*a);
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if adt.is_enum {
                        body.push_str("  switch (p->tag) {\n");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            for (fi, f) in v.fields.iter().enumerate() {
                                let ft = cty(&p.tys, f.ty);
                                if !is_copy_c(p, &ft) {
                                    let c = clone_of(&ft, &format!("p->u.v{vi}.f{fi}"), &mut need);
                                    let _ = write!(body, " r.u.v{vi}.f{fi} = {c};");
                                }
                            }
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n");
                    } else {
                        for (fi, f) in adt.variants[0].fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            if !is_copy_c(p, &ft) {
                                let c = clone_of(&ft, &format!("p->f{fi}"), &mut need);
                                let _ = writeln!(body, "  r.f{fi} = {c};");
                            }
                        }
                    }
                    body.push_str("  return r;\n");
                }
                _ => body.push_str("  return *p;\n"),
            }
            let _ = writeln!(defs, "{ct} clone_{m}({ct} *p) {{\n{body}}}\n");
        }
        Glue::Eq => {
            let _ = writeln!(protos, "uint8_t eq_{m}({ct} *a, {ct} *b);");
            let eq_of = |t: &CTy, x: &str, y: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                match t {
                    CTy::Unit => "1".into(),
                    CTy::Bool | CTy::Char | CTy::Int(_) => format!("({x} == {y})"),
                    _ => {
                        need(Glue::Eq, t);
                        format!("eq_{}(&{x}, &{y})", mangle(t))
                    }
                }
            };
            match t {
                CTy::String => body.push_str("  return lust_str_eq(lust_string_as_str(a), lust_string_as_str(b));\n"),
                CTy::Ref(inner) if **inner == CTy::Str => body.push_str("  return lust_str_eq(*a, *b);\n"),
                CTy::Option(e) => {
                    let c = eq_of(e, "a->v", "b->v", &mut need);
                    let _ = writeln!(body, "  return a->tag == b->tag && (!a->tag || {c});");
                }
                CTy::Ref(inner) => {
                    let e = eq_of(inner, "(**a)", "(**b)", &mut need);
                    let _ = writeln!(body, "  return {e};");
                }
                CTy::Vec(e) => {
                    let et = ctype(e);
                    let c = eq_of(e, &format!("(({et}*)a->ptr)[i]"), &format!("(({et}*)b->ptr)[i]"), &mut need);
                    let _ = writeln!(
                        body,
                        "  if (a->len != b->len) return 0;\n  for (uint64_t i = 0; i < a->len; i++) if (!{c}) return 0;\n  return 1;"
                    );
                }
                CTy::Adt(a) => {
                    let adt = p.adt(*a);
                    if adt.is_enum {
                        body.push_str("  if (a->tag != b->tag) return 0;\n  switch (a->tag) {\n");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let _ = write!(body, "  case {vi}:");
                            for (fi, f) in v.fields.iter().enumerate() {
                                let ft = cty(&p.tys, f.ty);
                                let c = eq_of(&ft, &format!("a->u.v{vi}.f{fi}"), &format!("b->u.v{vi}.f{fi}"), &mut need);
                                let _ = write!(body, " if (!{c}) return 0;");
                            }
                            body.push_str(" break;\n");
                        }
                        body.push_str("  }\n  return 1;\n");
                    } else {
                        for (fi, f) in adt.variants[0].fields.iter().enumerate() {
                            let ft = cty(&p.tys, f.ty);
                            let c = eq_of(&ft, &format!("a->f{fi}"), &format!("b->f{fi}"), &mut need);
                            let _ = writeln!(body, "  if (!{c}) return 0;");
                        }
                        body.push_str("  return 1;\n");
                    }
                }
                _ => body.push_str("  return *a == *b;\n"),
            }
            let _ = writeln!(defs, "uint8_t eq_{m}({ct} *a, {ct} *b) {{\n{body}}}\n");
        }
        Glue::Debug => {
            let _ = writeln!(protos, "void dbg_{m}(lust_String *out, {ct} *p);");
            let dbg_of = |t: &CTy, e: &str, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                match t {
                    CTy::Int(i) if i.signed() => format!("lust_fmt_i64(out, (int64_t){e});"),
                    CTy::Int(_) => format!("lust_fmt_u64(out, (uint64_t){e});"),
                    CTy::Bool => format!("lust_fmt_bool(out, {e});"),
                    CTy::Char => format!("lust_fmt_char_debug(out, {e});"),
                    CTy::String => format!("lust_fmt_str_debug(out, lust_string_as_str(&{e}));"),
                    CTy::Ref(inner) if **inner == CTy::Str => format!("lust_fmt_str_debug(out, {e});"),
                    CTy::Unit => "lust_string_push_bytes(out, \"()\", 2);".into(),
                    _ => {
                        need(Glue::Debug, t);
                        format!("dbg_{}(out, &{e});", mangle(t))
                    }
                }
            };
            let lit = |s: &str| format!("lust_string_push_bytes(out, {}, {});", c_string_lit(s.as_bytes()), s.len());
            match t {
                CTy::Option(inner) => {
                    let e = dbg_of(inner, "p->v", &mut need);
                    let _ = writeln!(body, "  if (p->tag) {{ {} {e} {} }} else {}", lit("Some("), lit(")"), lit("None"));
                }
                CTy::Ref(inner) => {
                    let e = dbg_of(inner, "(**p)", &mut need);
                    let _ = writeln!(body, "  {e}");
                }
                CTy::Vec(e) => {
                    let et = ctype(e);
                    let d = dbg_of(e, &format!("(({et}*)p->ptr)[i]"), &mut need);
                    let _ = writeln!(
                        body,
                        "  {}\n  for (uint64_t i = 0; i < p->len; i++) {{ if (i) {} {d} }}\n  {}",
                        lit("["),
                        lit(", "),
                        lit("]")
                    );
                }
                CTy::Adt(a) => {
                    let adt = p.adt(*a);
                    let variant_body = |v: &Variant, access: &dyn Fn(usize) -> String, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                        let mut s = lit(p.name(v.name));
                        match v.shape {
                            VariantShape::Unit => {}
                            VariantShape::Tuple => {
                                s.push_str(&lit("("));
                                for (fi, f) in v.fields.iter().enumerate() {
                                    if fi > 0 {
                                        s.push_str(&lit(", "));
                                    }
                                    s.push_str(&dbg_of(&cty(&p.tys, f.ty), &access(fi), need));
                                }
                                s.push_str(&lit(")"));
                            }
                            VariantShape::Named => {
                                if !v.fields.is_empty() {
                                    for (fi, f) in v.fields.iter().enumerate() {
                                        let sep = if fi == 0 { " { " } else { ", " };
                                        s.push_str(&lit(&format!("{sep}{}: ", p.name(f.name))));
                                        s.push_str(&dbg_of(&cty(&p.tys, f.ty), &access(fi), need));
                                    }
                                    s.push_str(&lit(" }"));
                                }
                            }
                        }
                        s
                    };
                    if adt.is_enum {
                        body.push_str("  switch (p->tag) {\n");
                        for (vi, v) in adt.variants.iter().enumerate() {
                            let b = variant_body(v, &|fi| format!("p->u.v{vi}.f{fi}"), &mut need);
                            let _ = writeln!(body, "  case {vi}: {b} break;");
                        }
                        body.push_str("  }\n");
                    } else {
                        let b = variant_body(&adt.variants[0], &|fi| format!("p->f{fi}"), &mut need);
                        let _ = writeln!(body, "  {b}");
                    }
                }
                _ => {
                    let e = dbg_of(t, "(*p)", &mut need);
                    let _ = writeln!(body, "  {e}");
                }
            }
            let _ = writeln!(defs, "void dbg_{m}(lust_String *out, {ct} *p) {{\n{body}}}\n");
        }
    }
}

fn rvalue_mentions(rv: &Rvalue, l: Local) -> bool {
    let place_has = |p: &Place| p.local == l || p.proj.iter().any(|x| matches!(x, Proj::Index(i) if *i == l));
    let op_has = |o: &Operand| matches!(o, Operand::Copy(p) | Operand::Move(p) if place_has(p));
    let parts_has = |ps: &[FmtPart]| ps.iter().any(|p| matches!(p, FmtPart::Arg { value, .. } if op_has(value)));
    match rv {
        Rvalue::Use(o) | Rvalue::Un(_, o) | Rvalue::Cast(o, _) => op_has(o),
        Rvalue::Ref(_, p) | Rvalue::Discriminant(p) => place_has(p),
        Rvalue::Bin(_, a, b) | Rvalue::StrCmp(_, a, b) | Rvalue::StringAdd(a, b) | Rvalue::VecRepeat(_, a, b) | Rvalue::Eq { a, b, .. } => {
            op_has(a) || op_has(b)
        }
        Rvalue::Aggregate(_, _, ops) | Rvalue::VecLit(_, ops) | Rvalue::Call(_, ops) | Rvalue::Builtin(_, ops) => ops.iter().any(op_has),
        Rvalue::Opt(_, o) => o.as_ref().is_some_and(op_has),
        Rvalue::Format(parts) => parts_has(parts),
    }
}

fn succ(t: &Terminator) -> Vec<Bb> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::If(_, a, b) => vec![*a, *b],
        Terminator::Switch(_, cases, other) => cases.iter().map(|c| c.1).chain(std::iter::once(*other)).collect(),
        _ => Vec::new(),
    }
}
