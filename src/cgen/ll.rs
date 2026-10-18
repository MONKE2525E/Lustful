// LLVM IR backend for release builds (`LUST_RELEASE_BACKEND=llvm` with `LUST_RELEASE_C=1`).
//
// Each fn body becomes one LLVM IR fn `fl_<id>` in its unit's `.ll` text, next to the
// unit's C. The LLVM fn owns the frame: an alloca per local and per drop or move flag,
// the control flow (blocks, branches, switches, returns) and the unwinding: a call or a
// statement with a cleanup entry is an `invoke`, its landing pad keeps the exception and
// runs the cleanup blocks, and the end of a cleanup ladder is `resume`. There is no frame
// struct and no ladder state store (the C backend's unwind tables scheme, cgen/unwind.rs).
// The runtime's C++ throw and catch (runtime/unwind.cc) stay as they are.
//
// A statement whose form has no native lowering runs as a small C helper `lh_<id>_<n>`
// cut from cgen's own C for that statement (`FnGen::stmt`, `FnGen::term`): it takes
// pointers to the locals and flags its text names, so the C and the LLVM code share one
// frame. A unit compiles as one module (cc.rs links the C module's bitcode into the LLVM
// module before -O2), so the helpers inline (always_inline) and SROA promotes the frame
// as for native code.
//
// ABI: `fl_<id>` takes scalars (ints, floats, thin pointers) by value and every other
// value by pointer to a copy the callee owns; an aggregate result goes through a leading
// sret pointer. C callers (glue, vtable shims, trampolines, helpers) keep calling
// `f_<id>` with the C signature: a C wrapper in the unit forwards to `fl_<id>`.
use super::unwind::{is_ident, skip_lit};
use super::*;

/// True when this thread emits LLVM IR for release C fn bodies: release C names, the
/// `LUST_RELEASE_BACKEND=llvm` switch, and a program whose panics abort or unwind with
/// tables (the flag scheme stays C).
pub(crate) fn on(p: &Program) -> bool {
    static ENV: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    let env = *ENV.get_or_init(|| std::env::var("LUST_RELEASE_BACKEND").is_ok_and(|v| v == "llvm"));
    env && names::release() && (!p.unwind || p.unwind_tables)
}

/// How the internal ABI passes a C value: not at all (zero-sized), in a register as the
/// given LLVM type with its extension attribute, as the bits of a small aggregate in one
/// integer register (`Bits(bytes)`: a newtype id, a small `Option`; rustc passes these as
/// integers too), or by pointer to memory.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Pass {
    Skip,
    Scalar(&'static str, &'static str),
    Bits(u64),
    /// A 16-byte aggregate (a `&str`, a slice, `Option<u64>`) as two 8-byte words.
    Pair,
    Mem,
}

/// The C type of a `Pass::Pair` result: clang returns it in two registers, as `{ i64, i64 }`.
pub(crate) const PAIR_TYPEDEF: &str = "typedef struct { uint64_t a, b; } ll_pair;\n";

/// The LLVM and C integer types of a `Pass::Bits` value of `n` bytes.
fn bits_types(n: u64) -> (&'static str, &'static str) {
    match n {
        1 => ("i8", "uint8_t"),
        2 => ("i16", "uint16_t"),
        4 => ("i32", "uint32_t"),
        _ => ("i64", "uint64_t"),
    }
}

pub(super) fn pass_of(p: &Program, t: &CTy) -> Pass {
    if c_size_align(p, t).0 == 0 {
        return Pass::Skip;
    }
    let c = ctype(t);
    if c.ends_with('*') || c.starts_with("Fp_") {
        return Pass::Scalar("ptr", "");
    }
    match c.as_str() {
        "uint8_t" => Pass::Scalar("i8", "zeroext"),
        "int8_t" => Pass::Scalar("i8", "signext"),
        "uint16_t" => Pass::Scalar("i16", "zeroext"),
        "int16_t" => Pass::Scalar("i16", "signext"),
        "uint32_t" | "int32_t" => Pass::Scalar("i32", ""),
        "uint64_t" | "int64_t" => Pass::Scalar("i64", ""),
        "double" => Pass::Scalar("double", ""),
        "float" => Pass::Scalar("float", ""),
        // An aggregate of exactly 1, 2, 4 or 8 bytes (exact layout) travels as its bits.
        _ => match c_layout(p, t) {
            Some(l) if matches!(l.size, 1 | 2 | 4 | 8) && bits_on() => Pass::Bits(l.size),
            Some(l) if l.size == 16 && bits_on() && pair_on() => Pass::Pair,
            _ => Pass::Mem,
        },
    }
}

/// True unless `LUST_LL_PAIR=0` (16-byte aggregates by pointer, to measure `Pass::Pair`).
fn pair_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("LUST_LL_PAIR").map_or(true, |v| v != "0"))
}

/// True unless `LUST_LL_BITS=0` (small aggregates by pointer, to measure `Pass::Bits`).
fn bits_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("LUST_LL_BITS").map_or(true, |v| v != "0"))
}

/// True unless `LUST_LL_FACTS=0`: the LLVM fns carry the facts Rust gives references
/// (`ref_facts`). The switch exists to measure their payoff.
fn facts_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("LUST_LL_FACTS").map_or(true, |v| v != "0"))
}

/// The LLVM attributes Rust's rules give a thin pointer of semantic type `ty` passed or
/// returned by value, as rustc emits them: a reference or `Box` is non-null, aligned and
/// dereferenceable for its pointee's size (when its layout is exact); `&mut T`, `Box<T>`
/// and `&T` of a type without interior mutability are `noalias` (a parameter only), and
/// such a `&T` is `readonly`.
fn ref_facts(p: &Program, tys: &Tys, ty: Ty, param: bool) -> String {
    if !facts_on() {
        return String::new();
    }
    let (pointee, unique, shared) = match tys.kind(ty) {
        TyKind::Ref(_, m, e) => (e, m == Mut::Mut, m == Mut::Shared),
        TyKind::Adt(..) if tys.builtin_of(ty) == Some(BuiltinTy::Boxed) => match tys.adt_first_ty_arg(ty) {
            Some(e) => (e, true, false),
            None => return String::new(),
        },
        _ => return String::new(),
    };
    let pc = cty(tys, pointee);
    let Some(l) = c_layout(p, &pc) else { return String::new() };
    let mut a = format!("nonnull align {}", l.align.max(1));
    if l.size > 0 {
        let _ = write!(a, " dereferenceable({})", l.size);
    }
    // Freeze as rustc asks it: no `UnsafeCell` inline (the semantic check knows std's
    // cell, once and lazy models; the C form knows the sync types). A `LocalKey` is a
    // slot word the runtime may fill in place.
    let freeze = shared
        && !crate::check::collect::interior_mut(p, tys, pointee)
        && is_freeze_c(p, &pc, &mut HashSet::new())
        && tys.builtin_of(pointee) != Some(BuiltinTy::LocalKey);
    if param && (unique || freeze) {
        a.push_str(" noalias");
    }
    if param && freeze {
        a.push_str(" readonly");
    }
    a
}

/// True unless `LUST_LL_NATIVE=0`: simple statements lower to LLVM IR directly instead of
/// C helpers (`FnGen::ll_native_stmt`).
fn native_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("LUST_LL_NATIVE").map_or(true, |v| v != "0"))
}

/// One step from a place's base to its address (`FnGen::ll_plan`).
#[derive(Clone, Debug)]
enum PStep {
    /// Load the thin pointer stored here (a reference or `Box`) to a value of this C type.
    Load(CTy),
    /// Move this many bytes into the value; the C member path, for the layout check.
    Offset(u64, String),
}

/// A place lowered natively: its local, the steps, and the C type at the end.
struct Plan {
    local: usize,
    steps: Vec<PStep>,
    ty: CTy,
}

/// A name of the fn's frame that a statement's C reads.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Name {
    Local(usize),
    Drop(usize),
    Move(usize, usize),
    Ltc,
    Ex,
}

/// One fn's LLVM side: its definition, the declarations it names, and its helpers' C
/// (cc.rs links that module internalized, so the helpers vanish once inlined).
#[derive(Default)]
pub struct LlFn {
    pub def: String,
    pub decls: BTreeSet<String>,
    pub helpers: String,
    /// The fn's size for cross-unit inlining (`ll_inline_set`): statements and blocks of its
    /// body outside cleanup, whatever form they take in IR.
    pub cost: u32,
}

/// The per-fn state of LLVM emission.
struct Ll {
    tag: String,
    /// Helper definitions (C), in order.
    helpers: String,
    n_helpers: usize,
    /// Locals with static storage (promoted constants, byte string temps): C file statics.
    statics: Vec<bool>,
    /// The cleanup blocks each landing pad enters.
    pads: BTreeSet<u32>,
    decls: BTreeSet<String>,
    body: String,
    /// The number of continuation blocks made so far.
    conts: usize,
    /// An internal error (an unsupported C form in a helper): the driver reports it.
    error: Option<String>,
    /// `_Static_assert`s of the field offsets native code uses, for the helper C.
    asserts: BTreeSet<String>,
    /// Temporaries native code needs (call arguments and results), as entry-block allocas.
    allocas: String,
    /// Per block: the locals whose drop flag may be set at its terminator (`flags_maybe_set`).
    flags_at_term: Vec<Vec<bool>>,
}

impl FnGen<'_, '_> {
    /// The frame names `text` reads (sorted, deduplicated): locals, their drop and move
    /// flags, the caller location `ltc`, the exception slot `ex`.
    fn frame_names(&self, text: &str) -> Vec<Name> {
        let n = self.local_cty.len();
        let b = text.as_bytes();
        let mut out = BTreeSet::new();
        let mut i = 0;
        while i < b.len() {
            match b[i] {
                b'"' | b'\'' => i = skip_lit(b, i),
                c if is_ident(c) && (i == 0 || !is_ident(b[i - 1])) => {
                    let start = i;
                    while i < b.len() && is_ident(b[i]) {
                        i += 1;
                    }
                    // A member (`x.l3`, `p->d1`) is not a frame name.
                    let member = start > 0 && (b[start - 1] == b'.' || (start > 1 && &b[start - 2..start] == b"->"));
                    if member {
                        continue;
                    }
                    let w = &text[start..i];
                    // A cgen number: digits with no leading zero, under `bound`.
                    let num = |s: &str, bound: usize| {
                        let ok = !s.is_empty() && s.bytes().all(|c| c.is_ascii_digit()) && (s == "0" || !s.starts_with('0'));
                        if ok { s.parse::<usize>().ok().filter(|&k| k < bound) } else { None }
                    };
                    let name = match w.as_bytes()[0] {
                        _ if w == "ltc" => Some(Name::Ltc),
                        _ if w == "ex" => Some(Name::Ex),
                        b'l' => num(&w[1..], n).map(Name::Local),
                        b'd' => num(&w[1..], n).filter(|&k| self.local_drop[k]).map(Name::Drop),
                        b'm' => w[1..].split_once('_').and_then(|(a, k)| {
                            let l = num(a, n)?;
                            Some(Name::Move(l, num(k, self.move_paths[l].len())?))
                        }),
                        _ => None,
                    };
                    if let Some(nm) = name {
                        out.insert(nm);
                    }
                }
                c if c.is_ascii_digit() => {
                    while i < b.len() && is_ident(b[i]) {
                        i += 1;
                    }
                }
                _ => i += 1,
            }
        }
        out.into_iter().collect()
    }

    /// Makes a C helper of statement text `text` (and, with `ret`, a value: its C type and
    /// expression, returned after the text) and returns the LLVM call operands: the
    /// callee name, its LLVM return type with its extension, and the argument list.
    fn ll_helper(&self, ll: &mut Ll, text: &str, ret: Option<(&str, &str, Pass)>) -> (String, String, String) {
        let names = self.frame_names(&format!("{text}{}", ret.map_or("", |r| r.1)));
        if contains_word(text, "return") || text.contains("goto bb") {
            ll.error.get_or_insert_with(|| {
                format!(
                    "internal: LLVM backend: a statement of `{}` jumps out of its C ({}), which a helper cannot hold",
                    self.p.display_path(self.p.fn_info(self.body.fn_id).name),
                    text.trim().chars().take(120).collect::<String>()
                )
            });
        }
        let name = format!("lh_{}_{}", ll.tag, ll.n_helpers);
        ll.n_helpers += 1;
        let mut params = Vec::new();
        let mut args = Vec::new();
        let mut ex = false;
        for nm in &names {
            match *nm {
                Name::Local(l) if ll.statics[l] => {}
                Name::Local(l) => {
                    params.push(format!("{} *q{l}", ctype(&self.local_cty[l])));
                    args.push(format!("ptr %l{l}"));
                }
                Name::Drop(l) => {
                    params.push(format!("uint8_t *qd{l}"));
                    args.push(format!("ptr %d{l}"));
                }
                Name::Move(l, k) => {
                    params.push(format!("uint8_t *qm{l}_{k}"));
                    args.push(format!("ptr %m{l}_{k}"));
                }
                Name::Ltc => {
                    params.push("lust_loc *qltc".to_string());
                    args.push("ptr %ltc".to_string());
                }
                Name::Ex => ex = true,
            }
        }
        let (cret, llret) = match ret {
            Some((ct, _, Pass::Scalar(t, ext))) => (ct.to_string(), if ext.is_empty() { t.to_string() } else { format!("{ext} {t}") }),
            _ => ("void".to_string(), "void".to_string()),
        };
        let plist = if params.is_empty() { "void".to_string() } else { params.join(", ") };
        let _ = writeln!(ll.helpers, "__attribute__((visibility(\"hidden\"), always_inline)) {cret} {name}({plist}) {{");
        if ex {
            ll.helpers.push_str("  lust_exc ex; (void)ex;\n");
        }
        ll.helpers.push_str(text);
        if let Some((_, e, _)) = ret {
            let _ = writeln!(ll.helpers, "  return ({e});");
        }
        ll.helpers.push_str("}\n");
        let decl_params: Vec<&str> = args.iter().map(|_| "ptr").collect();
        ll.decls.insert(format!("declare {llret} @{name}({})", decl_params.join(", ")));
        (name, llret, args.join(", "))
    }

    /// Emits a call of a helper (`invoke` when `unwind` names a cleanup entry), and returns
    /// the value name when it has one.
    fn ll_call(&self, ll: &mut Ll, callee: &(String, String, String), unwind: Option<u32>) -> Option<String> {
        let (name, ret, args) = callee;
        let v = if ret == "void" {
            None
        } else {
            ll.conts += 1;
            Some(format!("%v{}", ll.conts))
        };
        let assign = v.as_ref().map_or(String::new(), |v| format!("{v} = "));
        match unwind {
            Some(u) => {
                ll.conts += 1;
                let cont = format!("c{}", ll.conts);
                ll.pads.insert(u);
                let _ = writeln!(ll.body, "  {assign}invoke {ret} @{name}({args}) to label %{cont} unwind label %lp{u}\n{cont}:");
            }
            None => {
                let _ = writeln!(ll.body, "  {assign}call {ret} @{name}({args})");
            }
        }
        v
    }

    /// The C of statement `s` (block `bi`, index `si`) as cgen writes it for a fn with no
    /// frame struct.
    fn stmt_text(&mut self, bi: usize, si: usize, s: &Stmt) -> String {
        self.unw = self.stmt_action(bi, si).filter(|_| !matches!(s.kind, StmtKind::StorageDead(_) | StmtKind::FakeRead(_)));
        let saved = std::mem::take(&mut self.out);
        self.stmt(&s.kind, s.span);
        self.unw = None;
        std::mem::replace(&mut self.out, saved)
    }

    /// An operand as an LLVM value of its scalar type: a plain local's load or a
    /// constant, else a helper that computes it.
    fn ll_operand(&mut self, ll: &mut Ll, o: &Operand, span: Span) -> (String, Pass) {
        if native_on()
            && let Some((t, _)) = self.ll_scalar_ok(ll, o)
        {
            let pass = pass_of(self.p, &t);
            return (self.ll_scalar(ll, o), pass);
        }
        match o {
            Operand::Copy(pl) | Operand::Move(pl) if pl.proj.is_empty() && !ll.statics[pl.local as usize] => {
                let l = pl.local as usize;
                let pass = pass_of(self.p, &self.local_cty[l]);
                if let Pass::Scalar(t, _) = pass {
                    ll.conts += 1;
                    let v = format!("%v{}", ll.conts);
                    let _ = writeln!(ll.body, "  {v} = load {t}, ptr %l{l}");
                    return (v, pass);
                }
            }
            Operand::Const(Const::Bool(b)) => return ((*b as u8).to_string(), Pass::Scalar("i8", "zeroext")),
            _ => {}
        }
        let loc = self.loc(span);
        let mut post = Vec::new();
        let saved = std::mem::take(&mut self.out);
        let (e, t) = self.operand(o, &loc, &mut post);
        let pre = std::mem::replace(&mut self.out, saved);
        let pass = pass_of(self.p, &t);
        let ct = ctype(&t);
        let h = self.ll_helper(ll, &pre, Some((&ct, &e, pass)));
        (self.ll_call(ll, &h, None).unwrap_or_else(|| "0".into()), pass)
    }

    /// Generates fn `fl_<id>` and its C side (helpers, the C ABI wrapper `f_<id>`, the
    /// trampoline) into `self.out`. Returns the LLVM definition and declarations, or an
    /// internal error.
    pub(super) fn function_ll(&mut self) -> Result<LlFn, String> {
        let p = self.p;
        let fid = self.body.fn_id;
        let slot = self.slots.of(fid);
        let tag = names::fn_tag(slot);
        let n = self.body.blocks.len();
        let mut reachable = vec![false; n];
        let mut stack = vec![0usize];
        while let Some(b) = stack.pop() {
            if std::mem::replace(&mut reachable[b], true) {
                continue;
            }
            stack.extend(succ(&self.body.blocks[b].term).into_iter().map(|s| s.0 as usize));
            stack.extend(self.body.stmt_unwind.iter().filter(|e| e.0.0 as usize == b).map(|e| e.2.0 as usize));
        }
        let order: Vec<usize> = (0..n).filter(|&b| reachable[b]).collect();
        let cost = order
            .iter()
            .filter(|&&b| !self.cleanup.get(b).copied().unwrap_or(false))
            .map(|&b| 1 + self.body.blocks[b].stmts.iter().filter(|s| !matches!(s.kind, StmtKind::StorageDead(_) | StmtKind::FakeRead(_))).count() as u32)
            .sum();
        let nl = self.local_cty.len();
        let statics: Vec<bool> = (0..nl)
            .map(|i| self.body.promoted.contains(&(i as Local)) || self.byte_blobs.get(i).is_some_and(|b| b.is_some()))
            .collect();
        let mut ll = Ll {
            tag: tag.clone(),
            helpers: String::new(),
            n_helpers: 0,
            statics,
            pads: BTreeSet::new(),
            decls: BTreeSet::new(),
            body: String::new(),
            conts: 0,
            error: None,
            asserts: BTreeSet::new(),
            allocas: String::new(),
            flags_at_term: self.flags_maybe_set(),
        };
        // Str literal caches (`kstr`) are on: the slots and their interning go in a prologue
        // helper below.
        self.kdecl_at = Some(0);
        for &bi in &order {
            let block = self.body.block(Bb(bi as u32));
            let cleanup = self.cleanup.get(bi).copied().unwrap_or(false);
            let _ = writeln!(ll.body, "bb{bi}:");
            for (si, s) in block.stmts.iter().enumerate() {
                if matches!(s.kind, StmtKind::StorageDead(_) | StmtKind::FakeRead(_)) {
                    continue;
                }
                let unwind = if cleanup || !p.unwind { None } else { self.stmt_unw.get(&(bi as u32, si as u32)).copied() };
                if native_on() && self.ll_native_stmt(&mut ll, s, unwind) {
                    continue;
                }
                let text = self.stmt_text(bi, si, s);
                if text.trim().is_empty() {
                    continue;
                }
                let h = self.ll_helper(&mut ll, &text, None);
                self.ll_call(&mut ll, &h, unwind);
            }
            let term_unwind = if cleanup { None } else { self.stmt_unw.get(&(bi as u32, block.stmts.len() as u32)).copied() };
            self.ll_term(&mut ll, bi, cleanup, term_unwind.filter(|_| p.unwind));
        }
        if let Some(e) = ll.error.take() {
            return Err(e);
        }
        // The landing pads: keep the exception, enter the cleanup block.
        for &u in &ll.pads {
            let _ = writeln!(
                ll.body,
                "lp{u}:\n  %lpv{u} = landingpad {{ ptr, i32 }} cleanup\n  store {{ ptr, i32 }} %lpv{u}, ptr %exn\n  br label %bb{u}"
            );
        }
        let kstr_init = self.ll_kstr_init(&mut ll);
        let def = self.ll_define(&mut ll, kstr_init.as_deref());
        // The C sides: the helpers with the macros and statics they read; then the C ABI
        // wrapper and the trampoline, which stay in the unit's plain C.
        let saved = std::mem::take(&mut self.out);
        self.ll_c_side(&ll, kstr_init.as_deref());
        let helpers = std::mem::replace(&mut self.out, saved);
        let wrapper = self.ll_wrapper(slot);
        let _ = writeln!(self.out, "/* {} */\n{wrapper}{}", p.display_path(p.fn_info(fid).name), trampoline(p, fid, slot));
        ll.decls.insert("declare i32 @__gcc_personality_v0(...)".into());
        // The inline cost on a comment line above the fn, for reading the IR.
        let def = format!("; cost {cost}\n{def}");
        Ok(LlFn { def, decls: std::mem::take(&mut ll.decls), helpers, cost })
    }

    /// The terminator of block `bi`.
    fn ll_term(&mut self, ll: &mut Ll, bi: usize, cleanup: bool, unwind: Option<u32>) {
        let block = self.body.block(Bb(bi as u32));
        let span = block.term_span;
        match &block.term {
            Terminator::Goto(t) => {
                let _ = writeln!(ll.body, "  br label %bb{}", t.0);
            }
            Terminator::If(o, a, b) => {
                let (v, pass) = self.ll_operand(ll, o, span);
                let t = match pass {
                    Pass::Scalar(t, _) => t,
                    _ => "i8",
                };
                ll.conts += 1;
                let c = format!("%v{}", ll.conts);
                let _ = writeln!(ll.body, "  {c} = icmp ne {t} {v}, 0\n  br i1 {c}, label %bb{}, label %bb{}", a.0, b.0);
            }
            Terminator::Switch(o, cases, other) => {
                let (v, pass) = self.ll_operand(ll, o, span);
                let t = match pass {
                    Pass::Scalar(t, _) => t,
                    _ => "i32",
                };
                let _ = write!(ll.body, "  switch {t} {v}, label %bb{} [", other.0);
                for (val, b) in cases {
                    let _ = write!(ll.body, " {t} {val}, label %bb{}", b.0);
                }
                ll.body.push_str(" ]\n");
            }
            Terminator::Call { target: CallTarget::Fn(f), args, dest, next, unwind: call_unwind }
                if native_on() && {
                    let dest_clear = !ll.flags_at_term[bi][dest.local as usize];
                    self.ll_native_call(ll, *f, args, dest, dest_clear, if cleanup || !self.p.unwind { None } else { call_unwind.map(|u| u.0) })
                } =>
            {
                let _ = writeln!(ll.body, "  br label %bb{}", next.0);
            }
            Terminator::Call { next, unwind: call_unwind, .. } => {
                self.unw = self.stmt_action(bi, block.stmts.len());
                let saved = std::mem::take(&mut self.out);
                let term = block.term.clone();
                self.term(&term, span, Some(next.0 as usize));
                self.unw = None;
                let text = std::mem::replace(&mut self.out, saved);
                let h = self.ll_helper(ll, &text, None);
                let u = if cleanup || !self.p.unwind { None } else { call_unwind.map(|u| u.0) };
                self.ll_call(ll, &h, u);
                let _ = writeln!(ll.body, "  br label %bb{}", next.0);
            }
            Terminator::Return => match pass_of(self.p, &self.local_cty[0]) {
                Pass::Scalar(t, _) => {
                    ll.conts += 1;
                    let _ = writeln!(ll.body, "  %v{0} = load {t}, ptr %l0\n  ret {t} %v{0}", ll.conts);
                }
                Pass::Bits(n) => {
                    ll.conts += 1;
                    let t = bits_types(n).0;
                    let _ = writeln!(ll.body, "  %v{0} = load {t}, ptr %l0, align {n}\n  ret {t} %v{0}", ll.conts);
                }
                Pass::Pair => {
                    ll.conts += 1;
                    let _ = writeln!(
                        ll.body,
                        "  %pa{0} = load i64, ptr %l0, align 8\n  %pq{0} = getelementptr inbounds i8, ptr %l0, i64 8\n  %pb{0} = load i64, ptr %pq{0}, align 8\n  %pv{0} = insertvalue {{ i64, i64 }} poison, i64 %pa{0}, 0\n  %pw{0} = insertvalue {{ i64, i64 }} %pv{0}, i64 %pb{0}, 1\n  ret {{ i64, i64 }} %pw{0}",
                        ll.conts
                    );
                }
                _ => ll.body.push_str("  ret void\n"),
            },
            Terminator::Unreachable if cleanup && self.p.unwind => {
                ll.conts += 1;
                let _ = writeln!(ll.body, "  %v{0} = load {{ ptr, i32 }}, ptr %exn\n  resume {{ ptr, i32 }} %v{0}", ll.conts);
            }
            Terminator::Unreachable => {
                ll.decls.insert("declare void @abort() noreturn nounwind".into());
                ll.body.push_str("  call void @abort()\n  unreachable\n");
            }
            Terminator::Panic(_) => {
                self.unw = self.stmt_action(bi, block.stmts.len());
                let saved = std::mem::take(&mut self.out);
                let term = block.term.clone();
                self.term(&term, span, None);
                self.unw = None;
                let text = std::mem::replace(&mut self.out, saved);
                let h = self.ll_helper(ll, &text, None);
                self.ll_call(ll, &h, unwind);
                ll.body.push_str("  unreachable\n");
            }
        }
    }

    /// The prologue helper that interns the fn's str literals (`kstr`), if it has any.
    fn ll_kstr_init(&mut self, ll: &mut Ll) -> Option<String> {
        self.kdecl_at = None;
        if self.kstrs.is_empty() {
            return None;
        }
        let mut lits: Vec<(&Vec<u8>, &usize)> = self.kstrs.iter().collect();
        lits.sort_by_key(|(_, id)| **id);
        let name = format!("lh_{}_k", ll.tag);
        let mut text = format!("__attribute__((visibility(\"hidden\"), always_inline)) void {name}(void) {{\n  if (!lks_ok) {{\n");
        for (b, id) in lits {
            let _ = writeln!(text, "    lust_kintern(&lks[{id}], {}, {}, 1, 0);", c_string_lit(b), b.len());
        }
        text.push_str("    lks_ok = 1;\n  }\n}\n");
        ll.helpers.push_str(&text);
        ll.decls.insert(format!("declare void @{name}()"));
        Some(name)
    }

    /// The LLVM definition of `fl_<id>`.
    fn ll_define(&mut self, ll: &mut Ll, kstr_init: Option<&str>) -> String {
        let p = self.p;
        let fid = self.body.fn_id;
        let info = p.fn_info(fid);
        let mut params: Vec<String> = Vec::new();
        let mut entry = String::new();
        let mut is_param = vec![false; self.local_cty.len()];
        let ret_pass = pass_of(p, &self.local_cty[0]);
        let (ret_size, ret_align) = c_size_align(p, &self.local_cty[0]);
        let ret_ll = match ret_pass {
            Pass::Scalar("ptr", _) => {
                let facts = ref_facts(p, &self.body.tys, self.body.locals[0].ty, false);
                if facts.is_empty() { "ptr".to_string() } else { format!("{facts} ptr") }
            }
            Pass::Scalar(t, ext) => {
                if ext.is_empty() {
                    t.to_string()
                } else {
                    format!("{ext} {t}")
                }
            }
            Pass::Bits(n) => bits_types(n).0.to_string(),
            Pass::Pair => "{ i64, i64 }".to_string(),
            Pass::Mem => {
                // No `sret`: C callers declare this pointer plainly (`ll_proto`).
                params.push(format!("ptr noalias nocapture noundef nonnull align {ret_align} dereferenceable({ret_size}) %l0"));
                is_param[0] = true;
                "void".to_string()
            }
            Pass::Skip => "void".to_string(),
        };
        for i in 1..=self.body.arg_count.min(self.local_cty.len() - 1) {
            let t = &self.local_cty[i];
            let (size, align) = c_size_align(p, t);
            match pass_of(p, t) {
                Pass::Skip => {}
                Pass::Scalar(ty, ext) => {
                    let mut ext = if ext.is_empty() { String::new() } else { format!("{ext} ") };
                    if ty == "ptr" {
                        let facts = ref_facts(p, &self.body.tys, self.body.locals[i].ty, true);
                        if !facts.is_empty() {
                            ext = format!("{facts} ");
                        }
                    }
                    params.push(format!("{ty} {ext}noundef %p{i}"));
                    let _ = writeln!(entry, "  %l{i} = alloca {ty}, align {align}\n  store {ty} %p{i}, ptr %l{i}");
                    is_param[i] = true;
                }
                // No `noundef`: an aggregate's bits may hold padding or an inactive variant's
                // bytes (an `Ok(())` leaves its error word unwritten).
                Pass::Bits(n) => {
                    let ty = bits_types(n).0;
                    params.push(format!("{ty} %p{i}"));
                    let _ = writeln!(entry, "  %l{i} = alloca [{size} x i8], align {}\n  store {ty} %p{i}, ptr %l{i}, align {n}", align.max(n));
                    is_param[i] = true;
                }
                Pass::Pair => {
                    params.push(format!("i64 %p{i}a, i64 %p{i}b"));
                    let _ = writeln!(
                        entry,
                        "  %l{i} = alloca [16 x i8], align {}\n  store i64 %p{i}a, ptr %l{i}, align 8\n  %l{i}h = getelementptr inbounds i8, ptr %l{i}, i64 8\n  store i64 %p{i}b, ptr %l{i}h, align 8",
                        align.max(8)
                    );
                    is_param[i] = true;
                }
                Pass::Mem => {
                    params.push(format!("ptr noalias nocapture noundef nonnull align {align} dereferenceable({size}) %l{i}"));
                    is_param[i] = true;
                }
            }
        }
        if crate::check::caller::is_track_caller(p, fid) {
            params.push("i64 noundef %ltc.v".into());
            entry.push_str("  %ltc = alloca i64, align 8\n  store i64 %ltc.v, ptr %ltc\n");
        }
        let mut allocas = String::new();
        for (i, t) in self.local_cty.iter().enumerate() {
            if is_param[i] || ll.statics[i] {
                continue;
            }
            let (size, align) = c_size_align(p, t);
            match pass_of(p, t) {
                Pass::Scalar(ty, _) => {
                    let _ = writeln!(allocas, "  %l{i} = alloca {ty}, align {align}");
                }
                // The return local is read back as one integer (`Terminator::Return`).
                Pass::Bits(n) => {
                    let _ = writeln!(allocas, "  %l{i} = alloca [{size} x i8], align {}", align.max(n));
                }
                Pass::Pair => {
                    let _ = writeln!(allocas, "  %l{i} = alloca [16 x i8], align {}", align.max(8));
                }
                _ => {
                    let _ = writeln!(allocas, "  %l{i} = alloca [{size} x i8], align {}", align.max(1));
                }
            }
        }
        let mut flags = String::new();
        let n_flags: usize = (0..self.local_cty.len()).map(|i| self.local_drop[i] as usize + self.move_paths[i].len()).sum();
        // Drop and move flags live in memory (an empty asm use makes them escape, as cgen's
        // frame struct does) when a fn has many of them and many landing pads: promoting
        // them puts a phi per flag on every merge of the cleanup paths, and SROA then runs
        // for minutes (`LUST_LL_FLAGMEM`, flags x pads, default 100000; 0: never).
        static FLAGMEM: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        let flagmem = *FLAGMEM.get_or_init(|| std::env::var("LUST_LL_FLAGMEM").ok().and_then(|v| v.parse().ok()).unwrap_or(100_000));
        let escape = flagmem > 0 && n_flags * ll.pads.len() > flagmem;
        for i in 0..self.local_cty.len() {
            let param = i >= 1 && i <= self.body.arg_count;
            let mut names: Vec<String> = Vec::new();
            if self.local_drop[i] {
                let _ = writeln!(flags, "  store i8 {}, ptr %d{i}", param as u8);
                names.push(format!("%d{i}"));
            }
            for k in 0..self.move_paths[i].len() {
                let _ = writeln!(flags, "  store i8 1, ptr %m{i}_{k}");
                names.push(format!("%m{i}_{k}"));
            }
            for n in names {
                let _ = writeln!(allocas, "  {n} = alloca i8");
                if escape {
                    let _ = writeln!(flags, "  call void asm sideeffect \"\", \"r\"(ptr {n})");
                }
            }
        }
        // The exception slot: landing pads store it, ladder ends load it (a cleanup block
        // whose every entry became native code stays, unreachable, and still names it).
        if !ll.pads.is_empty() || self.cleanup.iter().any(|&c| c) {
            allocas.push_str("  %exn = alloca { ptr, i32 }\n");
        }
        allocas.push_str(&ll.allocas);
        let mut attrs = String::new();
        // A giant body (`LUST_LL_HUGE` lines of IR, default 40000; tsgo has one, a cold
        // table initializer) is not optimized: promoting its thousands of allocas and drop
        // flags over thousands of blocks costs the optimizer minutes per run.
        static HUGE: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
        let huge = *HUGE.get_or_init(|| std::env::var("LUST_LL_HUGE").ok().and_then(|v| v.parse().ok()).unwrap_or(40_000));
        if huge > 0 && ll.body.lines().count() > huge {
            attrs.push_str(" optnone noinline");
        } else {
            attrs.push_str(&source_fn_attrs(p, fid));
        }
        if p.unwind {
            attrs.push_str(" uwtable");
            // The C personality, as the helpers' cleanup guards have it: every landing pad
            // here only cleans up, and LLVM inlines no fn of another personality.
            if !ll.pads.is_empty() {
                attrs.push_str(" personality ptr @__gcc_personality_v0");
            }
        } else {
            attrs.push_str(" nounwind");
        }
        let id = names::fn_tag(self.slots.of(fid));
        let mut d = String::new();
        let _ = writeln!(d, "; {}", p.display_path(info.name).replace('\n', " "));
        let _ = writeln!(d, "define {ret_ll} @fl_{id}({}){attrs} {{\nentry:", params.join(", "));
        d.push_str(&allocas);
        d.push_str(&entry);
        d.push_str(&flags);
        if let Some(k) = kstr_init {
            let _ = writeln!(d, "  call void @{k}()");
        }
        d.push_str("  br label %bb0\n");
        d.push_str(&ll.body);
        d.push_str("}\n");
        d
    }

    /// The helper side of a fn emitted as LLVM IR, into `self.out`: the prelude (vtables,
    /// shims, outlined panics), the frame macros and file statics the helpers read, and the
    /// helpers.
    fn ll_c_side(&mut self, ll: &Ll, kstr_init: Option<&str>) {
        let p = self.p;
        let fid = self.body.fn_id;
        let tag = &ll.tag;
        let prelude = std::mem::take(&mut self.prelude);
        let _ = writeln!(self.out, "/* {} */", p.display_path(p.fn_info(fid).name));
        self.out.push_str(&prelude);
        let mut undef: Vec<String> = Vec::new();
        let mut def = |out: &mut String, name: String, val: String| {
            let _ = writeln!(out, "#define {name} {val}");
            undef.push(name);
        };
        for i in 0..self.local_cty.len() {
            if ll.statics[i] {
                def(&mut self.out, format!("l{i}"), format!("l{i}_{tag}"));
                if self.kconst_local(i) {
                    def(&mut self.out, format!("lk{i}"), format!("lk{i}_{tag}"));
                    def(&mut self.out, format!("lkd{i}"), format!("lkd{i}_{tag}"));
                }
            } else {
                def(&mut self.out, format!("l{i}"), format!("(*q{i})"));
            }
            if self.local_drop[i] {
                def(&mut self.out, format!("d{i}"), format!("(*qd{i})"));
            }
            for k in 0..self.move_paths[i].len() {
                def(&mut self.out, format!("m{i}_{k}"), format!("(*qm{i}_{k})"));
            }
        }
        if crate::check::caller::is_track_caller(p, fid) {
            def(&mut self.out, "ltc".into(), "(*qltc)".into());
        }
        if kstr_init.is_some() {
            def(&mut self.out, "lks".into(), format!("lks_{tag}"));
            def(&mut self.out, "lks_ok".into(), format!("lks_ok_{tag}"));
            let _ = writeln!(self.out, "static const void *lks[{}];\nstatic int32_t lks_ok;", self.kstrs.len());
        }
        // Statics: promoted constants (zeroed, written by their statement) and byte string
        // temps (initialized here), with their interning slots.
        for i in 0..self.local_cty.len() {
            if !ll.statics[i] {
                continue;
            }
            let ct = ctype(&self.local_cty[i]);
            match self.byte_blobs.get(i).cloned().flatten() {
                Some(b) => {
                    let init = if b.is_empty() { "{0}".to_string() } else { format!("{{ .v = {} }}", c_bytes_lit(b.as_slice())) };
                    let _ = writeln!(self.out, "static {ct} l{i} = {init};");
                }
                None => {
                    let _ = writeln!(self.out, "static {ct} l{i};");
                }
            }
            if self.kconst_local(i) {
                let d = self.kconst_decls(i);
                self.out.push_str(&d);
            }
        }
        self.kstrs.clear();
        // The LLVM fn sizes each aggregate local's alloca (and a by-pointer parameter's
        // dereferenceable bytes) by `c_size_align`: the C type the helpers read must agree.
        let mut asserted: HashSet<String> = HashSet::new();
        for t in &self.local_cty {
            if matches!(pass_of(p, t), Pass::Mem | Pass::Bits(_) | Pass::Pair) {
                let ct = ctype(t);
                if asserted.insert(ct.clone()) {
                    let (size, align) = c_size_align(p, t);
                    let _ = writeln!(self.out, "_Static_assert(sizeof({ct}) == {size} && _Alignof({ct}) == {align}, \"ll layout\");");
                }
            }
        }
        for a in &ll.asserts {
            self.out.push_str(a);
        }
        self.out.push_str(&ll.helpers);
        for u in undef {
            let _ = writeln!(self.out, "#undef {u}");
        }
        self.out.push('\n');
    }

    /// The C prototype of `fl_<id>` and the C ABI wrapper `f_<id>` that forwards to it.
    fn ll_wrapper(&self, slot: u32) -> String {
        let p = self.p;
        let f = self.body.fn_id;
        let info = p.fn_info(f);
        let id = names::fn_tag(slot);
        let ret_c = cty(&p.tys, info.ret);
        let rp = pass_of(p, &ret_c);
        let large = ret_is_large(p, f);
        let rt = ctype(&ret_c);
        let mut args: Vec<String> = Vec::new();
        let mut pre = String::new();
        if rp == Pass::Mem {
            args.push(if large { "out".into() } else { "&r".into() });
        }
        for (i, &t) in info.params.iter().enumerate() {
            let ct = cty(&p.tys, t);
            match pass_of(p, &ct) {
                Pass::Skip => {}
                Pass::Scalar(..) => args.push(format!("p{}", i + 1)),
                Pass::Bits(n) => {
                    let _ = write!(pre, "{} b{}; memcpy(&b{1}, &p{1}, {n}); ", bits_types(n).1, i + 1);
                    args.push(format!("b{}", i + 1));
                }
                Pass::Pair => {
                    let _ = write!(pre, "uint64_t b{}[2]; memcpy(b{0}, &p{0}, 16); ", i + 1);
                    args.push(format!("b{0}[0], b{0}[1]", i + 1));
                }
                Pass::Mem => args.push(if param_by_ptr(p, &ct) { format!("p{}", i + 1) } else { format!("&p{}", i + 1) }),
            }
        }
        if crate::check::caller::is_track_caller(p, f) {
            args.push("ltc".into());
        }
        let call = format!("fl_{id}({})", args.join(", "));
        let body = match (rp, large) {
            (Pass::Scalar(..), _) => format!("return {call};"),
            (Pass::Bits(n), _) => format!("{} rb = {call}; {rt} r; memcpy(&r, &rb, {n}); return r;", bits_types(n).1),
            (Pass::Pair, _) => format!("ll_pair rb = {call}; {rt} r; memcpy(&r, &rb, 16); return r;"),
            (Pass::Mem, true) => format!("{call};"),
            (Pass::Skip, true) => format!("(void)out; {call};"),
            _ => format!("{rt} r; {call}; return r;"),
        };
        format!("{}{} {{ {pre}{body} }}\n", ll_proto(p, f, &id), fn_sig(p, f, slot))
    }

    /// A call of written fn `f` with C argument values `args` (all of its params, in
    /// order) through its internal ABI entry `fl_<id>` (an LLVM fn), from a helper's C:
    /// an aggregate argument goes as the address of a fresh copy the callee owns, an
    /// aggregate result through a fresh temporary. Pre-statements go to `self.out`;
    /// returns the value expression. `loc` is the call's location (`#[track_caller]`).
    pub(super) fn ll_fn_call(&mut self, f: LocalDefId, args: &[String], loc: &str) -> String {
        let p = self.p;
        let slot = self.slots.of(f);
        let id = names::fn_tag(slot);
        self.slots.externs.borrow_mut().insert(ll_proto(p, f, &id));
        let info = p.fn_info(f);
        let mut all: Vec<String> = Vec::new();
        let rt = cty(&p.tys, info.ret);
        let rp = pass_of(p, &rt);
        let r = self.tmp();
        if rp == Pass::Mem {
            all.push(format!("&{r}"));
        }
        for (a, &t) in args.iter().zip(&info.params) {
            let ct = cty(&p.tys, t);
            match pass_of(p, &ct) {
                Pass::Skip => {}
                Pass::Scalar(..) => all.push(a.clone()),
                Pass::Bits(n) => {
                    let (v, b) = (self.tmp(), self.tmp());
                    let _ = writeln!(self.out, "    {} {v} = {a}; {} {b}; memcpy(&{b}, &{v}, {n});", ctype(&ct), bits_types(n).1);
                    all.push(b);
                }
                Pass::Pair => {
                    let (v, b) = (self.tmp(), self.tmp());
                    let _ = writeln!(self.out, "    {} {v} = {a}; uint64_t {b}[2]; memcpy({b}, &{v}, 16);", ctype(&ct));
                    all.push(format!("{b}[0], {b}[1]"));
                }
                Pass::Mem => {
                    let v = self.tmp();
                    let _ = writeln!(self.out, "    {} {v} = {a};", ctype(&ct));
                    all.push(format!("&{v}"));
                }
            }
        }
        if crate::check::caller::is_track_caller(p, f) {
            all.push(loc.to_string());
        }
        let call = format!("fl_{id}({})", all.join(", "));
        match rp {
            Pass::Scalar(..) => call,
            Pass::Bits(n) => {
                let _ = writeln!(self.out, "    {} {r}b = {call}; {} {r}; memcpy(&{r}, &{r}b, {n});", bits_types(n).1, ctype(&rt));
                r
            }
            Pass::Pair => {
                let _ = writeln!(self.out, "    ll_pair {r}b = {call}; {} {r}; memcpy(&{r}, &{r}b, 16);", ctype(&rt));
                r
            }
            Pass::Mem => {
                let _ = writeln!(self.out, "    {} {r}; {call};", ctype(&rt));
                r
            }
            Pass::Skip => {
                let _ = writeln!(self.out, "    {call};");
                zero_lit(p, &rt)
            }
        }
    }
}

impl FnGen<'_, '_> {
    /// The native address plan of `pl`: a non-static local, then derefs of references and
    /// boxes to sized values, and fields of structs, tuples and enum variants whose C layout
    /// is exact (cgen's `place` reads the same members). None for any other form.
    fn ll_plan(&self, ll: &Ll, pl: &Place) -> Option<Plan> {
        let l = pl.local as usize;
        if ll.statics[l] {
            return None;
        }
        let mut t = self.local_cty[l].clone();
        let mut steps = Vec::new();
        let mut variant: Option<u32> = None;
        let mut path = String::new();
        for pr in &pl.proj {
            match (pr, t.clone()) {
                (Proj::Deref, CTy::Ref(inner) | CTy::Boxed(inner)) if *inner != CTy::Str && c_layout(self.p, &inner).is_some() => {
                    steps.push(PStep::Load((*inner).clone()));
                    path.clear();
                    t = *inner;
                }
                (&Proj::Field(i), CTy::Adt(a)) => {
                    let lay = c_layout(self.p, &t)?;
                    let adt = self.p.adt(a);
                    let v = if adt.is_enum { variant.take()? } else { 0 };
                    let off = if adt.is_enum { *lay.variant_offsets.get(v as usize)?.get(i as usize)? } else { *lay.field_offsets.get(i as usize)? };
                    let member = if adt.is_enum { format!("u.v{v}.f{i}") } else { format!("f{i}") };
                    path = if path.is_empty() { member.clone() } else { format!("{path}.{member}") };
                    t = cty(&self.p.tys, adt.variants.get(v as usize)?.fields.get(i as usize)?.ty);
                    // A zero-sized field has no bytes to find (C may place it elsewhere).
                    if c_size_align(self.p, &t).0 == 0 {
                        return None;
                    }
                    steps.push(PStep::Offset(off, member));
                }
                (&Proj::Field(i), CTy::Tuple(es)) => {
                    let lay = c_layout(self.p, &t)?;
                    let off = *lay.field_offsets.get(i as usize)?;
                    t = es.get(i as usize)?.clone();
                    if c_size_align(self.p, &t).0 == 0 {
                        return None;
                    }
                    steps.push(PStep::Offset(off, format!("f{i}")));
                }
                (Proj::Downcast(_), CTy::Option(_)) => {}
                (Proj::Field(_), CTy::Option(inner)) => {
                    let lay = c_layout(self.p, &t)?;
                    let off = *lay.variant_offsets.get(1)?.first()?;
                    t = *inner;
                    if c_size_align(self.p, &t).0 == 0 {
                        return None;
                    }
                    steps.push(PStep::Offset(off, "u.v1.f0".into()));
                }
                (Proj::Downcast(v), CTy::Result(..) | CTy::Adt(_)) => variant = Some(*v),
                (Proj::Field(_), CTy::Result(a, b)) => {
                    let lay = c_layout(self.p, &t)?;
                    let v = variant.take().unwrap_or(0);
                    let off = *lay.variant_offsets.get(v as usize)?.first()?;
                    t = if v == 0 { *a } else { *b };
                    if c_size_align(self.p, &t).0 == 0 {
                        return None;
                    }
                    steps.push(PStep::Offset(off, format!("u.v{v}.f0")));
                }
                _ => return None,
            }
        }
        // A pending variant view with no field is not a place this file reads.
        if variant.is_some() {
            return None;
        }
        c_layout(self.p, &t)?;
        Some(Plan { local: l, steps, ty: t })
    }

    /// Emits the address of plan `pl`; returns the pointer and the alignment known there.
    /// Each offset gets its C layout check (`Ll::asserts`).
    fn ll_addr(&mut self, ll: &mut Ll, pl: &Plan) -> (String, u64) {
        let mut cur = format!("%l{}", pl.local);
        let mut ty = self.local_cty[pl.local].clone();
        let mut align = c_size_align(self.p, &ty).1.max(1);
        let mut members: Vec<String> = Vec::new();
        // The offset from the last load (or the local) to here: what the member path names.
        let mut cum = 0u64;
        for st in &pl.steps {
            match st {
                PStep::Load(inner) => {
                    ll.conts += 1;
                    let v = format!("%v{}", ll.conts);
                    let a = c_size_align(self.p, inner).1.max(1);
                    let facts = if facts_on() { format!(", !nonnull !{{}}, !noundef !{{}}, !align !{{i64 {a}}}") } else { String::new() };
                    let _ = writeln!(ll.body, "  {v} = load ptr, ptr {cur}, align {}{facts}", align.min(8));
                    cur = v;
                    ty = inner.clone();
                    align = a;
                    members.clear();
                    cum = 0;
                }
                PStep::Offset(off, member) => {
                    members.push(member.clone());
                    cum += off;
                    // The helper C must define what native code projects into (release C
                    // defines only what a unit holds by value, `gen_fn`).
                    collect_types(&ty, &mut self.sig_types);
                    let _ = ll.asserts.insert(format!(
                        "_Static_assert(__builtin_offsetof({}, {}) == {cum}, \"ll offset\");\n",
                        ctype(&ty),
                        members.join(".")
                    ));
                    if *off != 0 {
                        ll.conts += 1;
                        let v = format!("%v{}", ll.conts);
                        let _ = writeln!(ll.body, "  {v} = getelementptr inbounds i8, ptr {cur}, i64 {off}");
                        cur = v;
                        align = align.min(1 << off.trailing_zeros());
                    }
                }
            }
        }
        (cur, align)
    }

    /// The load facts of a scalar of C type `t` read from memory: a reference or box is
    /// non-null and aligned, a bool 0 or 1, a char below 0x110000.
    fn ll_load_facts(&self, t: &CTy) -> String {
        if !facts_on() {
            return String::new();
        }
        match t {
            CTy::Bool => ", !range !{i8 0, i8 2}, !noundef !{}".into(),
            CTy::Char => ", !range !{i32 0, i32 1114112}, !noundef !{}".into(),
            CTy::Ref(inner) | CTy::Boxed(inner) if **inner != CTy::Str => match c_layout(self.p, inner) {
                Some(l) => format!(", !nonnull !{{}}, !noundef !{{}}, !align !{{i64 {}}}", l.align.max(1)),
                None => String::new(),
            },
            _ => String::new(),
        }
    }

    /// The C type of operand `o` when native code can read it as one scalar (a native
    /// place's value or a literal), with the flag a move of it clears. None otherwise.
    fn ll_scalar_ok(&self, ll: &Ll, o: &Operand) -> Option<(CTy, Option<String>)> {
        match o {
            Operand::Copy(pl) | Operand::Move(pl) => {
                let plan = self.ll_plan(ll, pl)?;
                if !matches!(pass_of(self.p, &plan.ty), Pass::Scalar(..)) {
                    return None;
                }
                let mut clear = None;
                if matches!(o, Operand::Move(_)) && self.local_drop[pl.local as usize] {
                    clear = Some(if pl.proj.is_empty() {
                        format!("%d{}", pl.local)
                    } else {
                        format!("%m{}_{}", pl.local, self.move_flag(pl.local, &self.steps_of(pl)?)?)
                    });
                }
                Some((plan.ty, clear))
            }
            Operand::Const(Const::Int(_, it)) if !is128(*it) => Some((CTy::Int(*it), None)),
            Operand::Const(Const::Bool(_)) => Some((CTy::Bool, None)),
            Operand::Const(Const::Char(_)) => Some((CTy::Char, None)),
            Operand::Const(Const::Float(_, f)) => Some((CTy::Float(*f), None)),
            _ => None,
        }
    }

    /// Emits the value of an operand `ll_scalar_ok` accepted (and its move's flag clear).
    fn ll_scalar(&mut self, ll: &mut Ll, o: &Operand) -> String {
        match o {
            Operand::Copy(pl) | Operand::Move(pl) => {
                let plan = self.ll_plan(ll, pl).expect("checked by ll_scalar_ok");
                let Pass::Scalar(t, _) = pass_of(self.p, &plan.ty) else { unreachable!() };
                let (a, align) = self.ll_addr(ll, &plan);
                ll.conts += 1;
                let v = format!("%v{}", ll.conts);
                let facts = self.ll_load_facts(&plan.ty);
                let _ = writeln!(ll.body, "  {v} = load {t}, ptr {a}, align {align}{facts}");
                if let Some((_, Some(flag))) = self.ll_scalar_ok(ll, o) {
                    let _ = writeln!(ll.body, "  store i8 0, ptr {flag}");
                }
                v
            }
            Operand::Const(Const::Int(v, it)) => {
                let bits = it.bits();
                let m = if bits >= 128 { *v } else { *v & ((1u128 << bits) - 1) };
                // Printed as a signed value of the width (LLVM reads any bit pattern of it).
                let sv = if bits < 128 && (m >> (bits - 1)) & 1 == 1 { (m as i128) - (1i128 << bits) } else { m as i128 };
                sv.to_string()
            }
            Operand::Const(Const::Bool(b)) => (*b as u8).to_string(),
            Operand::Const(Const::Char(c)) => (*c as u32).to_string(),
            Operand::Const(Const::Float(bits, f)) => match f {
                FloatTy::F64 => format!("0x{bits:016X}"),
                // LLVM writes a float constant as the double of the same value.
                FloatTy::F32 => format!("0x{:016X}", (f32::from_bits(*bits as u32) as f64).to_bits()),
            },
            _ => unreachable!("checked by ll_scalar_ok"),
        }
    }

    /// The native value of a scalar rvalue (release arithmetic, comparisons, int casts,
    /// discriminants), stored to `dp`; false (nothing emitted) for any other form.
    fn ll_native_value(&mut self, ll: &mut Ll, rv: &Rvalue, dp: &Plan) -> bool {
        let Pass::Scalar(dt, _) = pass_of(self.p, &dp.ty) else { return false };
        let int_signed = |t: &CTy| matches!(t, CTy::Int(i) if i.signed());
        let value = match rv {
            Rvalue::Bin(op, a, b) => {
                let (Some((at, _)), Some((bt, _))) = (self.ll_scalar_ok(ll, a), self.ll_scalar_ok(ll, b)) else { return false };
                use BinOp::*;
                let float = matches!(at, CTy::Float(_));
                let ok_operands = matches!(at, CTy::Int(i) if !is128(i)) || at == CTy::Bool || at == CTy::Char || float;
                if !ok_operands || (at != bt && !matches!(op, Shl | Shr)) {
                    return false;
                }
                if op.is_cmp() {
                    if dp.ty != CTy::Bool {
                        return false;
                    }
                } else if dp.ty != at {
                    return false;
                }
                let t = match pass_of(self.p, &at) {
                    Pass::Scalar(t, _) => t,
                    _ => return false,
                };
                let inst = match (op, float) {
                    (Add, false) if !self.p.overflow_checks && at != CTy::Bool => "add",
                    (Sub, false) if !self.p.overflow_checks && at != CTy::Bool => "sub",
                    (Mul, false) if !self.p.overflow_checks && at != CTy::Bool => "mul",
                    (Add, true) => "fadd",
                    (Sub, true) => "fsub",
                    (Mul, true) => "fmul",
                    (Div, true) => "fdiv",
                    (BitAnd, false) => "and",
                    (BitOr, false) => "or",
                    (BitXor, false) => "xor",
                    (Shl | Shr, false) if !self.p.overflow_checks && matches!(at, CTy::Int(_)) && matches!(bt, CTy::Int(i) if !is128(i)) => "shift",
                    (Eq | Ne | Lt | Le | Gt | Ge, _) => "cmp",
                    _ => return false,
                };
                let av = self.ll_scalar(ll, a);
                let bv = self.ll_scalar(ll, b);
                ll.conts += 1;
                let k = ll.conts;
                match inst {
                    "cmp" => {
                        let pred = if float {
                            match op {
                                Eq => "fcmp oeq",
                                Ne => "fcmp une",
                                Lt => "fcmp olt",
                                Le => "fcmp ole",
                                Gt => "fcmp ogt",
                                _ => "fcmp oge",
                            }
                        } else {
                            let s = int_signed(&at);
                            match (op, s) {
                                (Eq, _) => "icmp eq",
                                (Ne, _) => "icmp ne",
                                (Lt, true) => "icmp slt",
                                (Lt, false) => "icmp ult",
                                (Le, true) => "icmp sle",
                                (Le, false) => "icmp ule",
                                (Gt, true) => "icmp sgt",
                                (Gt, false) => "icmp ugt",
                                (Ge, true) => "icmp sge",
                                _ => "icmp uge",
                            }
                        };
                        let _ = writeln!(ll.body, "  %c{k} = {pred} {t} {av}, {bv}\n  %v{k} = zext i1 %c{k} to i8");
                    }
                    "shift" => {
                        // The amount masked to the width (overflow checks off), as cgen's C.
                        let CTy::Int(ai) = at else { unreachable!() };
                        let CTy::Int(bi) = bt else { unreachable!() };
                        let bty = match pass_of(self.p, &bt) {
                            Pass::Scalar(x, _) => x,
                            _ => return false,
                        };
                        let wide = if bty == "i64" {
                            bv
                        } else {
                            let ext = if bi.signed() { "sext" } else { "zext" };
                            let _ = writeln!(ll.body, "  %w{k} = {ext} {bty} {bv} to i64");
                            format!("%w{k}")
                        };
                        let _ = writeln!(ll.body, "  %m{k} = and i64 {wide}, {}", ai.bits() - 1);
                        let amt = if t == "i64" {
                            format!("%m{k}")
                        } else {
                            let _ = writeln!(ll.body, "  %n{k} = trunc i64 %m{k} to {t}");
                            format!("%n{k}")
                        };
                        let sh = match (op, ai.signed()) {
                            (Shl, _) => "shl",
                            (_, true) => "ashr",
                            _ => "lshr",
                        };
                        let _ = writeln!(ll.body, "  %v{k} = {sh} {t} {av}, {amt}");
                    }
                    i => {
                        let _ = writeln!(ll.body, "  %v{k} = {i} {t} {av}, {bv}");
                    }
                }
                format!("%v{k}")
            }
            Rvalue::Un(op, a) => {
                let Some((at, _)) = self.ll_scalar_ok(ll, a) else { return false };
                if at != dp.ty {
                    return false;
                }
                let inst = match (op, &at) {
                    (UnOp::Neg, CTy::Float(_)) => "fneg",
                    (UnOp::Neg, CTy::Int(i)) if !self.p.overflow_checks && !is128(*i) => "neg",
                    (UnOp::Not, CTy::Bool) => "notb",
                    (UnOp::Not, CTy::Int(i)) if !is128(*i) => "not",
                    _ => return false,
                };
                let av = self.ll_scalar(ll, a);
                ll.conts += 1;
                let k = ll.conts;
                let _ = match inst {
                    "fneg" => writeln!(ll.body, "  %v{k} = fneg {dt} {av}"),
                    "neg" => writeln!(ll.body, "  %v{k} = sub {dt} 0, {av}"),
                    "notb" => writeln!(ll.body, "  %v{k} = xor i8 {av}, 1"),
                    _ => writeln!(ll.body, "  %v{k} = xor {dt} {av}, -1"),
                };
                format!("%v{k}")
            }
            Rvalue::Cast(a, to) => {
                let Some((at, _)) = self.ll_scalar_ok(ll, a) else { return false };
                let to_c = cty(&self.body.tys, *to);
                if to_c != dp.ty {
                    return false;
                }
                let int_like = |t: &CTy| matches!(t, CTy::Int(i) if !is128(*i)) || matches!(t, CTy::Bool | CTy::Char);
                // Int to int (a bool or char source is unsigned); only `u8 as char` makes a char.
                if !int_like(&at) || !matches!(to_c, CTy::Int(i) if !is128(i)) && !(to_c == CTy::Char && at == CTy::Int(IntTy::U8)) {
                    return false;
                }
                let (Pass::Scalar(ft, _), Pass::Scalar(tt, _)) = (pass_of(self.p, &at), pass_of(self.p, &to_c)) else { return false };
                let av = self.ll_scalar(ll, a);
                let width = |t: &str| t[1..].parse::<u32>().unwrap_or(64);
                let (fw, tw) = (width(ft), width(tt));
                if fw == tw {
                    av
                } else {
                    ll.conts += 1;
                    let k = ll.conts;
                    let inst = if tw < fw {
                        "trunc"
                    } else if int_signed(&at) {
                        "sext"
                    } else {
                        "zext"
                    };
                    let _ = writeln!(ll.body, "  %v{k} = {inst} {ft} {av} to {tt}");
                    format!("%v{k}")
                }
            }
            Rvalue::Discriminant(pl) => {
                let Some(plan) = self.ll_plan(ll, pl) else { return false };
                let Some(lay) = c_layout(self.p, &plan.ty) else { return false };
                let n = adt_discs(self.p, &plan.ty).len();
                if !matches!(dp.ty, CTy::Int(i) if !is128(i)) {
                    return false;
                }
                match lay.enum_tag {
                    Some(EnumTag::None(vi)) => vi.to_string(),
                    // A sequential tag holds the variant index (`disc_call`).
                    Some(EnumTag::Explicit { size, .. }) if size <= 8 && n > 0 && discs_sequential(&adt_discs(self.p, &plan.ty)) => {
                        let tt = bits_types(size).0;
                        let (a, align) = self.ll_addr(ll, &plan);
                        ll.conts += 1;
                        let k = ll.conts;
                        let range = if facts_on() { format!(", !range !{{{tt} 0, {tt} {n}}}, !noundef !{{}}") } else { String::new() };
                        let _ = writeln!(ll.body, "  %t{k} = load {tt}, ptr {a}, align {}{range}", align.min(size));
                        let (tw, dw) = (size * 8, dt[1..].parse::<u64>().unwrap_or(64));
                        if tw == dw {
                            format!("%t{k}")
                        } else {
                            let inst = if dw < tw { "trunc" } else { "zext" };
                            let _ = writeln!(ll.body, "  %v{k} = {inst} {tt} %t{k} to {dt}");
                            format!("%v{k}")
                        }
                    }
                    _ => return false,
                }
            }
            _ => return false,
        };
        let (da, dalign) = self.ll_addr(ll, dp);
        let _ = writeln!(ll.body, "  store {dt} {value}, ptr {da}, align {dalign}");
        true
    }

    /// A call of written fn `f` (args `args`, result to `dest`) lowered natively: arguments
    /// by the callee's internal ABI from native places or literals (an aggregate through a
    /// fresh copy the callee owns), moved arguments' flags cleared first (the callee owns
    /// them from the start, as cgen's `emit_assign`), an `invoke` when `unwind` names a
    /// cleanup entry, then the result stored to `dest`, dropping the value a whole local
    /// held. False (nothing emitted) for any other shape.
    /// `dest_clear`: the destination local's drop flag is surely clear here, so it holds no
    /// old value (a result can go straight into it).
    fn ll_native_call(&mut self, ll: &mut Ll, f: LocalDefId, args: &[Operand], dest: &Place, dest_clear: bool, unwind: Option<u32>) -> bool {
        let p = self.p;
        if !has_generated_body(p, f) || crate::check::caller::is_track_caller(p, f) {
            return false;
        }
        let info = p.fn_info(f);
        if args.len() != info.params.len() {
            return false;
        }
        let rt = cty(&p.tys, info.ret);
        let Some(dp) = self.ll_plan(ll, dest) else { return false };
        if dp.ty != rt {
            return false;
        }
        let dl = dest.local as usize;
        let drop_old = needs_drop_c(p, &dp.ty);
        if drop_old && (!dest.proj.is_empty() || !self.local_drop[dl] || !self.move_paths[dl].is_empty()) {
            return false;
        }
        // Check every argument before emitting anything.
        let pts: Vec<CTy> = info.params.iter().map(|&t| cty(&p.tys, t)).collect();
        let mut clears: Vec<String> = Vec::new();
        for (a, pt) in args.iter().zip(&pts) {
            match pass_of(p, pt) {
                Pass::Scalar(..) => match self.ll_scalar_ok(ll, a) {
                    Some((t, _)) if t == *pt => {}
                    _ => return false,
                },
                Pass::Skip | Pass::Bits(_) | Pass::Pair | Pass::Mem => {
                    let (Operand::Copy(pl) | Operand::Move(pl)) = a else { return false };
                    match self.ll_plan(ll, pl) {
                        Some(plan) if plan.ty == *pt => {}
                        _ => return false,
                    }
                }
            }
            if let Operand::Move(pl) = a
                && self.local_drop[pl.local as usize]
            {
                if pl.proj.is_empty() {
                    clears.push(format!("%d{}", pl.local));
                } else {
                    match self.steps_of(pl).and_then(|path| self.move_flag(pl.local, &path)) {
                        Some(k) => clears.push(format!("%m{}_{k}", pl.local)),
                        None => return false,
                    }
                }
            }
        }
        self.note_callee(f);
        let id = names::fn_tag(self.slots.of(f));
        self.slots.externs.borrow_mut().insert(ll_proto(p, f, &id));
        ll.decls.insert(ll_decl(p, f, &id));
        ll.conts += 1;
        let k = ll.conts;
        let mut vals: Vec<String> = Vec::new();
        // The call's temporaries live only around it (lifetime markers: their stack slots
        // can share space, as the C helpers' block locals do).
        let mut temps: Vec<(String, u64)> = Vec::new();
        ll.decls.insert("declare void @llvm.lifetime.start.p0(i64, ptr)".into());
        ll.decls.insert("declare void @llvm.lifetime.end.p0(i64, ptr)".into());
        let rp = pass_of(p, &rt);
        // A moved whole local passed by pointer goes as itself: the caller never reads it
        // again (its flag is clear), so the callee may own that memory, as rustc does.
        let direct: Vec<bool> = args
            .iter()
            .zip(&pts)
            .map(|(a, pt)| matches!(a, Operand::Move(pl) if pl.proj.is_empty() && !ll.statics[pl.local as usize] && pass_of(p, pt) == Pass::Mem))
            .collect();
        let direct_locals: Vec<usize> =
            args.iter().zip(&direct).filter(|(_, d)| **d).filter_map(|(a, _)| if let Operand::Move(pl) = a { Some(pl.local as usize) } else { None }).collect();
        // An old value the call result replaces (dropped after the call returns), unless the
        // destination's flag is surely clear here.
        let old_live = drop_old && !dest_clear;
        // The result goes straight to a whole-local destination that holds nothing to drop
        // (a panic before the end leaves nothing that reads it: its flag is clear), unless
        // that local is an argument passed as itself.
        let ret_direct = rp == Pass::Mem && dest.proj.is_empty() && !old_live && !ll.statics[dl] && !direct_locals.contains(&dl);
        if rp == Pass::Mem {
            if ret_direct {
                vals.push(format!("ptr %l{dl}"));
            } else {
                let (size, align) = c_size_align(p, &rt);
                let _ = writeln!(ll.allocas, "  %r{k} = alloca [{size} x i8], align {align}");
                let _ = writeln!(ll.body, "  call void @llvm.lifetime.start.p0(i64 {size}, ptr %r{k})");
                vals.push(format!("ptr %r{k}"));
            }
        }
        for (j, (a, pt)) in args.iter().zip(&pts).enumerate() {
            match pass_of(p, pt) {
                Pass::Skip => {}
                Pass::Scalar(t, ext) => {
                    let v = self.ll_scalar_operand_value(ll, a);
                    let ext = if ext.is_empty() { String::new() } else { format!("{ext} ") };
                    vals.push(format!("{t} {ext}{v}"));
                }
                Pass::Bits(n) => {
                    let (Operand::Copy(pl) | Operand::Move(pl)) = a else { unreachable!() };
                    let plan = self.ll_plan(ll, pl).expect("checked");
                    let (addr, align) = self.ll_addr(ll, &plan);
                    let t = bits_types(n).0;
                    let _ = writeln!(ll.body, "  %a{k}_{j} = load {t}, ptr {addr}, align {}", align.min(n));
                    vals.push(format!("{t} %a{k}_{j}"));
                }
                Pass::Pair => {
                    let (Operand::Copy(pl) | Operand::Move(pl)) = a else { unreachable!() };
                    let plan = self.ll_plan(ll, pl).expect("checked");
                    let (addr, align) = self.ll_addr(ll, &plan);
                    let al = align.min(8);
                    let _ = writeln!(
                        ll.body,
                        "  %a{k}_{j} = load i64, ptr {addr}, align {al}\n  %a{k}_{j}q = getelementptr inbounds i8, ptr {addr}, i64 8\n  %a{k}_{j}b = load i64, ptr %a{k}_{j}q, align {al}"
                    );
                    vals.push(format!("i64 %a{k}_{j}, i64 %a{k}_{j}b"));
                }
                Pass::Mem if direct[j] => {
                    let (Operand::Copy(pl) | Operand::Move(pl)) = a else { unreachable!() };
                    vals.push(format!("ptr %l{}", pl.local));
                }
                Pass::Mem => {
                    let (Operand::Copy(pl) | Operand::Move(pl)) = a else { unreachable!() };
                    let plan = self.ll_plan(ll, pl).expect("checked");
                    let (addr, align) = self.ll_addr(ll, &plan);
                    let (size, palign) = c_size_align(p, pt);
                    let _ = writeln!(ll.allocas, "  %a{k}_{j} = alloca [{size} x i8], align {palign}");
                    ll.decls.insert("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)".into());
                    let _ = writeln!(
                        ll.body,
                        "  call void @llvm.lifetime.start.p0(i64 {size}, ptr %a{k}_{j})\n  call void @llvm.memcpy.p0.p0.i64(ptr align {palign} %a{k}_{j}, ptr align {align} {addr}, i64 {size}, i1 false)"
                    );
                    temps.push((format!("%a{k}_{j}"), size));
                    vals.push(format!("ptr %a{k}_{j}"));
                }
            }
        }
        for flag in &clears {
            let _ = writeln!(ll.body, "  store i8 0, ptr {flag}");
        }
        let ret_ty = match rp {
            Pass::Scalar(t, ext) => {
                if ext.is_empty() {
                    t.to_string()
                } else {
                    format!("{ext} {t}")
                }
            }
            Pass::Bits(n) => bits_types(n).0.to_string(),
            Pass::Pair => "{ i64, i64 }".into(),
            _ => "void".into(),
        };
        let assign = if ret_ty == "void" { String::new() } else { format!("%v{k} = ") };
        let call = format!("{ret_ty} @fl_{id}({})", vals.join(", "));
        match unwind {
            Some(u) => {
                ll.pads.insert(u);
                let _ = writeln!(ll.body, "  {assign}invoke {call} to label %c{k} unwind label %lp{u}\nc{k}:");
            }
            None => {
                let _ = writeln!(ll.body, "  {assign}call {call}");
            }
        }
        for (t, size) in &temps {
            let _ = writeln!(ll.body, "  call void @llvm.lifetime.end.p0(i64 {size}, ptr {t})");
        }
        // The old value of a whole local drops once the call returned (`drop_old_value`).
        if old_live {
            let glue = format!("drop_{}", mangle(&dp.ty));
            self.want(Glue::Drop, &dp.ty);
            ll.decls.insert(format!("declare void @{glue}(ptr)"));
            let _ = writeln!(
                ll.body,
                "  %o{k} = load i8, ptr %d{dl}\n  %oc{k} = icmp ne i8 %o{k}, 0\n  br i1 %oc{k}, label %od{k}, label %on{k}\nod{k}:\n  store i8 0, ptr %d{dl}"
            );
            match unwind {
                Some(u) => {
                    let _ = writeln!(ll.body, "  invoke void @{glue}(ptr %l{dl}) to label %on{k} unwind label %lp{u}");
                }
                None => {
                    let _ = writeln!(ll.body, "  call void @{glue}(ptr %l{dl})\n  br label %on{k}");
                }
            }
            let _ = writeln!(ll.body, "on{k}:");
        }
        let (da, dalign) = self.ll_addr(ll, &dp);
        match rp {
            Pass::Scalar(t, _) => {
                let _ = writeln!(ll.body, "  store {t} %v{k}, ptr {da}, align {dalign}");
            }
            Pass::Bits(n) => {
                let _ = writeln!(ll.body, "  store {} %v{k}, ptr {da}, align {}", bits_types(n).0, dalign.min(n));
            }
            Pass::Pair => {
                let al = dalign.min(8);
                let _ = writeln!(
                    ll.body,
                    "  %v{k}a = extractvalue {{ i64, i64 }} %v{k}, 0\n  %v{k}b = extractvalue {{ i64, i64 }} %v{k}, 1\n  store i64 %v{k}a, ptr {da}, align {al}\n  %v{k}q = getelementptr inbounds i8, ptr {da}, i64 8\n  store i64 %v{k}b, ptr %v{k}q, align {al}"
                );
            }
            Pass::Mem if ret_direct => {}
            Pass::Mem => {
                let (size, align) = c_size_align(p, &rt);
                ll.decls.insert("declare void @llvm.memcpy.p0.p0.i64(ptr, ptr, i64, i1)".into());
                let _ = writeln!(
                    ll.body,
                    "  call void @llvm.memcpy.p0.p0.i64(ptr align {dalign} {da}, ptr align {align} %r{k}, i64 {size}, i1 false)\n  call void @llvm.lifetime.end.p0(i64 {size}, ptr %r{k})"
                );
            }
            Pass::Skip => {}
        }
        if drop_old {
            let _ = writeln!(ll.body, "  store i8 1, ptr %d{dl}");
        }
        true
    }

    /// For each block, the locals whose drop flag may be set at its terminator: a write to a
    /// local (an assign to it or a part, a call result) may set its flag; a move of the whole
    /// local or its drop clears it. A move this does not model counts as still set, so a
    /// clear answer is exact.
    fn flags_maybe_set(&self) -> Vec<Vec<bool>> {
        let body = self.body;
        let (nl, nb) = (body.locals.len(), body.blocks.len());
        let mut entry: Vec<Option<Vec<bool>>> = vec![None; nb];
        let mut at_term = vec![vec![true; nl]; nb];
        // Parameters own their values at entry.
        entry[0] = Some((0..nl).map(|l| l >= 1 && l <= body.arg_count).collect());
        let mut work = vec![0usize];
        fn join(entry: &mut [Option<Vec<bool>>], work: &mut Vec<usize>, b: Bb, st: &[bool]) {
            let b = b.0 as usize;
            match &mut entry[b] {
                Some(e) => {
                    let mut grew = false;
                    for (x, &y) in e.iter_mut().zip(st) {
                        grew |= y && !*x;
                        *x |= y;
                    }
                    if grew {
                        work.push(b);
                    }
                }
                None => {
                    entry[b] = Some(st.to_vec());
                    work.push(b);
                }
            }
        }
        while let Some(b) = work.pop() {
            let mut st = entry[b].clone().expect("queued blocks have a state");
            for s in &body.blocks[b].stmts {
                match &s.kind {
                    StmtKind::Assign(pl, rv) => {
                        if let Rvalue::Use(Operand::Move(src)) = rv
                            && src.proj.is_empty()
                        {
                            st[src.local as usize] = false;
                        }
                        st[pl.local as usize] = true;
                    }
                    StmtKind::Drop(l) => st[*l as usize] = false,
                    _ => {}
                }
            }
            at_term[b] = st.clone();
            match &body.blocks[b].term {
                Terminator::Call { args, dest, next, unwind, .. } => {
                    // A call owns its moved arguments from the start.
                    for a in args {
                        if let Operand::Move(p) = a
                            && p.proj.is_empty()
                        {
                            st[p.local as usize] = false;
                        }
                    }
                    if let Some(u) = unwind {
                        join(&mut entry, &mut work, *u, &st);
                    }
                    st[dest.local as usize] = true;
                    join(&mut entry, &mut work, *next, &st);
                }
                Terminator::Goto(t) => join(&mut entry, &mut work, *t, &st),
                Terminator::If(_, a, c) => {
                    join(&mut entry, &mut work, *a, &st);
                    join(&mut entry, &mut work, *c, &st);
                }
                Terminator::Switch(_, cases, other) => {
                    for (_, t) in cases {
                        join(&mut entry, &mut work, *t, &st);
                    }
                    join(&mut entry, &mut work, *other, &st);
                }
                Terminator::Return | Terminator::Unreachable | Terminator::Panic(_) => {}
            }
        }
        at_term
    }

    /// `ll_scalar` without the move's flag clear: a call clears its arguments' flags itself.
    fn ll_scalar_operand_value(&mut self, ll: &mut Ll, o: &Operand) -> String {
        match o {
            Operand::Move(pl) => self.ll_scalar(ll, &Operand::Copy(pl.clone())),
            o => self.ll_scalar(ll, o),
        }
    }

    /// Lowers statement `s` to LLVM IR directly when it has a simple form: a copy, move,
    /// constant or address of native places into a place that owns nothing to drop, or the
    /// drop of a local that no partial move touches. False: the statement runs as a helper.
    /// `unwind` is its cleanup entry (a drop can unwind).
    fn ll_native_stmt(&mut self, ll: &mut Ll, s: &Stmt, unwind: Option<u32>) -> bool {
        match &s.kind {
            StmtKind::Assign(dest, rv) => {
                let Some(dp) = self.ll_plan(ll, dest) else { return false };
                if needs_drop_c(self.p, &dp.ty) {
                    return false;
                }
                match rv {
                    Rvalue::Use(o @ (Operand::Copy(src) | Operand::Move(src))) => {
                        let Some(sp) = self.ll_plan(ll, src) else { return false };
                        if sp.ty != dp.ty {
                            return false;
                        }
                        // The flag a move clears (`operand`): the whole local's, or its path's.
                        let mut clear: Option<String> = None;
                        if matches!(o, Operand::Move(_)) && self.local_drop[src.local as usize] {
                            if src.proj.is_empty() {
                                clear = Some(format!("%d{}", src.local));
                            } else {
                                match self.steps_of(src).and_then(|path| self.move_flag(src.local, &path)) {
                                    Some(k) => clear = Some(format!("%m{}_{k}", src.local)),
                                    None => return false,
                                }
                            }
                        }
                        let (sa, salign) = self.ll_addr(ll, &sp);
                        let (da, dalign) = self.ll_addr(ll, &dp);
                        match pass_of(self.p, &dp.ty) {
                            Pass::Skip => {}
                            Pass::Scalar(t, _) => {
                                ll.conts += 1;
                                let facts = self.ll_load_facts(&sp.ty);
                                let _ = writeln!(ll.body, "  %v{0} = load {t}, ptr {sa}, align {salign}{facts}\n  store {t} %v{0}, ptr {da}, align {dalign}", ll.conts);
                            }
                            _ => {
                                let size = c_size_align(self.p, &dp.ty).0;
                                // A source inside the destination's own local may overlap it.
                                let f = if src.local == dest.local { "memmove" } else { "memcpy" };
                                ll.decls.insert(format!("declare void @llvm.{f}.p0.p0.i64(ptr, ptr, i64, i1)"));
                                let _ = writeln!(ll.body, "  call void @llvm.{f}.p0.p0.i64(ptr align {dalign} {da}, ptr align {salign} {sa}, i64 {size}, i1 false)");
                            }
                        }
                        if let Some(flag) = clear {
                            let _ = writeln!(ll.body, "  store i8 0, ptr {flag}");
                        }
                        true
                    }
                    Rvalue::Use(Operand::Const(c)) => {
                        let lit = match (c, &dp.ty) {
                            (Const::Int(v, it), CTy::Int(dt)) if it == dt && !is128(*it) => (*v as i128 & ((1i128 << it.bits()) - 1)).to_string(),
                            (Const::Bool(b), CTy::Bool) => (*b as u8).to_string(),
                            (Const::Char(ch), CTy::Char) => (*ch as u32).to_string(),
                            (Const::Unit, CTy::Unit) => return true,
                            _ => return false,
                        };
                        let Pass::Scalar(t, _) = pass_of(self.p, &dp.ty) else { return false };
                        let (da, dalign) = self.ll_addr(ll, &dp);
                        let _ = writeln!(ll.body, "  store {t} {lit}, ptr {da}, align {dalign}");
                        true
                    }
                    Rvalue::Ref(_, place) => {
                        let Some(sp) = self.ll_plan(ll, place) else { return false };
                        // Only a thin reference to the place: fat places (str, slices, dyn) keep cgen's forms.
                        let thin = matches!(&dp.ty, CTy::Ref(inner) if **inner == sp.ty) || matches!(&dp.ty, CTy::Ptr(inner) if **inner == sp.ty);
                        if !thin || matches!(sp.ty, CTy::Str | CTy::Slice(_) | CTy::Dyn | CTy::Unsized(..) | CTy::DynCell | CTy::DynLock(_)) {
                            return false;
                        }
                        if pass_of(self.p, &dp.ty) != Pass::Scalar("ptr", "") {
                            return false;
                        }
                        let (sa, _) = self.ll_addr(ll, &sp);
                        let (da, dalign) = self.ll_addr(ll, &dp);
                        let _ = writeln!(ll.body, "  store ptr {sa}, ptr {da}, align {dalign}");
                        true
                    }
                    rv => self.ll_native_value(ll, rv, &dp),
                }
            }
            StmtKind::Drop(l) => {
                let l = *l as usize;
                if !self.local_drop[l] {
                    return true;
                }
                if !self.move_paths[l].is_empty() || ll.statics[l] {
                    return false;
                }
                let t = self.local_cty[l].clone();
                self.want(Glue::Drop, &t);
                let glue = format!("drop_{}", mangle(&t));
                ll.decls.insert(format!("declare void @{glue}(ptr)"));
                ll.conts += 1;
                let k = ll.conts;
                let _ = writeln!(
                    ll.body,
                    "  %v{k} = load i8, ptr %d{l}\n  %c{k} = icmp ne i8 %v{k}, 0\n  br i1 %c{k}, label %dr{k}, label %dn{k}\ndr{k}:\n  store i8 0, ptr %d{l}"
                );
                match unwind {
                    Some(u) => {
                        ll.pads.insert(u);
                        let _ = writeln!(ll.body, "  invoke void @{glue}(ptr %l{l}) to label %dn{k} unwind label %lp{u}");
                    }
                    None => {
                        let _ = writeln!(ll.body, "  call void @{glue}(ptr %l{l})\n  br label %dn{k}");
                    }
                }
                let _ = writeln!(ll.body, "dn{k}:");
                true
            }
            _ => false,
        }
    }
}

/// The LLVM fn attributes of fn `f`'s source attributes, as rustc maps them: `#[inline]`
/// inlinehint, `#[inline(always)]` alwaysinline, `#[inline(never)]` noinline, `#[cold]`
/// cold. A closure body fn or a trait method stub borrows another fn's def: none.
fn source_fn_attrs(p: &Program, f: LocalDefId) -> String {
    use crate::check::generics::FnClass;
    use crate::lexer::{Tok, TokenTree};
    if p.gx.closure_fns.contains_key(&f) || matches!(p.gx.fn_class.get(f.0 as usize), Some(FnClass::Stub)) {
        return String::new();
    }
    let mut out = String::new();
    for a in &p.fn_info(f).def(&p.ast).attrs {
        if a.path.len() != 1 {
            continue;
        }
        match p.name(a.path[0].name) {
            "cold" => out.push_str(" cold"),
            "inline" => {
                let mut how = " inlinehint";
                if let crate::ast::AttrInput::List(_, trees) = &a.input {
                    for t in trees {
                        if let TokenTree::Token(t) = t
                            && let Tok::Ident(n) = t.tok
                        {
                            match p.name(n) {
                                "always" => how = " alwaysinline",
                                "never" => how = " noinline",
                                _ => {}
                            }
                        }
                    }
                }
                out.push_str(how);
            }
            _ => {}
        }
    }
    out
}

/// The C prototype of written fn `f`'s internal ABI entry `fl_<id>` (`pass_of` per
/// parameter; an aggregate result through a leading pointer).
fn ll_proto(p: &Program, f: LocalDefId, id: &str) -> String {
    let info = p.fn_info(f);
    let ret_c = cty(&p.tys, info.ret);
    let rp = pass_of(p, &ret_c);
    let rt = ctype(&ret_c);
    let mut params: Vec<String> = Vec::new();
    if rp == Pass::Mem {
        params.push(format!("{rt} *"));
    }
    for &t in &info.params {
        let ct = cty(&p.tys, t);
        match pass_of(p, &ct) {
            Pass::Skip => {}
            Pass::Scalar(..) => params.push(ctype(&ct)),
            Pass::Bits(n) => params.push(bits_types(n).1.into()),
            Pass::Pair => params.push("uint64_t, uint64_t".into()),
            Pass::Mem => params.push(format!("{}*", ctype(&ct))),
        }
    }
    if crate::check::caller::is_track_caller(p, f) {
        params.push("lust_loc".into());
    }
    let fret = match rp {
        Pass::Scalar(..) => rt,
        Pass::Bits(n) => bits_types(n).1.into(),
        Pass::Pair => "ll_pair".into(),
        _ => "void".into(),
    };
    let plist = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    format!("{fret} fl_{id}({plist});\n")
}

/// The LLVM declaration of written fn `f`'s internal ABI entry `fl_<id>`: the types and
/// extension attributes of its definition (`FnGen::ll_define`).
fn ll_decl(p: &Program, f: LocalDefId, id: &str) -> String {
    let info = p.fn_info(f);
    let rt = cty(&p.tys, info.ret);
    let mut params: Vec<String> = Vec::new();
    let ret = match pass_of(p, &rt) {
        Pass::Scalar(t, ext) => {
            if ext.is_empty() {
                t.to_string()
            } else {
                format!("{ext} {t}")
            }
        }
        Pass::Bits(n) => bits_types(n).0.to_string(),
        Pass::Pair => "{ i64, i64 }".into(),
        Pass::Mem => {
            params.push("ptr".into());
            "void".into()
        }
        Pass::Skip => "void".into(),
    };
    for &t in &info.params {
        match pass_of(p, &cty(&p.tys, t)) {
            Pass::Skip => {}
            Pass::Scalar(t, ext) => params.push(if ext.is_empty() { t.to_string() } else { format!("{t} {ext}") }),
            Pass::Bits(n) => params.push(bits_types(n).0.into()),
            Pass::Pair => params.push("i64, i64".into()),
            Pass::Mem => params.push("ptr".into()),
        }
    }
    if crate::check::caller::is_track_caller(p, f) {
        params.push("i64".into());
    }
    format!("declare {ret} @fl_{id}({})", params.join(", "))
}

/// True when `text` holds `word` as a whole C identifier outside literals.
fn contains_word(text: &str, word: &str) -> bool {
    let b = text.as_bytes();
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'"' | b'\'' => i = skip_lit(b, i),
            c if is_ident(c) && (i == 0 || !is_ident(b[i - 1])) => {
                let start = i;
                while i < b.len() && is_ident(b[i]) {
                    i += 1;
                }
                if &text[start..i] == word {
                    return true;
                }
            }
            _ => i += 1,
        }
    }
    false
}

/// The LLVM triple of a Rust target triple (the release targets).
pub fn llvm_triple(triple: &str) -> String {
    match triple {
        "x86_64-unknown-linux-musl" => "x86_64-unknown-linux-musl".into(),
        t => t.replace("-unknown-", "-pc-").replace("-pc-linux", "-unknown-linux"),
    }
}

/// The fn ids (`names::fn_tag`) a fn's helpers call through `fl_<id>` (`ll_fn_call`
/// records each callee's prototype in `externs`).
fn ll_callee_ids(f: &FnOut) -> impl Iterator<Item = &str> {
    f.externs.iter().filter_map(|e| {
        let at = e.find(" fl_")? + 4;
        let id = e.get(at..at + 16)?;
        id.bytes().all(|c| c.is_ascii_hexdigit()).then_some(id)
    })
}

/// Cross-unit inlining for the LLVM backend (`LUST_LL_INLINE=<cost>`, 0 or unset: off;
/// `LUST_LL_INLINE_DEPTH`, default 3): the fns outside `slots` that a fn of the unit calls,
/// directly or through such fns up to the depth, whose cost (`LlFn::cost`: statements and
/// blocks) is at most that. `LUST_LL_INLINE_HINT=<n>` (default 1) multiplies the limit by n
/// for `#[inline]` fns and by 2n for `#[inline(always)]` ones. `LUST_LL_INLINE_TINY=<cost>`
/// and `LUST_LL_INLINE_TINY_DEPTH=<levels>` (default 0: off) follow fns of at most that
/// cost that many levels past the depth (a tiny accessor called from a copy at the last
/// level otherwise stays a call). The unit gets an
/// `available_externally` copy of each (`ll_unit`) and its helpers (`fn_unit_parts`), so the
/// optimizer can inline it, as LTO would; its own unit still emits it. `slot_of` maps a fn
/// id to its slot. The copies come in fn id order (slot order carries a persistent
/// session's history, and its units are a one-shot build's).
pub fn ll_inline_set(fns: &[FnOut], slots: &[usize], slot_of: &std::collections::HashMap<&str, usize>) -> Vec<usize> {
    static LIMITS: std::sync::OnceLock<(usize, usize, usize, usize, usize)> = std::sync::OnceLock::new();
    let (bytes, depth, hint, tiny, tiny_depth) = *LIMITS.get_or_init(|| {
        let n = |k: &str, d: usize| std::env::var(k).ok().and_then(|v| v.parse().ok()).unwrap_or(d);
        (n("LUST_LL_INLINE", 0), n("LUST_LL_INLINE_DEPTH", 3), n("LUST_LL_INLINE_HINT", 1), n("LUST_LL_INLINE_TINY", 0), n("LUST_LL_INLINE_TINY_DEPTH", 0))
    });
    if bytes == 0 {
        return Vec::new();
    }
    // The limit for one fn, from the attributes of its `define` line (`source_fn_attrs`).
    let limit = |f: &FnOut| {
        let head = f.ll.lines().find(|l| l.starts_with("define ")).unwrap_or_default();
        let head = head.rsplit_once(')').map_or(head, |(_, attrs)| attrs);
        if head.contains(" noinline") {
            0
        } else if head.contains(" alwaysinline") {
            bytes * hint * 2
        } else if head.contains(" inlinehint") {
            bytes * hint
        } else {
            bytes
        }
    };
    let own: HashSet<usize> = slots.iter().copied().collect();
    let mut picked: Vec<(&str, usize)> = Vec::new();
    let mut seen: HashSet<usize> = HashSet::new();
    let mut frontier: Vec<usize> = slots.to_vec();
    for level in 0..depth + tiny_depth {
        let mut next = Vec::new();
        for &s in &frontier {
            for id in ll_callee_ids(&fns[s]) {
                let Some(&g) = slot_of.get(id) else { continue };
                let f = &fns[g];
                let max = if level < depth { limit(f) } else { tiny };
                if own.contains(&g) || f.ll.is_empty() || f.ll_cost as usize > max || !seen.insert(g) {
                    continue;
                }
                picked.push((id, g));
                next.push(g);
            }
        }
        frontier = next;
    }
    picked.sort_unstable();
    picked.into_iter().map(|(_, g)| g).collect()
}

/// The `.ll` text of one release fn unit: the declarations its fns name (each once) and
/// their definitions, then an `available_externally` copy of each fn in `inl`
/// (`ll_inline_set`). Empty when no fn of the unit has LLVM IR.
pub fn ll_unit(fns: &[FnOut], slots: &[usize], inl: &[usize], triple: &str) -> String {
    if slots.iter().all(|&s| fns[s].ll.is_empty()) {
        return String::new();
    }
    // No target line: clang compiles the IR for its own target, as it does the C halves.
    let _ = triple;
    let mut out = String::from("; lust release LLVM IR unit\n\n");
    let mut decls: BTreeSet<&str> = BTreeSet::new();
    for &s in slots.iter().chain(inl) {
        decls.extend(fns[s].ll_decls.iter().map(String::as_str));
    }
    // A fn the unit defines (its own, or an inline copy) is not declared again.
    let defined: HashSet<&str> = slots
        .iter()
        .chain(inl)
        .filter_map(|&s| {
            let d = &fns[s].ll;
            let at = d.find(" @fl_")? + 2;
            d.get(at..at + 19)
        })
        .collect();
    for d in decls {
        if d.starts_with("declare ")
            && let Some(at) = d.find(" @fl_")
            && d.get(at + 2..at + 21).is_some_and(|n| defined.contains(n))
        {
            continue;
        }
        out.push_str(d);
        out.push('\n');
    }
    out.push('\n');
    for &s in slots {
        out.push_str(&fns[s].ll);
    }
    for &s in inl {
        out.push_str(&fns[s].ll.replacen("\ndefine ", "\ndefine available_externally ", 1));
    }
    out
}
