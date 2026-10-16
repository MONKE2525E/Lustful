// Constant storage with rustc's addresses (runtime/kconst.c): equal
// constants share one address program-wide, as rustc gives them in one
// codegen unit. A promoted temp or byte string temp keeps its function
// static, and the place a borrow takes is the canonical copy (interned
// on the site's first run, then read from its slot); a function's str
// literals intern once, on its first call. The pointees of statics are the canonical storage of
// their content: the glue unit registers them before main
// (`lust_kstatics_init`). Comparing equal constants used from different
// fns gives a config-dependent answer in rustc (docs/ARCH.md, rule
// zero), so tests compare them only inside one fn.
use super::*;

/// The layout descriptor of a value of C type `t` (the words that
/// runtime/kconst.c reads), or None when every byte is init and no word
/// is a pointer.
pub(super) fn kdesc(p: &Program, t: &CTy) -> Option<Vec<u64>> {
    let mut ops = Vec::new();
    walk(p, t, 0, &mut ops);
    if let [Op::Bytes(0, n)] = ops[..]
        && n == c_size_align(p, t).0
    {
        return None;
    }
    let mut words = Vec::new();
    emit(&ops, &mut words);
    let mut d = vec![words.len() as u64];
    d.extend(words);
    Some(d)
}

/// A descriptor as a C initializer list.
pub(super) fn kdesc_init(d: &[u64]) -> String {
    let words: Vec<String> = d.iter().map(|w| format!("{w}ull")).collect();
    format!("{{{}}}", words.join(", "))
}

/// One descriptor op (runtime/kconst.c has the word forms).
#[derive(PartialEq)]
enum Op {
    /// Init bytes: offset, count.
    Bytes(u64, u64),
    /// A pointer word at the offset.
    Ptr(u64),
    /// An array: offset, element count, stride, the element's ops.
    Arr(u64, u64, u64, Vec<Op>),
    /// A tagged enum: offset, tag size, each variant's discriminant and ops.
    Tag(u64, u64, Vec<u64>, Vec<Vec<Op>>),
    /// A niche enum: offset, niche offset, niche size, niche start, the
    /// dataful variant, each variant's ops.
    Niche(u64, u64, u64, u64, u64, Vec<Vec<Op>>),
}

/// The words of `ops`.
fn emit(ops: &[Op], w: &mut Vec<u64>) {
    let sub = |ops: &[Op], w: &mut Vec<u64>| {
        let mut s = Vec::new();
        emit(ops, &mut s);
        w.push(s.len() as u64);
        w.extend(s);
    };
    for op in ops {
        match op {
            Op::Bytes(off, n) => w.extend([1, *off, *n]),
            Op::Ptr(off) => w.extend([2, *off]),
            Op::Arr(off, count, stride, el) => {
                w.extend([3, *off, *count, *stride]);
                sub(el, w);
            }
            Op::Tag(off, size, discs, vars) => {
                w.extend([4, *off, *size, vars.len() as u64]);
                w.extend(discs);
                for v in vars {
                    sub(v, w);
                }
            }
            Op::Niche(off, noff, nsize, start, dataful, vars) => {
                w.extend([5, *off, *noff, *nsize, *start, *dataful, vars.len() as u64]);
                for v in vars {
                    sub(v, w);
                }
            }
        }
    }
}

/// Pushes `n` init bytes at `off`, joined to init bytes that end there.
fn init_bytes(out: &mut Vec<Op>, off: u64, n: u64) {
    if n == 0 {
        return;
    }
    if let Some(Op::Bytes(o, m)) = out.last_mut()
        && *o + *m == off
    {
        *m += n;
        return;
    }
    out.push(Op::Bytes(off, n));
}

/// The descriptor ops of a value of type `t` at offset `off`.
fn walk(p: &Program, t: &CTy, off: u64, out: &mut Vec<Op>) {
    let size = c_size_align(p, t).0;
    if size == 0 {
        return;
    }
    match t {
        CTy::Int(_) | CTy::Float(_) | CTy::Bool | CTy::Char => init_bytes(out, off, size),
        // A fat `&str` or `&[T]`: the data pointer, then the length.
        CTy::Ref(inner) if **inner == CTy::Str => {
            out.push(Op::Ptr(off));
            init_bytes(out, off + 8, 8);
        }
        CTy::Slice(_) => {
            out.push(Op::Ptr(off));
            init_bytes(out, off + 8, 8);
        }
        CTy::Ref(_) | CTy::FnPtr(..) | CTy::Ptr(_) => out.push(Op::Ptr(off)),
        // An empty `Vec::new()` or `String::new()` of a const value: its
        // dangling pointer, then the length and capacity.
        CTy::String | CTy::Vec(_) => {
            out.push(Op::Ptr(off));
            init_bytes(out, off + 8, 16);
        }
        CTy::Tuple(es) => match c_layout(p, t) {
            Some(l) => {
                for (e, fo) in es.iter().zip(&l.field_offsets) {
                    walk(p, e, off + fo, out);
                }
            }
            None => init_bytes(out, off, size),
        },
        CTy::Array(e, n) => {
            let es = c_size_align(p, e).0;
            let mut el = Vec::new();
            walk(p, e, 0, &mut el);
            if el == [Op::Bytes(0, es)] {
                init_bytes(out, off, es * n);
            } else if !el.is_empty() {
                out.push(Op::Arr(off, *n, es, el));
            }
        }
        CTy::Adt(a) if !p.adt(*a).is_enum => match c_layout(p, t) {
            Some(l) => {
                for (f, fo) in p.adt(*a).variants[0].fields.iter().zip(&l.field_offsets) {
                    walk(p, &cty(&p.tys, f.ty), off + fo, out);
                }
            }
            None => init_bytes(out, off, size),
        },
        CTy::Adt(_) | CTy::Option(_) | CTy::Result(..) => enum_ops(p, t, off, size, out),
        _ => init_bytes(out, off, size),
    }
}

/// The field types of each variant of an enum-like C type.
fn variant_fields(p: &Program, t: &CTy) -> Vec<Vec<CTy>> {
    match t {
        CTy::Option(e) => vec![vec![], vec![(**e).clone()]],
        CTy::Result(a, b) => vec![vec![(**a).clone()], vec![(**b).clone()]],
        CTy::Adt(a) => p.adt(*a).variants.iter().map(|v| v.fields.iter().map(|f| cty(&p.tys, f.ty)).collect()).collect(),
        _ => Vec::new(),
    }
}

/// The ops of an enum: its tag, then each variant's fields.
fn enum_ops(p: &Program, t: &CTy, off: u64, size: u64, out: &mut Vec<Op>) {
    let Some(l) = c_layout(p, t) else { return init_bytes(out, off, size) };
    let vars = variant_fields(p, t);
    let fields_at = |vi: usize, base: u64, out: &mut Vec<Op>| {
        for (f, fo) in vars[vi].iter().zip(&l.variant_offsets[vi]) {
            walk(p, f, base + fo, out);
        }
    };
    let subs = || {
        (0..vars.len())
            .map(|vi| {
                let mut s = Vec::new();
                fields_at(vi, 0, &mut s);
                s
            })
            .collect()
    };
    match l.enum_tag {
        Some(EnumTag::None(v)) => fields_at(v, off, out),
        Some(EnumTag::Explicit { size: ts, .. }) if ts <= 8 => {
            out.push(Op::Tag(off, ts, adt_discs(p, t).iter().map(|&d| d as u64).collect(), subs()));
        }
        Some(EnumTag::NicheFilled { variant, niche }) if niche.scalar_size <= 8 => {
            out.push(Op::Niche(off, niche.offset, niche.scalar_size, niche.start as u64, variant as u64, subs()));
        }
        _ => init_bytes(out, off, size),
    }
}

impl FnGen<'_, '_> {
    /// True when local `i` is constant storage a borrow may observe: a
    /// promoted temp or byte string temp that is not zero-sized.
    pub(super) fn kconst_local(&self, i: usize) -> bool {
        (self.body.promoted.contains(&(i as Local)) || self.byte_blobs.get(i).is_some_and(|b| b.is_some()))
            && c_size_align(self.p, &self.local_cty[i]).0 > 0
    }

    /// The prologue lines of a constant local `i`: its site cache, and
    /// its layout descriptor when it has one.
    pub(super) fn kconst_decls(&self, i: usize) -> String {
        let mut out = format!("  static const void *lk{i};\n");
        if !self.byte_blobs.get(i).is_some_and(|b| b.is_some())
            && let Some(d) = kdesc(self.p, &self.local_cty[i])
        {
            let _ = writeln!(out, "  static const uint64_t lkd{i}[] = {};", kdesc_init(&d));
        }
        out
    }

    /// `place` for a borrow: the place inside the canonical copy of a
    /// constant local (no Deref on the way), else the place itself. It
    /// writes the site's interning statement first.
    pub(super) fn kplace(&mut self, pl: &Place, loc: &str) -> (String, CTy) {
        let (e, t) = self.place(pl, loc);
        let i = pl.local as usize;
        if pl.proj.iter().any(|pr| matches!(pr, Proj::Deref)) || !self.kconst_local(i) {
            return (e, t);
        }
        let base = format!("l{i}");
        let Some(rest) = e.strip_prefix(&base) else { return (e, t) };
        let lt = &self.local_cty[i];
        let (n, a) = c_size_align(self.p, lt);
        let blob = self.byte_blobs.get(i).is_some_and(|b| b.is_some());
        let desc = if !blob && kdesc(self.p, lt).is_some() { format!("lkd{i}") } else { "0".into() };
        // The first run interns (a statement before the use); every run
        // then reads the cached address.
        let _ = writeln!(self.out, "    if (!lk{i}) lust_kintern(&lk{i}, &l{i}, {n}, {}, {desc});", a.max(1));
        (format!("(*({} *)lk{i}){rest}", ctype(lt)), t)
    }

    /// A `&str` literal operand: its bytes interned, so equal literals
    /// share an address. The function's literals intern once, at its
    /// prologue's first run (`kstr_finish`); a use reads its slot.
    /// Outside a function body, the plain C literal.
    pub(super) fn kstr(&mut self, bytes: &[u8]) -> String {
        if bytes.is_empty() || self.kdecl_at.is_none() {
            return str_lit_c(bytes);
        }
        let n = self.kstrs.len();
        let id = *self.kstrs.entry(bytes.to_vec()).or_insert(n);
        format!("((lust_str){{(uint8_t*)lks[{id}], {}}})", bytes.len())
    }

    /// Inserts the slots of the literals `kstr` made, and their interning,
    /// at the prologue's end. Two threads may both intern on a first run:
    /// both get the same addresses.
    pub(super) fn kstr_finish(&mut self) {
        let Some(at) = self.kdecl_at.take() else { return };
        if self.kstrs.is_empty() {
            return;
        }
        let mut lits: Vec<(&Vec<u8>, &usize)> = self.kstrs.iter().collect();
        lits.sort_by_key(|(_, id)| **id);
        let mut text = format!("  static const void *lks[{}];\n  static int32_t lks_ok;\n  if (!lks_ok) {{\n", lits.len());
        for (b, id) in lits {
            let _ = writeln!(text, "    lust_kintern(&lks[{id}], {}, {}, 1, 0);", c_string_lit(b), b.len());
        }
        text.push_str("    lks_ok = 1;\n  }\n");
        self.out.insert_str(at, &text);
        self.kstrs.clear();
    }
}

/// The state of one `static_defs` pass: names for promoted values, the
/// pointee definitions so far by content key (`static_key`; equal
/// content gets one definition), the macro names that stand for an
/// earlier definition, and the pointees to register as canonical storage.
#[derive(Default)]
pub(super) struct StaticCx {
    pub counter: u32,
    defs: HashMap<Vec<u8>, String>,
    alias: HashMap<String, String>,
    regs: Vec<(String, u64, u64, Option<Vec<u64>>)>,
}

/// Every static pointee is at least 16-aligned, so a site of a stricter
/// type finds it (rustc raises a shared constant's alignment to its
/// strictest use).
const KALIGN: u64 = 16;

/// Defines the static pointee `name` (value `v` at type `ct`, C
/// initializer `init`) in `pre`, or makes `name` a macro for an earlier
/// pointee with equal content.
pub(super) fn kdef(p: &Program, cx: &mut StaticCx, pre: &mut String, name: &str, v: &crate::ty::consteval::ConstValue, ct: &CTy, init: &str) {
    let c = ctype(ct);
    let (n, a) = c_size_align(p, ct);
    if n == 0 {
        let _ = writeln!(pre, "static const {c} {name} = {init};");
        return;
    }
    let key = static_key(p, cx, v, ct, &c, init);
    if let Some(prev) = cx.defs.get(&key) {
        let _ = writeln!(pre, "#define {name} (*({c} *)&{prev})");
        cx.alias.insert(name.to_string(), prev.clone());
        return;
    }
    cx.defs.insert(key, name.to_string());
    let _ = writeln!(pre, "static const {c} {name} __attribute__((aligned({}))) = {init};", KALIGN.max(a));
    cx.regs.push((name.to_string(), n, KALIGN.max(a), kdesc(p, ct)));
}

/// A `&str` in static data: its bytes in one registered array per
/// distinct content (shared with an equal byte array pointee).
pub(super) fn kstatic_str(cx: &mut StaticCx, pre: &mut String, bytes: &[u8]) -> String {
    if bytes.is_empty() {
        return str_lit_c(bytes);
    }
    let key = image_key(bytes.to_vec(), vec![1; bytes.len()]);
    let name = match cx.defs.get(&key) {
        Some(n) => n.clone(),
        None => {
            let name = format!("lust_ks{}", cx.regs.len());
            let _ = writeln!(pre, "static const uint8_t {name}[{}] __attribute__((aligned({KALIGN}))) = {};", bytes.len(), c_string_lit(bytes));
            cx.regs.push((name.clone(), bytes.len() as u64, KALIGN, None));
            cx.defs.insert(key, name.clone());
            name
        }
    };
    format!("((lust_str){{(uint8_t*)&{name}, {}}})", bytes.len())
}

/// The content key of a static pointee: its byte image under rustc's
/// rule (`image_key`) when the value holds no pointer, else its C type
/// and initializer, with alias names read as the names they stand for.
fn static_key(p: &Program, cx: &StaticCx, v: &crate::ty::consteval::ConstValue, ct: &CTy, c: &str, init: &str) -> Vec<u8> {
    let n = c_size_align(p, ct).0 as usize;
    let (mut b, mut cls) = (vec![0u8; n], vec![0u8; n]);
    if put(p, v, ct, 0, &mut b, &mut cls).is_some() {
        return image_key(b, cls);
    }
    let mut key = format!("T{c}=");
    let mut word = String::new();
    for ch in init.chars().chain(std::iter::once(' ')) {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            word.push(ch);
            continue;
        }
        key.push_str(cx.alias.get(&word).unwrap_or(&word));
        word.clear();
        key.push(ch);
    }
    key.into_bytes()
}

/// rustc's equality of constants as a key (runtime/kconst.c `lust_kkey`
/// does the same at run time): a 4, 8, 16 or 32 byte image is its
/// bytes; any other is its bytes and init classes, where more than 16
/// init and uninit chunks make all of it init.
fn image_key(b: Vec<u8>, mut cls: Vec<u8>) -> Vec<u8> {
    let n = b.len();
    let mut key = vec![b'B'];
    key.extend((n as u64).to_le_bytes());
    key.extend(&b);
    if matches!(n, 4 | 8 | 16 | 32) {
        return key;
    }
    let chunks = 1 + cls.windows(2).filter(|w| w[0] != w[1]).count();
    if chunks > 16 {
        cls.iter_mut().for_each(|c| *c = 1);
    }
    key.extend(cls);
    key
}

/// Writes the byte image of const value `v` at type `t` at offset `off`
/// (`cls` 1 for an init byte). None for a value with a pointer or a
/// shape this does not lay out.
fn put(p: &Program, v: &crate::ty::consteval::ConstValue, t: &CTy, off: usize, b: &mut [u8], cls: &mut [u8]) -> Option<()> {
    use crate::ty::consteval::ConstValue as CV;
    let mut bytes = |at: usize, val: u128, n: usize, b: &mut [u8], cls: &mut [u8]| {
        for k in 0..n {
            b[at + k] = (val >> (8 * k)) as u8;
            cls[at + k] = 1;
        }
    };
    let size = c_size_align(p, t).0 as usize;
    match (v, t) {
        (_, CTy::Cell(inner)) => put(p, v, inner, off, b, cls),
        (CV::Int(i), CTy::Int(_)) => Some(bytes(off, *i as u128, size, b, cls)),
        (CV::Float(bits, _), CTy::Float(_)) => Some(bytes(off, *bits as u128, size, b, cls)),
        (CV::Bool(x), CTy::Bool) => Some(bytes(off, *x as u128, 1, b, cls)),
        (CV::Char(ch), CTy::Char) => Some(bytes(off, *ch as u128, 4, b, cls)),
        (CV::Unit, _) if size == 0 => Some(()),
        (CV::Bytes(bs), CTy::Array(..)) => {
            for (k, x) in bs.as_slice().iter().enumerate() {
                bytes(off + k, *x as u128, 1, b, cls);
            }
            Some(())
        }
        (CV::Aggregate(vals), CTy::Array(e, _)) => {
            let es = c_size_align(p, e).0 as usize;
            vals.iter().enumerate().try_for_each(|(k, x)| put(p, x, e, off + k * es, b, cls))
        }
        (CV::Repeat(x, n), CTy::Array(e, _)) => {
            let es = c_size_align(p, e).0 as usize;
            (0..*n as usize).try_for_each(|k| put(p, x, e, off + k * es, b, cls))
        }
        (CV::Aggregate(vals), CTy::Tuple(es)) => {
            let l = c_layout(p, t)?;
            vals.iter().zip(es).zip(&l.field_offsets).try_for_each(|((x, e), fo)| put(p, x, e, off + *fo as usize, b, cls))
        }
        (CV::Aggregate(vals), CTy::Adt(a)) if !p.adt(*a).is_enum => {
            let l = c_layout(p, t)?;
            let fields = &p.adt(*a).variants[0].fields;
            vals.iter().zip(fields).zip(&l.field_offsets).try_for_each(|((x, f), fo)| put(p, x, &cty(&p.tys, f.ty), off + *fo as usize, b, cls))
        }
        (CV::Variant(vi, vals), CTy::Adt(_) | CTy::Option(_) | CTy::Result(..)) => {
            let l = c_layout(p, t)?;
            let vi = *vi as usize;
            let vars = variant_fields(p, t);
            match l.enum_tag? {
                EnumTag::None(_) => {}
                EnumTag::Explicit { size: ts, .. } => bytes(off, adt_discs(p, t)[vi] as u128, ts as usize, b, cls),
                EnumTag::NicheFilled { variant, niche } => {
                    if vi != variant {
                        let k = (0..vi).filter(|&i| i != variant).count() as u128;
                        bytes(off + niche.offset as usize, niche_val(niche, k), niche.scalar_size as usize, b, cls);
                    }
                }
            }
            vals.iter().zip(vars.get(vi)?).zip(l.variant_offsets.get(vi)?).try_for_each(|((x, f), fo)| put(p, x, f, off + *fo as usize, b, cls))
        }
        _ => None,
    }
}

/// `lust_kstatics_init`, which registers the static pointees in
/// definition order (an inner pointee before the values that point at
/// it, so their pointer words read as relocs).
pub(super) fn kstatics_init(cx: &StaticCx) -> String {
    let mut out = String::new();
    for (i, (_, _, _, d)) in cx.regs.iter().enumerate() {
        if let Some(d) = d {
            let _ = writeln!(out, "static const uint64_t lust_ksd{i}[] = {};", kdesc_init(d));
        }
    }
    out.push_str("void lust_kstatics_init(void) {\n");
    for (i, (name, n, a, d)) in cx.regs.iter().enumerate() {
        let desc = if d.is_some() { format!("lust_ksd{i}") } else { "0".into() };
        let _ = writeln!(out, "  lust_kreg(&{name}, {n}, {a}, {desc});");
    }
    out.push_str("}\n");
    out
}
