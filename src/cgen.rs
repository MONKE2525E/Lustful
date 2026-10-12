// C backend. Each function is generated on its own (in parallel). Type helpers ("glue": drop, clone,
// eq, debug) are requested by structural type and generated once, after all functions.
use crate::ast::{BinOp, UnOp};
use crate::check::Builtin;
use crate::check::collect::*;
use crate::diag::{SourceMap, Span};
use crate::ir::*;
use crate::ty::lang::{self, SigTy};
use crate::ty::layout::{self, EnumTag, Layout, Niche, ReprKind};
use crate::ty::*;
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
    /// A tuple, emitted as a generated struct with fields f0, f1, ... (W-CORELANG).
    Tuple(Vec<CTy>),
    /// An array, emitted as a generated struct holding `v[len]` (W-CORELANG).
    Array(Box<CTy>, u64),
    /// A slice reference value or slice place: a generated fat struct holding
    /// `ptr` and `len` (W-CORELANG), the same role `lust_str` plays for `&str`.
    Slice(Box<CTy>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Glue {
    Drop,
    Clone,
    Eq,
    Debug,
}

/// Maps a semantic type to its body-independent C form. Builtin Adts reach this
/// through the v2 compat helpers; kinds the subset cannot form yet map to `Unit`,
/// as inference leftovers did before. They gain real C forms with their features.
pub fn cty(tys: &impl TyIntern, t: Ty) -> CTy {
    match tys.kind(t) {
        TyKind::Bool => CTy::Bool,
        TyKind::Char => CTy::Char,
        TyKind::Int(i) => CTy::Int(i),
        TyKind::Str => CTy::Str,
        TyKind::Tuple(ts) => CTy::Tuple(tys.tys_of(ts).iter().map(|&e| cty(tys, e)).collect()),
        TyKind::Array(e, c) => {
            let n = match tys.const_kind(c) {
                ConstKind::Int(n) => n as u64,
                _ => 0,
            };
            CTy::Array(Box::new(cty(tys, e)), n)
        }
        TyKind::Slice(e) => CTy::Slice(Box::new(cty(tys, e))),
        TyKind::Ref(_, _, e) => match tys.kind(e) {
            TyKind::Slice(el) => CTy::Slice(Box::new(cty(tys, el))),
            _ => CTy::Ref(Box::new(cty(tys, e))),
        },
        TyKind::Adt(..) => match tys.builtin_of(t) {
            Some(BuiltinTy::String) => CTy::String,
            Some(BuiltinTy::Vec) => CTy::Vec(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::Option) => CTy::Option(Box::new(cty(tys, tys.adt_first_ty_arg(t).unwrap_or(ERROR)))),
            Some(BuiltinTy::Chars) => CTy::Chars,
            Some(BuiltinTy::Args) => CTy::Args,
            None => match tys.local_adt(t) {
                Some(a) => CTy::Adt(a),
                None => CTy::Unit,
            },
        },
        _ => CTy::Unit,
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
        // tcc has no __int128: the runtime's two-word structs (runtime.h).
        IntTy::I128 => "lust_i128",
        IntTy::U128 => "lust_u128",
    }
}

fn is128(i: IntTy) -> bool {
    matches!(i, IntTy::I128 | IntTy::U128)
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
        IntTy::I128 => "i128",
        IntTy::U128 => "u128",
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
        CTy::Tuple(_) => format!("Tup_{}", mangle(t)),
        CTy::Array(..) => format!("Arr_{}", mangle(t)),
        CTy::Slice(_) => format!("Sl_{}", mangle(t)),
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
        CTy::Tuple(es) => es.iter().map(|e| format!("{}_", mangle(e))).collect(),
        CTy::Array(e, n) => format!("{n}_{}_", mangle(e)),
        CTy::Slice(e) => format!("sl{}_", mangle(e)),
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
        CTy::Tuple(es) => {
            out.insert(t.clone());
            es.iter().for_each(|e| collect_types(e, out));
        }
        CTy::Array(e, _) => {
            out.insert(t.clone());
            collect_types(e, out);
        }
        CTy::Slice(e) => {
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
        CTy::Adt(_) | CTy::Option(_) | CTy::Tuple(_) | CTy::Array(..) | CTy::Slice(_) => out.push(t.clone()),
        _ => {}
    }
}

fn is_copy_c(p: &Program, t: &CTy) -> bool {
    match t {
        CTy::Unit | CTy::Bool | CTy::Char | CTy::Int(_) | CTy::Ref(_) | CTy::Args | CTy::Chars | CTy::Slice(_) => true,
        CTy::Option(e) => is_copy_c(p, e),
        CTy::Tuple(es) => es.iter().all(|e| is_copy_c(p, e)),
        CTy::Array(e, _) => is_copy_c(p, e),
        CTy::Adt(a) => p.adt(*a).derives.copy,
        _ => false,
    }
}

fn needs_drop_c(p: &Program, t: &CTy) -> bool {
    match t {
        CTy::String | CTy::Vec(_) => true,
        CTy::Option(e) => needs_drop_c(p, e),
        CTy::Tuple(es) => es.iter().any(|e| needs_drop_c(p, e)),
        CTy::Array(e, _) => needs_drop_c(p, e),
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
    map: &'b SourceMap,
    /// Types in the signatures of called functions, needed for the call casts.
    sig_types: HashSet<CTy>,
    /// Line of the function's `fn` keyword. Locations are stored relative to it, so the C for
    /// an unchanged function stays valid when code above it moves.
    base_line: u32,
    /// LocalDefId to table slot. Slots are stable across edits; local ids are not.
    slots: &'b [u32],
    tmp: u32,
    /// This function's return value uses the out-pointer ABI (`ret_is_large`).
    ret_large: bool,
}

/// A layout with no field or niche detail, for runtime struct types whose
/// C form is fixed in runtime.h (`lust_String`, `lust_Vec`, and kin).
fn plain_layout(size: u64, align: u64) -> Layout {
    Layout { size, align, field_offsets: Vec::new(), variant_offsets: Vec::new(), niche: None, enum_tag: None }
}

/// True when `type_decls` can emit an enum of this layout with the exact
/// Rust size: the tag or niche scalar fits a C integer of at most 8 bytes,
/// and niche tag values do not wrap the scalar range.
fn enum_is_exact(l: &Layout, variants: usize) -> bool {
    match l.enum_tag {
        Some(EnumTag::Explicit { size, .. }) => size <= 8,
        Some(EnumTag::NicheFilled { niche, .. }) => {
            matches!(niche.scalar_size, 1 | 2 | 4 | 8)
                && niche.start <= u64::MAX as u128
                && niche.start + variants.saturating_sub(1) as u128 <= (1u128 << (niche.scalar_size * 8))
        }
        Some(EnumTag::None) => variants == 1,
        None => false,
    }
}

/// The Rust layout of a CTy, when this file can emit a C type of exactly
/// that size, alignment, and field offsets. `None` means the type keeps
/// the legacy declaration-order emission below, with its old (wrong)
/// sizes: today that is aggregates with a direct `()` field (the C form
/// of `CTy::Unit` is one byte, not zero), by-value cycles, and enum
/// shapes `enum_is_exact` rejects. Every `Some` result is checked in the
/// emitted C by _Static_assert on sizeof and _Alignof (see `type_decls`).
///
/// The layout is computed over CTy, not over `Ty`, so glue types that
/// never existed as a semantic type (an Option of a reference, say) get
/// one too. Two niches are stripped against the engine in ty/layout.rs:
/// the fat-pointer data word and the String/Vec pointer word, because
/// the runtime produces null there for empty values today, so a
/// niche-filled outer enum could not tell a valid empty value from the
/// tag value. Options over those stay tagged (and oversized) until the
/// runtime uses dangling pointers for empty buffers.
fn c_layout(p: &Program, t: &CTy) -> Option<Layout> {
    fn go(p: &Program, t: &CTy, seen: &mut HashSet<AdtId>) -> Option<Layout> {
        match t {
            CTy::Unit => None,
            CTy::Bool => Some(layout::bool_layout()),
            CTy::Char => Some(layout::char_layout()),
            CTy::Int(i) => Some(layout::int_layout(*i)),
            CTy::Str => Some(plain_layout(16, 8)),
            CTy::String | CTy::Vec(_) | CTy::Chars => Some(plain_layout(24, 8)),
            CTy::Args => Some(plain_layout(8, 8)),
            CTy::Ref(inner) if **inner == CTy::Str => Some(plain_layout(16, 8)),
            CTy::Ref(_) => Some(layout::ptr_layout()),
            CTy::Slice(_) => Some(plain_layout(16, 8)),
            CTy::Tuple(es) => {
                let fields: Option<Vec<Layout>> = es.iter().map(|e| go(p, e, seen)).collect();
                layout::struct_layout(&fields?, layout::Repr::default()).ok()
            }
            CTy::Array(e, 0) => Some(plain_layout(0, go(p, e, seen).map_or(1, |l| l.align))),
            CTy::Array(e, n) => layout::array_layout(&go(p, e, seen)?, *n).ok(),
            CTy::Option(e) => {
                let l = layout::enum_layout(&[vec![], vec![go(p, e, seen)?]], &[0, 1], layout::Repr::default()).ok()?;
                enum_is_exact(&l, 2).then_some(l)
            }
            CTy::Adt(a) => {
                if !seen.insert(*a) {
                    return None;
                }
                let adt = p.adt(*a);
                let r = if adt.is_enum {
                    let mut variants = Vec::with_capacity(adt.variants.len());
                    for v in &adt.variants {
                        let mut fields = Vec::with_capacity(v.fields.len());
                        for f in &v.fields {
                            fields.push(go(p, &cty(&p.tys, f.ty), seen)?);
                        }
                        variants.push(fields);
                    }
                    let discs: Vec<i128> = adt.variants.iter().map(|v| v.disc).collect();
                    match layout::enum_layout(&variants, &discs, adt.repr) {
                        Ok(l) if enum_is_exact(&l, adt.variants.len()) => Some(l),
                        _ => None,
                    }
                } else {
                    let mut fields = Vec::with_capacity(adt.variants[0].fields.len());
                    for f in &adt.variants[0].fields {
                        fields.push(go(p, &cty(&p.tys, f.ty), seen)?);
                    }
                    layout::struct_layout(&fields, adt.repr).ok()
                };
                seen.remove(a);
                r
            }
        }
    }
    go(p, t, &mut HashSet::new())
}

/// C integer type for an explicit enum tag or a niche scalar of `size`
/// bytes. Niche scalars are read and written as unsigned bit patterns.
fn tag_c_type(size: u64, signed: bool) -> &'static str {
    match (size, signed) {
        (1, false) => "uint8_t",
        (1, true) => "int8_t",
        (2, false) => "uint16_t",
        (2, true) => "int16_t",
        (4, false) => "uint32_t",
        (4, true) => "int32_t",
        (_, false) => "uint64_t",
        (_, true) => "int64_t",
    }
}

/// A zero compound literal of type `t`, in value position. Types the
/// layout path emits at size 0 take the `{}` form, since tcc rejects
/// `{0}` for an empty struct.
fn zero_lit(p: &Program, t: &CTy) -> String {
    let ct = ctype(t);
    if c_layout(p, t).is_some_and(|l| l.size == 0) { format!("(({ct}){{}})") } else { format!("(({ct}){{0}})") }
}

/// The discriminant values of an enum or Option CTy, in variant order.
fn adt_discs(p: &Program, t: &CTy) -> Vec<i128> {
    match t {
        CTy::Option(_) => vec![0, 1],
        CTy::Adt(a) => p.adt(*a).variants.iter().map(|v| v.disc).collect(),
        _ => Vec::new(),
    }
}

/// True when every discriminant equals its variant index, so a stored
/// tag value reads back as the index with no mapping.
fn discs_sequential(discs: &[i128]) -> bool {
    discs.iter().enumerate().all(|(i, &d)| d == i as i128)
}

/// A C literal for one discriminant value, cast to the tag type. The
/// layout path only stores values that fit an 8 byte tag.
fn disc_lit(disc: i128, size: u64, signed: bool) -> String {
    let ct = tag_c_type(size, signed);
    if disc < 0 {
        if disc == i64::MIN as i128 { format!("(({ct})(-9223372036854775807LL - 1))") } else { format!("(({ct})({disc}LL))") }
    } else {
        format!("(({ct})({}ULL))", disc as u128)
    }
}

/// The C expression that reads the variant index of an enum or Option
/// value at the pointer expression `ptr`. The layout path stores the
/// discriminant value in the tag: sequential discriminants read
/// inline, the rest go through the generated `disc_` mapping helper.
/// Legacy types store the variant index in `tag` directly.
fn disc_call(p: &Program, t: &CTy, ptr: &str) -> String {
    match c_layout(p, t) {
        Some(l) => match l.enum_tag {
            Some(EnumTag::Explicit { .. }) if discs_sequential(&adt_discs(p, t)) => format!("(({ptr})->u._tag)"),
            Some(EnumTag::Explicit { .. }) | Some(EnumTag::NicheFilled { .. }) => format!("disc_{}({ptr})", mangle(t)),
            _ => "0".into(),
        },
        None => format!("({ptr})->tag"),
    }
}

/// The C field access for field `fi` of variant `vi` in the enum or
/// Option value expression `e`. Only Options differ between the layout
/// and legacy shapes; Adt enums keep `.u.v{vi}.f{fi}` in both.
fn variant_field(p: &Program, t: &CTy, e: &str, vi: usize, fi: usize) -> String {
    match t {
        CTy::Option(_) if c_layout(p, t).is_none() => format!("{e}.v"),
        _ => format!("{e}.u.v{vi}.f{fi}"),
    }
}

/// A C statement (no trailing newline) that stores variant `vi`'s
/// discriminant into the enum or Option value expression `e`. Empty
/// when the variant is the niche variant (its payload writes the niche
/// scalar) or the enum stores no tag.
fn disc_set(p: &Program, t: &CTy, e: &str, vi: usize) -> String {
    let Some(l) = c_layout(p, t) else { return format!("{e}.tag = {vi};") };
    match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => format!("{e}.u._tag = {};", disc_lit(adt_discs(p, t)[vi], size, signed)),
        Some(EnumTag::NicheFilled { variant, niche }) => {
            if vi == variant {
                String::new()
            } else {
                let k = (0..vi).filter(|&i| i != variant).count() as u128;
                format!("{e}.u._n._s = {}ULL;", niche.start + k)
            }
        }
        _ => String::new(),
    }
}

/// Size and alignment of a CTy as the emitted C types lay it out under
/// the legacy emission: declaration order, natural alignment, a uint32
/// tag first in enums and Options. Used for the types `c_layout`
/// rejects, and only for the return-ABI threshold below, so it must
/// match the legacy C structs this file emits, nothing else.
fn c_size_align_legacy(p: &Program, t: &CTy) -> (u64, u64) {
    fn go(p: &Program, t: &CTy, seen: &mut HashSet<AdtId>) -> (u64, u64) {
        fn align_up(x: u64, a: u64) -> u64 {
            (x + a - 1) / a * a
        }
        fn fields(p: &Program, v: &Variant, seen: &mut HashSet<AdtId>) -> (u64, u64) {
            let (mut size, mut align) = (0u64, 1u64);
            for f in &v.fields {
                let (fs, fa) = go(p, &cty(&p.tys, f.ty), seen);
                size = align_up(size, fa) + fs;
                align = align.max(fa);
            }
            (align_up(size, align), align)
        }
        match t {
            CTy::Unit | CTy::Bool => (1, 1),
            CTy::Char => (4, 4),
            CTy::Int(i) => {
                let s = (i.bits() / 8) as u64;
                (s, if is128(*i) { 16 } else { s.min(8) })
            }
            CTy::Str => (16, 8),
            CTy::String | CTy::Vec(_) | CTy::Chars => (24, 8),
            CTy::Args => (8, 8),
            CTy::Ref(inner) if **inner == CTy::Str => (16, 8),
            CTy::Ref(_) => (8, 8),
            CTy::Option(e) => {
                let (es, ea) = go(p, e, seen);
                let align = ea.max(4);
                (align_up(align_up(4, ea) + es, align), align)
            }
            CTy::Tuple(es) => {
                if es.is_empty() {
                    (1, 1) // the emitted `uint8_t unused`
                } else {
                    let (mut size, mut align) = (0u64, 1u64);
                    for e in es {
                        let (fs, fa) = go(p, e, seen);
                        size = align_up(size, fa) + fs;
                        align = align.max(fa);
                    }
                    (align_up(size, align), align)
                }
            }
            CTy::Array(e, n) => {
                let (es, ea) = go(p, e, seen);
                (es * (*n).max(1), ea)
            }
            CTy::Slice(_) => (16, 8),
            CTy::Adt(a) => {
                if !seen.insert(*a) {
                    // A by-value cycle has no finite size; check rejects
                    // it long before here. Report huge, never loop.
                    return (u64::MAX / 2, 8);
                }
                let adt = p.adt(*a);
                let r = if adt.is_enum {
                    let (mut usize_, mut ualign) = (0u64, 1u64);
                    for v in &adt.variants {
                        if !v.fields.is_empty() {
                            let (vs, va) = fields(p, v, seen);
                            usize_ = usize_.max(vs);
                            ualign = ualign.max(va);
                        }
                    }
                    if usize_ == 0 {
                        (4, 4)
                    } else {
                        let align = ualign.max(4);
                        (align_up(align_up(4, ualign) + usize_, align), align)
                    }
                } else if adt.variants[0].fields.is_empty() {
                    (1, 1) // the emitted `uint8_t unused`
                } else {
                    fields(p, &adt.variants[0], seen)
                };
                seen.remove(a);
                r
            }
        }
    }
    go(p, t, &mut HashSet::new())
}

/// Size and alignment of a CTy as the emitted C types lay it out: the
/// Rust layout when `c_layout` is exact, the legacy layout otherwise.
fn c_size_align(p: &Program, t: &CTy) -> (u64, u64) {
    match c_layout(p, t) {
        Some(l) => (l.size, l.align),
        None => c_size_align_legacy(p, t),
    }
}

/// Returns over 32 bytes go through a hidden out-pointer (ARCH 4.5);
/// parameters stay by value, which keeps the slot cast simple.
fn ret_is_large(p: &Program, f: LocalDefId) -> bool {
    c_size_align(p, &cty(&p.tys, p.fn_info(f).ret)).0 > 32
}

/// `(RET (*)(PARAMS))`, the cast that calls function `f` through the table.
/// A large return becomes `(void (*)(RET*, PARAMS))` (see `ret_is_large`).
fn fn_ptr_cast(p: &Program, f: LocalDefId) -> String {
    let info = p.fn_info(f);
    let ret = ctype(&cty(&p.tys, info.ret));
    let mut params: Vec<String> = Vec::new();
    if ret_is_large(p, f) {
        params.push(format!("{ret}*"));
    }
    params.extend(info.params.iter().map(|&t| ctype(&cty(&p.tys, t))));
    let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    if ret_is_large(p, f) { format!("(void (*)({params}))") } else { format!("({ret} (*)({params}))") }
}

/// The C signature of function `f`, defined under the C name `f<slot>`.
fn fn_sig(p: &Program, f: LocalDefId, slot: u32) -> String {
    let info = p.fn_info(f);
    let ret = ctype(&cty(&p.tys, info.ret));
    let mut params: Vec<String> = Vec::new();
    if ret_is_large(p, f) {
        params.push(format!("{ret} *out"));
    }
    params.extend(info.params.iter().enumerate().map(|(i, &t)| format!("{} p{}", ctype(&cty(&p.tys, t)), i + 1)));
    let params = if params.is_empty() { "void".to_string() } else { params.join(", ") };
    if ret_is_large(p, f) { format!("void f{slot}({params})") } else { format!("{ret} f{slot}({params})") }
}

/// Generates C for one function body. `base_line` is the line of its `fn` keyword, in the
/// file that defines it; `slots` maps every LocalDefId to its slot in `lust_fns`.
pub fn gen_fn(p: &Program, body: &Body, map: &SourceMap, base_line: u32, slots: &[u32]) -> FnOut {
    let local_cty: Vec<CTy> = body.locals.iter().map(|l| cty(&body.tys, l.ty)).collect();
    let local_drop = local_cty.iter().map(|t| needs_drop_c(p, t)).collect();
    let mut g = FnGen {
        p,
        body,
        out: String::new(),
        glue: HashSet::new(),
        local_cty,
        local_drop,
        map,
        sig_types: HashSet::new(),
        base_line,
        slots,
        tmp: 0,
        ret_large: ret_is_large(p, body.fn_id),
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
    /// The runtime prints one file path for the whole program (`lust_file`), so the packed
    /// value carries line and column only; an expanded span reports at its call site.
    fn loc(&self, span: Span) -> String {
        let (l, c) = self.map.line_col(self.map.call_site(span));
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
            self.term(&block.term, block.term_span, next);
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
                    e = variant_field(self.p, &t, &e, 1, 0);
                    t = *inner;
                }
                (Proj::Downcast(v), _) => variant = Some(*v),
                (Proj::Index(l), CTy::Vec(el)) => {
                    e = format!("(({}*){e}.ptr)[lust_bounds(l{l}, {e}.len, {loc})]", ctype(&el));
                    t = *el;
                }
                (Proj::Field(i), CTy::Tuple(es)) => {
                    e = format!("{e}.f{i}");
                    t = es[*i as usize].clone();
                }
                (Proj::Index(l), CTy::Array(el, n)) => {
                    e = format!("{e}.v[lust_bounds(l{l}, {n}, {loc})]");
                    t = *el;
                }
                (Proj::Deref, CTy::Slice(_)) => {
                    // A slice place is represented by its fat value, like `str`.
                }
                (Proj::Index(l), CTy::Slice(el)) => {
                    e = format!("{e}.ptr[lust_bounds(l{l}, {e}.len, {loc})]");
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
                        post.push(format!("{e} = {};", zero_lit(self.p, &t)));
                    }
                }
                (e, t)
            }
            Operand::Const(c) => match c {
                Const::Int(v, it) => {
                    // IR consts carry 64 bits today, so a 128-bit literal
                    // is a zero-extended word pair until consts widen.
                    let lit = if is128(*it) {
                        format!("(({}){{{}ULL, 0}})", int_c(*it), v)
                    } else if *v < (1 << 31) {
                        v.to_string()
                    } else {
                        format!("(({}){}ULL)", int_c(*it), v)
                    };
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

    /// Stores a computed value into `dest`, dropping the old value first when
    /// the local owns one. Shared by `Assign` statements and `Call`
    /// terminators: `make_value` produces the value text (and may emit helper
    /// statements into the block this opens), and `mentions` says whether
    /// producing the value reads `dest` itself.
    fn emit_assign(
        &mut self,
        dest: &Place,
        mentions: bool,
        loc: &str,
        make_value: impl FnOnce(&mut Self, &str, &mut Vec<String>) -> String,
    ) {
        // Value generation may emit helper statements with temporaries, so open a C block lazily.
        let mark = self.out.len();
        self.out.push_str("  {\n");
        let body_start = self.out.len();
        let mut post = Vec::new();
        let value = make_value(self, loc, &mut post);
        let (d, dt) = self.place(dest, loc);
        let drop = needs_drop_c(self.p, &dt);
        if drop && dest.proj.is_empty() && !mentions {
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

    fn stmt(&mut self, s: &StmtKind, span: Span) {
        let loc = self.loc(span);
        match s {
            StmtKind::Assign(dest, rv) => {
                let mentions = rvalue_mentions(rv, dest.local);
                self.emit_assign(dest, mentions, &loc, |s, loc, post| s.rvalue(rv, loc, post));
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

    fn term(&mut self, t: &Terminator, span: Span, next_block: Option<usize>) {
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
            Terminator::Call { target, args, dest, next, unwind } => {
                // No unwind edges exist yet (W-PANIC builds them); the slot
                // is carried so that work needs no IR change.
                debug_assert!(unwind.is_none(), "cgen has no unwind edges yet");
                let mentions = args.iter().any(|o| operand_mentions(o, dest.local));
                self.emit_assign(dest, mentions, &loc, |s, loc, post| s.call_value(*target, args, loc, post));
                if Some(next.0 as usize) != next_block {
                    let _ = writeln!(self.out, "  goto bb{};", next.0);
                }
            }
            Terminator::Return => {
                if self.ret_large {
                    self.out.push_str("  *out = l0; return;\n")
                } else {
                    self.out.push_str("  return l0;\n")
                }
            }
            Terminator::Unreachable => self.out.push_str("  abort();\n"),
            Terminator::Panic(parts) => {
                self.out.push_str("  {\n");
                let s = self.format(parts, &loc, &mut post);
                let _ = writeln!(self.out, "    lust_panic(&{s}, {loc});\n  }}");
            }
        }
    }

    // ---------- Rvalues ----------

    /// The C text of one call's result value. Every user fn call goes through
    /// `lust_fns`, so a changed function can be swapped in without relinking
    /// its callers.
    fn call_value(&mut self, target: CallTarget, args: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        match target {
            CallTarget::Fn(f) => {
                let info = self.p.fn_info(f);
                for &t in info.params.iter().chain(std::iter::once(&info.ret)) {
                    let ct = cty(&self.p.tys, t);
                    collect_types(&ct, &mut self.sig_types);
                }
                let args: Vec<String> = args.iter().map(|o| self.operand(o, loc, post).0).collect();
                if ret_is_large(self.p, f) {
                    let t = self.tmp();
                    let ret = ctype(&cty(&self.p.tys, info.ret));
                    let pre = if args.is_empty() { String::new() } else { format!(", {}", args.join(", ")) };
                    let _ =
                        writeln!(self.out, "    {ret} {t}; ({}lust_fns[{}])(&{t}{pre});", fn_ptr_cast(self.p, f), self.slots[f.0 as usize]);
                    t
                } else {
                    format!("({}lust_fns[{}])({})", fn_ptr_cast(self.p, f), self.slots[f.0 as usize], args.join(", "))
                }
            }
            CallTarget::Builtin(b) => self.builtin(b, args, loc, post),
            CallTarget::Intrinsic(id) => self.intrinsic(id, args, loc, post),
        }
    }

    /// Builds one enum or Option value. Most shapes are one compound
    /// literal that designates a single union member (the variant
    /// struct, whose first member is the explicit tag when there is
    /// one). A niche-filled enum's non-niche variants need statements:
    /// zero fill, store the fields, then store the niche tag value.
    /// Field stores come first so they cannot clobber the niche scalar.
    fn make_variant(&mut self, t: &CTy, variant: usize, vals: &[String]) -> String {
        let ct = ctype(t);
        let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
        match c_layout(self.p, t) {
            None => match t {
                CTy::Option(_) => {
                    if vals.is_empty() {
                        format!("(({ct}){{ .tag = 0 }})")
                    } else {
                        format!("(({ct}){{ .tag = 1, .v = {} }})", vals[0])
                    }
                }
                _ => {
                    if fields.is_empty() {
                        format!("(({ct}){{ .tag = {variant} }})")
                    } else {
                        format!("(({ct}){{ .tag = {variant}, .u = {{ .v{variant} = {{ {} }} }} }})", fields.join(", "))
                    }
                }
            },
            Some(l) => match l.enum_tag {
                Some(EnumTag::Explicit { size, signed }) => {
                    let mut init = format!("._tag = {}", disc_lit(adt_discs(self.p, t)[variant], size, signed));
                    if !fields.is_empty() {
                        init.push_str(", ");
                        init.push_str(&fields.join(", "));
                    }
                    format!("(({ct}){{ .u = {{ .v{variant} = {{ {init} }} }} }})")
                }
                Some(EnumTag::NicheFilled { variant: niche_variant, .. }) if variant != niche_variant => {
                    let tmp = self.tmp();
                    let _ = writeln!(self.out, "    {ct} {tmp} = {};", zero_lit(self.p, t));
                    for (i, v) in vals.iter().enumerate() {
                        let f = variant_field(self.p, t, &tmp, variant, i);
                        let _ = writeln!(self.out, "    {f} = {v};");
                    }
                    let set = disc_set(self.p, t, &tmp, variant);
                    if !set.is_empty() {
                        let _ = writeln!(self.out, "    {set}");
                    }
                    tmp
                }
                _ => {
                    if fields.is_empty() {
                        zero_lit(self.p, t)
                    } else {
                        format!("(({ct}){{ .u = {{ .v{variant} = {{ {} }} }} }})", fields.join(", "))
                    }
                }
            },
        }
    }

    fn rvalue(&mut self, rv: &Rvalue, loc: &str, post: &mut Vec<String>) -> String {
        match rv {
            Rvalue::Use(o) => self.operand(o, loc, post).0,
            Rvalue::Ref(_, pl) => {
                let (e, t) = self.place(pl, loc);
                // A slice place (a deref of a fat value, or a bare-slice
                // temporary from a range index) is already the fat value;
                // a place holding a slice reference takes an address as usual.
                let slice_place = matches!(t, CTy::Slice(_))
                    && (matches!(pl.proj.last(), Some(Proj::Deref))
                        || matches!(self.body.tys.kind(self.body.locals[pl.local as usize].ty), TyKind::Slice(_)));
                if t == CTy::Str || slice_place { e } else { format!("(&{e})") }
            }
            Rvalue::SliceOf(pl) => {
                let (e, t) = self.place(pl, loc);
                self.slice_of(&e, &t)
            }
            Rvalue::Subslice { base, lo, hi, inclusive, .. } => {
                let (e, t) = self.place(base, loc);
                let (ptr, len) = self.slice_ptr_len(&e, &t);
                let (lo_v, _) = self.operand(lo, loc, post);
                let ct = match &t {
                    CTy::Array(el, _) | CTy::Slice(el) | CTy::Vec(el) => ctype(&CTy::Slice(el.clone())),
                    _ => "lust_str".into(),
                };
                let (tmp, end) = (self.tmp(), self.tmp());
                let hi_v = match hi {
                    Some(h) => self.operand(h, loc, post).0,
                    None => len.clone(),
                };
                let incl = if *inclusive { 1 } else { 0 };
                let _ = writeln!(self.out, "    uint64_t {end} = lust_slice_range({lo_v}, {hi_v}, {incl}, {len}, {loc});");
                let _ = writeln!(self.out, "    {ct} {tmp} = {{ {ptr} + {lo_v}, {end} - {lo_v} }};");
                tmp
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
                    (UnOp::Not, CTy::Int(i)) if is128(*i) => format!("lust_{}_not({a})", int_fn(*i)),
                    (UnOp::Not, CTy::Int(i)) => format!("(({})~{a})", int_c(*i)),
                    _ => panic!("bad unary op"),
                }
            }
            Rvalue::Cast(o, to) => {
                let (a, from) = self.operand(o, loc, post);
                let to = cty(&self.body.tys, *to);
                // Casts to or from a 128-bit struct value are not C casts.
                match (&from, &to) {
                    (CTy::Int(fi), CTy::Int(ti)) if is128(*fi) && is128(*ti) => {
                        if fi == ti {
                            a
                        } else {
                            format!("lust_{}_from_{}({a})", int_fn(*ti), int_fn(*fi))
                        }
                    }
                    (CTy::Int(fi), _) if is128(*fi) => format!("(({})(({a}).lo))", ctype(&to)),
                    (CTy::Adt(aid), CTy::Int(ti)) => {
                        // A fieldless enum cast to an integer gives its
                        // discriminant value. Layout types store the value
                        // in the tag, so read it back; legacy types store
                        // the variant index, so map index to value.
                        let adt = self.p.adt(*aid);
                        let ct = ctype(&to);
                        let raw = match c_layout(self.p, &from) {
                            Some(l) => match l.enum_tag {
                                Some(EnumTag::Explicit { signed, .. }) => Some((format!("(({a}).u._tag)"), signed)),
                                _ => {
                                    let d = adt.variants.first().map_or(0, |v| v.disc);
                                    Some((disc_lit(d, 8, d < 0), d < 0))
                                }
                            },
                            None => None,
                        };
                        match raw {
                            Some((raw, raw_signed)) => {
                                if is128(*ti) {
                                    if raw_signed {
                                        format!("(({}){{(uint64_t)(int64_t)({raw}), (uint64_t)((int64_t)({raw}) >> 63)}})", int_c(*ti))
                                    } else {
                                        format!("(({}){{(uint64_t)({raw}), 0}})", int_c(*ti))
                                    }
                                } else {
                                    format!("(({ct})({raw}))")
                                }
                            }
                            None => {
                                let t = self.tmp();
                                let zero = if is128(*ti) { "{0, 0}" } else { "0" };
                                let _ = write!(self.out, "    {ct} {t} = {zero};\n    switch ({a}.tag) {{");
                                for (vi, v) in adt.variants.iter().enumerate() {
                                    let lit = if is128(*ti) {
                                        let bits = v.disc as u128;
                                        format!("(({ct}){{{}ULL, {}ULL}})", bits as u64, (bits >> 64) as u64)
                                    } else if v.disc < 0 {
                                        format!("(({ct})((int64_t){}))", v.disc)
                                    } else {
                                        format!("(({ct})((uint64_t){}ull))", v.disc as u128)
                                    };
                                    let _ = write!(self.out, " case {vi}: {t} = {lit}; break;");
                                }
                                let _ = writeln!(self.out, " }}");
                                t
                            }
                        }
                    }
                    (_, CTy::Int(ti)) if is128(*ti) => {
                        let signed = matches!(&from, CTy::Int(si) if si.signed());
                        if signed {
                            format!("(({}){{(uint64_t)(int64_t)({a}), (uint64_t)((int64_t)({a}) >> 63)}})", int_c(*ti))
                        } else {
                            format!("(({}){{(uint64_t)({a}), 0}})", int_c(*ti))
                        }
                    }
                    _ => format!("(({}){a})", ctype(&to)),
                }
            }
            Rvalue::Opt(ty, op) => {
                let t = cty(&self.body.tys, *ty);
                match op {
                    Some(o) => {
                        let (v, _) = self.operand(o, loc, post);
                        self.make_variant(&t, 1, &[v])
                    }
                    None => self.make_variant(&t, 0, &[]),
                }
            }
            Rvalue::Aggregate(a, v, ops) => {
                let adt = self.p.adt(*a);
                let vals: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                if adt.is_enum {
                    self.make_variant(&CTy::Adt(*a), *v as usize, &vals)
                } else if vals.is_empty() {
                    zero_lit(self.p, &CTy::Adt(*a))
                } else {
                    let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                    format!("((A{}){{ {} }})", a.0, fields.join(", "))
                }
            }
            Rvalue::VecLit(elem, ops) => {
                let et = ctype(&cty(&self.body.tys, *elem));
                let t = self.tmp();
                let _ = writeln!(self.out, "    lust_Vec {t} = lust_vec_with_capacity({}, sizeof({et}), _Alignof({et}));", ops.len());
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
                let _ = writeln!(self.out, "    lust_Vec {t} = lust_vec_with_capacity({i}_n, sizeof({et}), _Alignof({et}));");
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
            Rvalue::Eq { a, b, ty, ne } => {
                let (a, at) = self.operand(a, loc, post);
                let (b, bt) = self.operand(b, loc, post);
                // A slice operand is already the fat value (not a pointer to
                // it), so take its address for the glue call.
                let a = if matches!(at, CTy::Slice(_)) { format!("(&{a})") } else { a };
                let b = if matches!(bt, CTy::Slice(_)) { format!("(&{b})") } else { b };
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
            Rvalue::TupleAgg(ty, ops) => {
                let t = cty(&self.body.tys, *ty);
                let ct = ctype(&t);
                let vals: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                if vals.is_empty() {
                    zero_lit(self.p, &t)
                } else {
                    let fields: Vec<String> = vals.iter().enumerate().map(|(i, v)| format!(".f{i} = {v}")).collect();
                    format!("(({ct}){{ {} }})", fields.join(", "))
                }
            }
            Rvalue::ArrayAgg(ty, ops) => {
                let t = cty(&self.body.tys, *ty);
                let ct = ctype(&t);
                let vals: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
                if vals.is_empty() { zero_lit(self.p, &t) } else { format!("(({ct}){{ .v = {{ {} }} }})", vals.join(", ")) }
            }
            Rvalue::ArrayRepeat(ty, o, n) => {
                let at = cty(&self.body.tys, *ty);
                let ct = ctype(&at);
                let et = match &at {
                    CTy::Array(e, _) => ctype(e),
                    _ => "uint8_t".into(),
                };
                let (v, _) = self.operand(o, loc, post);
                let (t, xt, i) = (self.tmp(), self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {et} {xt} = {v};\n    {ct} {t};");
                let _ = writeln!(self.out, "    for (uint64_t {i} = 0; {i} < {n}; {i}++) {t}.v[{i}] = {xt};");
                t
            }
            Rvalue::Format(parts) => self.format(parts, loc, post),
            Rvalue::Discriminant(pl) => {
                let (e, t) = self.place(pl, loc);
                disc_call(self.p, &t, &format!("(&{e})"))
            }
            Rvalue::StaticLoad(idx) => format!("lust_static_{idx}"),
            Rvalue::StaticRef(idx) => format!("(&lust_static_{idx})"),
            Rvalue::LenOf(pl) => {
                let (e, t) = self.place(pl, loc);
                match &t {
                    CTy::Array(_, n) => n.to_string(),
                    CTy::Slice(_) | CTy::Vec(_) | CTy::String | CTy::Str => format!("{e}.len"),
                    CTy::Ref(inner) if **inner == CTy::Str => format!("{e}.len"),
                    _ => format!("({e})->len"),
                }
            }
        }
    }

    fn bin(&mut self, op: BinOp, a: &str, at: &CTy, b: &str, bt: &CTy, loc: &str) -> String {
        use BinOp::*;
        // 128-bit values are C structs: no C operators apply, so every
        // operation is a runtime helper call.
        if let CTy::Int(i) = at
            && is128(*i)
        {
            let f = int_fn(*i);
            if op.is_cmp() {
                return format!("(lust_{f}_cmp({a}, {b}) {} 0)", op.symbol());
            }
            return match op {
                Add => format!("lust_add_{f}({a}, {b}, {loc})"),
                Sub => format!("lust_sub_{f}({a}, {b}, {loc})"),
                Mul => format!("lust_mul_{f}({a}, {b}, {loc})"),
                Div => format!("lust_div_{f}({a}, {b}, {loc})"),
                Rem => format!("lust_rem_{f}({a}, {b}, {loc})"),
                BitAnd => format!("lust_{f}_and({a}, {b})"),
                BitOr => format!("lust_{f}_or({a}, {b})"),
                BitXor => format!("lust_{f}_xor({a}, {b})"),
                Shl | Shr => {
                    let amount = match bt {
                        CTy::Int(bi) if is128(*bi) => format!("({b}).lo"),
                        CTy::Int(bi) if bi.signed() => format!("(uint64_t)(int64_t)({b})"),
                        _ => format!("(uint64_t)({b})"),
                    };
                    let dir = if op == Shl { "left" } else { "right" };
                    let sh = format!("lust_shift_amount({amount}, 128, \"{dir}\", {loc})");
                    let how = if op == Shl { "shl" } else { "shr" };
                    format!("lust_{f}_{how}({a}, {sh})")
                }
                _ => unreachable!(),
            };
        }
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
                            CTy::Int(bi) if is128(*bi) => format!("({b}).lo"),
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
    /// The data pointer and length C expressions of an array, Vec, or slice place.
    fn slice_ptr_len(&self, e: &str, t: &CTy) -> (String, String) {
        match t {
            CTy::Array(_, n) => (format!("{e}.v"), n.to_string()),
            CTy::Vec(el) => (format!("(({}*){e}.ptr)", ctype(el)), format!("{e}.len")),
            CTy::Slice(_) => (format!("{e}.ptr"), format!("{e}.len")),
            _ => (format!("(({e}))"), "0".into()),
        }
    }

    /// A fat slice value over the whole of an array, Vec, or slice place.
    fn slice_of(&mut self, e: &str, t: &CTy) -> String {
        match t {
            CTy::Slice(_) => e.to_string(),
            CTy::Array(el, _) | CTy::Vec(el) => {
                let ct = ctype(&CTy::Slice(el.clone()));
                let (ptr, len) = self.slice_ptr_len(e, t);
                format!("(({ct}){{ {ptr}, {len} }})")
            }
            _ => e.to_string(),
        }
    }

    fn eq_expr(&mut self, t: &CTy, a: &str, b: &str) -> String {
        match t {
            CTy::Unit => "1".into(),
            CTy::Int(i) if is128(*i) => format!("({a}->lo == {b}->lo && {a}->hi == {b}->hi)"),
            CTy::Bool | CTy::Char | CTy::Int(_) => format!("(*{a} == *{b})"),
            _ => {
                self.want(Glue::Eq, t);
                format!("eq_{}({a}, {b})", mangle(t))
            }
        }
    }

    /// Emits one intrinsic call as a plain runtime call (section 3.2: no
    /// IR node per family, codegen emits the C call direct). This is the
    /// second privilege line behind check: an intrinsic that reaches
    /// codegen from a crate its registry row does not allow is a
    /// compiler bug, so it stops here instead of emitting the call.
    fn intrinsic(&mut self, id: u32, ops: &[Operand], loc: &str, post: &mut Vec<String>) -> String {
        let def = lang::intrinsic(id);
        let krate = self.p.fn_shipped_crate(self.body.fn_id);
        assert!(
            def.allows(krate),
            "internal: intrinsic `core::intrinsics::{}` reached codegen from a crate that may not call it",
            def.name
        );
        assert!(def.implemented, "internal: intrinsic `core::intrinsics::{}` reached codegen with no body", def.name);
        let args: Vec<String> = ops.iter().map(|o| self.operand(o, loc, post).0).collect();
        if def.ret == SigTy::Never {
            // The C callee never returns (its C type is void). The comma
            // form still gives the assignment a value of the right shape
            // for the dead continuation.
            format!("({}({}), 0)", def.c_symbol, args.join(", "))
        } else {
            format!("{}({})", def.c_symbol, args.join(", "))
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
            B::SliceLen => match &tys[0] {
                CTy::Slice(_) => format!("{}.len", vals[0]),
                CTy::Ref(inner) => match &**inner {
                    CTy::Array(_, n) => n.to_string(),
                    CTy::Slice(_) => format!("{}.len", vals[0]),
                    _ => format!("({})->len", vals[0]),
                },
                _ => format!("{}.len", vals[0]),
            },
            B::SliceIsEmpty => match &tys[0] {
                CTy::Slice(_) => format!("({}.len == 0)", vals[0]),
                CTy::Ref(inner) => match &**inner {
                    CTy::Array(_, n) => format!("({n} == 0)"),
                    CTy::Slice(_) => format!("({}.len == 0)", vals[0]),
                    _ => format!("(({})->len == 0)", vals[0]),
                },
                _ => format!("({}.len == 0)", vals[0]),
            },
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
                let _ = writeln!(self.out, "    *({et}*)lust_vec_push_slot({}, sizeof({et}), _Alignof({et})) = {t};", vals[0]);
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
                let it = int_of(&tys[0]);
                if is128(it) {
                    let f = int_fn(it);
                    let how = match b {
                        B::WrappingAdd => "add",
                        B::WrappingSub => "sub",
                        _ => "mul",
                    };
                    format!("lust_{f}_{how}({}, {})", vals[0], vals[1])
                } else {
                    let c = int_c(it);
                    let op = match b {
                        B::WrappingAdd => "+",
                        B::WrappingSub => "-",
                        _ => "*",
                    };
                    format!("(({c})((uint64_t)({}) {op} (uint64_t)({})))", vals[0], vals[1])
                }
            }
            B::Abs => format!("lust_abs_{}({}, {loc})", int_fn(int_of(&tys[0])), vals[0]),
            B::Pow => format!("lust_pow_{}({}, {}, {loc})", int_fn(int_of(&tys[0])), vals[0], vals[1]),
            B::Min | B::Max => {
                let it = int_of(&tys[0]);
                if is128(it) {
                    let f = int_fn(it);
                    let rel = if b == B::Min { "<" } else { ">" };
                    format!("(lust_{f}_cmp({0}, {1}) {rel} 0 ? {0} : {1})", vals[0], vals[1])
                } else if b == B::Min {
                    format!("({0} < {1} ? {0} : {1})", vals[0], vals[1])
                } else {
                    format!("({0} > {1} ? {0} : {1})", vals[0], vals[1])
                }
            }
            B::OptIsSome | B::OptIsNone => {
                let ot = match &tys[0] {
                    CTy::Ref(inner) => (**inner).clone(),
                    t => t.clone(),
                };
                let want = if b == B::OptIsSome { 1 } else { 0 };
                format!("({} == {want})", disc_call(self.p, &ot, &vals[0]))
            }
            B::OptUnwrap | B::OptExpect => {
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t} = {};", ctype(&tys[0]), vals[0]);
                let disc = disc_call(self.p, &tys[0], &format!("(&{t})"));
                if b == B::OptUnwrap {
                    let _ = writeln!(self.out, "    if (!{disc}) lust_panic_cstr(\"called `Option::unwrap()` on a `None` value\", {loc});");
                } else {
                    let _ = writeln!(self.out, "    if (!{disc}) lust_panic_str({}, {loc});", vals[1]);
                }
                variant_field(self.p, &tys[0], &t, 1, 0)
            }
            B::OptUnwrapOr => {
                let CTy::Option(inner) = &tys[0] else { unreachable!() };
                let (t, d) = (self.tmp(), self.tmp());
                let _ = writeln!(self.out, "    {} {t} = {};\n    {} {d} = {};", ctype(&tys[0]), vals[0], ctype(inner), vals[1]);
                let disc = disc_call(self.p, &tys[0], &format!("(&{t})"));
                if needs_drop_c(self.p, inner) {
                    // The unused default is dropped, as in Rust.
                    self.want(Glue::Drop, inner);
                    let _ = writeln!(self.out, "    if ({disc}) drop_{}(&{d});", mangle(inner));
                }
                format!("({disc} ? {} : {d})", variant_field(self.p, &tys[0], &t, 1, 0))
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
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    if ({cond}) {{ {field} = {r}(({et}*){v}->ptr)[{idx}];{some} }}");
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
                let _ = writeln!(
                    self.out,
                    "    lust_vec_insert_at({vv}, {i}, sizeof({et}), _Alignof({et}), {loc});\n    (({et}*){vv}->ptr)[{i}] = {x};"
                );
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
                let opt = CTy::Option(Box::new(CTy::Char));
                let ot = ctype(&opt);
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ =
                    writeln!(self.out, "    if ({it}->pos < {it}->s.len) {{ {field} = lust_utf8_next({it}->s.ptr, &{it}->pos);{some} }}");
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
                let opt = CTy::Option(Box::new(CTy::Int(IntTy::U32)));
                let ot = ctype(&opt);
                let t = self.tmp();
                let field = variant_field(self.p, &opt, &t, 1, 0);
                let some = disc_set(self.p, &opt, &t, 1);
                let some = if some.is_empty() { String::new() } else { format!(" {some}") };
                let _ = writeln!(self.out, "    {ot} {t}; {}", disc_set(self.p, &opt, &t, 0));
                let _ = writeln!(
                    self.out,
                    "    {{ uint32_t d = lust_digit({}, {}, {loc}); if (d != 0xFFFFFFFFu) {{ {field} = d;{some} }} }}",
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
            (CTy::Int(i), _) if is128(*i) => format!("lust_fmt_{}(&{out}, {e});", int_fn(*i)),
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
// fixed groups of slots. Grouping depends only on the slot count, so an edit that keeps the
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

/// The full runtime source, assembled from `src/runtime/`: runtime.h first, then core.c
/// with its `#include` lines replaced by the included text (panic.c inline; float.h and
/// hash.h at the end). Units compile from strings, so file includes cannot read files;
/// declaration units get float.h's prototypes only (`with_impls` false),
/// the runtime unit gets float.c's and hash.c's bodies too. The runtime stays one
/// amalgamated unit (see `runtime_unit`), so the split files are source fragments, not
/// separate translation units, and the includes are also what a plain C compiler
/// follows when a test harness includes runtime.h and core.c directly. The panic
/// include sits where the panic section belonged in the old single runtime.c: after
/// the string helpers it calls, before the checked math that calls it.
fn runtime_source(with_impls: bool) -> String {
    let header = include_str!("runtime/float.h");
    let header = if with_impls {
        let body = include_str!("runtime/float.c").replacen("#include \"ryu_tables.h\"", include_str!("runtime/ryu_tables.h"), 1);
        header.replacen("#include \"float.c\"", &body, 1)
    } else {
        header.replacen("#include \"float.c\"", "", 1)
    };
    // The hash core's declarations are not in the common unit header:
    // they cost about 26 KB of C per unit and no generated code calls
    // the core yet. The runtime unit carries header plus bodies, so
    // the symbols link; a unit whose code calls the core adds
    // `hash_decls()` to its header.
    let hash = if with_impls { hash_source(true) } else { String::new() };
    let core = include_str!("runtime/core.c").replacen("#include \"escape_table.h\"", include_str!("runtime/escape_table.h"), 1);
    let (h, core, panic) = (include_str!("runtime/runtime.h"), core.as_str(), include_str!("runtime/panic.c"));
    let mut src = String::with_capacity(h.len() + core.len() + panic.len() + header.len() + hash.len());
    src.push_str(h);
    src.push_str(core);
    let src = src.replacen("#include \"panic.c\"\n", panic, 1);
    let src = src.replacen("#include \"float.h\"", &header, 1);
    src.replacen("#include \"hash.h\"", &hash, 1)
}

/// Removes C comments, replacing each with one space (the C meaning of a
/// comment). String and char literals pass through untouched. The
/// runtime header is about a third comments by bytes, and every unit
/// would otherwise make tcc lex them again.
fn strip_c_comments(src: &str) -> String {
    let b = src.as_bytes();
    let mut out = String::with_capacity(src.len());
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b'"' | b'\'' => {
                let quote = b[i];
                let start = i;
                i += 1;
                while i < b.len() && b[i] != quote {
                    i += if b[i] == b'\\' { 2 } else { 1 };
                }
                i = (i + 1).min(b.len());
                out.push_str(&src[start..i]);
            }
            b'/' if i + 1 < b.len() && b[i + 1] == b'*' => {
                i += 2;
                while i + 1 < b.len() && !(b[i] == b'*' && b[i + 1] == b'/') {
                    i += 1;
                }
                i = (i + 2).min(b.len());
                out.push(' ');
            }
            b'/' if i + 1 < b.len() && b[i + 1] == b'/' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
                out.push(' ');
            }
            _ => {
                let start = i;
                while i < b.len() && b[i] != b'"' && b[i] != b'\'' && b[i] != b'/' {
                    i += 1;
                }
                if i == start {
                    i += 1;
                    out.push('/');
                } else {
                    out.push_str(&src[start..i]);
                }
            }
        }
    }
    out
}

/// The runtime without function bodies: `LUST_BODY(...)` regions are cut out once, so units do
/// not make tcc tokenize code that would expand to nothing.
fn runtime_decls() -> &'static str {
    static DECLS: std::sync::OnceLock<String> = std::sync::OnceLock::new();
    DECLS.get_or_init(|| {
        let src = runtime_source(false);
        let mut out = String::with_capacity(src.len() / 2);
        let mut rest = src.as_str();
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
        strip_c_comments(&out.replacen(
            "#include <stdint.h>\n#include <stddef.h>\n",
            "typedef signed char int8_t; typedef unsigned char uint8_t; typedef short int16_t; typedef unsigned short uint16_t;\ntypedef int int32_t; typedef unsigned int uint32_t;\n#ifdef __INT64_TYPE__\ntypedef __INT64_TYPE__ int64_t; typedef unsigned __INT64_TYPE__ uint64_t;\n#else\ntypedef long long int64_t; typedef unsigned long long uint64_t;\n#endif\n#ifdef __SIZE_TYPE__\ntypedef __SIZE_TYPE__ size_t; typedef __PTRDIFF_TYPE__ ptrdiff_t; typedef __UINTPTR_TYPE__ uintptr_t; typedef __INTPTR_TYPE__ intptr_t;\n#else\ntypedef unsigned long size_t; typedef long ptrdiff_t; typedef unsigned long uintptr_t; typedef long intptr_t;\n#endif\n#define INT64_MIN (-9223372036854775807LL-1)\n#ifndef NULL\n#define NULL ((void*)0)\n#endif\n",
            1,
        ))
    })
}

/// The hash core text for splicing: hash.h, with hash.c inlined when
/// `with_bodies`. hash.h includes <stddef.h>/<stdint.h> for direct
/// inclusion by test harnesses; spliced copies drop both lines because
/// runtime.h already provided the types, and declaration units must
/// not re-read the system headers (see `runtime_decls`).
fn hash_source(with_bodies: bool) -> String {
    let hash = include_str!("runtime/hash.h").replacen("#include <stddef.h>\n#include <stdint.h>\n", "", 1);
    if with_bodies {
        hash.replacen("#include \"hash.c\"", include_str!("runtime/hash.c"), 1)
    } else {
        hash.replacen("#include \"hash.c\"", "", 1)
    }
}

/// Declarations for the erased hash core, for the header of a unit
/// whose generated code calls it (the std typed layer, when it lands).
/// Not part of the common unit header; see `runtime_source`.
#[allow(dead_code)]
pub fn hash_decls() -> String {
    hash_source(false)
}

/// The unit with the runtime's function definitions. It only changes when lust itself does.
pub fn runtime_unit() -> String {
    format!("#define LUST_IMPL 1\n{}", runtime_source(true))
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
    for st in &p.statics {
        collect_types(&cty(&p.tys, st.ty), &mut types);
    }
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
        c.push_str(&static_defs(p));
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
    c.push_str(&static_defs(p));
    c
}

/// The C initializer for one const value at the given C type. Referenced
/// aggregates are promoted to file-scope constants first, written to `pre`.
fn const_init(p: &Program, v: &crate::ty::consteval::ConstValue, t: &CTy, pre: &mut String, counter: &mut u32) -> String {
    use crate::ty::consteval::ConstValue as CV;
    match (v, t) {
        (CV::Int(i), CTy::Int(it)) => {
            if *i < 0 {
                format!("(({})((int64_t){i}))", int_c(*it))
            } else {
                format!("(({})((uint64_t){}ull))", int_c(*it), *i as u128)
            }
        }
        (CV::Bool(b), _) => (*b as u8).to_string(),
        (CV::Char(c), _) => format!("((uint32_t){})", *c as u32),
        (CV::Unit, _) => "0".into(),
        (CV::Str(i), _) => {
            let s = &p.ast.strings[*i as usize];
            format!("((lust_str){{(uint8_t*){}, {}}})", c_string_lit(s.as_bytes()), s.len())
        }
        (CV::StaticRef(idx), CTy::Slice(_)) => {
            let st = &p.statics[*idx as usize];
            let sct = cty(&p.tys, st.ty);
            match sct {
                CTy::Array(_, n) => format!("(({}){{ lust_static_{idx}.v, {n} }})", ctype(t)),
                _ => format!("(({}){{0}})", ctype(t)),
            }
        }
        (CV::StaticRef(idx), _) => format!("(&lust_static_{idx})"),
        (CV::Ref(inner), CTy::Slice(el)) => {
            // A slice over a promoted aggregate.
            match &**inner {
                CV::Aggregate(vals) => {
                    let at = CTy::Array(el.clone(), vals.len() as u64);
                    let init = const_init(p, inner, &at, pre, counter);
                    *counter += 1;
                    let name = format!("lust_promoted_{counter}");
                    let _ = writeln!(pre, "static const {} {name} = {init};", ctype(&at));
                    format!("(({}){{ {name}.v, {} }})", ctype(t), vals.len())
                }
                _ => format!("(({}){{0}})", ctype(t)),
            }
        }
        (CV::Ref(inner), CTy::Ref(inner_ct)) => {
            let init = const_init(p, inner, inner_ct, pre, counter);
            *counter += 1;
            let name = format!("lust_promoted_{counter}");
            let _ = writeln!(pre, "static const {} {name} = {init};", ctype(inner_ct));
            format!("(&{name})")
        }
        (CV::Aggregate(vals), CTy::Tuple(es)) => {
            if vals.is_empty() {
                format!("(({}){{0}})", ctype(t))
            } else {
                let parts: Vec<String> =
                    vals.iter().enumerate().map(|(i, x)| format!(".f{i} = {}", const_init(p, x, &es[i], pre, counter))).collect();
                format!("(({}){{ {} }})", ctype(t), parts.join(", "))
            }
        }
        (CV::Aggregate(vals), CTy::Array(e, _)) => {
            if vals.is_empty() {
                format!("(({}){{0}})", ctype(t))
            } else {
                let parts: Vec<String> = vals.iter().map(|x| const_init(p, x, e, pre, counter)).collect();
                format!("(({}){{ .v = {{ {} }} }})", ctype(t), parts.join(", "))
            }
        }
        (CV::Repeat(x, n), CTy::Array(e, _)) => {
            if *n == 0 {
                format!("(({}){{0}})", ctype(t))
            } else {
                let one = const_init(p, x, e, pre, counter);
                let parts: Vec<String> = (0..*n).map(|_| one.clone()).collect();
                format!("(({}){{ .v = {{ {} }} }})", ctype(t), parts.join(", "))
            }
        }
        (CV::Aggregate(vals), CTy::Adt(a)) => {
            let adt = p.adt(*a);
            if vals.is_empty() {
                format!("((A{}){{0}})", a.0)
            } else {
                let parts: Vec<String> = vals
                    .iter()
                    .enumerate()
                    .map(|(i, x)| format!(".f{i} = {}", const_init(p, x, &cty(&p.tys, adt.variants[0].fields[i].ty), pre, counter)))
                    .collect();
                format!("((A{}){{ {} }})", a.0, parts.join(", "))
            }
        }
        (CV::Variant(variant, vals), CTy::Adt(a)) => {
            let adt = p.adt(*a);
            if vals.is_empty() {
                format!("((A{}){{ .tag = {variant} }})", a.0)
            } else {
                let parts: Vec<String> = vals
                    .iter()
                    .enumerate()
                    .map(|(i, x)| {
                        format!(".f{i} = {}", const_init(p, x, &cty(&p.tys, adt.variants[*variant as usize].fields[i].ty), pre, counter))
                    })
                    .collect();
                format!("((A{}){{ .tag = {variant}, .u = {{ .v{variant} = {{ {} }} }} }})", a.0, parts.join(", "))
            }
        }
        (CV::Variant(variant, vals), CTy::Option(e)) => {
            let ct = ctype(t);
            if *variant == 1 && !vals.is_empty() {
                format!("(({ct}){{ .tag = 1, .v = {} }})", const_init(p, &vals[0], e, pre, counter))
            } else {
                format!("(({ct}){{ .tag = 0 }})")
            }
        }
        (CV::Aggregate(vals), CTy::Slice(e)) => {
            let at = CTy::Array(e.clone(), vals.len() as u64);
            let init = const_init(p, v, &at, pre, counter);
            *counter += 1;
            let name = format!("lust_promoted_{counter}");
            let _ = writeln!(pre, "static const {} {name} = {init};", ctype(&at));
            format!("(({}){{ {name}.v, {} }})", ctype(t), vals.len())
        }
        _ => format!("(({}){{0}})", ctype(t)),
    }
}

/// Definitions of the program's statics as C globals (ARCH 2.13 static data).
fn static_defs(p: &Program) -> String {
    let mut pre = String::new();
    let mut out = String::new();
    let mut counter = 0u32;
    for (i, st) in p.statics.iter().enumerate() {
        let ct = cty(&p.tys, st.ty);
        let init = const_init(p, &st.value, &ct, &mut pre, &mut counter);
        let _ = writeln!(out, "{} lust_static_{i} = {init};", ctype(&ct));
    }
    format!("{pre}{out}")
}

/// Extern declarations of the statics, for function units.
fn static_decls(p: &Program) -> String {
    let mut out = String::new();
    for (i, st) in p.statics.iter().enumerate() {
        let _ = writeln!(out, "extern {} lust_static_{i};", ctype(&cty(&p.tys, st.ty)));
    }
    out
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
    for st in &p.statics {
        collect_types(&cty(&p.tys, st.ty), &mut types);
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
    c.push_str(&static_decls(p));
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

/// The members of one C struct for fields at layout offsets: fields in
/// offset order with explicit padding byte arrays between them, so the
/// C offsets equal the layout offsets no matter what the C compiler
/// would pick on its own. `fields` holds (declaration, field layout,
/// offset) per field; `total` pads to the full size when given.
fn layout_members(fields: &[(String, Layout, u64)], total: Option<u64>, struct_align: u64) -> String {
    let mut order: Vec<usize> = (0..fields.len()).collect();
    order.sort_by(|&a, &b| fields[a].2.cmp(&fields[b].2).then(fields[b].1.align.cmp(&fields[a].1.align)).then(a.cmp(&b)));
    let mut members: Vec<String> = Vec::new();
    let mut cur = 0u64;
    let mut pad = 0u32;
    for &i in &order {
        let (decl, fl, off) = &fields[i];
        if *off > cur {
            members.push(format!("uint8_t _p{pad}[{}]", off - cur));
            pad += 1;
            cur = *off;
        }
        members.push(decl.clone());
        cur = cur.max(off + fl.size);
    }
    if let Some(sz) = total
        && sz > cur
    {
        members.push(format!("uint8_t _p{pad}[{}]", sz - cur));
    }
    let natural = fields.iter().map(|f| f.1.align).max().unwrap_or(1);
    if struct_align > natural && !members.is_empty() {
        members[0] = format!("_Alignas({struct_align}) {}", members[0]);
    }
    members.iter().map(|m| format!("{m}; ")).collect()
}

/// The compile-time layout proof for one emitted type: the C sizeof and
/// _Alignof must equal the layout the type was emitted from.
fn layout_assert(out: &mut String, ct: &str, l: &Layout) {
    let _ = writeln!(out, "_Static_assert(sizeof({ct}) == {} && _Alignof({ct}) == {}, \"layout\");", l.size, l.align);
}

/// One field's layout for `layout_members`, for a parent whose own
/// `c_layout` is already exact. A miss here means the parent check and
/// this one disagree; size 0 keeps the C layout assert as the failure.
fn field_layout(p: &Program, t: &CTy) -> Layout {
    c_layout(p, t).unwrap_or_else(|| plain_layout(0, 1))
}

/// Emits one layout-exact enum type (an Adt enum or an Option) plus its
/// `disc_<mangle>` reader. The shape is one union: a struct per variant
/// with fields at their absolute layout offsets, the tag scalar or a
/// niche view struct, and a size member that pins the total size and
/// alignment. `opener` is the declaration up to the opening brace.
fn emit_enum_decl(p: &Program, out: &mut String, opener: &str, t: &CTy, variants: &[Vec<CTy>], l: &Layout) {
    let ct = ctype(t);
    let _ = write!(out, "{opener} {{ union {{ ");
    // An explicit tag also appears as the first member of every variant
    // struct, so a value can be built with one compound literal that
    // designates a single union member (see `make_variant`).
    let explicit = match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => Some((size, signed)),
        _ => None,
    };
    for (vi, v) in variants.iter().enumerate() {
        if v.is_empty() && explicit.is_none() {
            continue;
        }
        let mut fields: Vec<(String, Layout, u64)> = Vec::new();
        if let Some((size, signed)) = explicit {
            fields.push((format!("{} _tag", tag_c_type(size, signed)), plain_layout(size, size), 0));
        }
        fields
            .extend(v.iter().enumerate().map(|(fi, ft)| (format!("{} f{fi}", ctype(ft)), field_layout(p, ft), l.variant_offsets[vi][fi])));
        let _ = write!(out, "struct {{ {}}} v{vi}; ", layout_members(&fields, None, 1));
    }
    match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => {
            let _ = write!(out, "{} _tag; ", tag_c_type(size, signed));
        }
        Some(EnumTag::NicheFilled { niche: Niche { offset, scalar_size, .. }, .. }) => {
            let pad = if offset > 0 { format!("uint8_t _p[{offset}]; ") } else { String::new() };
            let _ = write!(out, "struct {{ {pad}{} _s; }} _n; ", tag_c_type(scalar_size, false));
        }
        _ => {}
    }
    if l.size > 0 {
        let al = if l.align > 1 { format!("_Alignas({}) ", l.align) } else { String::new() };
        let _ = write!(out, "{al}uint8_t _size[{}]; ", l.size);
    }
    out.push_str("} u; }");
    if opener.starts_with("typedef") {
        let _ = write!(out, " {ct}");
    }
    out.push_str(";\n");
    layout_assert(out, &ct, l);
    let m = mangle(t);
    match l.enum_tag {
        Some(EnumTag::Explicit { size, signed }) => {
            let discs = adt_discs(p, t);
            if !discs_sequential(&discs) {
                let _ = write!(out, "static inline uint32_t disc_{m}(const {ct} *p) {{ switch (p->u._tag) {{");
                for (vi, &d) in discs.iter().enumerate() {
                    let _ = write!(out, " case {}: return {vi};", disc_lit(d, size, signed));
                }
                let _ = writeln!(out, " default: return 0; }} }}");
            }
        }
        Some(EnumTag::NicheFilled { variant, niche }) => {
            let others: Vec<usize> = (0..variants.len()).filter(|&i| i != variant).collect();
            let start = niche.start as u64;
            let ret = if others.len() == 1 {
                format!("return {};", others[0])
            } else {
                let map: Vec<String> = others.iter().map(|i| i.to_string()).collect();
                format!("static const uint32_t map[{}] = {{{}}}; return map[s - {start}ULL];", others.len(), map.join(","))
            };
            let _ = writeln!(
                out,
                "static inline uint32_t disc_{m}(const {ct} *p) {{ uint64_t s = p->u._n._s; if (s >= {start}ULL && s < {}ULL) {{ {ret} }} return {variant}; }}",
                start + others.len() as u64
            );
        }
        _ => {}
    }
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
            CTy::Tuple(es) => es.iter().for_each(|e| collect_types(e, &mut inner)),
            CTy::Array(e, _) => collect_types(e, &mut inner),
            CTy::Slice(e) => collect_types(e, &mut inner),
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
            CTy::Tuple(es) => es.iter().for_each(|e| by_value_deps(e, &mut deps)),
            CTy::Array(e, _) => by_value_deps(e, &mut deps),
            CTy::Slice(e) => by_value_deps(e, &mut deps),
            _ => {}
        }
        for d in &deps {
            emit(p, d, emitted, out);
        }
        match t {
            CTy::Option(e) => match c_layout(p, t) {
                Some(l) => emit_enum_decl(p, out, &format!("typedef struct {}", ctype(t)), t, &[vec![], vec![(**e).clone()]], &l),
                None => {
                    let _ = writeln!(out, "typedef struct {0} {{ uint32_t tag; {1} v; }} {0};", ctype(t), ctype(e));
                }
            },
            CTy::Tuple(es) => match c_layout(p, t) {
                Some(l) => {
                    let ct = ctype(t);
                    if es.is_empty() {
                        let _ = writeln!(out, "typedef struct {ct} {{ }} {ct};");
                    } else {
                        let fields: Vec<(String, Layout, u64)> = es
                            .iter()
                            .enumerate()
                            .map(|(i, e)| (format!("{} f{i}", ctype(e)), field_layout(p, e), l.field_offsets[i]))
                            .collect();
                        let _ = writeln!(out, "typedef struct {ct} {{ {}}} {ct};", layout_members(&fields, Some(l.size), l.align));
                    }
                    layout_assert(out, &ct, &l);
                }
                None => {
                    let fields: String = es.iter().enumerate().map(|(i, e)| format!("{} f{i}; ", ctype(e))).collect();
                    let fields = if fields.is_empty() { "uint8_t unused; ".to_string() } else { fields };
                    let _ = writeln!(out, "typedef struct {0} {{ {fields}}} {0};", ctype(t));
                }
            },
            CTy::Array(e, n) => match c_layout(p, t) {
                Some(l) => {
                    let ct = ctype(t);
                    let _ = writeln!(out, "typedef struct {ct} {{ {} v[{n}]; }} {ct};", ctype(e));
                    layout_assert(out, &ct, &l);
                }
                None => {
                    let _ = writeln!(out, "typedef struct {0} {{ {1} v[{2}]; }} {0};", ctype(t), ctype(e), (*n).max(1));
                }
            },
            CTy::Slice(e) => {
                let _ = writeln!(out, "typedef struct {0} {{ {1}* ptr; uint64_t len; }} {0};", ctype(t), ctype(e));
                if let Some(l) = c_layout(p, t) {
                    layout_assert(out, &ctype(t), &l);
                }
            }
            CTy::Adt(a) => {
                let adt = p.adt(*a);
                let an = a.0;
                let _ = writeln!(out, "/* {} */", p.name(adt.name));
                let packed = adt.repr.kind == ReprKind::Packed;
                if packed {
                    out.push_str("#pragma pack(push, 1)\n");
                }
                let layout = c_layout(p, t);
                if adt.is_enum {
                    match layout {
                        Some(l) => {
                            let variants: Vec<Vec<CTy>> =
                                adt.variants.iter().map(|v| v.fields.iter().map(|f| cty(&p.tys, f.ty)).collect()).collect();
                            emit_enum_decl(p, out, &format!("struct A{an}"), t, &variants, &l);
                        }
                        None => {
                            let fields = |v: &Variant| -> String {
                                v.fields.iter().enumerate().map(|(i, f)| format!("{} f{i}; ", ctype(&cty(&p.tys, f.ty)))).collect()
                            };
                            let _ = write!(out, "struct A{an} {{ uint32_t tag; ");
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
                        }
                    }
                } else {
                    match layout {
                        Some(l) => {
                            let v = &adt.variants[0];
                            if v.fields.is_empty() && l.align > 1 {
                                let _ = writeln!(out, "struct A{an} {{ _Alignas({}) uint8_t _z[0]; }};", l.align);
                            } else if v.fields.is_empty() {
                                let _ = writeln!(out, "struct A{an} {{ }};");
                            } else {
                                let fields: Vec<(String, Layout, u64)> = v
                                    .fields
                                    .iter()
                                    .enumerate()
                                    .map(|(i, f)| {
                                        let ft = cty(&p.tys, f.ty);
                                        (format!("{} f{i}", ctype(&ft)), field_layout(p, &ft), l.field_offsets[i])
                                    })
                                    .collect();
                                let _ = writeln!(out, "struct A{an} {{ {}}};", layout_members(&fields, Some(l.size), l.align));
                            }
                            layout_assert(out, &format!("A{an}"), &l);
                        }
                        None => {
                            let f: String = adt.variants[0]
                                .fields
                                .iter()
                                .enumerate()
                                .map(|(i, f)| format!("{} f{i}; ", ctype(&cty(&p.tys, f.ty))))
                                .collect();
                            let f = if f.is_empty() { "uint8_t unused; ".to_string() } else { f };
                            let _ = writeln!(out, "struct A{an} {{ {f}}};");
                        }
                    }
                }
                if packed {
                    out.push_str("#pragma pack(pop)\n");
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
    // Discriminant reads and the Option payload access for the enum
    // shaped glue arms below (unused strings for other shapes).
    let disc_p = disc_call(p, t, "p");
    let pf = variant_field(p, t, "(*p)", 1, 0);
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
                    // A zero-sized element never allocates; its pointer is
                    // the dangling aligned address, not a heap block.
                    if c_layout(p, e).is_none_or(|l| l.size > 0) {
                        body.push_str("  free(p->ptr);\n");
                    }
                }
                CTy::Option(e) => {
                    need(Glue::Drop, e);
                    let _ = writeln!(body, "  if ({disc_p}) drop_{}(&{pf});", mangle(e));
                }
                CTy::Tuple(es) => {
                    for (fi, ft) in es.iter().enumerate() {
                        if needs_drop_c(p, ft) {
                            need(Glue::Drop, ft);
                            let _ = writeln!(body, "  drop_{}(&p->f{fi});", mangle(ft));
                        }
                    }
                }
                CTy::Array(e, n) => {
                    if needs_drop_c(p, e) {
                        need(Glue::Drop, e);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < {n}; i++) drop_{}(&p->v[i]);", mangle(e));
                    }
                }
                CTy::Adt(a) => {
                    let adt = p.adt(*a);
                    if adt.is_enum {
                        let _ = writeln!(body, "  switch ({disc_p}) {{");
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
                    let c = clone_of(e, &pf, &mut need);
                    let rf = variant_field(p, t, "r", 1, 0);
                    let _ = writeln!(body, "  {ct} r = *p;\n  if ({disc_p}) {rf} = {c};\n  return r;");
                }
                CTy::Tuple(es) => {
                    let _ = writeln!(body, "  {ct} r = *p;");
                    for (fi, ft) in es.iter().enumerate() {
                        if !is_copy_c(p, ft) {
                            let c = clone_of(ft, &format!("p->f{fi}"), &mut need);
                            let _ = writeln!(body, "  r.f{fi} = {c};");
                        }
                    }
                    body.push_str("  return r;\n");
                }
                CTy::Array(e, n) => {
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if !is_copy_c(p, e) {
                        let c = clone_of(e, "p->v[i]", &mut need);
                        let _ = writeln!(body, "  for (uint64_t i = 0; i < {n}; i++) r.v[i] = {c};");
                    }
                    body.push_str("  return r;\n");
                }
                CTy::Vec(e) => {
                    let et = ctype(e);
                    let _ = writeln!(body, "  lust_Vec r = lust_vec_with_capacity(p->len, sizeof({et}), _Alignof({et}));");
                    let c = clone_of(e, &format!("(({et}*)p->ptr)[i]"), &mut need);
                    let _ =
                        writeln!(body, "  for (uint64_t i = 0; i < p->len; i++) (({et}*)r.ptr)[i] = {c};\n  r.len = p->len;\n  return r;");
                }
                CTy::Adt(a) => {
                    let adt = p.adt(*a);
                    let _ = writeln!(body, "  {ct} r = *p;");
                    if adt.is_enum {
                        let _ = writeln!(body, "  switch ({disc_p}) {{");
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
                    CTy::Int(i) if is128(*i) => format!("(({x}).lo == ({y}).lo && ({x}).hi == ({y}).hi)"),
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
                    let (af, bf) = (variant_field(p, t, "(*a)", 1, 0), variant_field(p, t, "(*b)", 1, 0));
                    let c = eq_of(e, &af, &bf, &mut need);
                    let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                    let _ = writeln!(body, "  return {da} == {db} && (!{da} || {c});");
                }
                CTy::Tuple(es) => {
                    for (fi, ft) in es.iter().enumerate() {
                        let c = eq_of(ft, &format!("a->f{fi}"), &format!("b->f{fi}"), &mut need);
                        let _ = writeln!(body, "  if (!{c}) return 0;");
                    }
                    body.push_str("  return 1;\n");
                }
                CTy::Array(e, n) => {
                    let c = eq_of(e, "a->v[i]", "b->v[i]", &mut need);
                    let _ = writeln!(body, "  for (uint64_t i = 0; i < {n}; i++) if (!{c}) return 0;\n  return 1;");
                }
                CTy::Slice(e) => {
                    let c = eq_of(e, "a->ptr[i]", "b->ptr[i]", &mut need);
                    let _ = writeln!(
                        body,
                        "  if (a->len != b->len) return 0;\n  for (uint64_t i = 0; i < a->len; i++) if (!{c}) return 0;\n  return 1;"
                    );
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
                        let (da, db) = (disc_call(p, t, "a"), disc_call(p, t, "b"));
                        let _ = writeln!(body, "  if ({da} != {db}) return 0;\n  switch ({da}) {{");
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
                    CTy::Int(i) if is128(*i) => format!("lust_fmt_{}(out, {e});", int_fn(*i)),
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
                    let e = dbg_of(inner, &pf, &mut need);
                    let _ = writeln!(body, "  if ({disc_p}) {{ {} {e} {} }} else {}", lit("Some("), lit(")"), lit("None"));
                }
                CTy::Tuple(es) => {
                    let mut s = lit("(");
                    for (fi, ft) in es.iter().enumerate() {
                        if fi > 0 {
                            s.push_str(&lit(", "));
                        }
                        s.push_str(&dbg_of(ft, &format!("p->f{fi}"), &mut need));
                    }
                    if es.len() == 1 {
                        s.push_str(&lit(","));
                    }
                    s.push_str(&lit(")"));
                    let _ = writeln!(body, "  {s}");
                }
                CTy::Array(e, n) => {
                    let d = dbg_of(e, "p->v[i]", &mut need);
                    let _ = writeln!(
                        body,
                        "  {}\n  for (uint64_t i = 0; i < {n}; i++) {{ if (i) {} {d} }}\n  {}",
                        lit("["),
                        lit(", "),
                        lit("]")
                    );
                }
                CTy::Slice(e) => {
                    let d = dbg_of(e, "p->ptr[i]", &mut need);
                    let _ = writeln!(
                        body,
                        "  {}\n  for (uint64_t i = 0; i < p->len; i++) {{ if (i) {} {d} }}\n  {}",
                        lit("["),
                        lit(", "),
                        lit("]")
                    );
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
                        let _ = writeln!(body, "  switch ({disc_p}) {{");
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

fn place_mentions(p: &Place, l: Local) -> bool {
    p.local == l || p.proj.iter().any(|x| matches!(x, Proj::Index(i) if *i == l))
}

fn operand_mentions(o: &Operand, l: Local) -> bool {
    matches!(o, Operand::Copy(p) | Operand::Move(p) if place_mentions(p, l))
}

fn rvalue_mentions(rv: &Rvalue, l: Local) -> bool {
    let op_has = |o: &Operand| operand_mentions(o, l);
    let parts_has = |ps: &[FmtPart]| ps.iter().any(|p| matches!(p, FmtPart::Arg { value, .. } if op_has(value)));
    match rv {
        Rvalue::Use(o) | Rvalue::Un(_, o) | Rvalue::Cast(o, _) => op_has(o),
        Rvalue::Ref(_, p) | Rvalue::Discriminant(p) | Rvalue::SliceOf(p) | Rvalue::LenOf(p) => place_mentions(p, l),
        Rvalue::StaticLoad(_) | Rvalue::StaticRef(_) => false,
        Rvalue::Subslice { base, lo, hi, .. } => place_mentions(base, l) || op_has(lo) || hi.as_ref().is_some_and(op_has),
        Rvalue::Bin(_, a, b) | Rvalue::StrCmp(_, a, b) | Rvalue::StringAdd(a, b) | Rvalue::VecRepeat(_, a, b) | Rvalue::Eq { a, b, .. } => {
            op_has(a) || op_has(b)
        }
        Rvalue::Aggregate(_, _, ops) | Rvalue::VecLit(_, ops) | Rvalue::TupleAgg(_, ops) | Rvalue::ArrayAgg(_, ops) => {
            ops.iter().any(op_has)
        }
        Rvalue::ArrayRepeat(_, o, _) => op_has(o),
        Rvalue::Opt(_, o) => o.as_ref().is_some_and(op_has),
        Rvalue::Format(parts) => parts_has(parts),
    }
}

fn succ(t: &Terminator) -> Vec<Bb> {
    match t {
        Terminator::Goto(b) => vec![*b],
        Terminator::If(_, a, b) => vec![*a, *b],
        Terminator::Switch(_, cases, other) => cases.iter().map(|c| c.1).chain(std::iter::once(*other)).collect(),
        Terminator::Call { next, unwind, .. } => std::iter::once(*next).chain(*unwind).collect(),
        _ => Vec::new(),
    }
}
