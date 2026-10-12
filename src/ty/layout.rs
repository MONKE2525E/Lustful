// The layout engine (docs/ARCH.md section 4.4). One engine computes size, align,
// field offsets, enum tag placement, and the niche for every sized type lust
// accepts. A type outside the supported-shape grammar of 4.4 returns `Err(())`;
// the caller turns that into L0652. The engine never guesses a size.
//
// The core functions work on field `Layout`s, so the standalone gate test can
// build the real nested Type/TypeData field graph directly (4.4). `layout_of_ty`
// is the adapter from semantic `Ty` to those functions; it reads Adt shapes
// through the `AdtShapes` trait so this file does not depend on collect's tables.
#![allow(dead_code)] // Wired into size_of/align_of by check and into codegen by W-CGEN.

use super::{AdtId, BuiltinTy, FloatTy, IntTy, Ty, TyIntern, TyKind};

/// A niche: a scalar range inside a type whose unused values can hold enum tags
/// of an outer type. `free` counts the usable values; they start at `start`
/// (the first value in the niche scalar's bit pattern that is not a valid value
/// of the scalar, following rustc's valid-range model).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Niche {
    pub offset: u64,
    /// Width of the niche scalar in bytes.
    pub scalar_size: u64,
    pub free: u128,
    pub start: u128,
}

/// How an enum stores its discriminant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnumTag {
    /// One variant only: no tag is stored.
    None,
    /// A tag scalar at offset 0 with this width in bytes.
    Explicit { size: u64, signed: bool },
    /// The discriminant lives in the niche of the named variant; the other
    /// variants take successive niche values from `niche.start`, in order.
    NicheFilled { variant: usize, niche: Niche },
}

/// The layout of one sized type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Layout {
    pub size: u64,
    pub align: u64,
    /// Field offsets for a struct or tuple, in declaration order. For an enum,
    /// the offsets of each variant's fields, in declaration order per variant.
    pub field_offsets: Vec<u64>,
    pub variant_offsets: Vec<Vec<u64>>,
    pub niche: Option<Niche>,
    pub enum_tag: Option<EnumTag>,
}

impl Layout {
    /// A plain scalar or aggregate layout with no field or tag detail.
    fn simple(size: u64, align: u64, niche: Option<Niche>) -> Layout {
        Layout { size, align, field_offsets: Vec::new(), variant_offsets: Vec::new(), niche, enum_tag: None }
    }
}

/// The `repr` of an Adt, in layout terms. `packed` means `repr(packed)` or
/// `repr(packed(1))`; any other packed bound is outside the grammar.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Repr {
    pub kind: ReprKind,
    /// A fixed integer tag (`repr(u8)` and kin): width in bits and signedness.
    pub int: Option<(u32, bool)>,
    /// `repr(align(n))`.
    pub align: Option<u64>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ReprKind {
    #[default]
    Default,
    C,
    Transparent,
    Packed,
}

impl Repr {
    /// True when the repr fixes the enum tag, so the niche-filled candidate is off.
    fn fixes_tag(&self) -> bool {
        self.int.is_some() || self.kind != ReprKind::Default
    }
}

fn align_up(v: u64, align: u64) -> u64 {
    if align <= 1 { v } else { v.div_ceil(align) * align }
}

/// The layout of an integer scalar.
pub fn int_layout(t: IntTy) -> Layout {
    let size = (t.bits() / 8) as u64;
    Layout::simple(size, size, None)
}

/// The layout of a float scalar.
pub fn float_layout(t: FloatTy) -> Layout {
    match t {
        FloatTy::F32 => Layout::simple(4, 4, None),
        FloatTy::F64 => Layout::simple(8, 8, None),
    }
}

/// `bool`: one byte; values 2 to 255 are free.
pub fn bool_layout() -> Layout {
    Layout::simple(1, 1, Some(Niche { offset: 0, scalar_size: 1, free: 254, start: 2 }))
}

/// `char`: four bytes; values above 0x10FFFF are free for niche purposes
/// (rustc models the valid range as 0..=0x10FFFF here).
pub fn char_layout() -> Layout {
    Layout::simple(4, 4, Some(Niche { offset: 0, scalar_size: 4, free: (1u128 << 32) - 0x110000, start: 0x110000 }))
}

/// A non-null thin pointer scalar (`&T`, `Box<T>`, a fn pointer): null is free.
pub fn ptr_layout() -> Layout {
    Layout::simple(8, 8, Some(Niche { offset: 0, scalar_size: 8, free: 1, start: 0 }))
}

/// A raw pointer: may be null, so no niche.
pub fn raw_ptr_layout() -> Layout {
    Layout::simple(8, 8, None)
}

/// A fat pointer (slice, str, or dyn reference): the data word keeps the
/// non-null niche.
pub fn fat_ptr_layout() -> Layout {
    Layout::simple(16, 8, Some(Niche { offset: 0, scalar_size: 8, free: 1, start: 0 }))
}

/// A zero-sized type with the given alignment.
pub fn zst_layout(align: u64) -> Layout {
    Layout::simple(0, align.max(1), None)
}

/// A `NonZero` integer scalar: zero is free.
pub fn nonzero_layout(t: IntTy) -> Layout {
    let mut l = int_layout(t);
    l.niche = Some(Niche { offset: 0, scalar_size: l.size, free: 1, start: 0 });
    l
}

/// The layout of `[elem; len]`. A one-element array keeps the element niche.
pub fn array_layout(elem: &Layout, len: u64) -> Result<Layout, ()> {
    let size = elem.size.checked_mul(len).ok_or(())?;
    let niche = if len == 1 { elem.niche } else { None };
    Ok(Layout::simple(size, elem.align, niche))
}

/// Places fields in the given order with normal padding. Returns size before
/// the final round-up and the offsets in placement order.
fn place_in_order(fields: &[Layout], order: &[usize]) -> (u64, Vec<u64>) {
    let mut offsets = vec![0u64; fields.len()];
    let mut cur = 0u64;
    for &i in order {
        cur = align_up(cur, fields[i].align);
        offsets[i] = cur;
        cur += fields[i].size;
    }
    (cur, offsets)
}

/// The niche a struct-like aggregate reports: the field niche with the most
/// free values, at that field's offset; ties go to the first field in layout
/// (placement) order.
fn best_niche(fields: &[Layout], offsets: &[u64], order: &[usize]) -> Option<Niche> {
    let mut best: Option<Niche> = None;
    for &i in order {
        if let Some(n) = fields[i].niche {
            let cand = Niche { offset: offsets[i] + n.offset, ..n };
            if best.is_none_or(|b| cand.free > b.free) {
                best = Some(cand);
            }
        }
    }
    best
}

/// The layout of a struct or tuple with the given field layouts and repr.
pub fn struct_layout(fields: &[Layout], repr: Repr) -> Result<Layout, ()> {
    match repr.kind {
        ReprKind::Transparent => {
            let mut out = zst_layout(fields.iter().map(|f| f.align).max().unwrap_or(1));
            for f in fields {
                if f.size > 0 {
                    out = f.clone();
                    break;
                }
            }
            out.field_offsets = vec![0; fields.len()];
            return finish(out, repr);
        }
        ReprKind::Packed => {
            let mut offsets = Vec::with_capacity(fields.len());
            let mut cur = 0u64;
            for f in fields {
                offsets.push(cur);
                cur += f.size;
            }
            let order: Vec<usize> = (0..fields.len()).collect();
            let niche = best_niche(fields, &offsets, &order);
            let mut out = Layout::simple(cur, 1, niche);
            out.field_offsets = offsets;
            return finish(out, repr);
        }
        ReprKind::C => {
            let order: Vec<usize> = (0..fields.len()).collect();
            let (end, offsets) = place_in_order(fields, &order);
            let align = fields.iter().map(|f| f.align).max().unwrap_or(1);
            let niche = best_niche(fields, &offsets, &order);
            let mut out = Layout::simple(align_up(end, align), align, niche);
            out.field_offsets = offsets;
            return finish(out, repr);
        }
        ReprKind::Default => {}
    }
    // repr(Rust): largest alignment first, then largest size, then declaration order.
    let mut order: Vec<usize> = (0..fields.len()).collect();
    order.sort_by(|&a, &b| fields[b].align.cmp(&fields[a].align).then(fields[b].size.cmp(&fields[a].size)).then(a.cmp(&b)));
    let (end, offsets) = place_in_order(fields, &order);
    let align = fields.iter().map(|f| f.align).max().unwrap_or(1);
    let niche = best_niche(fields, &offsets, &order);
    let mut out = Layout::simple(align_up(end, align), align, niche);
    out.field_offsets = offsets;
    finish(out, repr)
}

/// The smallest tag width in bytes (1, 2, 4, 8, 16) whose range holds every
/// discriminant. Signedness is signed when any discriminant is negative.
fn tag_width(discs: &[i128]) -> Result<(u64, bool), ()> {
    let signed = discs.iter().any(|&d| d < 0);
    for w in [1u64, 2, 4, 8, 16] {
        let bits = w * 8;
        let (lo, hi): (i128, i128) = if signed {
            if bits >= 128 { (i128::MIN, i128::MAX) } else { (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1) }
        } else if bits >= 128 {
            (0, i128::MAX)
        } else {
            (0, (1i128 << bits) - 1)
        };
        if discs.iter().all(|&d| d >= lo && d <= hi) {
            return Ok((w, signed));
        }
    }
    Err(())
}

/// Free values and first free value of an explicit tag scalar, under rustc's
/// valid-range model: valid values are the contiguous range from the smallest
/// to the largest discriminant, read as bit patterns of the tag width.
fn tag_niche(width: u64, discs: &[i128]) -> Option<Niche> {
    if discs.is_empty() {
        return None;
    }
    let bits = width * 8;
    let total: u128 = if bits >= 128 { u128::MAX } else { 1u128 << bits };
    let mask: u128 = if bits >= 128 { u128::MAX } else { (1u128 << bits) - 1 };
    let lo = (*discs.iter().min().unwrap() as u128) & mask;
    let hi = (*discs.iter().max().unwrap() as u128) & mask;
    // Discriminants that wrap the signed range edge make the valid range
    // non-contiguous in bit order; report no niche rather than a wrong one.
    if hi < lo {
        return None;
    }
    let valid = hi - lo + 1;
    let free = total.saturating_sub(valid);
    if free == 0 {
        return None;
    }
    Some(Niche { offset: 0, scalar_size: width, free, start: (hi + 1) & mask })
}

/// One variant laid out as a struct that starts with a tag of `tag_w` bytes:
/// tag first, then fields by smallest alignment first, ties in declaration
/// order (the tagged-enum rule of 4.4). Returns (end, align, field offsets).
fn tagged_variant(fields: &[Layout], tag_w: u64) -> (u64, u64, Vec<u64>) {
    let mut order: Vec<usize> = (0..fields.len()).collect();
    order.sort_by(|&a, &b| fields[a].align.cmp(&fields[b].align).then(a.cmp(&b)));
    let mut offsets = vec![0u64; fields.len()];
    let mut cur = tag_w;
    let mut align = tag_w.max(1);
    for &i in &order {
        align = align.max(fields[i].align);
        cur = align_up(cur, fields[i].align);
        offsets[i] = cur;
        cur += fields[i].size;
    }
    (cur, align, offsets)
}

/// Tries to place `fields` inside `size` bytes without using the niche scalar
/// bytes. Greedy first-fit in declaration order at each field's alignment.
fn fits_outside_niche(fields: &[Layout], size: u64, niche: Niche) -> Option<Vec<u64>> {
    let n_lo = niche.offset;
    let n_hi = niche.offset + niche.scalar_size;
    let mut placed: Vec<(u64, u64)> = vec![(n_lo, n_hi)];
    let mut offsets = Vec::with_capacity(fields.len());
    for f in fields {
        if f.size == 0 {
            offsets.push(0);
            continue;
        }
        let mut at = 0u64;
        loop {
            at = align_up(at, f.align);
            if at + f.size > size {
                return None;
            }
            let clash = placed.iter().find(|&&(lo, hi)| at < hi && lo < at + f.size).map(|&(_, hi)| hi);
            match clash {
                Some(hi) => at = hi,
                None => break,
            }
        }
        placed.push((at, at + f.size));
        offsets.push(at);
    }
    Some(offsets)
}

/// The layout of an enum. `variants` holds each variant's field layouts in
/// declaration order; `discs` holds the discriminant of each variant.
pub fn enum_layout(variants: &[Vec<Layout>], discs: &[i128], repr: Repr) -> Result<Layout, ()> {
    if variants.is_empty() {
        return finish(zst_layout(1), repr);
    }
    if discs.len() != variants.len() {
        return Err(());
    }
    if repr.kind == ReprKind::Transparent {
        return Err(());
    }
    // A fixed integer tag must hold every discriminant.
    if let Some((bits, signed)) = repr.int {
        let (lo, hi): (i128, i128) = if signed {
            if bits >= 128 { (i128::MIN, i128::MAX) } else { (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1) }
        } else if bits >= 128 {
            (0, i128::MAX)
        } else {
            (0, (1i128 << bits) - 1)
        };
        if !discs.iter().all(|&d| d >= lo && d <= hi) {
            return Err(());
        }
    }
    // One variant under the default repr is just its fields as a plain struct.
    if variants.len() == 1 && !repr.fixes_tag() {
        let mut l = struct_layout(&variants[0], Repr::default())?;
        l.variant_offsets = vec![l.field_offsets.clone()];
        l.enum_tag = Some(EnumTag::None);
        return finish(l, repr);
    }
    let tagged = tagged_enum_layout(variants, discs, repr)?;
    if repr.fixes_tag() {
        return Ok(tagged);
    }
    match niche_enum_layout(variants, discs, repr) {
        Some(niche) => {
            let pick_niche = niche.size < tagged.size
                || (niche.size == tagged.size && niche.niche.map_or(0, |n| n.free) > tagged.niche.map_or(0, |n| n.free));
            Ok(if pick_niche { niche } else { tagged })
        }
        None => Ok(tagged),
    }
}

/// The tagged candidate layout (and the only candidate when the repr fixes the tag).
fn tagged_enum_layout(variants: &[Vec<Layout>], discs: &[i128], repr: Repr) -> Result<Layout, ()> {
    let (mut tag_w, signed) = if let Some((bits, signed)) = repr.int {
        ((bits / 8) as u64, signed)
    } else if repr.kind == ReprKind::C {
        (4, true)
    } else {
        tag_width(discs)?
    };
    let fieldless = variants.iter().all(|v| v.is_empty());
    if fieldless {
        let mut l = Layout::simple(tag_w, tag_w, tag_niche(tag_w, discs));
        l.variant_offsets = variants.iter().map(|_| Vec::new()).collect();
        l.enum_tag = Some(EnumTag::Explicit { size: tag_w, signed });
        return finish(l, repr);
    }
    if repr.kind == ReprKind::Packed {
        // Tag first, then fields in declaration order, no padding anywhere.
        let mut size = 0u64;
        let mut variant_offsets = Vec::new();
        for v in variants {
            let mut cur = tag_w;
            let mut offs = Vec::new();
            for f in v {
                offs.push(cur);
                cur += f.size;
            }
            size = size.max(cur);
            variant_offsets.push(offs);
        }
        let mut l = Layout::simple(size, 1, tag_niche(tag_w, discs));
        l.variant_offsets = variant_offsets;
        l.enum_tag = Some(EnumTag::Explicit { size: tag_w, signed });
        return finish(l, repr);
    }
    let fixed = repr.int.is_some() || repr.kind == ReprKind::C;
    let layout_with = |tag_w: u64| -> (u64, u64, Vec<Vec<u64>>) {
        let mut size = 0u64;
        let mut align = tag_w.max(1);
        let mut variant_offsets = Vec::new();
        for v in variants {
            let (end, a, offs) = if fixed {
                // repr(int) and repr(C) keep declaration order after the tag.
                let mut offs = vec![0u64; v.len()];
                let mut cur = tag_w;
                let mut a = tag_w.max(1);
                for (i, f) in v.iter().enumerate() {
                    a = a.max(f.align);
                    cur = align_up(cur, f.align);
                    offs[i] = cur;
                    cur += f.size;
                }
                (cur, a, offs)
            } else {
                tagged_variant(v, tag_w)
            };
            align = align.max(a);
            size = size.max(align_up(end, a));
            variant_offsets.push(offs);
        }
        (align_up(size, align), align, variant_offsets)
    };
    let (size, align, mut variant_offsets) = layout_with(tag_w);
    if repr.int.is_none() && repr.kind == ReprKind::Default {
        // Widen the tag into the padding every variant leaves after it. The
        // size does not change; the enum's own niche grows.
        let mut min_gap: Option<u64> = None;
        for (v, offs) in variants.iter().zip(&variant_offsets) {
            if v.is_empty() {
                continue;
            }
            let first = offs.iter().copied().min().unwrap_or(tag_w);
            min_gap = Some(min_gap.map_or(first, |g: u64| g.min(first)));
        }
        if let Some(gap) = min_gap {
            for w in [16u64, 8, 4, 2, 1] {
                if w > tag_w && w <= gap {
                    let (s2, _, _) = layout_with(w);
                    if s2 == size {
                        tag_w = w;
                    }
                    break;
                }
            }
        }
        if tag_w > 0 {
            let (_, _, offs) = layout_with(tag_w);
            variant_offsets = offs;
        }
    }
    let mut l = Layout::simple(size, align, tag_niche(tag_w, discs));
    l.variant_offsets = variant_offsets;
    l.enum_tag = Some(EnumTag::Explicit { size: tag_w, signed });
    finish(l, repr)
}

/// The niche-filled candidate layout, when one exists.
fn niche_enum_layout(variants: &[Vec<Layout>], discs: &[i128], repr: Repr) -> Option<Layout> {
    let _ = discs;
    // The niche variant is the largest data-carrying variant as a plain struct.
    let mut cand: Option<(usize, Layout)> = None;
    for (i, v) in variants.iter().enumerate() {
        if v.is_empty() {
            continue;
        }
        let l = struct_layout(v, Repr::default()).ok()?;
        if cand.as_ref().is_none_or(|(_, c)| l.size > c.size) {
            cand = Some((i, l));
        }
    }
    let (vi, base) = cand?;
    let niche = base.niche?;
    let others = (variants.len() - 1) as u128;
    if niche.free < others {
        return None;
    }
    let mut variant_offsets: Vec<Vec<u64>> = Vec::with_capacity(variants.len());
    for (i, v) in variants.iter().enumerate() {
        if i == vi {
            variant_offsets.push(base.field_offsets.clone());
        } else {
            if v.iter().any(|f| f.align > base.align && f.size > 0) {
                return None;
            }
            variant_offsets.push(fits_outside_niche(v, base.size, niche)?);
        }
    }
    let remaining = niche.free - others;
    let mut l = Layout::simple(
        base.size,
        base.align,
        if remaining > 0 { Some(Niche { free: remaining, start: niche.start + others, ..niche }) } else { None },
    );
    l.variant_offsets = variant_offsets;
    l.enum_tag = Some(EnumTag::NicheFilled { variant: vi, niche });
    finish(l, repr).ok()
}

/// Applies `repr(align(n))` and the final size round-up.
fn finish(mut l: Layout, repr: Repr) -> Result<Layout, ()> {
    if let Some(a) = repr.align {
        if a == 0 || !a.is_power_of_two() {
            return Err(());
        }
        if a > l.align {
            l.align = a;
            l.size = align_up(l.size, a);
        }
    }
    Ok(l)
}

/// The shape of one Adt for layout: its repr, each variant's field types in
/// declaration order, and each variant's discriminant. A struct has one variant.
pub struct AdtShape {
    pub repr: Repr,
    pub is_enum: bool,
    pub variants: Vec<Vec<Ty>>,
    pub discs: Vec<i128>,
}

/// Adt shapes by session-local id, supplied by collect's tables.
pub trait AdtShapes {
    fn adt_shape(&self, id: AdtId) -> Option<AdtShape>;
}

/// The layout of a semantic type. `Err(())` means the type is outside the
/// supported-shape grammar of 4.4 (unsized, a generic parameter, an unknown
/// Adt such as `Box` before its wave, a user union, and so on).
pub fn layout_of_ty(tys: &impl TyIntern, shapes: &impl AdtShapes, t: Ty) -> Result<Layout, ()> {
    let mut memo: Vec<(Ty, Option<Layout>)> = Vec::new();
    let mut active: Vec<Ty> = Vec::new();
    go(tys, shapes, t, &mut memo, &mut active)
}

fn go(
    tys: &impl TyIntern,
    shapes: &impl AdtShapes,
    t: Ty,
    memo: &mut Vec<(Ty, Option<Layout>)>,
    active: &mut Vec<Ty>,
) -> Result<Layout, ()> {
    if let Some((_, l)) = memo.iter().find(|(m, _)| *m == t) {
        return l.clone().ok_or(());
    }
    if active.contains(&t) {
        return Err(()); // Recursive type without indirection: collect rejects it first.
    }
    active.push(t);
    let r = compute(tys, shapes, t, memo, active);
    active.pop();
    memo.push((t, r.as_ref().ok().cloned()));
    r
}

fn compute(
    tys: &impl TyIntern,
    shapes: &impl AdtShapes,
    t: Ty,
    memo: &mut Vec<(Ty, Option<Layout>)>,
    active: &mut Vec<Ty>,
) -> Result<Layout, ()> {
    match tys.kind(t) {
        TyKind::Unit | TyKind::Never => Ok(zst_layout(1)),
        TyKind::Bool => Ok(bool_layout()),
        TyKind::Char => Ok(char_layout()),
        TyKind::Int(i) => Ok(int_layout(i)),
        TyKind::Float(f) => Ok(float_layout(f)),
        TyKind::Ref(_, _, e) => match tys.kind(e) {
            TyKind::Slice(_) | TyKind::Str | TyKind::Dyn(..) => Ok(fat_ptr_layout()),
            _ => Ok(ptr_layout()),
        },
        TyKind::RawPtr(_, _) => Ok(raw_ptr_layout()),
        TyKind::FnPtr(_) => Ok(ptr_layout()),
        TyKind::FnDef(..) => Ok(zst_layout(1)),
        TyKind::Array(e, c) => {
            let len = match tys.const_kind(c) {
                super::ConstKind::Int(n) => u64::try_from(n).map_err(|_| ())?,
                _ => return Err(()),
            };
            let el = go(tys, shapes, e, memo, active)?;
            array_layout(&el, len)
        }
        TyKind::Tuple(ts) => {
            let elems: Vec<Ty> = tys.tys_of(ts).to_vec();
            let mut fields = Vec::with_capacity(elems.len());
            for e in elems {
                fields.push(go(tys, shapes, e, memo, active)?);
            }
            struct_layout(&fields, Repr::default())
        }
        TyKind::Adt(..) => match tys.builtin_of(t) {
            // String and Vec are (ptr, len, cap) words in this order for layout.
            Some(BuiltinTy::String) | Some(BuiltinTy::Vec) => {
                struct_layout(&[ptr_layout(), int_layout(IntTy::Usize), int_layout(IntTy::Usize)], Repr::default())
            }
            Some(BuiltinTy::Option) => {
                let e = tys.adt_first_ty_arg(t).ok_or(())?;
                let el = go(tys, shapes, e, memo, active)?;
                enum_layout(&[vec![], vec![el]], &[0, 1], Repr::default())
            }
            Some(_) => Err(()),
            None => {
                let id = tys.local_adt(t).ok_or(())?;
                let shape = shapes.adt_shape(id).ok_or(())?;
                // Generic Adts reach layout only after substitution; an Adt
                // with type arguments has no shape entry yet in this wave.
                if !tys.args(tys.adt_parts(t).map(|p| p.1).ok_or(())?).is_empty() {
                    return Err(());
                }
                let mut variants = Vec::with_capacity(shape.variants.len());
                for v in &shape.variants {
                    let mut fields = Vec::with_capacity(v.len());
                    for &f in v {
                        fields.push(go(tys, shapes, f, memo, active)?);
                    }
                    variants.push(fields);
                }
                if shape.is_enum {
                    enum_layout(&variants, &shape.discs, shape.repr)
                } else {
                    struct_layout(&variants.into_iter().next().unwrap_or_default(), shape.repr)
                }
            }
        },
        _ => Err(()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ints(ts: &[IntTy]) -> Vec<Layout> {
        ts.iter().map(|&t| int_layout(t)).collect()
    }
    fn sz(l: &Layout) -> (u64, u64) {
        (l.size, l.align)
    }

    #[test]
    fn scalars() {
        assert_eq!(sz(&bool_layout()), (1, 1));
        assert_eq!(sz(&char_layout()), (4, 4));
        assert_eq!(sz(&int_layout(IntTy::U128)), (16, 16));
        assert_eq!(sz(&int_layout(IntTy::I128)), (16, 16));
        assert_eq!(sz(&float_layout(FloatTy::F32)), (4, 4));
        assert_eq!(sz(&float_layout(FloatTy::F64)), (8, 8));
        assert_eq!(sz(&ptr_layout()), (8, 8));
        assert_eq!(sz(&fat_ptr_layout()), (16, 8));
    }

    #[test]
    fn rust_struct_reorder() {
        // struct S { a: u8, b: u64, c: u8 } is 16, not 24.
        let l = struct_layout(&ints(&[IntTy::U8, IntTy::U64, IntTy::U8]), Repr::default()).unwrap();
        assert_eq!(sz(&l), (16, 8));
        assert_eq!(l.field_offsets, vec![8, 0, 9]);
        // The same fields under repr(C) keep declaration order: 24.
        let c = struct_layout(&ints(&[IntTy::U8, IntTy::U64, IntTy::U8]), Repr { kind: ReprKind::C, ..Repr::default() }).unwrap();
        assert_eq!(sz(&c), (24, 8));
        assert_eq!(c.field_offsets, vec![0, 8, 16]);
        // repr(packed): no padding, align 1.
        let p = struct_layout(&ints(&[IntTy::U8, IntTy::U64, IntTy::U8]), Repr { kind: ReprKind::Packed, ..Repr::default() }).unwrap();
        assert_eq!(sz(&p), (10, 1));
    }

    #[test]
    fn pinned_tagged_enums() {
        // enum { A(u8, u32), B } is 8: tag, u8, padding, u32.
        let l = enum_layout(&[ints(&[IntTy::U8, IntTy::U32]), vec![]], &[0, 1], Repr::default()).unwrap();
        assert_eq!(sz(&l), (8, 4));
        // Variant (u16, [u8; 3]) gives a 6-byte enum.
        let arr3 = array_layout(&int_layout(IntTy::U8), 3).unwrap();
        let l = enum_layout(&[vec![int_layout(IntTy::U16), arr3], vec![]], &[0, 1], Repr::default()).unwrap();
        assert_eq!(l.size, 6);
        // Variants (u8, u64, u8) and (u32, u64) give 16 each.
        let l = enum_layout(&[ints(&[IntTy::U8, IntTy::U64, IntTy::U8])], &[0], Repr::default()).unwrap();
        assert_eq!(l.size, 16);
        let l = enum_layout(&[ints(&[IntTy::U32, IntTy::U64]), vec![]], &[0, 1], Repr::default()).unwrap();
        assert_eq!(l.size, 16);
        // TypeMapper-like: Array(Box, bool) variant gives 16 (tag, bool, pad, Box).
        let l = enum_layout(&[vec![ptr_layout(), bool_layout()], vec![]], &[0, 1], Repr::default()).unwrap();
        assert_eq!(sz(&l), (16, 8));
    }

    #[test]
    fn pinned_niche_enums() {
        // Option<&u8> is 8; Option<bool> is 1.
        let l = enum_layout(&[vec![], vec![ptr_layout()]], &[0, 1], Repr::default()).unwrap();
        assert_eq!(sz(&l), (8, 8));
        assert!(matches!(l.enum_tag, Some(EnumTag::NicheFilled { .. })));
        let l = enum_layout(&[vec![], vec![bool_layout()]], &[0, 1], Repr::default()).unwrap();
        assert_eq!(l.size, 1);
        // Pointer(Byte) does not niche-fill: the u8 has nowhere to sit. 16.
        let l = enum_layout(&[vec![ptr_layout()], ints(&[IntTy::U8])], &[0, 1], Repr::default()).unwrap();
        assert_eq!(sz(&l), (16, 8));
        // repr(u8) and repr(C) turn the niche candidate off: 16 each.
        let l = enum_layout(&[vec![ptr_layout()], vec![]], &[0, 1], Repr { int: Some((8, false)), ..Repr::default() }).unwrap();
        assert_eq!(l.size, 16);
        let l = enum_layout(&[vec![ptr_layout()], vec![]], &[0, 1], Repr { kind: ReprKind::C, ..Repr::default() }).unwrap();
        assert_eq!(l.size, 16);
    }

    #[test]
    fn most_free_values_niche() {
        // Payload { pointer: &u8, flag: bool } reports the bool niche (254 free),
        // so Data(Payload) plus two empty variants stays 16.
        let payload = struct_layout(&[ptr_layout(), bool_layout()], Repr::default()).unwrap();
        assert_eq!(payload.size, 16);
        assert_eq!(payload.niche.map(|n| n.free), Some(254));
        let l = enum_layout(&[vec![payload], vec![], vec![]], &[0, 1, 2], Repr::default()).unwrap();
        assert_eq!(l.size, 16);
        // Option<Option<S>> for S { a: bool, b: &u8 } is 16.
        let s = struct_layout(&[bool_layout(), ptr_layout()], Repr::default()).unwrap();
        let one = enum_layout(&[vec![], vec![s]], &[0, 1], Repr::default()).unwrap();
        let two = enum_layout(&[vec![], vec![one]], &[0, 1], Repr::default()).unwrap();
        assert_eq!(two.size, 16);
    }

    #[test]
    fn tag_widening_and_discriminants() {
        // enum { A(u32), B(u32) } under three nested Options stays 8.
        let e = enum_layout(&[ints(&[IntTy::U32]), ints(&[IntTy::U32])], &[0, 1], Repr::default()).unwrap();
        assert_eq!(sz(&e), (8, 4));
        assert_eq!(e.enum_tag, Some(EnumTag::Explicit { size: 4, signed: false }));
        let o1 = enum_layout(&[vec![], vec![e]], &[0, 1], Repr::default()).unwrap();
        let o2 = enum_layout(&[vec![], vec![o1]], &[0, 1], Repr::default()).unwrap();
        let o3 = enum_layout(&[vec![], vec![o2]], &[0, 1], Repr::default()).unwrap();
        assert_eq!(o3.size, 8);
        // enum { A = 1000, B } needs a 2-byte tag.
        let l = enum_layout(&[vec![], vec![]], &[1000, 1001], Repr::default()).unwrap();
        assert_eq!(sz(&l), (2, 2));
        // A negative discriminant forces a signed tag.
        let l = enum_layout(&[vec![], vec![]], &[-1, 0], Repr::default()).unwrap();
        assert_eq!(l.enum_tag, Some(EnumTag::Explicit { size: 1, signed: true }));
        // repr(u64) with few variants leaves a large niche for outer Options.
        let l = enum_layout(&[vec![], vec![], vec![]], &[0, 1, 2], Repr { int: Some((64, false)), ..Repr::default() }).unwrap();
        assert_eq!(sz(&l), (8, 8));
        let o = enum_layout(&[vec![], vec![l]], &[0, 1], Repr::default()).unwrap();
        assert_eq!(o.size, 8);
    }

    #[test]
    fn nested_type_data_shape() {
        // The 4.4 standalone shape, built from field layouts directly:
        // a repr(u64) memo enum gives its outer enum a niche-filled tag.
        // GenericArgumentsMemo-like: repr(u64) enum with 3 unit variants.
        let memo = enum_layout(&[vec![], vec![], vec![]], &[0, 1, 2], Repr { int: Some((64, false)), ..Repr::default() }).unwrap();
        // A payload struct that carries the memo plus a pointer word.
        let payload = struct_layout(&[memo, ptr_layout()], Repr::default()).unwrap();
        assert_eq!(payload.size, 16);
        // TypeData-like: Data(payload) plus two unit variants niche-fills into 16.
        let data = enum_layout(&[vec![payload], vec![], vec![]], &[0, 1, 2], Repr::default()).unwrap();
        assert_eq!(data.size, 16);
        // TypeReference-like: a plain struct of a thin and a fat pointer.
        let reference = struct_layout(&[ptr_layout(), fat_ptr_layout()], Repr::default()).unwrap();
        assert_eq!(reference.size, 24);
    }
}
