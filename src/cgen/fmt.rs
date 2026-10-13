// Format strings and the Debug/Display glue over the runtime Formatter
// (src/runtime/fmt.h; W-STD-B owns this file, W-CGEN reviews).
//
// Every format argument becomes one C int expression (0 Ok, 1 Err)
// that formats a value through a `lust_Formatter *`: leaves call the
// runtime's Rust ports directly, compound types call `dbg_*` glue
// (`int dbg_<m>(lust_Formatter *f, T *p)`), which writes through the
// Debug builders exactly as Rust's derived and std impls do, so width,
// fill, `#?` pretty printing, and `x?` flags reach every leaf.
use super::*;

/// The C int expression that formats the value `v` points at (a
/// `ctype(t)*` expression) with the trait of `kind`, into the
/// Formatter pointer expression `f`. Compound types ask for glue
/// through `need`.
pub(super) fn fmt_expr(t: &CTy, kind: FmtKind, f: &str, v: &str, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let debug = kind == FmtKind::Debug;
    match t {
        CTy::Int(i) => int_expr(*i, kind, f, &format!("(*{v})")),
        CTy::Float(fl) => {
            let mode = match kind {
                FmtKind::Debug => 1,
                FmtKind::LowerExp => 2,
                FmtKind::UpperExp => 3,
                _ => 0,
            };
            format!("lust_f_{}({f}, *{v}, {mode})", fl.name())
        }
        CTy::Bool => format!("lust_f_bool({f}, *{v})"),
        CTy::Char if debug => format!("lust_f_dbg_char({f}, *{v})"),
        CTy::Char => format!("lust_f_char({f}, *{v})"),
        CTy::Str => str_expr(debug, f, &format!("(*{v})")),
        CTy::Ref(inner) if **inner == CTy::Str => str_expr(debug, f, &format!("(*{v})")),
        CTy::String => str_expr(debug, f, &format!("lust_string_as_str({v})")),
        CTy::Unit => format!("lust_f_unit({f})"),
        CTy::FnPtr(..) => format!("lust_f_fnptr({f}, (const void*)(*{v}))"),
        CTy::Ref(inner) | CTy::Boxed(inner) => fmt_expr(inner, kind, f, &format!("(*{v})"), need),
        CTy::Rc(inner) => fmt_expr(inner, kind, f, &format!("(&(*{v})->v)"), need),
        _ if debug => {
            need(Glue::Debug, t);
            format!("dbg_{}({f}, {v})", mangle(t))
        }
        _ => {
            need(Glue::Display, t);
            format!("disp_{}({f}, {v})", mangle(t))
        }
    }
}

fn str_expr(debug: bool, f: &str, s: &str) -> String {
    if debug { format!("lust_f_dbg_str({f}, {s})") } else { format!("lust_f_pad({f}, {s})") }
}

/// The mask that keeps a signed value's bits at its type width, for
/// the radix formats (`{:x}` of `-1i8` is `ff`).
fn width_mask(i: IntTy) -> &'static str {
    match i.bits() {
        8 => "0xffull",
        16 => "0xffffull",
        32 => "0xffffffffull",
        _ => "0xffffffffffffffffull",
    }
}

fn int_expr(i: IntTy, kind: FmtKind, f: &str, e: &str) -> String {
    let mode = match kind {
        FmtKind::LowerHex => 1,
        FmtKind::UpperHex => 2,
        FmtKind::Octal => 3,
        FmtKind::Binary => 4,
        _ => 0,
    };
    if mode != 0 {
        return if is128(i) {
            format!("lust_f_radix({f}, ({e}).lo, ({e}).hi, {mode})")
        } else {
            format!("lust_f_radix({f}, (uint64_t){e} & {}, 0, {mode})", width_mask(i))
        };
    }
    let dbg = if kind == FmtKind::Debug { "dbg_" } else { "" };
    if is128(i) {
        format!("lust_f_{dbg}{}({f}, {e})", if i.signed() { "i128" } else { "u128" })
    } else if i.signed() && kind == FmtKind::Debug {
        format!("lust_f_dbg_i64({f}, (int64_t){e}, {})", width_mask(i))
    } else if i.signed() {
        format!("lust_f_i64({f}, (int64_t){e})")
    } else {
        format!("lust_f_{dbg}u64({f}, (uint64_t){e})")
    }
}

/// A `lust_str` literal for `s`.
fn lit(s: &str) -> String {
    format!("(lust_str){{(uint8_t*){}, {}}}", c_string_lit(s.as_bytes()), s.len())
}

/// Builder code: one `debug_tuple`/`debug_struct` value of the fields
/// (name, value pointer expression, type), returning its result. A
/// named shape with no fields writes the bare name, as derived Debug.
fn builder_fields(name: &str, named: bool, fields: &[(String, String, CTy)], need: &mut dyn FnMut(Glue, &CTy)) -> String {
    if fields.is_empty() {
        return format!("return lust_f_write_str(f, {});", lit(name));
    }
    let (ty, kind) = if named { ("lust_DebugStruct", "dstruct") } else { ("lust_DebugTuple", "dtuple") };
    let mut s = format!("{{ {ty} b; lust_fmt_slot s; lust_Formatter *w; lust_{kind}_new(&b, f, {});", lit(name));
    for (fname, v, ft) in fields {
        let e = fmt_expr(ft, FmtKind::Debug, "w", v, need);
        let begin = if named { format!("lust_dstruct_field(&b, &s, {})", lit(fname)) } else { "lust_dtuple_field(&b, &s)".to_string() };
        let _ = write!(s, " if ((w = {begin})) lust_{kind}_field_end(&b, &s, {e});");
    }
    let _ = write!(s, " return lust_{kind}_finish(&b); }}");
    s
}

/// Builder code for `debug_list` over `n` elements at `elem(i)`.
fn builder_list(n: &str, elem: &str, et: &CTy, need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let e = fmt_expr(et, FmtKind::Debug, "w", elem, need);
    format!(
        "{{ lust_DebugList b; lust_fmt_slot s; lust_Formatter *w; lust_dlist_new(&b, f, 0); for (uint64_t i = 0; i < {n}; i++) if ((w = lust_dlist_entry(&b, &s))) lust_dlist_entry_end(&b, &s, {e}); return lust_dlist_finish(&b); }}"
    )
}

/// The body of `dbg_<m>`: Rust's Debug for `t`, through the builders.
pub(super) fn debug_glue_body(p: &Program, t: &CTy, slots: &[u32], need: &mut dyn FnMut(Glue, &CTy)) -> String {
    let disc_p = disc_call(p, t, "p");
    let mut body = String::new();
    match t {
        CTy::Option(inner) => {
            let some = builder_fields("Some", false, &[(String::new(), format!("&{}", variant_field(p, t, "(*p)", 1, 0)), (**inner).clone())], need);
            let _ = writeln!(body, "  if ({disc_p}) {some}\n  return lust_f_write_str(f, {});", lit("None"));
        }
        CTy::Result(a, b) => {
            let ok = builder_fields("Ok", false, &[(String::new(), format!("&{}", variant_field(p, t, "(*p)", 0, 0)), (**a).clone())], need);
            let err = builder_fields("Err", false, &[(String::new(), format!("&{}", variant_field(p, t, "(*p)", 1, 0)), (**b).clone())], need);
            let _ = writeln!(body, "  if ({disc_p}) {err}\n  {ok}");
        }
        CTy::Tuple(es) => {
            let fields: Vec<(String, String, CTy)> = es.iter().enumerate().map(|(i, e)| (String::new(), format!("&p->f{i}"), e.clone())).collect();
            // `()` has its own Debug (`f.pad("()")`); a tuple of fields
            // is a nameless debug_tuple.
            if fields.is_empty() {
                body.push_str("  return lust_f_unit(f);\n");
            } else {
                let _ = writeln!(body, "  {}", builder_fields("", false, &fields, need));
            }
        }
        CTy::Array(e, n) => {
            let _ = writeln!(body, "  {}", builder_list(&n.to_string(), "&p->v[i]", e, need));
        }
        CTy::Slice(e) => {
            let _ = writeln!(body, "  {}", builder_list("p->len", "&p->ptr[i]", e, need));
        }
        CTy::Vec(e) => {
            let et = ctype(e);
            let _ = writeln!(body, "  {}", builder_list("p->len", &format!("&(({et}*)p->ptr)[i]"), e, need));
        }
        CTy::Adt(a) => {
            if let Some(call) = user_fmt_call(p, *a, FmtKind::Debug, slots) {
                let _ = writeln!(body, "  {call}");
            } else {
                let adt = p.adt(*a);
                let variant = |v: &Variant, access: &dyn Fn(usize) -> String, need: &mut dyn FnMut(Glue, &CTy)| -> String {
                    // The struct's pseudo-variant carries the flat name;
                    // rustc prints the source name.
                    let name = p.display_name(v.name);
                    let fields: Vec<(String, String, CTy)> =
                        v.fields.iter().enumerate().map(|(fi, fd)| (p.name(fd.name).to_string(), format!("&{}", access(fi)), cty(&p.tys, fd.ty))).collect();
                    builder_fields(name, v.shape == VariantShape::Named, &fields, need)
                };
                if adt.is_enum {
                    let _ = writeln!(body, "  switch ({disc_p}) {{");
                    for (vi, v) in adt.variants.iter().enumerate() {
                        let b = variant(v, &|fi| format!("p->u.v{vi}.f{fi}"), need);
                        let _ = writeln!(body, "  case {vi}: {b}");
                    }
                    body.push_str("  }\n  return 0;\n");
                } else {
                    let b = variant(&adt.variants[0], &|fi| format!("p->f{fi}"), need);
                    let _ = writeln!(body, "  {b}");
                }
            }
        }
        _ => {
            let e = fmt_expr(t, FmtKind::Debug, "f", "p", need);
            let _ = writeln!(body, "  return {e};");
        }
    }
    body
}

/// The body of `disp_<m>`: only types with a user Display impl reach
/// Display glue (every other Display type is a leaf in `fmt_expr`).
pub(super) fn display_glue_body(p: &Program, t: &CTy, slots: &[u32]) -> String {
    match t {
        // `impl Display for fmt::Error`: str Display of core's text.
        CTy::Adt(a) if p.tys.local_adt_of(crate::check::generics::fmt_error_def()) == Some(*a) => {
            format!("  return lust_f_pad(f, {});\n", lit("an error occurred when formatting an argument"))
        }
        CTy::Adt(a) => match user_fmt_call(p, *a, FmtKind::Display, slots) {
            Some(call) => format!("  {call}\n"),
            None => "  abort();\n".to_string(),
        },
        _ => "  abort();\n".to_string(),
    }
}

/// The call of a user fmt impl's method instance for Adt `a`, as a C
/// statement that returns 0 or 1, when the program has one.
fn user_fmt_call(p: &Program, a: AdtId, kind: FmtKind, slots: &[u32]) -> Option<String> {
    let m = *p.gx.fmt_methods.get(&(a, kind as u8))?;
    let ret = cty(&p.tys, p.fn_info(m).ret);
    let rt = ctype(&ret);
    let cast = fn_ptr_cast(p, m);
    let slot = slots[m.0 as usize];
    let disc = disc_call(p, &ret, "(&r)");
    Some(if ret_is_large(p, m) {
        format!("{{ {rt} r; ({cast}lust_fns[{slot}])(&r, p, f); return {disc} != 0; }}")
    } else {
        format!("{{ {rt} r = ({cast}lust_fns[{slot}])(p, f); return {disc} != 0; }}")
    })
}

/// True when formatting a value of `t` can fail (reach a user fmt impl
/// that may return Err): it holds an Adt somewhere. Other values only
/// write to a String sink, which never fails.
fn may_fail(t: &CTy) -> bool {
    match t {
        CTy::Adt(_) => true,
        CTy::Vec(e) | CTy::Option(e) | CTy::Ref(e) | CTy::Array(e, _) | CTy::Slice(e) | CTy::Boxed(e) | CTy::Rc(e) => may_fail(e),
        CTy::Result(a, b) => may_fail(a) || may_fail(b),
        CTy::Tuple(es) => es.iter().any(may_fail),
        _ => false,
    }
}

/// The runtime option words of one spec: (fill, align, flags, width,
/// precision), as `lust_f_set` takes them.
fn spec_words(spec: &FmtSpec) -> (u32, u32, u32, u32, u32) {
    let align = match spec.align {
        b'<' => 0,
        b'>' => 1,
        b'^' => 2,
        _ => 3,
    };
    let mut flags = 0u32;
    if spec.plus {
        flags |= 1;
    }
    if spec.minus {
        flags |= 2;
    }
    if spec.alt {
        flags |= 4;
    }
    if spec.zero {
        flags |= 8;
    }
    match spec.debug_hex {
        1 => flags |= 16,
        2 => flags |= 32,
        _ => {}
    }
    if spec.width.is_some() {
        flags |= 64;
    }
    if spec.precision.is_some() {
        flags |= 128;
    }
    let fill = if spec.fill == 0 { ' ' as u32 } else { spec.fill };
    (fill, align, flags, spec.width.unwrap_or(0), spec.precision.unwrap_or(0))
}

/// `fmt::Arguments::estimated_capacity` for these parts (the literal
/// pieces' length, doubled when there are arguments; nothing when the
/// string starts with an argument and the pieces are short). With no
/// arguments the text is `as_str()`, copied with exact capacity.
pub(super) fn estimated_capacity(parts: &[FmtPart]) -> usize {
    let pieces: usize = parts.iter().map(|p| if let FmtPart::Lit(s) = p { s.len() } else { 0 }).sum();
    let args = parts.iter().any(|p| matches!(p, FmtPart::Arg { .. }));
    if !args {
        pieces
    } else if matches!(parts.first(), Some(FmtPart::Arg { .. })) && pieces < 16 {
        0
    } else {
        pieces.saturating_mul(2)
    }
}

impl FnGen<'_, '_, '_> {
    /// Emits the formatting of `parts` into a new String temp (with
    /// Rust's capacity for `format!`) and returns the temp's name. A
    /// fmt impl error panics with the message of `what` (see
    /// `lust_fmt_failed`).
    pub(super) fn format(&mut self, parts: &[FmtPart], loc: &str, post: &mut Vec<String>, what: u32) -> String {
        let s = self.tmp();
        let cap = estimated_capacity(parts);
        let _ = writeln!(self.out, "    lust_String {s} = lust_string_with_capacity({cap});");
        if !parts.iter().any(|p| matches!(p, FmtPart::Arg { .. })) {
            for part in parts {
                if let FmtPart::Lit(text) = part
                    && !text.is_empty()
                {
                    let _ = writeln!(self.out, "    lust_string_push_bytes(&{s}, {}, {});", c_string_lit(text.as_bytes()), text.len());
                }
            }
            return s;
        }
        let _ = writeln!(self.out, "    lust_sink {s}k; lust_sink_string(&{s}k, &{s}); lust_Formatter {s}f; lust_f_init(&{s}f, &{s}k); int {s}e = 0;");
        let mut fallible = false;
        for part in parts {
            match part {
                FmtPart::Lit(text) => {
                    if !text.is_empty() {
                        let guard = if fallible { format!("if (!{s}e) ") } else { String::new() };
                        let _ = writeln!(self.out, "    {guard}lust_string_push_bytes(&{s}, {}, {});", c_string_lit(text.as_bytes()), text.len());
                    }
                }
                FmtPart::Arg { value, ty, spec, .. } => {
                    let (v, vt) = self.operand(value, loc, post);
                    let t = cty(&self.body.tys, *ty);
                    // An unsized `str` or `[T]` argument arrives as its
                    // fat value; the formatters take a pointer to it.
                    let ptr = if matches!(self.body.tys.kind(*ty), TyKind::Str | TyKind::Slice(_)) {
                        let tmp = self.tmp();
                        let _ = writeln!(self.out, "    {} {tmp} = {v};", ctype(&vt));
                        format!("(&{tmp})")
                    } else {
                        v
                    };
                    let mut want: Vec<(Glue, CTy)> = Vec::new();
                    let e = fmt_expr(&t, spec.kind, &format!("(&{s}f)"), &ptr, &mut |g, t| want.push((g, t.clone())));
                    for (g, t) in want {
                        self.want(g, &t);
                    }
                    let (fill, align, flags, width, prec) = spec_words(spec);
                    let guard = if fallible { format!("if (!{s}e) ") } else { String::new() };
                    let _ = writeln!(self.out, "    {guard}{{ lust_f_set(&{s}f, {fill}, {align}, {flags}, {width}, {prec}); {s}e = {e}; }}");
                    fallible |= may_fail(&t);
                }
            }
        }
        if fallible {
            let _ = writeln!(self.out, "    if ({s}e) lust_fmt_failed({what}, {loc});");
        }
        s
    }
}

/// `$signed::MAX.ilog10() + 1`: the capacity Rust's signed `to_string`
/// specialization starts from (one more for a negative value).
fn signed_digits(i: IntTy) -> u32 {
    match i.bits() {
        8 => 3,
        16 => 5,
        32 => 10,
        64 => 19,
        _ => 39,
    }
}

impl FnGen<'_, '_, '_> {
    /// `ToString::to_string` of the value `v` points at (Self type `t`),
    /// with Rust 1.99's capacity rules: signed integers preallocate
    /// their widest decimal form, unsigned integers, `char`, `bool`,
    /// `String`, `str`, and `&str` copy exactly, and everything else
    /// writes Display into `String::new()`.
    pub(super) fn to_string_value(&mut self, t: &CTy, v: &str, loc: &str) -> String {
        let s = self.tmp();
        match t {
            CTy::String => {
                let _ = writeln!(self.out, "    lust_String {s} = lust_string_from(lust_string_as_str({v}));");
                return s;
            }
            CTy::Str => {
                let _ = writeln!(self.out, "    lust_String {s} = lust_string_from(*{v});");
                return s;
            }
            CTy::Ref(inner) if **inner == CTy::Str => {
                let _ = writeln!(self.out, "    lust_String {s} = lust_string_from(*{v});");
                return s;
            }
            _ => {}
        }
        let exact = matches!(t, CTy::Int(i) if !i.signed()) || matches!(t, CTy::Char | CTy::Bool);
        let start = match t {
            CTy::Int(i) if i.signed() => {
                let neg = if is128(*i) { format!("((int64_t)(*{v}).hi < 0)") } else { format!("(*{v} < 0)") };
                let n = signed_digits(*i);
                format!("lust_string_with_capacity({neg} ? {} : {n})", n + 1)
            }
            _ => "lust_string_new()".to_string(),
        };
        let buf = if exact { self.tmp() } else { s.clone() };
        let mut want: Vec<(Glue, CTy)> = Vec::new();
        let e = fmt_expr(t, FmtKind::Display, &format!("(&{buf}f)"), v, &mut |g, t| want.push((g, t.clone())));
        for (g, t) in want {
            self.want(g, &t);
        }
        let _ = writeln!(
            self.out,
            "    lust_String {buf} = {start}; lust_sink {buf}k; lust_sink_string(&{buf}k, &{buf}); lust_Formatter {buf}f; lust_f_init(&{buf}f, &{buf}k);"
        );
        if may_fail(t) {
            let _ = writeln!(self.out, "    if ({e}) lust_fmt_failed(1, {loc});");
        } else {
            let _ = writeln!(self.out, "    (void)({e});");
        }
        if exact {
            let _ = writeln!(self.out, "    lust_String {s} = lust_string_from(lust_string_as_str(&{buf})); lust_string_drop(&{buf});");
        }
        s
    }
}

/// The C form of `fmt::Result` (`Result<(), fmt::Error>`).
fn fmt_result_cty(p: &Program) -> CTy {
    let e = p.tys.local_adt_of(crate::check::generics::fmt_error_def()).map_or(CTy::Unit, CTy::Adt);
    CTy::Result(Box::new(CTy::Unit), Box::new(e))
}

impl FnGen<'_, '_, '_> {
    /// The `fmt::Result` value of a runtime result int.
    fn fmt_result_of(&mut self, e: &str) -> String {
        let t = fmt_result_cty(self.p);
        let err_ty = match &t {
            CTy::Result(_, b) => (**b).clone(),
            _ => CTy::Unit,
        };
        let ok = self.make_variant(&t, 0, &["((lust_Unit){})".to_string()]);
        let err = self.make_variant(&t, 1, &[zero_lit(self.p, &err_ty)]);
        format!("(({e}) ? {err} : {ok})")
    }

    /// One `core::fmt` builtin call (check/fmt.rs) over the operand
    /// values and C types, or None for every other builtin.
    pub(super) fn fmt_builtin(&mut self, b: Builtin, vals: &[String], tys: &[CTy], loc: &str) -> Option<String> {
        use crate::ty::fmt::FmtTy as F;
        use Builtin as B;
        let opt_usize = CTy::Option(Box::new(CTy::Int(IntTy::Usize)));
        let recv_kind = match tys.first() {
            Some(CTy::Ref(inner)) => match &**inner {
                CTy::Fmt(k) => Some(*k),
                _ => None,
            },
            _ => None,
        };
        let mut want: Vec<(Glue, CTy)> = Vec::new();
        let value = |i: usize, f: &str, want: &mut Vec<(Glue, CTy)>| -> String {
            let inner = match &tys[i] {
                CTy::Ref(inner) => (**inner).clone(),
                t => t.clone(),
            };
            fmt_expr(&inner, FmtKind::Debug, f, &vals[i], &mut |g, t| want.push((g, t.clone())))
        };
        let on_string = matches!(tys.first(), Some(CTy::Ref(inner)) if **inner == CTy::String);
        let out = match b {
            // `<String as fmt::Write>`: append, always Ok.
            B::FmtWriteStr if on_string => self.fmt_result_of(&format!("(lust_string_push_str({}, {}), 0)", vals[0], vals[1])),
            B::FmtWriteChar if on_string => self.fmt_result_of(&format!("(lust_string_push_char({}, {}), 0)", vals[0], vals[1])),
            B::FmtWriteStr => self.fmt_result_of(&format!("lust_f_write_str({}, {})", vals[0], vals[1])),
            B::FmtWriteChar => self.fmt_result_of(&format!("lust_f_write_char({}, {})", vals[0], vals[1])),
            B::FmtPad => self.fmt_result_of(&format!("lust_f_pad({}, {})", vals[0], vals[1])),
            B::FmtPadIntegral => self.fmt_result_of(&format!("lust_f_pad_integral({}, {}, {}, {})", vals[0], vals[1], vals[2], vals[3])),
            B::FmtWidth | B::FmtPrecision => {
                let (flag, field) = if b == B::FmtWidth { ("LUST_FLAG_WIDTH", "width") } else { ("LUST_FLAG_PREC", "prec") };
                let some = self.make_variant(&opt_usize, 1, &[format!("(uint64_t){}->{field}", vals[0])]);
                let none = self.make_variant(&opt_usize, 0, &[]);
                format!("(({}->flags & {flag}) ? {some} : {none})", vals[0])
            }
            B::FmtFill => format!("({}->fill)", vals[0]),
            B::FmtAlternate => format!("(({}->flags & LUST_FLAG_ALT) != 0)", vals[0]),
            B::FmtSignPlus => format!("(({}->flags & LUST_FLAG_PLUS) != 0)", vals[0]),
            B::FmtSignMinus => format!("(({}->flags & LUST_FLAG_MINUS) != 0)", vals[0]),
            B::FmtSignAwareZeroPad => format!("(({}->flags & LUST_FLAG_ZERO) != 0)", vals[0]),
            B::FmtDebugStruct | B::FmtDebugTuple | B::FmtDebugList | B::FmtDebugSet | B::FmtDebugMap => {
                let t = self.tmp();
                let line = match b {
                    B::FmtDebugStruct => format!("lust_DebugStruct {t}; lust_dstruct_new(&{t}, {}, {});", vals[0], vals[1]),
                    B::FmtDebugTuple => format!("lust_DebugTuple {t}; lust_dtuple_new(&{t}, {}, {});", vals[0], vals[1]),
                    B::FmtDebugList => format!("lust_DebugList {t}; lust_dlist_new(&{t}, {}, 0);", vals[0]),
                    B::FmtDebugSet => format!("lust_DebugList {t}; lust_dlist_new(&{t}, {}, 1);", vals[0]),
                    _ => format!("lust_DebugMap {t}; lust_dmap_new(&{t}, {});", vals[0]),
                };
                let _ = writeln!(self.out, "    {line}");
                t
            }
            B::DsField => {
                let e = value(2, "w", &mut want);
                let _ = writeln!(
                    self.out,
                    "    {{ lust_fmt_slot s; lust_Formatter *w = lust_dstruct_field({}, &s, {}); if (w) lust_dstruct_field_end({}, &s, {e}); }}",
                    vals[0], vals[1], vals[0]
                );
                vals[0].clone()
            }
            B::DtField | B::DlEntry => {
                let e = value(1, "w", &mut want);
                let (begin, end) = if b == B::DtField { ("dtuple_field", "dtuple_field_end") } else { ("dlist_entry", "dlist_entry_end") };
                let _ = writeln!(
                    self.out,
                    "    {{ lust_fmt_slot s; lust_Formatter *w = lust_{begin}({}, &s); if (w) lust_{end}({}, &s, {e}); }}",
                    vals[0], vals[0]
                );
                vals[0].clone()
            }
            B::DmKey | B::DmValue | B::DmEntry => {
                let steps: &[(usize, &str)] = match b {
                    B::DmKey => &[(1, "key")],
                    B::DmValue => &[(1, "value")],
                    _ => &[(1, "key"), (2, "value")],
                };
                for &(i, which) in steps {
                    let e = value(i, "w", &mut want);
                    let _ = writeln!(
                        self.out,
                        "    {{ lust_fmt_slot s; lust_Formatter *w = lust_dmap_{which}({}, &s, {loc}); if (w) lust_dmap_{which}_end({}, &s, {e}); }}",
                        vals[0], vals[0]
                    );
                }
                vals[0].clone()
            }
            B::FmtFinish | B::FmtFinishNonExhaustive => {
                let ne = if b == B::FmtFinishNonExhaustive { "_ne" } else { "" };
                let call = match recv_kind {
                    Some(F::DebugStruct) => format!("lust_dstruct_finish{ne}({})", vals[0]),
                    Some(F::DebugTuple) => format!("lust_dtuple_finish{ne}({})", vals[0]),
                    Some(F::DebugMap) => format!("lust_dmap_finish{ne}({}, {loc})", vals[0]),
                    _ => format!("lust_dlist_finish{ne}({})", vals[0]),
                };
                self.fmt_result_of(&call)
            }
            // Conversion trait methods (check/convert.rs).
            B::ConvIdent => vals[0].clone(),
            B::ConvDeref => format!("(*{})", vals[0]),
            B::ConvRcInner => format!("(&(*{})->v)", vals[0]),
            B::ConvStrBytes | B::ConvArraySlice => {
                let (elem, ptr, len) = match &tys[0] {
                    CTy::Ref(inner) => match &**inner {
                        CTy::Array(e, n) => ((**e).clone(), format!("{}->v", vals[0]), format!("((uint64_t){n})")),
                        _ => (CTy::Int(IntTy::U8), format!("{}.ptr", vals[0]), format!("{}.len", vals[0])),
                    },
                    _ => (CTy::Int(IntTy::U8), format!("{}.ptr", vals[0]), format!("{}.len", vals[0])),
                };
                let sl = CTy::Slice(Box::new(elem));
                let t = self.tmp();
                let _ = writeln!(self.out, "    {} {t} = {{ {ptr}, {len} }};", ctype(&sl));
                t
            }
            B::FmtCallDisplay | B::FmtCallDebug => {
                let kind = if b == B::FmtCallDisplay { FmtKind::Display } else { FmtKind::Debug };
                let inner = match &tys[0] {
                    CTy::Ref(inner) => (**inner).clone(),
                    t => t.clone(),
                };
                let e = fmt_expr(&inner, kind, &vals[1], &vals[0], &mut |g, t| want.push((g, t.clone())));
                self.fmt_result_of(&e)
            }
            _ => return None,
        };
        for (g, t) in want {
            self.want(g, &t);
        }
        Some(out)
    }

    /// `Rvalue::WriteFmt`: the parts into `dst`'s sink through a fresh
    /// Formatter (Formatter::write_fmt and `<String as fmt::Write>`),
    /// stopping at the first error; the value is the `fmt::Result`.
    pub(super) fn write_fmt(&mut self, dst: &Operand, parts: &[FmtPart], loc: &str, post: &mut Vec<String>) -> String {
        let (d, dt) = self.operand(dst, loc, post);
        let s = self.tmp();
        let on_string = matches!(&dt, CTy::Ref(inner) if **inner == CTy::String);
        if on_string {
            let _ = writeln!(self.out, "    lust_sink {s}k; lust_sink_string(&{s}k, {d}); lust_Formatter {s}f; lust_f_init(&{s}f, &{s}k); int {s}e = 0;");
        } else {
            let _ = writeln!(self.out, "    lust_Formatter {s}f; lust_f_init(&{s}f, ({d})->buf); int {s}e = 0;");
        }
        for part in parts {
            match part {
                FmtPart::Lit(text) => {
                    if !text.is_empty() {
                        let _ = writeln!(self.out, "    if (!{s}e) {s}e = lust_f_write(&{s}f, {}, {});", c_string_lit(text.as_bytes()), text.len());
                    }
                }
                FmtPart::Arg { value, ty, spec, .. } => {
                    let (v, vt) = self.operand(value, loc, post);
                    let t = cty(&self.body.tys, *ty);
                    let ptr = if matches!(self.body.tys.kind(*ty), TyKind::Str | TyKind::Slice(_)) {
                        let tmp = self.tmp();
                        let _ = writeln!(self.out, "    {} {tmp} = {v};", ctype(&vt));
                        format!("(&{tmp})")
                    } else {
                        v
                    };
                    let mut want: Vec<(Glue, CTy)> = Vec::new();
                    let e = fmt_expr(&t, spec.kind, &format!("(&{s}f)"), &ptr, &mut |g, t| want.push((g, t.clone())));
                    for (g, t) in want {
                        self.want(g, &t);
                    }
                    let (fill, align, flags, width, prec) = spec_words(spec);
                    let _ = writeln!(self.out, "    if (!{s}e) {{ lust_f_set(&{s}f, {fill}, {align}, {flags}, {width}, {prec}); {s}e = {e}; }}");
                }
            }
        }
        self.fmt_result_of(&format!("{s}e"))
    }
}
