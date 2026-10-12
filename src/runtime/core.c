void lust_oom(void) LUST_BODY({ fputs("memory allocation failed\n", stderr); abort(); })

void *lust_realloc(void *p, uint64_t n) LUST_BODY({
    void *r = realloc(p, n ? n : 1);
    if (!r) lust_oom();
    return r;
})

/* ---------- Strings ---------- */

lust_String lust_string_new(void) LUST_BODY({ lust_String s = {0, 0, 0}; return s; })

void lust_string_reserve(lust_String *s, uint64_t extra) LUST_BODY({
    if (s->len + extra <= s->cap) return;
    uint64_t cap = s->cap ? s->cap * 2 : 8;
    while (cap < s->len + extra) cap *= 2;
    s->ptr = lust_realloc(s->ptr, cap);
    s->cap = cap;
})

lust_String lust_string_with_capacity(uint64_t n) LUST_BODY({
    lust_String s = {0, 0, 0};
    if (n) { s.ptr = lust_realloc(0, n); s.cap = n; }
    return s;
})

void lust_string_push_bytes(lust_String *s, const void *p, uint64_t n) LUST_BODY({
    if (!n) return;
    lust_string_reserve(s, n);
    memcpy(s->ptr + s->len, p, n);
    s->len += n;
})

void lust_string_push_str(lust_String *s, lust_str x) LUST_BODY({ lust_string_push_bytes(s, x.ptr, x.len); })

void lust_string_push_cstr(lust_String *s, const char *c) LUST_BODY({ lust_string_push_bytes(s, c, strlen(c)); })

void lust_string_push_char(lust_String *s, uint32_t c) LUST_BODY({
    uint8_t b[4];
    int n;
    if (c < 0x80) { b[0] = c; n = 1; }
    else if (c < 0x800) { b[0] = 0xC0 | (c >> 6); b[1] = 0x80 | (c & 0x3F); n = 2; }
    else if (c < 0x10000) { b[0] = 0xE0 | (c >> 12); b[1] = 0x80 | ((c >> 6) & 0x3F); b[2] = 0x80 | (c & 0x3F); n = 3; }
    else { b[0] = 0xF0 | (c >> 18); b[1] = 0x80 | ((c >> 12) & 0x3F); b[2] = 0x80 | ((c >> 6) & 0x3F); b[3] = 0x80 | (c & 0x3F); n = 4; }
    lust_string_push_bytes(s, b, n);
})

lust_String lust_string_from(lust_str x) LUST_BODY({
    lust_String s = lust_string_with_capacity(x.len);
    lust_string_push_str(&s, x);
    return s;
})

lust_str lust_string_as_str(lust_String *s) LUST_BODY({ lust_str r; r.ptr = s->ptr; r.len = s->len; return r; })
lust_String lust_string_clone(lust_String *s) LUST_BODY({ return lust_string_from(lust_string_as_str(s)); })
void lust_string_drop(lust_String *s) LUST_BODY({ free(s->ptr); })

int lust_str_cmp(lust_str a, lust_str b) LUST_BODY({
    uint64_t n = a.len < b.len ? a.len : b.len;
    int c = n ? memcmp(a.ptr, b.ptr, n) : 0;
    if (c) return c;
    return a.len < b.len ? -1 : a.len > b.len ? 1 : 0;
})
uint8_t lust_str_eq(lust_str a, lust_str b) LUST_BODY({ return a.len == b.len && (a.len == 0 || memcmp(a.ptr, b.ptr, a.len) == 0); })

#include "panic.c"
/* ---------- Formatting ---------- */

void lust_fmt_u64(lust_String *out, uint64_t v) LUST_BODY({
    char b[24];
    int i = 24;
    do { b[--i] = '0' + v % 10; v /= 10; } while (v);
    lust_string_push_bytes(out, b + i, 24 - i);
})

void lust_fmt_i64(lust_String *out, int64_t v) LUST_BODY({
    if (v < 0) { lust_string_push_bytes(out, "-", 1); lust_fmt_u64(out, (uint64_t)0 - (uint64_t)v); }
    else lust_fmt_u64(out, (uint64_t)v);
})

void lust_fmt_bool(lust_String *out, uint8_t v) LUST_BODY({ lust_string_push_cstr(out, v ? "true" : "false"); })

void lust_fmt_escape(lust_String *out, uint32_t c, uint32_t quote) LUST_BODY({
    switch (c) {
    case '\t': lust_string_push_cstr(out, "\\t"); return;
    case '\r': lust_string_push_cstr(out, "\\r"); return;
    case '\n': lust_string_push_cstr(out, "\\n"); return;
    case '\\': lust_string_push_cstr(out, "\\\\"); return;
    case 0: lust_string_push_cstr(out, "\\0"); return;
    }
    if (c == quote) { lust_string_push_bytes(out, "\\", 1); lust_string_push_char(out, c); return; }
    if (c < 0x20 || c == 0x7f) {
        char b[16];
        snprintf(b, sizeof b, "\\u{%x}", c);
        lust_string_push_cstr(out, b);
        return;
    }
    lust_string_push_char(out, c);
})

/* Decodes one UTF-8 scalar. Input is valid UTF-8 (all lust strings are). */
uint32_t lust_utf8_next(const uint8_t *p, uint64_t *i) LUST_BODY({
    uint8_t b = p[*i];
    if (b < 0x80) { *i += 1; return b; }
    if (b < 0xE0) { uint32_t c = ((b & 0x1F) << 6) | (p[*i + 1] & 0x3F); *i += 2; return c; }
    if (b < 0xF0) { uint32_t c = ((b & 0x0F) << 12) | ((p[*i + 1] & 0x3F) << 6) | (p[*i + 2] & 0x3F); *i += 3; return c; }
    uint32_t c = ((b & 0x07) << 18) | ((p[*i + 1] & 0x3F) << 12) | ((p[*i + 2] & 0x3F) << 6) | (p[*i + 3] & 0x3F);
    *i += 4;
    return c;
})

void lust_fmt_str_debug(lust_String *out, lust_str s) LUST_BODY({
    lust_string_push_bytes(out, "\"", 1);
    uint64_t i = 0;
    while (i < s.len) lust_fmt_escape(out, lust_utf8_next(s.ptr, &i), '"');
    lust_string_push_bytes(out, "\"", 1);
})

void lust_fmt_char_debug(lust_String *out, uint32_t c) LUST_BODY({
    lust_string_push_bytes(out, "'", 1);
    lust_fmt_escape(out, c, '\'');
    lust_string_push_bytes(out, "'", 1);
})

void lust_write(int to_stderr, lust_String *s) LUST_BODY({
    FILE *f = to_stderr ? stderr : stdout;
    if (s->len) fwrite(s->ptr, 1, s->len, f);
    if (to_stderr) fflush(stderr);
    free(s->ptr);
})

void lust_flush(void) LUST_BODY({ fflush(stdout); })

/* The `exit` intrinsic behind std::process::exit: lust print output is
   buffered in stdio, so flush before the libc exit. Destructors do not
   run, as in Rust. */
void lust_exit(int32_t code) LUST_BODY({ fflush(stdout); exit(code); })

/* ---------- Vec ---------- */

void lust_vec_reserve(lust_Vec *v, uint64_t extra, uint64_t elem) LUST_BODY({
    if (v->len + extra <= v->cap) return;
    uint64_t cap = v->cap ? v->cap * 2 : 4;
    while (cap < v->len + extra) cap *= 2;
    v->ptr = lust_realloc(v->ptr, cap * elem);
    v->cap = cap;
})

lust_Vec lust_vec_with_capacity(uint64_t n, uint64_t elem) LUST_BODY({
    lust_Vec v = {0, 0, 0};
    if (n) { v.ptr = lust_realloc(0, n * elem); v.cap = n; }
    return v;
})

void *lust_vec_push_slot(lust_Vec *v, uint64_t elem) LUST_BODY({
    lust_vec_reserve(v, 1, elem);
    return (char *)v->ptr + (v->len++) * elem;
})

uint64_t lust_bounds(uint64_t i, uint64_t len, lust_loc loc) LUST_BODY({
    if (i >= len) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "index out of bounds: the len is ");
        lust_fmt_u64(&s, len);
        lust_string_push_cstr(&s, " but the index is ");
        lust_fmt_u64(&s, i);
        lust_panic(&s, loc);
    }
    return i;
})

/* ---------- Checked integer math ---------- */

#define LUST_OVF(op) lust_panic_cstr("attempt to " op " with overflow", loc)

/* Narrow signed types: compute exactly in int64_t, then range check. */
#define LUST_SIGNED_NARROW(T, N, MINV, MAXV) \
T lust_add_##N(T a, T b, lust_loc loc) LUST_BODY({ int64_t r = (int64_t)a + b; if (r < MINV || r > MAXV) LUST_OVF("add"); return (T)r; }) \
T lust_sub_##N(T a, T b, lust_loc loc) LUST_BODY({ int64_t r = (int64_t)a - b; if (r < MINV || r > MAXV) LUST_OVF("subtract"); return (T)r; }) \
T lust_mul_##N(T a, T b, lust_loc loc) LUST_BODY({ int64_t r = (int64_t)a * b; if (r < MINV || r > MAXV) LUST_OVF("multiply"); return (T)r; }) \
T lust_neg_##N(T a, lust_loc loc) LUST_BODY({ if (a == MINV) LUST_OVF("negate"); return (T)-a; }) \
T lust_div_##N(T a, T b, lust_loc loc) LUST_BODY({ if (b == 0) lust_panic_cstr("attempt to divide by zero", loc); if (a == MINV && b == -1) LUST_OVF("divide"); return (T)(a / b); }) \
T lust_rem_##N(T a, T b, lust_loc loc) LUST_BODY({ if (b == 0) lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); if (a == MINV && b == -1) LUST_OVF("calculate the remainder"); return (T)(a % b); })

#define LUST_UNSIGNED_NARROW(T, N, MAXV) \
T lust_add_##N(T a, T b, lust_loc loc) LUST_BODY({ uint64_t r = (uint64_t)a + b; if (r > MAXV) LUST_OVF("add"); return (T)r; }) \
T lust_sub_##N(T a, T b, lust_loc loc) LUST_BODY({ if (b > a) LUST_OVF("subtract"); return (T)(a - b); }) \
T lust_mul_##N(T a, T b, lust_loc loc) LUST_BODY({ uint64_t r = (uint64_t)a * (uint64_t)b; if (r > MAXV) LUST_OVF("multiply"); return (T)r; }) \
T lust_div_##N(T a, T b, lust_loc loc) LUST_BODY({ if (b == 0) lust_panic_cstr("attempt to divide by zero", loc); return (T)(a / b); }) \
T lust_rem_##N(T a, T b, lust_loc loc) LUST_BODY({ if (b == 0) lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); return (T)(a % b); })

LUST_SIGNED_NARROW(int8_t, i8, -128, 127)
LUST_SIGNED_NARROW(int16_t, i16, -32768, 32767)
LUST_SIGNED_NARROW(int32_t, i32, -2147483647 - 1, 2147483647)
LUST_UNSIGNED_NARROW(uint8_t, u8, 255u)
LUST_UNSIGNED_NARROW(uint16_t, u16, 65535u)
LUST_UNSIGNED_NARROW(uint32_t, u32, 4294967295u)

int64_t lust_add_i64(int64_t a, int64_t b, lust_loc loc) LUST_BODY({
    int64_t r = (int64_t)((uint64_t)a + (uint64_t)b);
    if (((a ^ r) & (b ^ r)) < 0) LUST_OVF("add");
    return r;
})
int64_t lust_sub_i64(int64_t a, int64_t b, lust_loc loc) LUST_BODY({
    int64_t r = (int64_t)((uint64_t)a - (uint64_t)b);
    if (((a ^ b) & (a ^ r)) < 0) LUST_OVF("subtract");
    return r;
})
int64_t lust_mul_i64(int64_t a, int64_t b, lust_loc loc) LUST_BODY({
    if (a == 0 || b == 0) return 0;
    if ((a == -1 && b == INT64_MIN) || (b == -1 && a == INT64_MIN)) LUST_OVF("multiply");
    int64_t r = (int64_t)((uint64_t)a * (uint64_t)b);
    if (r / b != a) LUST_OVF("multiply");
    return r;
})
int64_t lust_neg_i64(int64_t a, lust_loc loc) LUST_BODY({ if (a == INT64_MIN) LUST_OVF("negate"); return -a; })
int64_t lust_div_i64(int64_t a, int64_t b, lust_loc loc) LUST_BODY({
    if (b == 0) lust_panic_cstr("attempt to divide by zero", loc);
    if (a == INT64_MIN && b == -1) LUST_OVF("divide");
    return a / b;
})
int64_t lust_rem_i64(int64_t a, int64_t b, lust_loc loc) LUST_BODY({
    if (b == 0) lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc);
    if (a == INT64_MIN && b == -1) LUST_OVF("calculate the remainder");
    return a % b;
})
uint64_t lust_add_u64(uint64_t a, uint64_t b, lust_loc loc) LUST_BODY({ uint64_t r = a + b; if (r < a) LUST_OVF("add"); return r; })
uint64_t lust_sub_u64(uint64_t a, uint64_t b, lust_loc loc) LUST_BODY({ if (b > a) LUST_OVF("subtract"); return a - b; })
uint64_t lust_mul_u64(uint64_t a, uint64_t b, lust_loc loc) LUST_BODY({ uint64_t r = a * b; if (a != 0 && r / a != b) LUST_OVF("multiply"); return r; })
uint64_t lust_div_u64(uint64_t a, uint64_t b, lust_loc loc) LUST_BODY({ if (b == 0) lust_panic_cstr("attempt to divide by zero", loc); return a / b; })
uint64_t lust_rem_u64(uint64_t a, uint64_t b, lust_loc loc) LUST_BODY({ if (b == 0) lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc); return a % b; })

uint32_t lust_shift_amount(uint64_t b, uint32_t bits, const char *op, lust_loc loc) LUST_BODY({
    if (b >= bits) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "attempt to shift ");
        lust_string_push_cstr(&s, op);
        lust_string_push_cstr(&s, " with overflow");
        lust_panic(&s, loc);
    }
    return (uint32_t)b;
})

#define LUST_POW(T, N) \
T lust_pow_##N(T a, uint32_t e, lust_loc loc) LUST_BODY({ \
    T r = 1; \
    while (e) { if (e & 1) r = lust_mul_##N(r, a, loc); e >>= 1; if (e) a = lust_mul_##N(a, a, loc); } \
    return r; \
})
#define LUST_ABS(T, N) T lust_abs_##N(T a, lust_loc loc) LUST_BODY({ return a < 0 ? lust_neg_##N(a, loc) : a; })
LUST_POW(int8_t, i8) LUST_POW(int16_t, i16) LUST_POW(int32_t, i32) LUST_POW(int64_t, i64)
LUST_POW(uint8_t, u8) LUST_POW(uint16_t, u16) LUST_POW(uint32_t, u32) LUST_POW(uint64_t, u64)
LUST_ABS(int8_t, i8) LUST_ABS(int16_t, i16) LUST_ABS(int32_t, i32) LUST_ABS(int64_t, i64)

/* ---------- Vec insert/remove ---------- */

void lust_vec_insert_at(lust_Vec *v, uint64_t i, uint64_t elem, lust_loc loc) LUST_BODY({
    if (i > v->len) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "insertion index (is ");
        lust_fmt_u64(&s, i);
        lust_string_push_cstr(&s, ") should be <= len (is ");
        lust_fmt_u64(&s, v->len);
        lust_string_push_cstr(&s, ")");
        lust_panic(&s, loc);
    }
    lust_vec_reserve(v, 1, elem);
    memmove((char *)v->ptr + (i + 1) * elem, (char *)v->ptr + i * elem, (v->len - i) * elem);
    v->len++;
})

void lust_vec_check_remove(lust_Vec *v, uint64_t i, lust_loc loc) LUST_BODY({
    if (i >= v->len) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "removal index (is ");
        lust_fmt_u64(&s, i);
        lust_string_push_cstr(&s, ") should be < len (is ");
        lust_fmt_u64(&s, v->len);
        lust_string_push_cstr(&s, ")");
        lust_panic(&s, loc);
    }
})

void lust_vec_remove_at(lust_Vec *v, uint64_t i, uint64_t elem) LUST_BODY({
    memmove((char *)v->ptr + i * elem, (char *)v->ptr + (i + 1) * elem, (v->len - i - 1) * elem);
    v->len--;
})

/* ---------- str ---------- */

uint8_t lust_str_starts_with(lust_str s, lust_str p) LUST_BODY({ return p.len <= s.len && (p.len == 0 || memcmp(s.ptr, p.ptr, p.len) == 0); })
uint8_t lust_str_ends_with(lust_str s, lust_str p) LUST_BODY({ return p.len <= s.len && (p.len == 0 || memcmp(s.ptr + s.len - p.len, p.ptr, p.len) == 0); })
uint8_t lust_str_contains(lust_str s, lust_str p) LUST_BODY({
    if (p.len == 0) return 1;
    for (uint64_t i = 0; i + p.len <= s.len; i++)
        if (s.ptr[i] == p.ptr[0] && memcmp(s.ptr + i, p.ptr, p.len) == 0) return 1;
    return 0;
})

/* Unicode White_Space, as used by Rust's char::is_whitespace. */
int lust_is_space(uint32_t c) LUST_BODY({
    return (c >= 9 && c <= 13) || c == 32 || c == 0x85 || c == 0xA0 || c == 0x1680 || (c >= 0x2000 && c <= 0x200A) ||
           c == 0x2028 || c == 0x2029 || c == 0x202F || c == 0x205F || c == 0x3000;
})

lust_str lust_str_trim(lust_str s) LUST_BODY({
    uint64_t a = 0, b = s.len;
    while (a < b) { uint64_t j = a; if (!lust_is_space(lust_utf8_next(s.ptr, &j))) break; a = j; }
    while (b > a) {
        uint64_t k = b - 1;
        while (k > a && (s.ptr[k] & 0xC0) == 0x80) k--;
        uint64_t j = k;
        if (!lust_is_space(lust_utf8_next(s.ptr, &j))) break;
        b = k;
    }
    lust_str r; r.ptr = s.ptr + a; r.len = b - a;
    return r;
})

/* ASCII case mapping. Non-ASCII characters are copied unchanged (Rust maps them too). */
lust_String lust_str_ascii_case(lust_str s, int upper) LUST_BODY({
    lust_String r = lust_string_from(s);
    for (uint64_t i = 0; i < r.len; i++) {
        uint8_t c = r.ptr[i];
        if (upper && c >= 'a' && c <= 'z') r.ptr[i] = c - 32;
        if (!upper && c >= 'A' && c <= 'Z') r.ptr[i] = c + 32;
    }
    return r;
})

typedef struct { lust_str s; uint64_t pos; } lust_Chars;
lust_Chars lust_chars(lust_str s) LUST_BODY({ lust_Chars c; c.s = s; c.pos = 0; return c; })
uint64_t lust_chars_count(lust_Chars c) LUST_BODY({
    uint64_t n = 0;
    while (c.pos < c.s.len) { lust_utf8_next(c.s.ptr, &c.pos); n++; }
    return n;
})

/* char::to_digit. Returns 0xFFFFFFFF for "not a digit". */
uint32_t lust_digit(uint32_t c, uint32_t radix, lust_loc loc) LUST_BODY({
    if (radix < 2 || radix > 36) lust_panic_cstr("to_digit: radix is too high (maximum 36)", loc);
    uint32_t d = c >= '0' && c <= '9' ? c - '0' : (c | 32) >= 'a' && (c | 32) <= 'z' ? (c | 32) - 'a' + 10 : 0xFFFFFFFFu;
    return d < radix ? d : 0xFFFFFFFFu;
})

/* Float formatting, parsing, and casts (src/rt/float.h). */
#include "float.h"
