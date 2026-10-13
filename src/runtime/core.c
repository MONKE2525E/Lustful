/* tcc predefines __STDC_VERSION__ as 199901L, so glibc hides the C11
   aligned_alloc declaration; without an explicit declaration tcc truncates
   its pointer return to int (spike K3-18). Declare both aligned entry
   points here. */
void *aligned_alloc(size_t alignment, size_t size);
int posix_memalign(void **memptr, size_t alignment, size_t size);

void lust_oom(void) LUST_BODY({ fputs("memory allocation failed\n", stderr); abort(); })

void lust_oom_size(uint64_t n) LUST_BODY({
    fprintf(stderr, "memory allocation of %llu bytes failed\n", (unsigned long long)n);
    abort();
})

/* The `alloc(size, align)` intrinsic family (ARCH 3.2). `align` is a power
   of two, as Rust's Layout guarantees. Alignment up to 4 MiB works (the
   ts-rust jemalloc case). A zero size returns a dangling pointer with the
   requested alignment and allocates nothing; well-formed wrappers never
   ask for one, but the Vec core uses the same form for empty buffers.
   Every pointer these return can go to plain free(). */
void *lust_alloc(uint64_t size, uint64_t align) LUST_BODY({
    if (!size) return (void *)(uintptr_t)(align ? align : 1);
    void *p = 0;
    if (align <= 16) p = malloc(size);
    else if (size % align == 0) p = aligned_alloc(align, size);
    else if (posix_memalign(&p, align, size) != 0) p = 0;
    if (!p) lust_oom_size(size);
    return p;
})

void *lust_alloc_zeroed(uint64_t size, uint64_t align) LUST_BODY({
    void *p = lust_alloc(size, align);
    if (size) memset(p, 0, size);
    return p;
})

void lust_dealloc(void *ptr, uint64_t size, uint64_t align) LUST_BODY({
    (void)align;
    if (size) free(ptr);
})

/* realloc(ptr, old_size, align, new_size): the Rust GlobalAlloc argument
   order with Layout flattened. Always moves when the alignment exceeds
   what plain realloc promises; the copy is the smaller size. */
void *lust_realloc(void *ptr, uint64_t old_size, uint64_t align, uint64_t new_size) LUST_BODY({
    if (!new_size) {
        lust_dealloc(ptr, old_size, align);
        return (void *)(uintptr_t)(align ? align : 1);
    }
    if (!old_size) return lust_alloc(new_size, align);
    void *p = lust_alloc(new_size, align);
    memcpy(p, ptr, old_size < new_size ? old_size : new_size);
    free(ptr);
    return p;
})

/* Byte and raw-pointer intrinsics (ARCH 3.2). ptr_read and ptr_write are
   unaligned byte copies of `size` bytes: read is (dst, src, size), write
   is (dst, src, size), matching memcpy argument order. ptr_offset adds a
   signed byte offset carried in a usize. */
void lust_memcpy(void *dst, const void *src, uint64_t n) LUST_BODY({ memcpy(dst, src, n); })
void lust_memmove(void *dst, const void *src, uint64_t n) LUST_BODY({ memmove(dst, src, n); })
void lust_memset(void *dst, uint32_t byte, uint64_t n) LUST_BODY({ memset(dst, (int)byte, n); })
int32_t lust_memcmp(const void *a, const void *b, uint64_t n) LUST_BODY({ return memcmp(a, b, n); })
void lust_ptr_read(void *dst, const void *src, uint64_t size) LUST_BODY({ memcpy(dst, src, size); })
void lust_ptr_write(void *dst, const void *src, uint64_t size) LUST_BODY({ memcpy(dst, src, size); })
void *lust_ptr_offset(void *ptr, uint64_t offset) LUST_BODY({ return (char *)ptr + (int64_t)offset; })

/* ---------- Strings ---------- */

/* Empty buffers hold the dangling aligned pointer, never null, as in
   Rust: that is what makes the pointer-word niche of String and Vec
   valid (an empty value's pointer word is never a niche tag value). */
lust_String lust_string_new(void) LUST_BODY({ lust_String s = {(uint8_t *)(uintptr_t)1, 0, 0}; return s; })

/* String capacity follows the Vec<u8> RawVec rules below: minimum
   capacity 8, then max(cap * 2, len + extra) on the amortized path and
   exactly len + extra on the exact path. */
void lust_string_reserve(lust_String *s, uint64_t extra) LUST_BODY({
    if (s->cap - s->len >= extra) return;
    uint64_t cap = s->cap * 2;
    if (cap < s->len + extra) cap = s->len + extra;
    if (cap < 8) cap = 8;
    s->ptr = lust_realloc(s->ptr, s->cap, 1, cap);
    s->cap = cap;
})

void lust_string_reserve_exact(lust_String *s, uint64_t extra) LUST_BODY({
    if (s->cap - s->len >= extra) return;
    uint64_t cap = s->len + extra;
    s->ptr = lust_realloc(s->ptr, s->cap, 1, cap);
    s->cap = cap;
})

lust_String lust_string_with_capacity(uint64_t n) LUST_BODY({
    lust_String s = {(uint8_t *)(uintptr_t)1, 0, 0};
    if (n) { s.ptr = lust_alloc(n, 1); s.cap = n; }
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
void lust_string_drop(lust_String *s) LUST_BODY({ lust_dealloc(s->ptr, s->cap, 1); })

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

#ifdef LUST_IMPL
#include "escape_table.h"

/* True when Rust's escape_debug writes this scalar as \u{...}:
   binary search over the generated range table. */
static int lust_escape_unicode(uint32_t c) {
    uint32_t lo = 0, hi = (uint32_t)(sizeof lust_escape_ranges / sizeof lust_escape_ranges[0]);
    while (lo < hi) {
        uint32_t mid = (lo + hi) / 2;
        if (c < lust_escape_ranges[mid][0]) hi = mid;
        else if (c > lust_escape_ranges[mid][1]) lo = mid + 1;
        else return 1;
    }
    return 0;
}
#endif

/* Debug text of a function pointer: `0x` and the address in lowercase
   hex with no leading zeroes, as Rust prints it. */
void lust_fmt_fnptr_debug(lust_String *out, const void *p) LUST_BODY({
    uint64_t v = (uint64_t)(uintptr_t)p;
    char buf[16];
    int n = 0;
    lust_string_push_cstr(out, "0x");
    if (!v) {
        lust_string_push_cstr(out, "0");
        return;
    }
    while (v) {
        buf[n++] = "0123456789abcdef"[v & 15];
        v >>= 4;
    }
    while (n) lust_string_push_char(out, (uint32_t)buf[--n]);
})

void lust_fmt_escape(lust_String *out, uint32_t c, uint32_t quote) LUST_BODY({
    switch (c) {
    case '\t': lust_string_push_cstr(out, "\\t"); return;
    case '\r': lust_string_push_cstr(out, "\\r"); return;
    case '\n': lust_string_push_cstr(out, "\\n"); return;
    case '\\': lust_string_push_cstr(out, "\\\\"); return;
    case 0: lust_string_push_cstr(out, "\\0"); return;
    }
    if (c == quote) { lust_string_push_bytes(out, "\\", 1); lust_string_push_char(out, c); return; }
    if (lust_escape_unicode(c)) {
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
    lust_dealloc(s->ptr, s->cap, 1);
})

void lust_flush(void) LUST_BODY({ fflush(stdout); })

/* The `exit` intrinsic behind std::process::exit: lust print output is
   buffered in stdio, so flush before the libc exit. Destructors do not
   run, as in Rust. */
void lust_exit(int32_t code) LUST_BODY({ fflush(stdout); exit(code); })

/* ---------- Vec ---------- */

/* Erased Vec core (ARCH 3.3): capacity rules copy Rust 1.99 RawVec, so
   `capacity()` in the typed layer matches rustc byte for byte.
   - Minimum non-zero capacity: 8 elements when the element size is 1,
     4 when it is 2 to 1024, 1 above 1024.
   - Amortized reserve grows to max(cap * 2, len + extra, minimum).
   - Exact reserve and with_capacity take exactly the requested count.
   - A zero-sized element never allocates and reports capacity
     UINT64_MAX (usize::MAX), with a dangling aligned pointer.
   - A byte size above isize::MAX is a capacity overflow, as in Rust.
   The typed layer owns the shrink_to length assert; this core clamps
   the target at len, which is the same end state. */
void lust_vec_capacity_overflow(void) LUST_BODY({ fputs("capacity overflow\n", stderr); abort(); })

void lust_vec_grow_to(lust_Vec *v, uint64_t new_cap, uint64_t elem, uint64_t align) LUST_BODY({
    if (new_cap > (uint64_t)9223372036854775807ull / elem) lust_vec_capacity_overflow();
    v->ptr = lust_realloc(v->ptr, v->cap * elem, align, new_cap * elem);
    v->cap = new_cap;
})

void lust_vec_set_zst(lust_Vec *v, uint64_t align) LUST_BODY({
    v->ptr = (void *)(uintptr_t)(align ? align : 1);
    v->cap = 18446744073709551615ull;
})

void lust_vec_reserve(lust_Vec *v, uint64_t extra, uint64_t elem, uint64_t align) LUST_BODY({
    if (!elem) { lust_vec_set_zst(v, align); return; }
    if (v->cap - v->len >= extra) return;
    uint64_t needed = v->len + extra;
    if (needed < v->len) lust_vec_capacity_overflow();
    uint64_t cap = v->cap * 2;
    if (cap < needed) cap = needed;
    uint64_t min_cap = elem == 1 ? 8 : elem <= 1024 ? 4 : 1;
    if (cap < min_cap) cap = min_cap;
    lust_vec_grow_to(v, cap, elem, align);
})

void lust_vec_reserve_exact(lust_Vec *v, uint64_t extra, uint64_t elem, uint64_t align) LUST_BODY({
    if (!elem) { lust_vec_set_zst(v, align); return; }
    if (v->cap - v->len >= extra) return;
    uint64_t needed = v->len + extra;
    if (needed < v->len) lust_vec_capacity_overflow();
    lust_vec_grow_to(v, needed, elem, align);
})

lust_Vec lust_vec_with_capacity(uint64_t n, uint64_t elem, uint64_t align) LUST_BODY({
    lust_Vec v = {(void *)(uintptr_t)(align ? align : 1), 0, 0};
    if (!elem) { lust_vec_set_zst(&v, align); return v; }
    if (n) {
        if (n > (uint64_t)9223372036854775807ull / elem) lust_vec_capacity_overflow();
        v.ptr = lust_alloc(n * elem, align);
        v.cap = n;
    }
    return v;
})

void lust_vec_shrink_to(lust_Vec *v, uint64_t min_cap, uint64_t elem, uint64_t align) LUST_BODY({
    if (!elem) return;
    uint64_t target = min_cap > v->len ? min_cap : v->len;
    if (v->cap <= target) return;
    if (!target) {
        free(v->ptr);
        v->ptr = (void *)(uintptr_t)(align ? align : 1);
        v->cap = 0;
        return;
    }
    v->ptr = lust_realloc(v->ptr, v->cap * elem, align, target * elem);
    v->cap = target;
})

void *lust_vec_push_slot(lust_Vec *v, uint64_t elem, uint64_t align) LUST_BODY({
    lust_vec_reserve(v, 1, elem, align);
    return (char *)v->ptr + (v->len++) * elem;
})

/* The end of a slice range, checked the way Rust checks it: the start must
   not pass the end, and the end must not pass the length. An inclusive end
   of u64::MAX overflows the +1 and always fails the length check. */
uint64_t lust_slice_range(uint64_t lo, uint64_t hi, int inclusive, uint64_t len, lust_loc loc) LUST_BODY({
    uint64_t end = inclusive ? hi + 1 : hi;
    if ((inclusive && end == 0) || lo > end || end > len) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "slice index starts at ");
        lust_fmt_u64(&s, lo);
        lust_string_push_cstr(&s, " but ends at ");
        lust_fmt_u64(&s, inclusive ? hi : end);
        lust_panic(&s, loc);
    }
    return end;
})

/* The end of a str slice range: the slice range checks, plus both
   bounds must lie on UTF-8 char boundaries (the end of the string or
   a byte that is not a continuation byte), as Rust checks. */
uint64_t lust_str_range(const uint8_t *ptr, uint64_t lo, uint64_t hi, int inclusive, uint64_t len, lust_loc loc) LUST_BODY({
    uint64_t end = lust_slice_range(lo, hi, inclusive, len, loc);
    int lo_ok = lo == len || (ptr[lo] & 0xC0) != 0x80;
    int end_ok = end == len || (ptr[end] & 0xC0) != 0x80;
    if (!lo_ok || !end_ok) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "byte index ");
        lust_fmt_u64(&s, lo_ok ? end : lo);
        lust_string_push_cstr(&s, " is not a char boundary");
        lust_panic(&s, loc);
    }
    return end;
})

/* Exact float remainder (Rust `%`, truncating division), computed on the
   mantissa integers so no libm link is needed. The algorithm is the
   standard normalize-and-subtract loop over the exponent difference. */
double lust_fmod_f64(double x, double y) LUST_BODY({
    union { double f; uint64_t i; } ux, uy;
    ux.f = x;
    uy.f = y;
    int ex = (int)((ux.i >> 52) & 0x7ff);
    int ey = (int)((uy.i >> 52) & 0x7ff);
    uint64_t sx = ux.i >> 63;
    uint64_t ax = ux.i & (UINT64_MAX >> 1);
    uint64_t ay = uy.i & (UINT64_MAX >> 1);
    ux.i &= (1ULL << 52) - 1;
    uy.i &= (1ULL << 52) - 1;
    if (ay == 0 || ex == 0x7ff || (ey == 0x7ff && (ay & ((1ULL << 52) - 1)) != 0) || ax > 0x7ff0000000000000ULL) {
        return (x * y) / (x * y); /* NaN */
    }
    if (ax <= ay) {
        if (ax == ay) {
            ux.f = 0.0;
            ux.i |= sx << 63;
            return ux.f;
        }
        return x;
    }
    /* Normalize both mantissas to 53-bit integers. */
    if (ex == 0) {
        uint64_t i = ux.i;
        for (; !(i >> 52); i <<= 1) ex--;
        ux.i = i;
        ex += 1;
    } else {
        ux.i |= 1ULL << 52;
    }
    if (ey == 0) {
        uint64_t i = uy.i;
        for (; !(i >> 52); i <<= 1) ey--;
        uy.i = i;
        ey += 1;
    } else {
        uy.i |= 1ULL << 52;
    }
    for (; ex > ey; ex--) {
        if (ux.i >= uy.i) {
            ux.i -= uy.i;
            if (ux.i == 0) {
                ux.f = 0.0;
                ux.i |= sx << 63;
                return ux.f;
            }
        }
        ux.i <<= 1;
    }
    if (ux.i >= uy.i) {
        ux.i -= uy.i;
        if (ux.i == 0) {
            ux.f = 0.0;
            ux.i |= sx << 63;
            return ux.f;
        }
    }
    while (!(ux.i >> 52)) {
        ux.i <<= 1;
        ey--;
    }
    if (ey > 0) {
        ux.i -= 1ULL << 52;
        ux.i |= (uint64_t)ey << 52;
    } else {
        ux.i >>= (uint64_t)(1 - ey);
    }
    ux.i |= sx << 63;
    return ux.f;
})

float lust_fmod_f32(float x, float y) LUST_BODY({
    /* The f64 remainder of two f32 values is exact, and its result is an
       f32 value, so one rounding at the end is exact. */
    return (float)lust_fmod_f64((double)x, (double)y);
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

/* ---------- Checked, saturating, and bit ops on 64-bit words ----------
   One generic form for the checked_* and overflowing_* methods:
   operands arrive masked to the operand width (sign bits above the
   width are the caller's to mask off first), the result leaves
   masked the same way. Returns 1 on success, 0 on overflow (the
   wrapping result is still in *out), and -1 for division by zero.
   Ops: 0 add, 1 sub, 2 mul, 3 div, 4 rem. */

static uint64_t lust_mask64(unsigned bits) LUST_BODY({
    return bits >= 64 ? ~0ull : ((1ull << bits) - 1ull);
})
static int64_t lust_sext64(uint64_t v, unsigned bits) LUST_BODY({
    if (bits >= 64) return (int64_t)v;
    if (v & (1ull << (bits - 1))) return (int64_t)(v | ~lust_mask64(bits));
    return (int64_t)v;
})

int lust_checked_op(uint64_t a, uint64_t b, unsigned bits, int is_signed, int op, uint64_t *out) LUST_BODY({
    uint64_t mask = lust_mask64(bits);
    a &= mask;
    b &= mask;
    if (is_signed) {
        int64_t sa = lust_sext64(a, bits), sb = lust_sext64(b, bits);
        int64_t minv = bits >= 64 ? INT64_MIN : -(1ll << (bits - 1));
        int64_t maxv = bits >= 64 ? INT64_MAX : ((1ll << (bits - 1)) - 1);
        int64_t r = 0;
        int ok = 1;
        switch (op) {
            case 0:
                r = (int64_t)((uint64_t)sa + (uint64_t)sb);
                ok = bits < 64 ? (r >= minv && r <= maxv) : !(((sa ^ r) & (sb ^ r)) < 0);
                break;
            case 1:
                r = (int64_t)((uint64_t)sa - (uint64_t)sb);
                ok = bits < 64 ? (r >= minv && r <= maxv) : !(((sa ^ sb) & (sa ^ r)) < 0);
                break;
            case 2:
                r = (int64_t)((uint64_t)sa * (uint64_t)sb);
                if (bits < 64) {
                    ok = (r >= minv && r <= maxv);
                } else if (sa == 0 || sb == 0) {
                    ok = 1;
                } else if ((sa == -1 && sb == INT64_MIN) || (sb == -1 && sa == INT64_MIN)) {
                    ok = 0;
                } else {
                    ok = (r / sb == sa);
                }
                break;
            case 3:
            case 4:
                if (sb == 0) return -1;
                if (sa == minv && sb == -1) {
                    *out = (op == 3 ? (uint64_t)sa : 0ull) & mask;
                    return 0;
                }
                r = op == 3 ? sa / sb : sa % sb;
                break;
            default:
                return 0;
        }
        *out = (uint64_t)r & mask;
        return ok;
    }
    {
        uint64_t r = 0;
        int ok = 1;
        switch (op) {
            case 0:
                r = a + b;
                ok = bits < 64 ? (r <= mask) : (r >= a);
                break;
            case 1:
                r = a - b;
                ok = (a >= b);
                break;
            case 2:
                r = a * b;
                ok = bits < 64 ? (r <= mask) : (a == 0 || r / a == b);
                break;
            case 3:
                if (b == 0) return -1;
                r = a / b;
                break;
            case 4:
                if (b == 0) return -1;
                r = a % b;
                break;
            default:
                return 0;
        }
        *out = r & mask;
        return ok;
    }
})

/* checked_pow on the same representation: squaring loop, and the
   final unused square is not computed, as in core. */
int lust_checked_pow(uint64_t a, uint32_t e, unsigned bits, int is_signed, uint64_t *out) LUST_BODY({
    uint64_t r = 1, x = a & lust_mask64(bits), t;
    while (e) {
        if (e & 1) {
            if (!lust_checked_op(r, x, bits, is_signed, 2, &t)) {
                *out = t;
                return 0;
            }
            r = t;
        }
        e >>= 1;
        if (!e) break;
        if (!lust_checked_op(x, x, bits, is_signed, 2, &t)) {
            *out = t;
            return 0;
        }
        x = t;
    }
    *out = r;
    return 1;
})

/* wrapping_pow on the same representation: no checks at all. */
uint64_t lust_wrapping_pow(uint64_t a, uint32_t e, unsigned bits) LUST_BODY({
    uint64_t mask = lust_mask64(bits);
    uint64_t r = 1, x = a & mask;
    while (e) {
        if (e & 1) r = (r * x) & mask;
        e >>= 1;
        if (!e) break;
        x = (x * x) & mask;
    }
    return r & mask;
})

/* Euclid division: the quotient rounds toward negative infinity,
   the remainder is never negative. Both panic exactly as the plain
   operators do for a zero divisor and for MIN / -1. */
uint64_t lust_div_euclid(uint64_t a, uint64_t b, unsigned bits, int is_signed, lust_loc loc) LUST_BODY({
    uint64_t mask = lust_mask64(bits);
    a &= mask;
    b &= mask;
    if (!is_signed) {
        if (b == 0) lust_panic_cstr("attempt to divide by zero", loc);
        return a / b;
    }
    {
        int64_t sa = lust_sext64(a, bits), sb = lust_sext64(b, bits);
        int64_t minv = bits >= 64 ? INT64_MIN : -(1ll << (bits - 1));
        int64_t q;
        if (sb == 0) lust_panic_cstr("attempt to divide by zero", loc);
        if (sa == minv && sb == -1) LUST_OVF("divide");
        q = sa / sb;
        if (sa % sb < 0) q += sb > 0 ? -1 : 1;
        return (uint64_t)q & mask;
    }
})
uint64_t lust_rem_euclid(uint64_t a, uint64_t b, unsigned bits, int is_signed, lust_loc loc) LUST_BODY({
    uint64_t mask = lust_mask64(bits);
    a &= mask;
    b &= mask;
    if (!is_signed) {
        if (b == 0) lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc);
        return a % b;
    }
    {
        int64_t sa = lust_sext64(a, bits), sb = lust_sext64(b, bits);
        int64_t minv = bits >= 64 ? INT64_MIN : -(1ll << (bits - 1));
        int64_t r;
        if (sb == 0) lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc);
        if (sa == minv && sb == -1) LUST_OVF("calculate the remainder");
        r = sa % sb;
        if (r < 0) r += sb > 0 ? sb : -sb;
        return (uint64_t)r & mask;
    }
})

uint32_t lust_count_ones64(uint64_t v) LUST_BODY({
    v = v - ((v >> 1) & 0x5555555555555555ull);
    v = (v & 0x3333333333333333ull) + ((v >> 2) & 0x3333333333333333ull);
    v = (v + (v >> 4)) & 0x0F0F0F0F0F0F0F0Full;
    return (uint32_t)((v * 0x0101010101010101ull) >> 56);
})
uint32_t lust_leading_zeros64(uint64_t v, unsigned bits) LUST_BODY({
    uint32_t n = 0;
    int i;
    if (v == 0) return bits;
    for (i = 63; i >= 0 && !((v >> i) & 1ull); i--) n++;
    return n - (64 - bits);
})
uint32_t lust_trailing_zeros64(uint64_t v, unsigned bits) LUST_BODY({
    uint32_t n = 0;
    unsigned i;
    if (v == 0) return bits;
    for (i = 0; i < bits && !((v >> i) & 1ull); i++) n++;
    return n;
})

/* ---------- 128-bit integers ---------- */

/* Two-word helpers over lust_u128/lust_i128. Division is Knuth's
   Algorithm D over 32-bit limbs (the spike's bit-by-bit divider took
   1673 ns; this one is two orders of magnitude less), and formatting
   divides by 10^19 chunks through the 128-by-64 fast path. Checked
   wrappers panic with the same texts as the narrow types above. */

lust_u128 lust_u128_from_i128(lust_i128 a) LUST_BODY({ lust_u128 r; r.lo = a.lo; r.hi = a.hi; return r; })
lust_i128 lust_i128_from_u128(lust_u128 a) LUST_BODY({ lust_i128 r; r.lo = a.lo; r.hi = a.hi; return r; })

lust_u128 lust_u128_add(lust_u128 a, lust_u128 b) LUST_BODY({
    lust_u128 r;
    r.lo = a.lo + b.lo;
    r.hi = a.hi + b.hi + (r.lo < a.lo);
    return r;
})
lust_u128 lust_u128_sub(lust_u128 a, lust_u128 b) LUST_BODY({
    lust_u128 r;
    r.lo = a.lo - b.lo;
    r.hi = a.hi - b.hi - (a.lo < b.lo);
    return r;
})
lust_i128 lust_i128_add(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_add(lust_u128_from_i128(a), lust_u128_from_i128(b))); })
lust_i128 lust_i128_sub(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_sub(lust_u128_from_i128(a), lust_u128_from_i128(b))); })

int32_t lust_u128_cmp(lust_u128 a, lust_u128 b) LUST_BODY({
    if (a.hi != b.hi) return a.hi < b.hi ? -1 : 1;
    if (a.lo != b.lo) return a.lo < b.lo ? -1 : 1;
    return 0;
})
int32_t lust_i128_cmp(lust_i128 a, lust_i128 b) LUST_BODY({
    int64_t ah = (int64_t)a.hi, bh = (int64_t)b.hi;
    if (ah != bh) return ah < bh ? -1 : 1;
    if (a.lo != b.lo) return a.lo < b.lo ? -1 : 1;
    return 0;
})

lust_u128 lust_u128_and(lust_u128 a, lust_u128 b) LUST_BODY({ lust_u128 r; r.lo = a.lo & b.lo; r.hi = a.hi & b.hi; return r; })
lust_u128 lust_u128_or(lust_u128 a, lust_u128 b) LUST_BODY({ lust_u128 r; r.lo = a.lo | b.lo; r.hi = a.hi | b.hi; return r; })
lust_u128 lust_u128_xor(lust_u128 a, lust_u128 b) LUST_BODY({ lust_u128 r; r.lo = a.lo ^ b.lo; r.hi = a.hi ^ b.hi; return r; })
lust_u128 lust_u128_not(lust_u128 a) LUST_BODY({ lust_u128 r; r.lo = ~a.lo; r.hi = ~a.hi; return r; })
lust_i128 lust_i128_and(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_and(lust_u128_from_i128(a), lust_u128_from_i128(b))); })
lust_i128 lust_i128_or(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_or(lust_u128_from_i128(a), lust_u128_from_i128(b))); })
lust_i128 lust_i128_xor(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_xor(lust_u128_from_i128(a), lust_u128_from_i128(b))); })
lust_i128 lust_i128_not(lust_i128 a) LUST_BODY({ return lust_i128_from_u128(lust_u128_not(lust_u128_from_i128(a))); })

/* Full 64x64->128 product through 32-bit halves. Returns the low word;
   the high word goes to *hi. */
uint64_t lust_u128_mul64(uint64_t a, uint64_t b, uint64_t *hi) LUST_BODY({
    uint64_t al = a & 0xFFFFFFFFull, ah = a >> 32;
    uint64_t bl = b & 0xFFFFFFFFull, bh = b >> 32;
    uint64_t ll = al * bl, lh = al * bh, hl = ah * bl, hh = ah * bh;
    uint64_t mid = lh + (ll >> 32) + (hl & 0xFFFFFFFFull);
    *hi = hh + (hl >> 32) + (mid >> 32);
    return (mid << 32) | (ll & 0xFFFFFFFFull);
})

lust_u128 lust_u128_mul(lust_u128 a, lust_u128 b) LUST_BODY({
    lust_u128 r;
    uint64_t hi;
    r.lo = lust_u128_mul64(a.lo, b.lo, &hi);
    r.hi = hi + a.lo * b.hi + a.hi * b.lo;
    return r;
})
lust_i128 lust_i128_mul(lust_i128 a, lust_i128 b) LUST_BODY({ return lust_i128_from_u128(lust_u128_mul(lust_u128_from_i128(a), lust_u128_from_i128(b))); })

lust_u128 lust_u128_shl(lust_u128 a, uint32_t n) LUST_BODY({
    lust_u128 r;
    if (n >= 64) { r.lo = 0; r.hi = a.lo << (n - 64); }
    else if (n) { r.lo = a.lo << n; r.hi = (a.hi << n) | (a.lo >> (64 - n)); }
    else r = a;
    return r;
})
lust_u128 lust_u128_shr(lust_u128 a, uint32_t n) LUST_BODY({
    lust_u128 r;
    if (n >= 64) { r.lo = a.hi >> (n - 64); r.hi = 0; }
    else if (n) { r.lo = (a.lo >> n) | (a.hi << (64 - n)); r.hi = a.hi >> n; }
    else r = a;
    return r;
})
lust_i128 lust_i128_shl(lust_i128 a, uint32_t n) LUST_BODY({ return lust_i128_from_u128(lust_u128_shl(lust_u128_from_i128(a), n)); })
lust_i128 lust_i128_shr(lust_i128 a, uint32_t n) LUST_BODY({
    lust_i128 r;
    if (n >= 64) { r.lo = (uint64_t)((int64_t)a.hi >> (n - 64)); r.hi = (uint64_t)((int64_t)a.hi >> 63); }
    else if (n) { r.lo = (a.lo >> n) | (a.hi << (64 - n)); r.hi = (uint64_t)((int64_t)a.hi >> n); }
    else r = a;
    return r;
})

uint32_t lust_u128_clz32(uint32_t x) LUST_BODY({
    uint32_t n = 0;
    if (!(x >> 16)) { n += 16; x <<= 16; }
    if (!(x >> 24)) { n += 8; x <<= 8; }
    if (!(x >> 28)) { n += 4; x <<= 4; }
    if (!(x >> 30)) { n += 2; x <<= 2; }
    if (!(x >> 31)) n += 1;
    return n;
})

/* Unsigned 128/128. The caller guarantees b != 0. A one-limb divisor
   takes the schoolbook loop; wider divisors take Knuth's Algorithm D
   in base 2^32. */
lust_u128 lust_u128_divmod(lust_u128 a, lust_u128 b, lust_u128 *rem) LUST_BODY({
    if (lust_u128_cmp(a, b) < 0) {
        if (rem) *rem = a;
        lust_u128 z = {0, 0};
        return z;
    }
    uint32_t bl[4] = {(uint32_t)b.lo, (uint32_t)(b.lo >> 32), (uint32_t)b.hi, (uint32_t)(b.hi >> 32)};
    uint32_t al[4] = {(uint32_t)a.lo, (uint32_t)(a.lo >> 32), (uint32_t)a.hi, (uint32_t)(a.hi >> 32)};
    if (!bl[1] && !bl[2] && !bl[3]) {
        uint64_t d = bl[0], r = 0;
        uint32_t q[4];
        for (int i = 3; i >= 0; i--) {
            uint64_t t = (r << 32) | al[i];
            q[i] = (uint32_t)(t / d);
            r = t - (uint64_t)q[i] * d;
        }
        if (rem) { rem->lo = r; rem->hi = 0; }
        lust_u128 out;
        out.lo = (uint64_t)q[0] | ((uint64_t)q[1] << 32);
        out.hi = (uint64_t)q[2] | ((uint64_t)q[3] << 32);
        return out;
    }
    uint32_t u[5], v[4], q[4] = {0, 0, 0, 0};
    int n = bl[3] ? 4 : bl[2] ? 3 : 2;
    int m = 4;
    uint32_t s = lust_u128_clz32(bl[n - 1]);
    for (int i = n - 1; i > 0; i--) v[i] = s ? (bl[i] << s) | (bl[i - 1] >> (32 - s)) : bl[i];
    v[0] = bl[0] << s;
    u[4] = s ? al[3] >> (32 - s) : 0;
    for (int i = 3; i > 0; i--) u[i] = s ? (al[i] << s) | (al[i - 1] >> (32 - s)) : al[i];
    u[0] = al[0] << s;
    for (int j = m - n; j >= 0; j--) {
        uint64_t num = ((uint64_t)u[j + n] << 32) | u[j + n - 1];
        uint64_t qhat = num / v[n - 1];
        uint64_t rhat = num - qhat * v[n - 1];
        for (;;) {
            if (qhat > 0xFFFFFFFFull || qhat * v[n - 2] > ((rhat << 32) | u[j + n - 2])) {
                qhat--;
                rhat += v[n - 1];
                if (rhat <= 0xFFFFFFFFull) continue;
            }
            break;
        }
        int64_t borrow = 0;
        uint64_t carry = 0;
        for (int k = 0; k < n; k++) {
            uint64_t p = qhat * v[k] + carry;
            carry = p >> 32;
            int64_t t = (int64_t)u[j + k] - borrow - (int64_t)(uint32_t)p;
            u[j + k] = (uint32_t)t;
            borrow = t < 0 ? 1 : 0;
        }
        int64_t t = (int64_t)u[j + n] - borrow - (int64_t)carry;
        u[j + n] = (uint32_t)t;
        q[j] = (uint32_t)qhat;
        if (t < 0) {
            q[j]--;
            uint64_t c = 0;
            for (int k = 0; k < n; k++) {
                uint64_t sum = (uint64_t)u[j + k] + v[k] + c;
                u[j + k] = (uint32_t)sum;
                c = sum >> 32;
            }
            u[j + n] = (uint32_t)((uint64_t)u[j + n] + c);
        }
    }
    if (rem) {
        uint32_t r[4] = {0, 0, 0, 0};
        for (int i = 0; i < n; i++) r[i] = s ? (u[i] >> s) | (u[i + 1] << (32 - s)) : u[i];
        rem->lo = (uint64_t)r[0] | ((uint64_t)r[1] << 32);
        rem->hi = (uint64_t)r[2] | ((uint64_t)r[3] << 32);
    }
    lust_u128 out;
    out.lo = (uint64_t)q[0] | ((uint64_t)q[1] << 32);
    out.hi = (uint64_t)q[2] | ((uint64_t)q[3] << 32);
    return out;
})

/* 128 divided by a one-word divisor (b != 0); the format path. */
lust_u128 lust_u128_divmod64(lust_u128 a, uint64_t b, uint64_t *rem) LUST_BODY({
    lust_u128 d = {b, 0}, r;
    lust_u128 q = lust_u128_divmod(a, d, &r);
    if (rem) *rem = r.lo;
    return q;
})

lust_u128 lust_add_u128(lust_u128 a, lust_u128 b, lust_loc loc) LUST_BODY({
    lust_u128 r = lust_u128_add(a, b);
    if (lust_u128_cmp(r, a) < 0) LUST_OVF("add");
    return r;
})
lust_u128 lust_sub_u128(lust_u128 a, lust_u128 b, lust_loc loc) LUST_BODY({
    if (lust_u128_cmp(b, a) > 0) LUST_OVF("subtract");
    return lust_u128_sub(a, b);
})
lust_u128 lust_mul_u128(lust_u128 a, lust_u128 b, lust_loc loc) LUST_BODY({
    lust_u128 r = lust_u128_mul(a, b);
    if ((a.lo || a.hi) && lust_u128_cmp(lust_u128_divmod(r, a, 0), b) != 0) LUST_OVF("multiply");
    return r;
})
lust_u128 lust_div_u128(lust_u128 a, lust_u128 b, lust_loc loc) LUST_BODY({
    if (!b.lo && !b.hi) lust_panic_cstr("attempt to divide by zero", loc);
    return lust_u128_divmod(a, b, 0);
})
lust_u128 lust_rem_u128(lust_u128 a, lust_u128 b, lust_loc loc) LUST_BODY({
    if (!b.lo && !b.hi) lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc);
    lust_u128 r;
    (void)lust_u128_divmod(a, b, &r);
    return r;
})

lust_u128 lust_i128_mag(lust_i128 a) LUST_BODY({
    lust_u128 u = lust_u128_from_i128(a);
    if ((int64_t)a.hi < 0) {
        lust_u128 z = {0, 0};
        return lust_u128_sub(z, u);
    }
    return u;
})

lust_i128 lust_add_i128(lust_i128 a, lust_i128 b, lust_loc loc) LUST_BODY({
    lust_i128 r = lust_i128_add(a, b);
    if (((a.hi ^ r.hi) & (b.hi ^ r.hi)) >> 63) LUST_OVF("add");
    return r;
})
lust_i128 lust_sub_i128(lust_i128 a, lust_i128 b, lust_loc loc) LUST_BODY({
    lust_i128 r = lust_i128_sub(a, b);
    if (((a.hi ^ b.hi) & (a.hi ^ r.hi)) >> 63) LUST_OVF("subtract");
    return r;
})
lust_i128 lust_neg_i128(lust_i128 a, lust_loc loc) LUST_BODY({
    if (a.lo == 0 && a.hi == 0x8000000000000000ull) LUST_OVF("negate");
    lust_i128 z = {0, 0};
    return lust_i128_sub(z, a);
})
lust_i128 lust_mul_i128(lust_i128 a, lust_i128 b, lust_loc loc) LUST_BODY({
    if ((!a.lo && !a.hi) || (!b.lo && !b.hi)) { lust_i128 z = {0, 0}; return z; }
    if (a.lo == 0 && a.hi == 0x8000000000000000ull && b.lo == 0xFFFFFFFFFFFFFFFFull && b.hi == 0xFFFFFFFFFFFFFFFFull) LUST_OVF("multiply");
    if (b.lo == 0 && b.hi == 0x8000000000000000ull && a.lo == 0xFFFFFFFFFFFFFFFFull && a.hi == 0xFFFFFFFFFFFFFFFFull) LUST_OVF("multiply");
    lust_i128 r = lust_i128_mul(a, b);
    /* Divide back, as the i64 helper does; the -1 edges are handled above. */
    lust_u128 q = lust_u128_divmod(lust_i128_mag(r), lust_i128_mag(b), 0);
    if (lust_u128_cmp(q, lust_i128_mag(a)) != 0) LUST_OVF("multiply");
    return r;
})
lust_i128 lust_div_i128(lust_i128 a, lust_i128 b, lust_loc loc) LUST_BODY({
    if (!b.lo && !b.hi) lust_panic_cstr("attempt to divide by zero", loc);
    if (a.lo == 0 && a.hi == 0x8000000000000000ull && b.lo == 0xFFFFFFFFFFFFFFFFull && b.hi == 0xFFFFFFFFFFFFFFFFull) LUST_OVF("divide");
    lust_u128 q = lust_u128_divmod(lust_i128_mag(a), lust_i128_mag(b), 0);
    if (((a.hi ^ b.hi) >> 63) & 1) {
        lust_u128 z = {0, 0};
        q = lust_u128_sub(z, q);
    }
    return lust_i128_from_u128(q);
})
lust_i128 lust_rem_i128(lust_i128 a, lust_i128 b, lust_loc loc) LUST_BODY({
    if (!b.lo && !b.hi) lust_panic_cstr("attempt to calculate the remainder with a divisor of zero", loc);
    if (a.lo == 0 && a.hi == 0x8000000000000000ull && b.lo == 0xFFFFFFFFFFFFFFFFull && b.hi == 0xFFFFFFFFFFFFFFFFull) LUST_OVF("calculate the remainder");
    lust_u128 r;
    (void)lust_u128_divmod(lust_i128_mag(a), lust_i128_mag(b), &r);
    if ((int64_t)a.hi < 0) {
        lust_u128 z = {0, 0};
        r = lust_u128_sub(z, r);
    }
    return lust_i128_from_u128(r);
})

lust_i128 lust_abs_i128(lust_i128 a, lust_loc loc) LUST_BODY({ return (int64_t)a.hi < 0 ? lust_neg_i128(a, loc) : a; })
lust_u128 lust_pow_u128(lust_u128 a, uint32_t e, lust_loc loc) LUST_BODY({
    lust_u128 r = {1, 0};
    while (e) { if (e & 1) r = lust_mul_u128(r, a, loc); e >>= 1; if (e) a = lust_mul_u128(a, a, loc); }
    return r;
})
lust_i128 lust_pow_i128(lust_i128 a, uint32_t e, lust_loc loc) LUST_BODY({
    lust_i128 r = {1, 0};
    while (e) { if (e & 1) r = lust_mul_i128(r, a, loc); e >>= 1; if (e) a = lust_mul_i128(a, a, loc); }
    return r;
})

/* Decimal format: split by 10^19, the largest power of ten in a word. */
void lust_fmt_u128(lust_String *out, lust_u128 v) LUST_BODY({
    if (!v.hi) { lust_fmt_u64(out, v.lo); return; }
    uint64_t chunks[3];
    int n = 0;
    while (v.lo || v.hi) {
        uint64_t r;
        v = lust_u128_divmod64(v, 10000000000000000000ull, &r);
        chunks[n++] = r;
    }
    lust_fmt_u64(out, chunks[--n]);
    char b[24];
    while (n > 0) {
        snprintf(b, sizeof b, "%019llu", (unsigned long long)chunks[--n]);
        lust_string_push_cstr(out, b);
    }
})
void lust_fmt_i128(lust_String *out, lust_i128 v) LUST_BODY({
    if ((int64_t)v.hi < 0) {
        lust_string_push_bytes(out, "-", 1);
        lust_fmt_u128(out, lust_i128_mag(v));
    } else {
        lust_fmt_u128(out, lust_u128_from_i128(v));
    }
})

/* Integer formatting with a format spec, as Rust renders it. `lo` and
   `hi` are the magnitude (already negated by the caller for decimal,
   raw two's-complement bits truncated to the type width for the radix
   modes, with `negative` clear). Modes: 0 decimal, 1 lower hex,
   2 upper hex, 3 octal, 4 binary. `align` is '<', '>', or '^', and
   0 for the numeric default (right). Precision is a minimum digit
   count; zero padding fills after the sign and radix prefix and is
   ignored when a precision is given, as in Rust. */
void lust_fmt_int_spec(lust_String *out, uint64_t lo, uint64_t hi, int negative, int mode, int plus, int alt, int zero_pad, uint32_t width, uint32_t fill, int align, int has_prec, uint32_t prec) LUST_BODY({
    static const char lo_digits[] = "0123456789abcdef";
    static const char up_digits[] = "0123456789ABCDEF";
    const char *digs = mode == 2 ? up_digits : lo_digits;
    uint64_t base = mode == 1 || mode == 2 ? 16 : mode == 3 ? 8 : mode == 4 ? 2 : 10;
    char rev[130];
    int nd = 0;
    lust_u128 v;
    v.lo = lo;
    v.hi = hi;
    if (!v.lo && !v.hi) {
        rev[nd++] = '0';
    } else {
        while (v.lo || v.hi) {
            uint64_t r;
            v = lust_u128_divmod64(v, base, &r);
            rev[nd++] = digs[r];
        }
    }
    const char *prefix = "";
    if (alt) prefix = mode == 1 ? "0x" : mode == 2 ? "0X" : mode == 3 ? "0o" : mode == 4 ? "0b" : "";
    uint64_t prefix_len = 0;
    while (prefix[prefix_len]) prefix_len++;
    int sign = negative ? '-' : plus ? '+' : 0;
    /* Precision is ignored for integers in Rust (it neither pads
       digits nor disables the zero flag). */
    uint32_t lead = 0;
    (void)has_prec; (void)prec;
    uint32_t total = (sign ? 1 : 0) + (uint32_t)prefix_len + lead + (uint32_t)nd;
    uint32_t zeros = 0;
    uint32_t left = 0, right = 0;
    if (zero_pad && total < width) {
        zeros = width - total;
        total = width;
    } else if (total < width) {
        uint32_t pad = width - total;
        if (align == '<') right = pad;
        else if (align == '^') { left = pad / 2; right = pad - left; }
        else left = pad;
    }
    uint32_t fill_cp = fill ? fill : ' ';
    for (uint32_t k = 0; k < left; k++) lust_string_push_char(out, fill_cp);
    if (sign) { char sc = (char)sign; lust_string_push_bytes(out, &sc, 1); }
    if (prefix_len) lust_string_push_bytes(out, prefix, prefix_len);
    for (uint32_t k = 0; k < zeros + lead; k++) lust_string_push_bytes(out, "0", 1);
    for (int k = nd - 1; k >= 0; k--) lust_string_push_bytes(out, &rev[k], 1);
    for (uint32_t k = 0; k < right; k++) lust_string_push_char(out, fill_cp);
})

/* The char count of a UTF-8 string view (non-continuation bytes). */
uint64_t lust_str_char_count(lust_str s) LUST_BODY({
    uint64_t n = 0;
    for (uint64_t i = 0; i < s.len; i++) if ((s.ptr[i] & 0xC0) != 0x80) n++;
    return n;
})

/* Appends `body` padded with `fill` to `width` chars: align '<'
   pads right, '^' centers (the larger half goes right, as in
   Rust), and anything else pads left. */
void lust_fmt_pad(lust_String *out, lust_str body, uint32_t width, uint32_t fill, int align) LUST_BODY({
    uint64_t count = lust_str_char_count(body);
    if (count >= width) { lust_string_push_str(out, body); return; }
    uint32_t pad = width - (uint32_t)count;
    uint32_t left = 0, right = 0;
    if (align == '<') right = pad;
    else if (align == '^') { left = pad / 2; right = pad - left; }
    else left = pad;
    uint32_t fill_cp = fill ? fill : ' ';
    for (uint32_t k = 0; k < left; k++) lust_string_push_char(out, fill_cp);
    lust_string_push_str(out, body);
    for (uint32_t k = 0; k < right; k++) lust_string_push_char(out, fill_cp);
})

/* Truncates a string to at most `chars` Unicode scalar values,
   cutting on a char boundary (a format precision for strings). */
void lust_str_trunc_chars(lust_String *s, uint32_t chars) LUST_BODY({
    uint32_t seen = 0;
    for (uint64_t i = 0; i < s->len; i++) {
        if ((s->ptr[i] & 0xC0) != 0x80) {
            if (seen == chars) { s->len = i; return; }
            seen++;
        }
    }
})

/* ---------- Vec insert/remove ---------- */

void lust_vec_insert_at(lust_Vec *v, uint64_t i, uint64_t elem, uint64_t align, lust_loc loc) LUST_BODY({
    if (i > v->len) {
        lust_String s = lust_string_new();
        lust_string_push_cstr(&s, "insertion index (is ");
        lust_fmt_u64(&s, i);
        lust_string_push_cstr(&s, ") should be <= len (is ");
        lust_fmt_u64(&s, v->len);
        lust_string_push_cstr(&s, ")");
        lust_panic(&s, loc);
    }
    lust_vec_reserve(v, 1, elem, align);
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

/* Float formatting, parsing, and casts (src/runtime/float.h). */
#include "float.h"

/* Erased hash table core (src/runtime/hash.h): declarations in every
   unit, bodies only in the runtime unit (LUST_IMPL). */
#include "hash.h"
