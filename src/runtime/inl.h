/* Inline fast paths of the hottest small runtime helpers, for units an optimizing C
   compiler builds (release builds have no LTO, so each helper would be a call into the
   runtime unit: atomic loads, Once checks, leading_zeros, slice ranges and division were
   about 10% of a release tsgo's cycles). Each macro keeps its function's name, arguments
   and result; a slow path (a panic, a grow, a wait) calls that function, which a
   function-like macro does not expand inside its own body. cgen appends this text after
   the runtime declarations (`unit_header`); tcc units and the runtime unit itself call
   the functions, and so does a build with -DLUST_NO_INL (for A/B timing). */
#if !defined(__TINYC__) && !defined(LUST_IMPL) && !defined(LUST_NO_INL)
/* lust's atomic ordering (0 Relaxed, 1 Release, 2 Acquire, 3 AcqRel, 4 SeqCst) as a C
   memory order, as sync.c LUST_MO. A load's Release and AcqRel orders panic: the
   function does that. */
#define lust_inl_mo_(o) ((o) == 0 ? __ATOMIC_RELAXED : (o) == 1 ? __ATOMIC_RELEASE : (o) == 2 ? __ATOMIC_ACQUIRE : (o) == 3 ? __ATOMIC_ACQ_REL : __ATOMIC_SEQ_CST)
#define lust_inl_load_(N, U, p, o, loc)                                                                     \
    __extension__({                                                                                         \
        U *lust_p_ = (p);                                                                                   \
        uint32_t lust_o_ = (o);                                                                             \
        __builtin_expect(lust_o_ == 1 || lust_o_ == 3, 0) ? lust_at_load_##N(lust_p_, lust_o_, (loc))      \
                                                          : __atomic_load_n(lust_p_, lust_inl_mo_(lust_o_)); \
    })
#define lust_at_load_1(p, o, loc) lust_inl_load_(1, uint8_t, p, o, loc)
#define lust_at_load_2(p, o, loc) lust_inl_load_(2, uint16_t, p, o, loc)
#define lust_at_load_4(p, o, loc) lust_inl_load_(4, uint32_t, p, o, loc)
#define lust_at_load_8(p, o, loc) lust_inl_load_(8, uint64_t, p, o, loc)

/* A Once is set when its state is 2 (sync.c): no compare-exchange, no wait. */
#define lust_once_is_done(st) (__atomic_load_n((st), __ATOMIC_ACQUIRE) == 2)
#define lust_once_begin(st)                                                                         \
    __extension__({                                                                                 \
        uint32_t *lust_st_ = (st);                                                                  \
        __builtin_expect(__atomic_load_n(lust_st_, __ATOMIC_ACQUIRE) == 2, 1) ? 0 : lust_once_begin(lust_st_); \
    })

#define lust_leading_zeros64(v, bits)                                                                  \
    __extension__({                                                                                    \
        uint64_t lust_v_ = (v);                                                                        \
        unsigned lust_b_ = (bits);                                                                     \
        lust_v_ ? (uint32_t)(__builtin_clzll(lust_v_) - (64 - lust_b_)) : (uint32_t)lust_b_;           \
    })

/* A slice range in bounds; the function panics in Rust's order otherwise. */
#define lust_slice_range(lo, hi, inclusive, len, loc)                                                  \
    __extension__({                                                                                    \
        uint64_t lust_lo_ = (lo), lust_hi_ = (hi), lust_len_ = (len);                                  \
        int lust_inc_ = (inclusive);                                                                   \
        uint64_t lust_end_ = lust_inc_ ? lust_hi_ + 1 : lust_hi_;                                      \
        __builtin_expect(lust_lo_ <= lust_len_ && (lust_inc_ ? lust_hi_ < lust_len_ : lust_hi_ <= lust_len_) && lust_lo_ <= lust_end_, 1) \
            ? lust_end_                                                                                \
            : lust_slice_range(lust_lo_, lust_hi_, lust_inc_, lust_len_, (loc));                       \
    })

#define lust_div_u64(a, b, loc) \
    __extension__({ uint64_t lust_a_ = (a), lust_d_ = (b); __builtin_expect(lust_d_ != 0, 1) ? lust_a_ / lust_d_ : lust_div_u64(lust_a_, lust_d_, (loc)); })
#define lust_rem_u64(a, b, loc) \
    __extension__({ uint64_t lust_a_ = (a), lust_d_ = (b); __builtin_expect(lust_d_ != 0, 1) ? lust_a_ % lust_d_ : lust_rem_u64(lust_a_, lust_d_, (loc)); })
#define lust_div_i64(a, b, loc)                                                                         \
    __extension__({                                                                                     \
        int64_t lust_a_ = (a), lust_d_ = (b);                                                           \
        __builtin_expect(lust_d_ != 0 && !(lust_a_ == INT64_MIN && lust_d_ == -1), 1) ? lust_a_ / lust_d_ : lust_div_i64(lust_a_, lust_d_, (loc)); \
    })
#define lust_rem_i64(a, b, loc)                                                                         \
    __extension__({                                                                                     \
        int64_t lust_a_ = (a), lust_d_ = (b);                                                           \
        __builtin_expect(lust_d_ != 0 && !(lust_a_ == INT64_MIN && lust_d_ == -1), 1) ? lust_a_ % lust_d_ : lust_rem_i64(lust_a_, lust_d_, (loc)); \
    })

/* The C compiler's own memcpy and memmove: a small constant copy (a from_le_bytes, a
   moved value) becomes loads and stores instead of two calls. A macro whose arguments
   may be compound literals (`&(T){a, b}`, `(lust_u128){lo, hi}`: the comma in the braces
   splits a macro argument list) takes `...`; one that names them binds them with a
   struct initializer. */
#define lust_memcpy(...) ((void)__builtin_memcpy(__VA_ARGS__))
#define lust_memmove(...) ((void)__builtin_memmove(__VA_ARGS__))

/* A push or reserve that fits the capacity; growth (and zero-sized elements) take the
   function. */
#define lust_vec_push_slot(v, elem, align)                                                             \
    __extension__({                                                                                    \
        lust_Vec *lust_v_ = (v);                                                                       \
        uint64_t lust_e_ = (elem);                                                                     \
        __builtin_expect(lust_e_ != 0 && lust_v_->len < lust_v_->cap, 1)                              \
            ? (void *)((char *)lust_v_->ptr + (lust_v_->len++) * lust_e_)                              \
            : lust_vec_push_slot(lust_v_, lust_e_, (align));                                           \
    })
#define lust_vec_reserve(v, extra, elem, align)                                                        \
    __extension__({                                                                                    \
        lust_Vec *lust_v_ = (v);                                                                       \
        uint64_t lust_x_ = (extra), lust_e_ = (elem);                                                  \
        if (!__builtin_expect(lust_e_ != 0 && lust_v_->cap - lust_v_->len >= lust_x_, 1))             \
            lust_vec_reserve(lust_v_, lust_x_, lust_e_, (align));                                      \
        (void)0;                                                                                       \
    })
/* Atomic stores, swaps, compare-exchanges and fetch ops: the orders that panic take
   the function, as the narrow loads above. */
#define lust_inl_mo_cas_(s, f) (((f) == 4) ? __ATOMIC_SEQ_CST : ((f) == 2 && ((s) == 0 || (s) == 1)) ? ((s) == 0 ? __ATOMIC_ACQUIRE : __ATOMIC_ACQ_REL) : lust_inl_mo_(s))
#define lust_inl_store_(N, U, p, v, o, loc)                                                             \
    __extension__({                                                                                     \
        U *lust_p_ = (p);                                                                               \
        U lust_v_ = (v);                                                                                \
        uint32_t lust_o_ = (o);                                                                         \
        if (__builtin_expect(lust_o_ == 2 || lust_o_ == 3, 0)) lust_at_store_##N(lust_p_, lust_v_, lust_o_, (loc)); \
        else __atomic_store_n(lust_p_, lust_v_, lust_inl_mo_(lust_o_));                                 \
        (void)0;                                                                                        \
    })
#define lust_at_store_1(p, v, o, loc) lust_inl_store_(1, uint8_t, p, v, o, loc)
#define lust_at_store_2(p, v, o, loc) lust_inl_store_(2, uint16_t, p, v, o, loc)
#define lust_at_store_4(p, v, o, loc) lust_inl_store_(4, uint32_t, p, v, o, loc)
#define lust_at_store_8(p, v, o, loc) lust_inl_store_(8, uint64_t, p, v, o, loc)
#define lust_inl_cas_(N, U, p, cur, nv, s, f, old, weak)                                                \
    __extension__({                                                                                     \
        U *lust_p_ = (p);                                                                               \
        U lust_c_ = (cur), lust_n_ = (nv);                                                              \
        uint32_t lust_s_ = (s), lust_f_ = (f);                                                          \
        U *lust_old_ = (old);                                                                           \
        int lust_w_ = (weak), lust_ok_;                                                                 \
        if (__builtin_expect(lust_f_ == 1 || lust_f_ == 3, 0)) {                                        \
            lust_ok_ = lust_at_cas_##N(lust_p_, lust_c_, lust_n_, lust_s_, lust_f_, lust_old_, lust_w_); \
        } else {                                                                                        \
            U lust_e_ = lust_c_;                                                                        \
            lust_ok_ = __atomic_compare_exchange_n(lust_p_, &lust_e_, lust_n_, 0, lust_inl_mo_cas_(lust_s_, lust_f_), lust_inl_mo_(lust_f_)); \
            *lust_old_ = lust_e_;                                                                       \
        }                                                                                               \
        lust_ok_;                                                                                       \
    })
#define lust_at_cas_1(p, c, n, s, f, o, w) lust_inl_cas_(1, uint8_t, p, c, n, s, f, o, w)
#define lust_at_cas_2(p, c, n, s, f, o, w) lust_inl_cas_(2, uint16_t, p, c, n, s, f, o, w)
#define lust_at_cas_4(p, c, n, s, f, o, w) lust_inl_cas_(4, uint32_t, p, c, n, s, f, o, w)
#define lust_at_cas_8(p, c, n, s, f, o, w) lust_inl_cas_(8, uint64_t, p, c, n, s, f, o, w)
#define lust_at_swap_1(p, v, o) __atomic_exchange_n((p), (v), lust_inl_mo_(o))
#define lust_at_swap_2(p, v, o) __atomic_exchange_n((p), (v), lust_inl_mo_(o))
#define lust_at_swap_4(p, v, o) __atomic_exchange_n((p), (v), lust_inl_mo_(o))
#define lust_at_swap_8(p, v, o) __atomic_exchange_n((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_add_1(p, v, o) __atomic_fetch_add((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_add_2(p, v, o) __atomic_fetch_add((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_add_4(p, v, o) __atomic_fetch_add((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_add_8(p, v, o) __atomic_fetch_add((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_sub_1(p, v, o) __atomic_fetch_sub((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_sub_2(p, v, o) __atomic_fetch_sub((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_sub_4(p, v, o) __atomic_fetch_sub((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_sub_8(p, v, o) __atomic_fetch_sub((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_and_1(p, v, o) __atomic_fetch_and((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_and_2(p, v, o) __atomic_fetch_and((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_and_4(p, v, o) __atomic_fetch_and((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_and_8(p, v, o) __atomic_fetch_and((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_or_1(p, v, o) __atomic_fetch_or((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_or_2(p, v, o) __atomic_fetch_or((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_or_4(p, v, o) __atomic_fetch_or((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_or_8(p, v, o) __atomic_fetch_or((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_xor_1(p, v, o) __atomic_fetch_xor((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_xor_2(p, v, o) __atomic_fetch_xor((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_xor_4(p, v, o) __atomic_fetch_xor((p), (v), lust_inl_mo_(o))
#define lust_at_fetch_xor_8(p, v, o) __atomic_fetch_xor((p), (v), lust_inl_mo_(o))

/* Bit counts with the compiler's builtins (the runtime loops for tcc; same results). */
#define lust_count_ones64(v) ((uint32_t)__builtin_popcountll((uint64_t)(v)))
#define lust_trailing_zeros64(v, bits)                                                                 \
    __extension__({                                                                                    \
        uint64_t lust_v_ = (v);                                                                        \
        uint32_t lust_b_ = (bits), lust_n_ = lust_v_ ? (uint32_t)__builtin_ctzll(lust_v_) : lust_b_;   \
        lust_n_ < lust_b_ ? lust_n_ : lust_b_;                                                         \
    })

/* Narrow division and remainder: zero (and MIN / -1) take the function, which panics. */
#define lust_inl_divu_(T, N, op, a, b, loc) \
    __extension__({ T lust_a_ = (a), lust_d_ = (b); __builtin_expect(lust_d_ != 0, 1) ? (T)(lust_a_ op lust_d_) : N(lust_a_, lust_d_, (loc)); })
#define lust_inl_divs_(T, MINV, N, op, a, b, loc)                                                       \
    __extension__({                                                                                     \
        T lust_a_ = (a), lust_d_ = (b);                                                                 \
        __builtin_expect(lust_d_ != 0 && !(lust_a_ == (MINV) && lust_d_ == -1), 1) ? (T)(lust_a_ op lust_d_) : N(lust_a_, lust_d_, (loc)); \
    })
#define lust_div_u8(a, b, loc) lust_inl_divu_(uint8_t, lust_div_u8, /, a, b, loc)
#define lust_rem_u8(a, b, loc) lust_inl_divu_(uint8_t, lust_rem_u8, %, a, b, loc)
#define lust_div_u16(a, b, loc) lust_inl_divu_(uint16_t, lust_div_u16, /, a, b, loc)
#define lust_rem_u16(a, b, loc) lust_inl_divu_(uint16_t, lust_rem_u16, %, a, b, loc)
#define lust_div_u32(a, b, loc) lust_inl_divu_(uint32_t, lust_div_u32, /, a, b, loc)
#define lust_rem_u32(a, b, loc) lust_inl_divu_(uint32_t, lust_rem_u32, %, a, b, loc)
#define lust_div_i8(a, b, loc) lust_inl_divs_(int8_t, -128, lust_div_i8, /, a, b, loc)
#define lust_rem_i8(a, b, loc) lust_inl_divs_(int8_t, -128, lust_rem_i8, %, a, b, loc)
#define lust_div_i16(a, b, loc) lust_inl_divs_(int16_t, -32768, lust_div_i16, /, a, b, loc)
#define lust_rem_i16(a, b, loc) lust_inl_divs_(int16_t, -32768, lust_rem_i16, %, a, b, loc)
#define lust_div_i32(a, b, loc) lust_inl_divs_(int32_t, -2147483647 - 1, lust_div_i32, /, a, b, loc)
#define lust_rem_i32(a, b, loc) lust_inl_divs_(int32_t, -2147483647 - 1, lust_rem_i32, %, a, b, loc)

/* An uncontended Mutex lock or unlock: one compare-exchange; a contended one (a waiter to
   wake, a wait) takes the function. */
#define lust_mutex_lock(st)                                                                             \
    __extension__({                                                                                     \
        uint32_t *lust_st_ = (st), lust_z_ = 0;                                                         \
        if (!__builtin_expect(__atomic_compare_exchange_n(lust_st_, &lust_z_, 1, 0, __ATOMIC_ACQUIRE, __ATOMIC_RELAXED), 1)) \
            lust_mutex_lock(lust_st_);                                                                  \
        (void)0;                                                                                        \
    })
#define lust_mutex_unlock(st)                                                                           \
    __extension__({                                                                                     \
        uint32_t *lust_st_ = (st), lust_one_ = 1;                                                       \
        if (!__builtin_expect(__atomic_compare_exchange_n(lust_st_, &lust_one_, 0, 0, __ATOMIC_RELEASE, __ATOMIC_RELAXED), 1)) \
            lust_mutex_unlock(lust_st_);                                                                \
        (void)0;                                                                                        \
    })

/* An empty Vec with no allocation (its dangling pointer is the alignment). */
#define lust_vec_with_capacity(n, elem, align)                                                         \
    __extension__({                                                                                    \
        uint64_t lust_n_ = (n), lust_e_ = (elem), lust_al_ = (align);                                  \
        __builtin_expect(lust_n_ == 0 && lust_e_ != 0, 1)                                              \
            ? (lust_Vec){(void *)(uintptr_t)(lust_al_ ? lust_al_ : 1), 0, 0}                           \
            : lust_vec_with_capacity(lust_n_, lust_e_, lust_al_);                                      \
    })

#define lust_string_as_str(s) __extension__({ lust_String *lust_s_ = (s); (lust_str){lust_s_->ptr, lust_s_->len}; })
#define lust_str_eq(...)                                                                               \
    __extension__({                                                                                    \
        struct { lust_str a, b; } lust_x_ = {__VA_ARGS__};                                             \
        (uint8_t)(lust_x_.a.len == lust_x_.b.len                                                       \
                  && (lust_x_.a.len == 0 || __builtin_memcmp(lust_x_.a.ptr, lust_x_.b.ptr, lust_x_.a.len) == 0)); \
    })

/* A thread-local's cell once the thread made it: thread.c's block (its first fields). */
typedef struct { void **cells; uint64_t cap; } lust_inl_tls_block_;
extern __thread lust_inl_tls_block_ *lust_tls_cur;
#define lust_tls_cell(key, size, align)                                                                \
    __extension__({                                                                                    \
        uint64_t *lust_k_ = (key), lust_s_ = *lust_k_;                                                 \
        lust_inl_tls_block_ *lust_b_ = lust_tls_cur;                                                   \
        __builtin_expect(lust_b_ && lust_s_ <= lust_b_->cap && lust_b_->cells[lust_s_ - 1], 1)          \
            ? lust_b_->cells[lust_s_ - 1]                                                              \
            : lust_tls_cell(lust_k_, (size), (align));                                                 \
    })

/* Checked add, sub and mul of 64-bit and narrower integers (op 0, 1, 2) with the
   compiler's overflow builtins; division and 128 bits take the function. As the
   function: the wrapped result, masked to `bits`, goes to *out; 1 when it fits. */
#define lust_checked_op(a, b, bits, is_signed, op, out)                                                \
    __extension__({                                                                                    \
        uint64_t lust_a_ = (a), lust_b_ = (b), *lust_o_ = (out);                                       \
        unsigned lust_n_ = (bits);                                                                     \
        int lust_sg_ = (is_signed), lust_op_ = (op), lust_ok_;                                         \
        if (lust_n_ == 64 && lust_op_ <= 2 && lust_sg_) {                                              \
            int64_t lust_r_, lust_x_ = (int64_t)lust_a_, lust_y_ = (int64_t)lust_b_;                   \
            lust_ok_ = !(lust_op_ == 0   ? __builtin_add_overflow(lust_x_, lust_y_, &lust_r_)           \
                         : lust_op_ == 1 ? __builtin_sub_overflow(lust_x_, lust_y_, &lust_r_)           \
                                         : __builtin_mul_overflow(lust_x_, lust_y_, &lust_r_));         \
            *lust_o_ = (uint64_t)lust_r_;                                                              \
        } else if (lust_n_ == 64 && lust_op_ <= 2) {                                                   \
            uint64_t lust_r_;                                                                          \
            lust_ok_ = !(lust_op_ == 0   ? __builtin_add_overflow(lust_a_, lust_b_, &lust_r_)           \
                         : lust_op_ == 1 ? __builtin_sub_overflow(lust_a_, lust_b_, &lust_r_)           \
                                         : __builtin_mul_overflow(lust_a_, lust_b_, &lust_r_));         \
            *lust_o_ = lust_r_;                                                                        \
        } else if (lust_n_ <= 32 && lust_op_ <= 2) {                                                   \
            /* Exact in 64 bits: the result fits when it is in the type's range. */                   \
            uint64_t lust_m_ = (1ull << lust_n_) - 1ull;                                               \
            lust_a_ &= lust_m_;                                                                        \
            lust_b_ &= lust_m_;                                                                        \
            if (lust_sg_) {                                                                            \
                uint64_t lust_h_ = 1ull << (lust_n_ - 1);                                              \
                int64_t lust_x_ = (int64_t)((lust_a_ ^ lust_h_) - lust_h_), lust_y_ = (int64_t)((lust_b_ ^ lust_h_) - lust_h_); \
                int64_t lust_r_ = lust_op_ == 0 ? lust_x_ + lust_y_ : lust_op_ == 1 ? lust_x_ - lust_y_ : lust_x_ * lust_y_; \
                *lust_o_ = (uint64_t)lust_r_ & lust_m_;                                                \
                lust_ok_ = lust_r_ >= -(int64_t)lust_h_ && lust_r_ < (int64_t)lust_h_;                 \
            } else {                                                                                   \
                uint64_t lust_r_ = lust_op_ == 0 ? lust_a_ + lust_b_ : lust_op_ == 1 ? lust_a_ - lust_b_ : lust_a_ * lust_b_; \
                *lust_o_ = lust_r_ & lust_m_;                                                          \
                lust_ok_ = lust_op_ == 1 ? lust_a_ >= lust_b_ : lust_r_ <= lust_m_;                    \
            }                                                                                          \
        } else                                                                                         \
            lust_ok_ = lust_checked_op(lust_a_, lust_b_, lust_n_, lust_sg_, lust_op_, lust_o_);         \
        lust_ok_;                                                                                      \
    })

#ifdef __SIZEOF_INT128__
/* 128-bit compares, products and shifts with the compiler's __int128 (the functions
   build them from 64-bit halves). A shift of 128 or more takes the function. */
#define lust_inl_w_(x) (((unsigned __int128)(x).hi << 64) | (x).lo)
#define lust_inl_u128_of_(v)                                                                           \
    __extension__({                                                                                    \
        unsigned __int128 lust_w_ = (v);                                                               \
        (lust_u128){(uint64_t)lust_w_, (uint64_t)(lust_w_ >> 64)};                                     \
    })
#define lust_u128_cmp(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_u128 a, b; } lust_x_ = {__VA_ARGS__};                                            \
        unsigned __int128 lust_l_ = lust_inl_w_(lust_x_.a), lust_r_ = lust_inl_w_(lust_x_.b);          \
        (int32_t)((lust_l_ > lust_r_) - (lust_l_ < lust_r_));                                          \
    })
#define lust_i128_cmp(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_i128 a, b; } lust_x_ = {__VA_ARGS__};                                            \
        __int128 lust_l_ = (__int128)lust_inl_w_(lust_x_.a), lust_r_ = (__int128)lust_inl_w_(lust_x_.b); \
        (int32_t)((lust_l_ > lust_r_) - (lust_l_ < lust_r_));                                          \
    })
#define lust_u128_mul(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_u128 a, b; } lust_x_ = {__VA_ARGS__};                                            \
        lust_inl_u128_of_(lust_inl_w_(lust_x_.a) * lust_inl_w_(lust_x_.b));                            \
    })
#define lust_i128_mul(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_i128 a, b; } lust_x_ = {__VA_ARGS__};                                            \
        lust_u128 lust_p_ = lust_inl_u128_of_(lust_inl_w_(lust_x_.a) * lust_inl_w_(lust_x_.b));        \
        (lust_i128){lust_p_.lo, lust_p_.hi};                                                           \
    })
#define lust_u128_shl(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_u128 a; uint32_t n; } lust_x_ = {__VA_ARGS__};                                   \
        __builtin_expect(lust_x_.n < 128, 1) ? lust_inl_u128_of_(lust_inl_w_(lust_x_.a) << lust_x_.n)  \
                                             : lust_u128_shl(lust_x_.a, lust_x_.n);                    \
    })
#define lust_u128_shr(...)                                                                             \
    __extension__({                                                                                    \
        struct { lust_u128 a; uint32_t n; } lust_x_ = {__VA_ARGS__};                                   \
        __builtin_expect(lust_x_.n < 128, 1) ? lust_inl_u128_of_(lust_inl_w_(lust_x_.a) >> lust_x_.n)  \
                                             : lust_u128_shr(lust_x_.a, lust_x_.n);                    \
    })
#endif
#endif
