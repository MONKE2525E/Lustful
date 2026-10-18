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
   moved value) becomes loads and stores instead of two calls. */
#define lust_memcpy(d, s, n) ((void)__builtin_memcpy((d), (s), (n)))
#define lust_memmove(d, s, n) ((void)__builtin_memmove((d), (s), (n)))

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
#endif
