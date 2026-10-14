/* ---------- Atomics, threads, and sync (W-THREADS, ARCH 7.3) ----------

   Every atomic access in a lust program goes through these functions, so
   generated code holds no atomic syntax: tcc and gcc compile the same
   plain calls. The bodies use the __atomic builtins both compilers have
   (tcc lowers them to calls into libtcc1's lock-prefixed helpers).

   Orderings arrive as Rust's `atomic::Ordering` discriminant: 0 Relaxed,
   1 Release, 2 Acquire, 3 AcqRel, 4 SeqCst. The functions panic with
   core's messages for the orderings Rust's methods reject at run time
   (rustc rejects the same orderings at compile time when they are
   written as the variant itself; check/sync.rs gives L0542 there). */

/* Rust's Ordering to the C11 memory order. */
#define LUST_MO(o) ((o) == 0 ? 0 : (o) == 1 ? 3 : (o) == 2 ? 2 : (o) == 3 ? 4 : 5)
/* The order a compare-exchange uses on success: never weaker than its
   failure order (C11 asks for that; a stronger order is always correct). */
#define LUST_MO_CAS(s, f) (((f) == 4) ? 5 : ((f) == 2 && ((s) == 0 || (s) == 1)) ? ((s) == 0 ? 2 : 4) : LUST_MO(s))
/* The failure order of a compare-exchange loop that implements an RMW with
   order `o`: the load half of `o`. */
#define LUST_MO_LOADPART(o) ((o) == 4 ? 5 : ((o) == 2 || (o) == 3) ? 2 : 0)

#ifdef LUST_IMPL
#ifdef __TINYC__
/* tcc has no fence builtins: libtcc1 provides these two (stdatomic.h). */
extern void atomic_thread_fence(int);
extern void atomic_signal_fence(int);
#define LUST_THREAD_FENCE(o) atomic_thread_fence(o)
#define LUST_SIGNAL_FENCE(o) atomic_signal_fence(o)
#else
#define LUST_THREAD_FENCE(o) __atomic_thread_fence(o)
#define LUST_SIGNAL_FENCE(o) __atomic_signal_fence(o)
#endif
#endif

#define LUST_ATOMIC_WIDTH(N, U, S)                                                                                     \
    U lust_at_load_##N(U *p, uint32_t o, lust_loc loc) LUST_BODY({                                                    \
        if (o == 1) lust_panic_cstr("there is no such thing as a release load", loc);                                 \
        if (o == 3) lust_panic_cstr("there is no such thing as an acquire-release load", loc);                        \
        U r;                                                                                                           \
        __atomic_load(p, &r, LUST_MO(o));                                                                              \
        return r;                                                                                                      \
    })                                                                                                                 \
    void lust_at_store_##N(U *p, U v, uint32_t o, lust_loc loc) LUST_BODY({                                           \
        if (o == 2) lust_panic_cstr("there is no such thing as an acquire store", loc);                               \
        if (o == 3) lust_panic_cstr("there is no such thing as an acquire-release store", loc);                       \
        __atomic_store(p, &v, LUST_MO(o));                                                                             \
    })                                                                                                                 \
    U lust_at_swap_##N(U *p, U v, uint32_t o) LUST_BODY({                                                             \
        U r;                                                                                                           \
        __atomic_exchange(p, &v, &r, LUST_MO(o));                                                                      \
        return r;                                                                                                      \
    })                                                                                                                 \
    int lust_at_cas_##N(U *p, U cur, U nv, uint32_t s, uint32_t f, U *old, lust_loc loc) LUST_BODY({                  \
        if (f == 3) lust_panic_cstr("there is no such thing as an acquire-release failure ordering", loc);            \
        if (f == 1) lust_panic_cstr("there is no such thing as a release failure ordering", loc);                     \
        U e = cur;                                                                                                     \
        int ok = __atomic_compare_exchange(p, &e, &nv, 0, LUST_MO_CAS(s, f), LUST_MO(f));                              \
        *old = e;                                                                                                      \
        return ok;                                                                                                     \
    })                                                                                                                 \
    U lust_at_fetch_add_##N(U *p, U v, uint32_t o) LUST_BODY({ return __atomic_fetch_add(p, v, LUST_MO(o)); })        \
    U lust_at_fetch_sub_##N(U *p, U v, uint32_t o) LUST_BODY({ return __atomic_fetch_sub(p, v, LUST_MO(o)); })        \
    U lust_at_fetch_and_##N(U *p, U v, uint32_t o) LUST_BODY({ return __atomic_fetch_and(p, v, LUST_MO(o)); })        \
    U lust_at_fetch_or_##N(U *p, U v, uint32_t o) LUST_BODY({ return __atomic_fetch_or(p, v, LUST_MO(o)); })          \
    U lust_at_fetch_xor_##N(U *p, U v, uint32_t o) LUST_BODY({ return __atomic_fetch_xor(p, v, LUST_MO(o)); })        \
    U lust_at_fetch_nand_##N(U *p, U v, uint32_t o) LUST_BODY({                                                       \
        U cur;                                                                                                         \
        __atomic_load(p, &cur, 0);                                                                                     \
        for (;;) {                                                                                                     \
            U nv = (U) ~(cur & v);                                                                                     \
            if (__atomic_compare_exchange(p, &cur, &nv, 1, LUST_MO(o), LUST_MO_LOADPART(o))) return cur;               \
        }                                                                                                              \
    })                                                                                                                 \
    U lust_at_fetch_umax_##N(U *p, U v, uint32_t o) LUST_BODY({                                                       \
        U cur;                                                                                                         \
        __atomic_load(p, &cur, 0);                                                                                     \
        for (;;) {                                                                                                     \
            U nv = cur > v ? cur : v;                                                                                  \
            if (__atomic_compare_exchange(p, &cur, &nv, 1, LUST_MO(o), LUST_MO_LOADPART(o))) return cur;               \
        }                                                                                                              \
    })                                                                                                                 \
    U lust_at_fetch_umin_##N(U *p, U v, uint32_t o) LUST_BODY({                                                       \
        U cur;                                                                                                         \
        __atomic_load(p, &cur, 0);                                                                                     \
        for (;;) {                                                                                                     \
            U nv = cur < v ? cur : v;                                                                                  \
            if (__atomic_compare_exchange(p, &cur, &nv, 1, LUST_MO(o), LUST_MO_LOADPART(o))) return cur;               \
        }                                                                                                              \
    })                                                                                                                 \
    U lust_at_fetch_smax_##N(U *p, U v, uint32_t o) LUST_BODY({                                                       \
        U cur;                                                                                                         \
        __atomic_load(p, &cur, 0);                                                                                     \
        for (;;) {                                                                                                     \
            U nv = (S)cur > (S)v ? cur : v;                                                                            \
            if (__atomic_compare_exchange(p, &cur, &nv, 1, LUST_MO(o), LUST_MO_LOADPART(o))) return cur;               \
        }                                                                                                              \
    })                                                                                                                 \
    U lust_at_fetch_smin_##N(U *p, U v, uint32_t o) LUST_BODY({                                                       \
        U cur;                                                                                                         \
        __atomic_load(p, &cur, 0);                                                                                     \
        for (;;) {                                                                                                     \
            U nv = (S)cur < (S)v ? cur : v;                                                                            \
            if (__atomic_compare_exchange(p, &cur, &nv, 1, LUST_MO(o), LUST_MO_LOADPART(o))) return cur;               \
        }                                                                                                              \
    })

LUST_ATOMIC_WIDTH(1, uint8_t, int8_t)
LUST_ATOMIC_WIDTH(2, uint16_t, int16_t)
LUST_ATOMIC_WIDTH(4, uint32_t, int32_t)
LUST_ATOMIC_WIDTH(8, uint64_t, int64_t)

/* `AtomicBool::fetch_nand`, as core writes it: `fetch_xor(true)` when
   `v` is true (a nand with true is a not), else `swap(true)`. */
uint8_t lust_at_fetch_bnand_1(uint8_t *p, uint8_t v, uint32_t o) LUST_BODY({
    return v ? lust_at_fetch_xor_1(p, 1, o) : lust_at_swap_1(p, 1, o);
})

void lust_at_fence(uint32_t o, lust_loc loc) LUST_BODY({
    if (o == 0) lust_panic_cstr("there is no such thing as a relaxed fence", loc);
    LUST_THREAD_FENCE(LUST_MO(o));
})

void lust_at_compiler_fence(uint32_t o, lust_loc loc) LUST_BODY({
    if (o == 0) lust_panic_cstr("there is no such thing as a relaxed fence", loc);
    LUST_SIGNAL_FENCE(LUST_MO(o));
})
