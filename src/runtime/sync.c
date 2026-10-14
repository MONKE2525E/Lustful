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

/* ---------- Arc and sync::Weak ----------

   An `Arc<T>` points at the same counted header as an `Rc<T>` (`RcI_T`:
   `strong`, `weak`, then the value), but every count changes atomically,
   as alloc::sync does. `weak` counts the Weaks plus one implicit weak
   held by all the strong refs together. `get_mut`'s uniqueness test
   locks the weak count (UINT64_MAX) for a moment; `downgrade` waits it
   out. These functions take the header as `uint64_t *h`: h[0] is
   `strong`, h[1] is `weak`. */

/* Adds one to a count. Rust aborts when a count passes isize::MAX. */
void lust_arc_inc(uint64_t *c) LUST_BODY({
    if (__atomic_fetch_add(c, 1, 0) > (uint64_t)INT64_MAX) abort();
})

/* Takes one from a count; 1 when that was the last (with the acquire
   fence Rust's drop takes before it frees). */
int lust_arc_dec(uint64_t *c) LUST_BODY({
    if (__atomic_fetch_sub(c, 1, 3) != 1) return 0;
    LUST_THREAD_FENCE(2);
    return 1;
})

/* An acquire load of a count. */
uint64_t lust_arc_load(uint64_t *c) LUST_BODY({
    uint64_t v;
    __atomic_load(c, &v, 2);
    return v;
})

/* `Arc::downgrade`: one more weak ref. */
void lust_arc_downgrade(uint64_t *h) LUST_BODY({
    uint64_t cur;
    __atomic_load(&h[1], &cur, 0);
    for (;;) {
        if (cur == UINT64_MAX) {
            __atomic_load(&h[1], &cur, 0);
            continue;
        }
        if (cur > (uint64_t)INT64_MAX) abort();
        uint64_t nv = cur + 1;
        if (__atomic_compare_exchange(&h[1], &cur, &nv, 1, 2, 0)) return;
    }
})

/* `Weak::upgrade` on a live pointer: 1 when a strong ref was taken
   (the strong count was not zero). */
int lust_arc_upgrade(uint64_t *h) LUST_BODY({
    uint64_t n;
    __atomic_load(&h[0], &n, 0);
    for (;;) {
        if (n == 0) return 0;
        if (n > (uint64_t)INT64_MAX) abort();
        uint64_t nv = n + 1;
        if (__atomic_compare_exchange(&h[0], &n, &nv, 1, 2, 0)) return 1;
    }
})

/* `Arc::weak_count`: the Weaks, without the implicit one. */
uint64_t lust_arc_weak_count(uint64_t *h) LUST_BODY({
    uint64_t w = lust_arc_load(&h[1]);
    return w == UINT64_MAX ? 0 : w - 1;
})

/* `Weak::weak_count` on a live pointer: 0 once the value is gone. */
uint64_t lust_arc_weak_weak_count(uint64_t *h) LUST_BODY({
    uint64_t w = lust_arc_load(&h[1]);
    uint64_t s = lust_arc_load(&h[0]);
    if (s == 0) return 0;
    return w == UINT64_MAX ? 0 : w - 1;
})

/* `Arc::get_mut`'s test: no other strong ref and no Weak. */
int lust_arc_is_unique(uint64_t *h) LUST_BODY({
    uint64_t one = 1, locked = UINT64_MAX;
    if (!__atomic_compare_exchange(&h[1], &one, &locked, 0, 2, 0)) return 0;
    int unique = lust_arc_load(&h[0]) == 1;
    uint64_t back = 1;
    __atomic_store(&h[1], &back, 3);
    return unique;
})

/* `Arc::make_mut`'s three cases: 0 another strong ref exists (clone the
   value), 1 this was the only strong ref but Weaks exist (strong is now
   0: move the value out), 2 unique (nothing to do). */
int lust_arc_make_mut_state(uint64_t *h) LUST_BODY({
    uint64_t one = 1, zero = 0;
    if (!__atomic_compare_exchange(&h[0], &one, &zero, 0, 2, 0)) return 0;
    uint64_t w;
    __atomic_load(&h[1], &w, 0);
    if (w != 1) return 1;
    __atomic_store(&h[0], &one, 3);
    return 2;
})

/* `Arc::try_unwrap`'s test: 1 when this was the only strong ref (strong
   is now 0 and the caller owns the value). */
int lust_arc_take_unique(uint64_t *h) LUST_BODY({
    uint64_t one = 1, zero = 0;
    if (!__atomic_compare_exchange(&h[0], &one, &zero, 0, 0, 0)) return 0;
    LUST_THREAD_FENCE(2);
    return 1;
})
