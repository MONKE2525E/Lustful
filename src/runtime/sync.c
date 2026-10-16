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

/* Ordering panics come from core's atomic.rs (no track_caller), as rustc
   1.99 reports them; `weak` picks compare_exchange_weak's lines. The
   load and store `loc` params stay for the call shape. */
#define LUST_ATOMIC_RS "core/src/sync/atomic.rs:"

#define LUST_ATOMIC_WIDTH(N, U, S)                                                                                     \
    U lust_at_load_##N(U *p, uint32_t o, lust_loc loc) LUST_BODY({                                                    \
        if (o == 1) lust_panic_std_lit("there is no such thing as a release load", LUST_ATOMIC_RS "3997:24");                                       \
        if (o == 3) lust_panic_std_lit("there is no such thing as an acquire-release load", LUST_ATOMIC_RS "3998:23");                        \
        U r;                                                                                                           \
        __atomic_load(p, &r, LUST_MO(o));                                                                              \
        return r;                                                                                                      \
    })                                                                                                                 \
    void lust_at_store_##N(U *p, U v, uint32_t o, lust_loc loc) LUST_BODY({                                           \
        if (o == 2) { lust_panic_std_lit("there is no such thing as an acquire store", LUST_ATOMIC_RS "3981:24"); return; }                       \
        if (o == 3) { lust_panic_std_lit("there is no such thing as an acquire-release store", LUST_ATOMIC_RS "3982:23"); return; }           \
        __atomic_store(p, &v, LUST_MO(o));                                                                             \
    })                                                                                                                 \
    U lust_at_swap_##N(U *p, U v, uint32_t o) LUST_BODY({                                                             \
        U r;                                                                                                           \
        __atomic_exchange(p, &v, &r, LUST_MO(o));                                                                      \
        return r;                                                                                                      \
    })                                                                                                                 \
    int lust_at_cas_##N(U *p, U cur, U nv, uint32_t s, uint32_t f, U *old, int weak) LUST_BODY({                      \
        if (f == 3 || f == 1) {                                                                                        \
            if (f == 3) lust_panic_std_lit("there is no such thing as an acquire-release failure ordering", weak ? LUST_ATOMIC_RS "4184:28" : LUST_ATOMIC_RS "4118:28"); \
            else lust_panic_std_lit("there is no such thing as a release failure ordering", weak ? LUST_ATOMIC_RS "4185:29" : LUST_ATOMIC_RS "4119:29"); \
            *old = cur;                                                                                                \
            return 0;                                                                                                  \
        }                                                                                                              \
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
    (void)loc;
    if (o == 0) lust_panic_std_lit("there is no such thing as a relaxed fence", LUST_ATOMIC_RS "4497:24");
    LUST_THREAD_FENCE(LUST_MO(o));
})

void lust_at_compiler_fence(uint32_t o, lust_loc loc) LUST_BODY({
    (void)loc;
    if (o == 0) lust_panic_std_lit("there is no such thing as a relaxed fence", LUST_ATOMIC_RS "4582:24");
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

/* The one shared allocation of every empty `Arc<str>` and `Arc<[T]>`
   that `Default` makes (std's static ArcInner, w-unsized): its strong
   count starts at 1, so it is never freed. Takes one more strong ref and
   returns the data pointer, right after the two counts. */
void *lust_arc_empty(void) LUST_BODY({
    static _Alignas(16) uint64_t h[2] = { 1, 1 };
    lust_arc_inc(&h[0]);
    return (void *)(h + 2);
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

/* ---------- Locks: Mutex and RwLock over a futex word ----------

   A `Mutex<T>` is { uint32_t st; uint8_t poison; T v; } and an `RwLock<T>`
   { uint32_t st; uint32_t wn; uint8_t poison; T v; } (cgen/sync.rs). All
   zero is unlocked, so `Mutex::new` in a static needs no constructor. The
   poison flag stays 0: a panic aborts the process. Locking a lock this
   thread already holds deadlocks, as std's futex locks do on Linux. */
#ifdef LUST_IMPL
#if defined(__linux__)
long syscall(long number, ...);
#if defined(__x86_64__)
#define LUST_SYS_FUTEX 202
#define LUST_SYS_SCHED_GETAFFINITY 204
#elif defined(__aarch64__)
#define LUST_SYS_FUTEX 98
#define LUST_SYS_SCHED_GETAFFINITY 123
#endif
#endif
int sched_yield(void);
/* Sleep while *p == v (spurious wakeups are fine: callers loop). */
static void lust_futex_wait(uint32_t *p, uint32_t v) {
#ifdef LUST_SYS_FUTEX
    syscall(LUST_SYS_FUTEX, p, 128 /* FUTEX_WAIT_PRIVATE */, v, (void *)0, (void *)0, 0);
#else
    (void)p; (void)v;
    sched_yield();
#endif
}
static void lust_futex_wake(uint32_t *p, int n) {
#ifdef LUST_SYS_FUTEX
    syscall(LUST_SYS_FUTEX, p, 129 /* FUTEX_WAKE_PRIVATE */, n, (void *)0, (void *)0, 0);
#else
    (void)p; (void)n;
#endif
}
#endif

/* Poisoning (panic=unwind): the `poison` byte of a Mutex or RwLock. Bit 0
   is std's poison flag; bit 1 says the write guard that holds the lock was
   taken while its thread was panicking. A write guard dropped while
   panicking poisons the lock only when it was not taken that way (std's
   poison::Guard). */
void lust_poison_enter(uint8_t *f) LUST_BODY({
    if (lust_unw_panicking()) *f |= 2;
    else *f &= (uint8_t)~2;
})
void lust_poison_leave(uint8_t *f) LUST_BODY({
    if (!(*f & 2) && lust_unw_panicking()) *f |= 1;
})

/* Mutex states: 0 unlocked, 1 locked, 2 locked with waiters (Drepper's
   futex mutex, as std's). */
void lust_mutex_lock(uint32_t *st) LUST_BODY({
    uint32_t zero = 0, one = 1, two = 2, old;
    if (__atomic_compare_exchange(st, &zero, &one, 0, 2, 0)) return;
    for (;;) {
        __atomic_exchange(st, &two, &old, 2);
        if (old == 0) return;
        lust_futex_wait(st, 2);
    }
})

/* 1 when the lock was taken. */
int lust_mutex_trylock(uint32_t *st) LUST_BODY({
    uint32_t zero = 0, one = 1;
    return __atomic_compare_exchange(st, &zero, &one, 0, 2, 0);
})

void lust_mutex_unlock(uint32_t *st) LUST_BODY({
    uint32_t zero = 0, old;
    __atomic_exchange(st, &zero, &old, 3);
    if (old == 2) lust_futex_wake(st, 1);
})

/* RwLock: st is the reader count, or LUST_RW_WRITER while written; st[1]
   (wn) counts sleepers. Every step is SeqCst, so an unlock that reads
   wn == 0 happens before a sleeper's increment, and that sleeper's futex
   wait then sees the changed state and returns at once. */
#define LUST_RW_WRITER 0xffffffffu
void lust_rw_read(uint32_t *st) LUST_BODY({
    for (;;) {
        uint32_t s;
        __atomic_load(st, &s, 5);
        if (s < LUST_RW_WRITER - 1) {
            uint32_t n = s + 1;
            if (__atomic_compare_exchange(st, &s, &n, 0, 5, 5)) return;
            continue;
        }
        __atomic_fetch_add(&st[1], 1, 5);
        lust_futex_wait(st, s);
        __atomic_fetch_sub(&st[1], 1, 5);
    }
})

int lust_rw_tryread(uint32_t *st) LUST_BODY({
    uint32_t s;
    __atomic_load(st, &s, 5);
    while (s < LUST_RW_WRITER - 1) {
        uint32_t n = s + 1;
        if (__atomic_compare_exchange(st, &s, &n, 0, 5, 5)) return 1;
    }
    return 0;
})

void lust_rw_read_unlock(uint32_t *st) LUST_BODY({
    uint32_t w;
    if (__atomic_fetch_sub(st, 1, 5) == 1) {
        __atomic_load(&st[1], &w, 5);
        if (w) lust_futex_wake(st, 0x7fffffff);
    }
})

void lust_rw_write(uint32_t *st) LUST_BODY({
    for (;;) {
        uint32_t s = 0, wr = LUST_RW_WRITER;
        if (__atomic_compare_exchange(st, &s, &wr, 0, 5, 5)) return;
        __atomic_fetch_add(&st[1], 1, 5);
        lust_futex_wait(st, s);
        __atomic_fetch_sub(&st[1], 1, 5);
    }
})

int lust_rw_trywrite(uint32_t *st) LUST_BODY({
    uint32_t s = 0, wr = LUST_RW_WRITER;
    return __atomic_compare_exchange(st, &s, &wr, 0, 5, 5);
})

void lust_rw_write_unlock(uint32_t *st) LUST_BODY({
    uint32_t zero = 0, w;
    __atomic_store(st, &zero, 5);
    __atomic_load(&st[1], &w, 5);
    if (w) lust_futex_wake(st, 0x7fffffff);
})

/* ---------- Threads: spawn, join, current (pthreads) ----------

   A `JoinHandle<T>` points at a packet the generated code allocates:
   { lust_JoinHdr h; T ret; Env env; } (cgen/sync.rs). The spawned thread
   runs h.run (a generated trampoline that calls the closure and stores
   its result), then gives up its reference. The handle and the thread
   each hold one reference (h.rc); whichever lets go last drops the result
   (h.drop_ret) and frees the packet. `join` waits, takes the result, and
   frees the packet. A `Thread` is a counted lust_ThreadInfo; the current
   thread's lives in a pthread key (no C _Thread_local), whose destructor
   gives up the thread's reference at thread exit. */
typedef struct lust_ThreadInfo {
    uint64_t rc;
    uint64_t id;
    const uint8_t *name;
    uint64_t name_len;
    /* A Builder name's owned copy (0 for a static name). */
    uint8_t *name_buf;
} lust_ThreadInfo;

/* A `thread::Scope`: the count of its live packets. The scope's end
   waits until it is 0; a packet counts down when it is freed, after its
   result dropped, so no scoped thread touches borrowed data after. */
typedef struct lust_Scope {
    uint32_t live;
    uint32_t panicked; /* a thread of the scope panicked and nobody joined it */
} lust_Scope;

typedef struct lust_JoinHdr {
    unsigned long t; /* pthread_t */
    lust_ThreadInfo *th;
    uint32_t rc;
    uint32_t done;
    void (*run)(struct lust_JoinHdr *);
    void (*drop_ret)(struct lust_JoinHdr *);
    lust_Scope *scope; /* 0 for thread::spawn */
    uint32_t panicked; /* the thread ended by a panic; `payload` is its Box<dyn Any + Send> */
    lust_dyn payload;
} lust_JoinHdr;

#ifdef LUST_IMPL
int pthread_create(unsigned long *t, const void *attr, void *(*start)(void *), void *arg);
int pthread_join(unsigned long t, void **ret);
int pthread_detach(unsigned long t);
int pthread_key_create(unsigned int *key, void (*dtor)(void *));
void *pthread_getspecific(unsigned int key);
int pthread_setspecific(unsigned int key, const void *v);
int pthread_once(int *once, void (*init)(void));
static unsigned int lust_cur_key;
static int lust_cur_once;
/* ThreadId(1) is the main thread; spawned threads count from 2 in spawn
   order, as std assigns them. */
static uint64_t lust_next_tid = 2;
static lust_ThreadInfo lust_main_info = {1, 1, (const uint8_t *)"main", 4, 0};

static void lust_thread_info_release(void *p) {
    lust_ThreadInfo *t = (lust_ThreadInfo *)p;
    if (t && t != &lust_main_info && __atomic_sub_fetch(&t->rc, 1, 4) == 0) {
        free(t->name_buf);
        free(t);
    }
}
static int lust_cur_ready;
static void lust_cur_key_init(void) {
    pthread_key_create(&lust_cur_key, lust_thread_info_release);
    int one = 1;
    __atomic_store(&lust_cur_ready, &one, 3);
}

/* The calling thread's name for the panic hook: "main", the Builder's
   name, or "<unnamed>" (panic.c). */
static void lust_cur_thread_name(const uint8_t **p, uint64_t *n) {
    int ready;
    __atomic_load(&lust_cur_ready, &ready, 2);
    lust_ThreadInfo *t = ready ? (lust_ThreadInfo *)pthread_getspecific(lust_cur_key) : 0;
    if (!t) t = &lust_main_info;
    if (t->name) { *p = t->name; *n = t->name_len; }
    else { *p = (const uint8_t *)"<unnamed>"; *n = 9; }
}

/* Drops a packet's result: the value, or the payload of a panic. */
static void lust_packet_drop_result(lust_JoinHdr *h) {
    if (!h->panicked) { h->drop_ret(h); return; }
    if (h->payload.vt[0]) ((void (*)(void *))h->payload.vt[0])(h->payload.data);
    lust_dealloc(h->payload.data, (uint64_t)(uintptr_t)h->payload.vt[1], (uint64_t)(uintptr_t)h->payload.vt[2]);
}

/* Frees a packet whose result was moved out or dropped; a scoped one
   then counts down its scope. */
static void lust_packet_free(lust_JoinHdr *h) {
    lust_Scope *sc = h->scope;
    uint32_t one = 1;
    if (sc && h->panicked) __atomic_store(&sc->panicked, &one, 5);
    lust_thread_info_release(h->th);
    free(h);
    if (sc && __atomic_sub_fetch(&sc->live, 1, 5) == 0) lust_futex_wake(&sc->live, 0x7fffffff);
}

static void *lust_thread_entry(void *p) {
    lust_JoinHdr *h = (lust_JoinHdr *)p;
    pthread_setspecific(lust_cur_key, h->th);
    h->run(h);
    /* A panic that reached the thread's root ends the thread; its payload
       is the join's Err (std's spawn wrapper catches it). */
    lust_exc ex;
    if (lust_unwind_mode && lust_unw_pending && lust_unw_take(&ex)) {
        h->payload = lust_exc_box(&ex);
        h->panicked = 1;
    }
    uint32_t one = 1;
    __atomic_store(&h->done, &one, 3);
    if (__atomic_sub_fetch(&h->rc, 1, 4) == 0) {
        lust_packet_drop_result(h);
        lust_packet_free(h);
    }
    return 0;
}
#endif

/* Starts the thread for a filled packet (run, drop_ret, scope, ret, env). */
void lust_thread_spawn(lust_JoinHdr *h, lust_loc loc) LUST_BODY({
    if (h->scope) __atomic_add_fetch(&h->scope->live, 1, 5);
    pthread_once(&lust_cur_once, lust_cur_key_init);
    lust_ThreadInfo *t = (lust_ThreadInfo *)malloc(sizeof(lust_ThreadInfo));
    if (!t) lust_oom();
    t->rc = 2; /* the handle's (h->th) and the running thread's (its key) */
    t->id = __atomic_fetch_add(&lust_next_tid, 1, 0);
    t->name = 0;
    t->name_len = 0;
    t->name_buf = 0;
    h->th = t;
    h->rc = 2;
    h->done = 0;
    h->panicked = 0;
    if (pthread_create(&h->t, 0, lust_thread_entry, h) != 0) lust_panic_cstr_owned("failed to spawn thread", loc);
})

/* A `thread::Builder` value (cgen/sync.rs lays it out): the
   name as a String, the stack size in bytes (0 = default), and
   whether a name was set (an empty name is Some("")). */
typedef struct lust_ThreadBuilder {
    lust_String name;
    uint64_t stack;
    uint8_t has_name;
    uint8_t has_stack;
} lust_ThreadBuilder;

int pthread_attr_init(void *attr);
int pthread_attr_destroy(void *attr);
int pthread_attr_setstacksize(void *attr, uint64_t size);
int pthread_setname_np(unsigned long t, const char *name);

/* `Builder::spawn`: lust_thread_spawn with the builder's name
   and stack size. 0, or the errno of the failed call (the caller
   builds std's io::Error from it). The name bytes are copied:
   the ThreadInfo owns them. An interior NUL truncates the OS
   thread name; the Thread::name value keeps the full string, as
   std's does (its CString would fail there: see the check for
   the panic on a NUL in the caller). */
int lust_thread_spawn_builder(lust_JoinHdr *h, const lust_ThreadBuilder *b) LUST_BODY({
    if (h->scope) __atomic_add_fetch(&h->scope->live, 1, 5);
    pthread_once(&lust_cur_once, lust_cur_key_init);
    lust_ThreadInfo *t = (lust_ThreadInfo *)malloc(sizeof(lust_ThreadInfo));
    if (!t) lust_oom();
    t->rc = 2;
    t->id = __atomic_fetch_add(&lust_next_tid, 1, 0);
    t->name = 0;
    t->name_len = 0;
    t->name_buf = 0;
    if (b->has_name) {
        uint8_t *copy = (uint8_t *)malloc(b->name.len ? b->name.len : 1);
        if (!copy) lust_oom();
        for (uint64_t i = 0; i < b->name.len; i++) copy[i] = b->name.ptr[i];
        t->name = copy;
        t->name_len = b->name.len;
        t->name_buf = copy;
    }
    h->th = t;
    h->rc = 2;
    h->done = 0;
    h->panicked = 0;
    /* pthread_attr_t is opaque and platform-sized; a zeroed
       64-byte block covers glibc's (56 bytes) on the targets
       lust runs on. */
    uint64_t attr[8] = {0, 0, 0, 0, 0, 0, 0, 0};
    void *attrp = 0;
    if (b->has_stack) {
        pthread_attr_init(attr);
        uint64_t sz = b->stack < 16384 ? 16384 : b->stack;
        int e2 = pthread_attr_setstacksize(attr, sz);
        if (e2 != 0) {
            pthread_attr_destroy(attr);
            lust_thread_info_release(t);
            lust_thread_info_release(t);
            if (h->scope) __atomic_sub_fetch(&h->scope->live, 1, 5);
            return e2;
        }
        attrp = attr;
    }
    int r = pthread_create(&h->t, attrp, lust_thread_entry, h);
    if (attrp) pthread_attr_destroy(attr);
    if (r != 0) {
        lust_thread_info_release(t);
        lust_thread_info_release(t);
        if (h->scope) __atomic_sub_fetch(&h->scope->live, 1, 5);
        return r;
    }
    if (b->has_name) {
        char nm[16];
        uint64_t n = b->name.len < 15 ? b->name.len : 15;
        uint64_t i = 0;
        for (; i < n && b->name.ptr[i] != 0; i++) nm[i] = (char)b->name.ptr[i];
        nm[i] = 0;
        pthread_setname_np(h->t, nm);
    }
    return 0;
})

/* `thread::available_parallelism`: the cgroup quota when one
   applies (rounded up, at least 1), else the affinity count,
   as std computes it on Linux. 0 with *err set on failure. */
static uint64_t lust_cgroup_quota(void) LUST_BODY({
    /* cgroup v2 cpu.max: "<quota|max> <period>". */
    FILE *f = fopen("/sys/fs/cgroup/cpu.max", "r");
    if (f) {
        char buf[128];
        char *got = fgets(buf, sizeof buf, f);
        fclose(f);
        if (got && buf[0] >= '0' && buf[0] <= '9') {
            uint64_t quota = 0, period = 0;
            const char *p = buf;
            while (*p >= '0' && *p <= '9') quota = quota * 10 + (uint64_t)(*p++ - '0');
            while (*p == ' ') p++;
            while (*p >= '0' && *p <= '9') period = period * 10 + (uint64_t)(*p++ - '0');
            if (quota > 0 && period > 0) {
                uint64_t q = (quota + period - 1) / period;
                return q ? q : 1;
            }
        }
        return 0;
    }
    /* cgroup v1 cpu.cfs_quota_us / cpu.cfs_period_us. */
    long quota = -2, period = -2;
    f = fopen("/sys/fs/cgroup/cpu/cpu.cfs_quota_us", "r");
    if (!f) return 0;
    if (fscanf(f, "%ld", &quota) != 1) quota = -2;
    fclose(f);
    f = fopen("/sys/fs/cgroup/cpu/cpu.cfs_period_us", "r");
    if (!f) return 0;
    if (fscanf(f, "%ld", &period) != 1) period = -2;
    fclose(f);
    if (quota > 0 && period > 0) {
        uint64_t q = ((uint64_t)quota + (uint64_t)period - 1) / (uint64_t)period;
        return q ? q : 1;
    }
    return 0;
})

uint64_t lust_avail_parallelism(int32_t *err) LUST_BODY({
    *err = 0;
    uint64_t quota = lust_cgroup_quota();
    if (quota > 0) return quota;
#ifdef LUST_SYS_SCHED_GETAFFINITY
    uint64_t mask[16] = {0};
    long r = syscall(LUST_SYS_SCHED_GETAFFINITY, 0, sizeof mask, mask);
    if (r < 0) {
        *err = errno;
        return 0;
    }
    uint64_t n = 0;
    for (int i = 0; i < 16; i++) n += (uint64_t)__builtin_popcountll(mask[i]);
    if (n > 0) return n;
    *err = 0;
    return 1;
#else
    *err = 38; /* ENOSYS */
    return 0;
#endif
})

/* Waits for the thread; the caller then moves the result out and calls
   lust_join_free. */
void lust_thread_join(lust_JoinHdr *h) LUST_BODY({ pthread_join(h->t, 0); })

void lust_join_free(lust_JoinHdr *h) LUST_BODY({ lust_packet_free(h); })

/* A dropped JoinHandle detaches its thread. */
void lust_join_drop(lust_JoinHdr *h) LUST_BODY({
    pthread_detach(h->t);
    if (__atomic_sub_fetch(&h->rc, 1, 4) == 0) {
        lust_packet_drop_result(h);
        lust_packet_free(h);
    }
})

int lust_join_is_finished(lust_JoinHdr *h) LUST_BODY({
    uint32_t d;
    __atomic_load(&h->done, &d, 2);
    return d != 0;
})

/* `thread::current()`: a new reference to this thread's info. */
lust_ThreadInfo *lust_thread_current(void) LUST_BODY({
    pthread_once(&lust_cur_once, lust_cur_key_init);
    lust_ThreadInfo *t = (lust_ThreadInfo *)pthread_getspecific(lust_cur_key);
    if (!t) return &lust_main_info;
    __atomic_add_fetch(&t->rc, 1, 0);
    return t;
})

lust_ThreadInfo *lust_thread_clone(lust_ThreadInfo *t) LUST_BODY({
    if (t != &lust_main_info) __atomic_add_fetch(&t->rc, 1, 0);
    return t;
})

void lust_thread_drop(lust_ThreadInfo *t) LUST_BODY({ lust_thread_info_release(t); })

void lust_thread_yield(void) LUST_BODY({ sched_yield(); })

/* The end of `thread::scope`: waits for every packet of the scope. */
void lust_scope_wait(lust_Scope *sc) LUST_BODY({
    for (;;) {
        uint32_t n;
        __atomic_load(&sc->live, &n, 5);
        if (n == 0) return;
        lust_futex_wait(&sc->live, n);
    }
})

/* ---------- mpsc channels ----------

   One lust_Chan per channel, shared by every Sender/SyncSender and the
   Receiver (each of those is a lust_Chan*). A futex mutex guards it; `seq`
   is a condition word (waiters sleep on its value, every change bumps it
   and wakes all). Values move in and out by memcpy of `esize` bytes.
   `cap` is -1 for `channel()` and the bound for `sync_channel(n)`; a
   bound of 0 is a rendezvous: a sender places its value only while a
   receiver waits, then waits until that value is taken. The channel is
   freed when the last sender and the receiver are gone; values still
   queued then drop through `drop_elem`. */
typedef struct lust_Chan {
    uint32_t lock;
    uint32_t seq;
    uint64_t senders;
    uint32_t rx_alive;
    uint32_t rx_waiting;
    int64_t cap;
    uint64_t esize;
    uint64_t ealign;
    uint8_t *buf;
    uint64_t head, len, bufcap;
    uint64_t taken;
    void (*drop_elem)(void *);
} lust_Chan;

#ifdef LUST_IMPL
static void lust_chan_changed(lust_Chan *c) {
    __atomic_add_fetch(&c->seq, 1, 5);
    lust_futex_wake(&c->seq, 0x7fffffff);
}
/* Sleeps until the channel changes; the lock is dropped meanwhile. */
static void lust_chan_wait(lust_Chan *c) {
    uint32_t s;
    __atomic_load(&c->seq, &s, 5);
    lust_mutex_unlock(&c->lock);
    lust_futex_wait(&c->seq, s);
    lust_mutex_lock(&c->lock);
}
static void lust_chan_push(lust_Chan *c, const void *v) {
    if (c->esize == 0) { c->len++; return; }
    if (c->len == c->bufcap) {
        uint64_t nc = c->bufcap ? c->bufcap * 2 : 4;
        uint8_t *nb = (uint8_t *)lust_alloc(nc * c->esize, c->ealign);
        for (uint64_t i = 0; i < c->len; i++) memcpy(nb + i * c->esize, c->buf + ((c->head + i) % c->bufcap) * c->esize, c->esize);
        if (c->bufcap && c->esize) free(c->buf);
        c->buf = nb;
        c->bufcap = nc;
        c->head = 0;
    }
    memcpy(c->buf + ((c->head + c->len) % c->bufcap) * c->esize, v, c->esize);
    c->len++;
}
static void lust_chan_pop(lust_Chan *c, void *out) {
    if (c->esize == 0) { c->len--; c->taken++; return; }
    memcpy(out, c->buf + c->head * c->esize, c->esize);
    c->head = (c->head + 1) % c->bufcap;
    c->len--;
    c->taken++;
}
/* Drops the queued values and frees the channel (lock held, last user). */
static void lust_chan_drain(lust_Chan *c) {
    if (c->drop_elem)
        for (uint64_t i = 0; i < c->len; i++) c->drop_elem(c->esize ? c->buf + ((c->head + i) % c->bufcap) * c->esize : (uint8_t *)(uintptr_t)c->ealign);
    c->len = 0;
}
static void lust_chan_free(lust_Chan *c) {
    lust_chan_drain(c);
    if (c->bufcap && c->esize) free(c->buf);
    free(c);
}
#endif

lust_Chan *lust_chan_new(uint64_t esize, uint64_t ealign, int64_t cap, void (*drop_elem)(void *)) LUST_BODY({
    lust_Chan *c = (lust_Chan *)calloc(1, sizeof(lust_Chan));
    if (!c) lust_oom();
    c->senders = 1;
    c->rx_alive = 1;
    c->cap = cap;
    c->esize = esize;
    c->ealign = ealign;
    c->drop_elem = drop_elem;
    return c;
})

/* 0 sent; 1 the receiver is gone (the value stays with the caller). */
int lust_chan_send(lust_Chan *c, const void *v) LUST_BODY({
    lust_mutex_lock(&c->lock);
    if (c->cap == 0) {
        while (c->rx_alive && (c->rx_waiting == 0 || c->len > 0)) lust_chan_wait(c);
        if (!c->rx_alive) { lust_mutex_unlock(&c->lock); return 1; }
        uint64_t ticket = c->taken;
        lust_chan_push(c, v);
        lust_chan_changed(c);
        while (c->taken == ticket && c->rx_alive) lust_chan_wait(c);
        lust_mutex_unlock(&c->lock);
        return 0;
    }
    while (c->rx_alive && c->cap > 0 && c->len >= (uint64_t)c->cap) lust_chan_wait(c);
    if (!c->rx_alive) { lust_mutex_unlock(&c->lock); return 1; }
    lust_chan_push(c, v);
    lust_chan_changed(c);
    lust_mutex_unlock(&c->lock);
    return 0;
})

/* try_send: 0 sent; 1 full (the value stays with the caller);
   2 the receiver is gone (the value stays with the caller). A
   rendezvous channel (cap 0) sends only into a waiting receiver
   with nothing queued, as std's does. */
int lust_chan_try_send(lust_Chan *c, const void *v) LUST_BODY({
    lust_mutex_lock(&c->lock);
    if (!c->rx_alive) { lust_mutex_unlock(&c->lock); return 2; }
    if (c->cap == 0) {
        if (c->rx_waiting == 0 || c->len > 0) { lust_mutex_unlock(&c->lock); return 1; }
    } else if (c->cap > 0 && c->len >= (uint64_t)c->cap) {
        lust_mutex_unlock(&c->lock);
        return 1;
    }
    lust_chan_push(c, v);
    lust_chan_changed(c);
    lust_mutex_unlock(&c->lock);
    return 0;
})

/* 0 received into out; 1 every sender is gone and nothing is queued.
   `block` 0 is try_recv: 1 means empty, 2 disconnected. */
int lust_chan_recv(lust_Chan *c, void *out, int block) LUST_BODY({
    lust_mutex_lock(&c->lock);
    c->rx_waiting++;
    lust_chan_changed(c);
    for (;;) {
        if (c->len > 0) {
            lust_chan_pop(c, out);
            c->rx_waiting--;
            lust_chan_changed(c);
            lust_mutex_unlock(&c->lock);
            return 0;
        }
        if (c->senders == 0) { c->rx_waiting--; lust_mutex_unlock(&c->lock); return block ? 1 : 2; }
        if (!block) { c->rx_waiting--; lust_mutex_unlock(&c->lock); return 1; }
        lust_chan_wait(c);
    }
})

lust_Chan *lust_chan_clone_sender(lust_Chan *c) LUST_BODY({
    lust_mutex_lock(&c->lock);
    c->senders++;
    lust_mutex_unlock(&c->lock);
    return c;
})

void lust_chan_drop_sender(lust_Chan *c) LUST_BODY({
    lust_mutex_lock(&c->lock);
    if (--c->senders == 0) {
        if (!c->rx_alive) { lust_chan_free(c); return; }
        lust_chan_changed(c);
    }
    lust_mutex_unlock(&c->lock);
})

void lust_chan_drop_receiver(lust_Chan *c) LUST_BODY({
    lust_mutex_lock(&c->lock);
    c->rx_alive = 0;
    if (c->senders == 0) { lust_chan_free(c); return; }
    /* Queued values drop now, as std's receiver drop does. */
    lust_chan_drain(c);
    lust_chan_changed(c);
    lust_mutex_unlock(&c->lock);
})

/* ---------- Condvar, Barrier, OnceLock ----------

   A Condvar is a sequence word: a waiter reads it, unlocks the mutex,
   sleeps while it is unchanged, and locks again; a notify bumps it and
   wakes one or all (spurious wakeups are allowed, as std documents).
   A Barrier is { lock, seq, count, generation, n }: the n-th arrival
   starts a new generation, wakes the others, and is the leader. A
   OnceLock<T> is { state, T }: 0 empty, 1 being set, 2 set. */
void lust_cv_wait(uint32_t *cv, uint32_t *m) LUST_BODY({
    uint32_t s;
    __atomic_load(cv, &s, 5);
    lust_mutex_unlock(m);
    lust_futex_wait(cv, s);
    lust_mutex_lock(m);
})

void lust_cv_notify(uint32_t *cv, int all) LUST_BODY({
    __atomic_add_fetch(cv, 1, 5);
    lust_futex_wake(cv, all ? 0x7fffffff : 1);
})

/* `Condvar::wait_timeout`: like lust_cv_wait, but 1 when the
   duration elapsed with no notify seen (std's timed_out: true
   only when the timeout is known to have elapsed). The deadline
   is monotonic, as std's is on Linux; the futex wait takes the
   remaining time (a relative timeout, CLOCK_MONOTONIC). */
#if defined(__linux__)
#if defined(__x86_64__)
#define LUST_SYS_CLOCK_GETTIME 228
#elif defined(__aarch64__)
#define LUST_SYS_CLOCK_GETTIME 113
#endif
#endif

static void lust_mono_now(long ts[2]) LUST_BODY({
#ifdef LUST_SYS_CLOCK_GETTIME
    syscall(LUST_SYS_CLOCK_GETTIME, 1 /* CLOCK_MONOTONIC */, ts);
#else
    ts[0] = 0;
    ts[1] = 0;
#endif
})

int lust_cv_wait_timeout(uint32_t *cv, uint32_t *m, uint64_t secs, uint32_t nanos) LUST_BODY({
    long dl[2];
    lust_mono_now(dl);
    dl[0] += (long)secs;
    dl[1] += (long)nanos;
    if (dl[1] >= 1000000000L) {
        dl[0] += 1;
        dl[1] -= 1000000000L;
    }
    uint32_t s;
    __atomic_load(cv, &s, 5);
    lust_mutex_unlock(m);
    int timed = 0;
    for (;;) {
        uint32_t cur;
        __atomic_load(cv, &cur, 5);
        if (cur != s) break;
        long now[2];
        lust_mono_now(now);
        long rs = dl[0] - now[0];
        long rn = dl[1] - now[1];
        if (rn < 0) {
            rs -= 1;
            rn += 1000000000L;
        }
        if (rs < 0) {
            timed = 1;
            break;
        }
#ifdef LUST_SYS_FUTEX
        {
            long rel[2];
            rel[0] = rs;
            rel[1] = rn;
            syscall(LUST_SYS_FUTEX, cv, 128 /* FUTEX_WAIT_PRIVATE */, s, rel, (void *)0, 0);
        }
#else
        sched_yield();
#endif
    }
    lust_mutex_lock(m);
    return timed;
})

typedef struct lust_Barrier {
    uint32_t lock;
    uint32_t seq;
    uint64_t count;
    uint64_t gen;
    uint64_t n;
} lust_Barrier;

/* 1 for the leader (the arrival that releases the others). */
int lust_barrier_wait(lust_Barrier *b) LUST_BODY({
    lust_mutex_lock(&b->lock);
    uint64_t g = b->gen;
    if (++b->count < b->n) {
        while (b->gen == g) {
            uint32_t s;
            __atomic_load(&b->seq, &s, 5);
            lust_mutex_unlock(&b->lock);
            lust_futex_wait(&b->seq, s);
            lust_mutex_lock(&b->lock);
        }
        lust_mutex_unlock(&b->lock);
        return 0;
    }
    b->count = 0;
    b->gen++;
    lust_cv_notify(&b->seq, 1);
    lust_mutex_unlock(&b->lock);
    return 1;
})

/* 1 when the caller must set the value (state is now 1); 0 when it is
   set (after waiting out another thread's set). */
int lust_once_begin(uint32_t *st) LUST_BODY({
    for (;;) {
        uint32_t zero = 0, one = 1, s;
        if (__atomic_compare_exchange(st, &zero, &one, 0, 2, 2)) return 1;
        __atomic_load(st, &s, 2);
        if (s == 2) return 0;
        if (s == 1) lust_futex_wait(st, 1);
    }
})

void lust_once_finish(uint32_t *st) LUST_BODY({
    uint32_t two = 2;
    __atomic_store(st, &two, 3);
    lust_futex_wake(st, 0x7fffffff);
})

/* A set whose init closure panicked (panic=unwind): the lock is empty
   again, and one waiting thread becomes the next setter, as in std. */
void lust_once_abort(uint32_t *st) LUST_BODY({
    uint32_t zero = 0;
    __atomic_store(st, &zero, 3);
    lust_futex_wake(st, 0x7fffffff);
})

int lust_once_is_done(uint32_t *st) LUST_BODY({
    uint32_t s;
    __atomic_load(st, &s, 2);
    return s == 2;
})

/* ---------- Duration and thread::sleep ----------

   A Duration is { uint64_t secs; uint32_t nanos; } (nanos < 1e9). */
typedef struct lust_Duration {
    uint64_t secs;
    uint32_t nanos;
} lust_Duration;

/* `Duration::new(secs, nanos)`: carries whole seconds out of nanos;
   panics as std on overflow. */
lust_Duration lust_dur_new(uint64_t secs, uint32_t nanos, lust_loc loc) LUST_BODY({
    lust_Duration d;
    uint64_t extra = nanos / 1000000000u;
    (void)loc;
    if (secs > UINT64_MAX - extra) lust_panic_std("overflow in Duration::new", "core/src/time.rs:201:18");
    d.secs = secs + extra;
    d.nanos = nanos % 1000000000u;
    return d;
})

/* secs * per_sec + nanos / nanos_per as a u128 (as_millis and kin). */
lust_u128 lust_dur_as(lust_Duration d, uint64_t per_sec, uint64_t nanos_per) LUST_BODY({
    uint64_t a = d.secs, b = per_sec;
    uint64_t alo = a & 0xffffffffu, ahi = a >> 32, blo = b & 0xffffffffu, bhi = b >> 32;
    uint64_t ll = alo * blo, lh = alo * bhi, hl = ahi * blo, hh = ahi * bhi;
    uint64_t mid = (ll >> 32) + (lh & 0xffffffffu) + (hl & 0xffffffffu);
    lust_u128 r;
    r.lo = (ll & 0xffffffffu) | (mid << 32);
    r.hi = hh + (lh >> 32) + (hl >> 32) + (mid >> 32);
    lust_u128 add;
    add.lo = d.nanos / nanos_per;
    add.hi = 0;
    return lust_u128_add(r, add);
})

#ifdef LUST_IMPL
#if defined(__linux__) && defined(__x86_64__)
#define LUST_SYS_NANOSLEEP 35
#elif defined(__linux__) && defined(__aarch64__)
#define LUST_SYS_NANOSLEEP 101
#endif
#endif

/* `thread::sleep`: nanosleep through syscall (no <time.h> in the runtime
   text), resumed after a signal. */
void lust_thread_sleep(lust_Duration d) LUST_BODY({
#ifdef LUST_SYS_NANOSLEEP
    long ts[2], rem[2];
    while (d.secs > 0 || d.nanos > 0) {
        uint64_t s = d.secs > 0x7fffffff ? 0x7fffffff : d.secs;
        ts[0] = (long)s;
        ts[1] = (long)d.nanos;
        d.secs -= s;
        d.nanos = 0;
        while (syscall(LUST_SYS_NANOSLEEP, ts, rem) != 0) { ts[0] = rem[0]; ts[1] = rem[1]; }
    }
#else
    (void)d;
    sched_yield();
#endif
})
