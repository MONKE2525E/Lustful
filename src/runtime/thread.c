/* ---------- Thread-local keys (thread_local!, ARCH 7.3) ----------

   Storage is per thread from the start, through one pthread key: no C
   _Thread_local or __thread anywhere (tcc breaks TLS, spike K3). The key
   holds the thread's TLS block. The block has one cell per thread_local!
   static the thread touched, found by the static's slot, and the list of
   destructors to run when the thread ends.

   A `LocalKey` static is a `uint64_t` global holding the key's slot,
   1, 2, .. (collect numbers them). A cell is codegen's `(u8, T)` tuple:
   the state byte (0 initial, 1 alive, 2 destroyed) and the value. A new
   cell is all zero bytes.

   Destructors run newest first, as glibc's __cxa_thread_atexit_impl
   runs them (Rust std on Linux registers through it): a value that
   needs drop registers its destructor at its first access. A destructor
   can touch other keys, register new destructors (they run next), or
   find a destroyed key (codegen panics with Rust's AccessError message).
   Other threads run the list from the pthread key destructor; the main
   thread runs it at process exit, before stdout is flushed, from
   `main`'s return and from `lust_exit`, as glibc's exit() does. */

/* The calling thread's cell for the static `key`: `size` bytes with
   `align`, all zero (state initial) when the thread first asks. */
void *lust_tls_cell(uint64_t *key, uint64_t size, uint64_t align);
/* Queues `dtor(cell)` to run when the calling thread ends. */
void lust_tls_register(void *cell, void (*dtor)(void *));
/* Runs the calling thread's queued destructors, newest first, until none
   are left. The main thread calls it at process exit. */
void lust_tls_exit(void);

#ifdef LUST_IMPL
#include <pthread.h>
#include <stdatomic.h>

typedef struct {
    void *cell;
    void (*dtor)(void *);
} lust_tls_dtor;

typedef struct {
    void **cells;
    uint64_t cap;
    lust_tls_dtor *dtors;
    uint64_t ndtors;
    uint64_t dcap;
} lust_tls_block;

static pthread_key_t lust_tls_key;
static pthread_once_t lust_tls_once = PTHREAD_ONCE_INIT;
/* Set once the key exists: the fast path reads it before the key, and a
   program that never touches TLS makes no key at exit. */
static volatile int lust_tls_ready;

static void lust_tls_run(lust_tls_block *b) {
    while (b->ndtors) {
        lust_tls_dtor d = b->dtors[--b->ndtors];
        d.dtor(d.cell);
    }
}

/* The pthread key destructor of a thread other than main. The key's value
   is cleared before this runs; destructors may touch TLS again, so the
   block goes back under the key until the list is empty. */
static void lust_tls_thread_end(void *p) {
    lust_tls_block *b = (lust_tls_block *)p;
    pthread_setspecific(lust_tls_key, b);
    lust_tls_run(b);
    pthread_setspecific(lust_tls_key, 0);
    for (uint64_t i = 0; i < b->cap; i++) free(b->cells[i]);
    free(b->cells);
    free(b->dtors);
    free(b);
}

static void lust_tls_make_key(void) {
    if (pthread_key_create(&lust_tls_key, lust_tls_thread_end) != 0) abort();
    atomic_thread_fence(memory_order_release);
    lust_tls_ready = 1;
}

static lust_tls_block *lust_tls_block_get(void) {
    pthread_once(&lust_tls_once, lust_tls_make_key);
    lust_tls_block *b = (lust_tls_block *)pthread_getspecific(lust_tls_key);
    if (!b) {
        b = (lust_tls_block *)calloc(1, sizeof *b);
        if (!b) lust_oom();
        pthread_setspecific(lust_tls_key, b);
    }
    return b;
}

/* The first access to slot `s` on this thread: grows the block and makes
   a zeroed cell. */
static void *lust_tls_cell_slow(uint64_t s, uint64_t size, uint64_t align) {
    lust_tls_block *b = lust_tls_block_get();
    if (s > b->cap) {
        uint64_t cap = b->cap ? b->cap : 8;
        while (cap < s) cap *= 2;
        void **cells = (void **)realloc(b->cells, cap * sizeof(void *));
        if (!cells) lust_oom();
        memset(cells + b->cap, 0, (cap - b->cap) * sizeof(void *));
        b->cells = cells;
        b->cap = cap;
    }
    void *c = b->cells[s - 1];
    if (!c) {
        /* Cells are freed with plain free() (see lust_alloc). */
        c = lust_alloc_zeroed(size ? size : 1, align);
        b->cells[s - 1] = c;
    }
    return c;
}
#endif

void *lust_tls_cell(uint64_t *key, uint64_t size, uint64_t align) LUST_BODY({
    /* Fast path: plain reads (a key's slot never changes, and the block
       key exists before any block does). */
    uint64_t s = *key;
    if (lust_tls_ready) {
        lust_tls_block *b = (lust_tls_block *)pthread_getspecific(lust_tls_key);
        if (b && s <= b->cap && b->cells[s - 1]) return b->cells[s - 1];
    }
    return lust_tls_cell_slow(s, size, align);
})

void lust_tls_register(void *cell, void (*dtor)(void *)) LUST_BODY({
    lust_tls_block *b = lust_tls_block_get();
    if (b->ndtors == b->dcap) {
        uint64_t cap = b->dcap ? b->dcap * 2 : 8;
        lust_tls_dtor *d = (lust_tls_dtor *)realloc(b->dtors, cap * sizeof *d);
        if (!d) lust_oom();
        b->dtors = d;
        b->dcap = cap;
    }
    b->dtors[b->ndtors].cell = cell;
    b->dtors[b->ndtors].dtor = dtor;
    b->ndtors++;
})

void lust_tls_exit(void) LUST_BODY({
    if (!lust_tls_ready) return;
    lust_tls_block *b = (lust_tls_block *)pthread_getspecific(lust_tls_key);
    if (b) lust_tls_run(b);
})
