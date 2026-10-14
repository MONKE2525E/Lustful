/* ---------- Panics (abort mode) ----------
   Matches rustc 1.99 with -C panic=abort: the default hook prints
       \nthread 'main' (<os tid>) panicked at <file>:<line>:<col>:\n<msg>\nnote: ...\n
   to stderr, then the process aborts (SIGABRT, shell status 134). Stdout
   is Rust's LineWriter (below): an abort loses the bytes it still holds. */

#ifdef LUST_IMPL
#include <unistd.h>
#include <errno.h>
#include <signal.h>
#ifdef __APPLE__
#include <pthread.h>
#else
#include <sys/syscall.h>
#endif

/* The OS thread id Rust's default hook prints (`thread::current_os_id`). */
static unsigned long long lust_os_tid(void) {
#ifdef __APPLE__
    uint64_t t = 0;
    pthread_threadid_np(NULL, &t);
    return (unsigned long long)t;
#else
    return (unsigned long long)syscall(SYS_gettid);
#endif
}

/* Std source locations of panics that Rust raises inside std (no
   track_caller), as rustc 1.99 prints them. */
#define LUST_STD_SRC "/rustc/b940084d7eb6a299eb4bfeb8e34901bc051e7ac4/library/"
#endif

/* Prints the default hook text for `msg` at `file:line:col` and aborts. */
void lust_panic_at(const uint8_t *msg, uint64_t len, const char *file, uint32_t line, uint32_t col) LUST_BODY({
    fprintf(stderr, "\nthread 'main' (%llu) panicked at %s:%u:%u:\n%.*s\nnote: run with `RUST_BACKTRACE=1` environment variable to display a backtrace\n",
            lust_os_tid(), file, (unsigned)line, (unsigned)col, (int)len, (const char *)msg);
    fflush(stderr);
    abort();
})

/* A std source location in a lust_loc (cgen's `std_loc`): the slot
   field is LUST_STD_SLOT plus an index into lust_std_files, the line and
   col fields are absolute. Index bit LUST_STD_POW marks `pow`, whose
   overflow says "exponentiate" where its multiply says "multiply". */
#define LUST_STD_SLOT 0xFFFFFF00u
#define LUST_STD_POW 0x40u
#ifdef LUST_IMPL
static const char *const lust_std_files[] = {
    LUST_STD_SRC "core/src/num/mod.rs",
    LUST_STD_SRC "core/src/char/methods.rs",
    LUST_STD_SRC "core/src/char/convert.rs",
    LUST_STD_SRC "alloc/src/vec/mod.rs",
    LUST_STD_SRC "core/src/cmp.rs",
    LUST_STD_SRC "core/src/iter/adapters/step_by.rs",
    LUST_STD_SRC "alloc/src/vec/spec_from_iter_nested.rs",
    LUST_STD_SRC "core/src/iter/traits/accum.rs",
    LUST_STD_SRC "core/src/iter/range.rs",
    LUST_STD_SRC "core/src/cell.rs",
    LUST_STD_SRC "std/src/thread/local.rs",
};
#endif

/* Per-slot source files, set by the main unit when the crate has more
   than one file: slot s's fn lives in lust_files[lust_slot_file[s]].
   NULL for a one-file crate, which uses lust_file. */
extern const char *const *lust_files;
extern const uint32_t *lust_slot_file;
#ifdef LUST_IMPL
const char *const *lust_files;
const uint32_t *lust_slot_file;
#endif

void lust_panic(lust_String *msg, lust_loc loc) LUST_BODY({
    uint32_t slot = (uint32_t)(loc >> 32);
    if (slot >= LUST_STD_SLOT) {
        lust_panic_at(msg->ptr, msg->len, lust_std_files[(slot - LUST_STD_SLOT) & ~LUST_STD_POW], (loc >> 12) & 0xFFFFF, loc & 0xFFF);
    }
    const char *file = lust_slot_file ? lust_files[lust_slot_file[slot]] : lust_file;
    lust_panic_at(msg->ptr, msg->len, file, lust_fn_line[slot] + ((loc >> 12) & 0xFFFFF), loc & 0xFFF);
})

void lust_panic_str(lust_str msg, lust_loc loc) LUST_BODY({
    lust_String s = lust_string_from(msg);
    lust_panic(&s, loc);
})

void lust_panic_cstr(const char *msg, lust_loc loc) LUST_BODY({
    lust_String s = lust_string_new();
    lust_string_push_cstr(&s, msg);
    lust_panic(&s, loc);
})

/* "attempt to <op> with overflow" (checked integer math). */
void lust_ovf(const char *op, lust_loc loc) LUST_BODY({
    uint32_t slot = (uint32_t)(loc >> 32);
    if (slot >= LUST_STD_SLOT && ((slot - LUST_STD_SLOT) & LUST_STD_POW)) op = "exponentiate";
    lust_String s = lust_string_new();
    lust_string_push_cstr(&s, "attempt to ");
    lust_string_push_cstr(&s, op);
    lust_string_push_cstr(&s, " with overflow");
    lust_panic(&s, loc);
})

/* A panic Rust raises at a fixed line of its own std source: `where` is
   "path:line:col" under library/. */
void lust_panic_std(const char *msg, const char *where) LUST_BODY({
    fprintf(stderr, "\nthread 'main' (%llu) panicked at " LUST_STD_SRC "%s:\n%s\nnote: run with `RUST_BACKTRACE=1` environment variable to display a backtrace\n",
            lust_os_tid(), where, msg);
    fflush(stderr);
    abort();
})

/* ---------- Stdout as Rust's LineWriter ----------
   Rust's stdout is a LineWriter with a 1024-byte buffer over fd 1, tty
   or not: a write that holds a newline sends everything up to its last
   newline at once, and only the tail stays buffered (BufWriter rules:
   a tail that does not fit flushes the buffer, one of 1024 bytes or
   more is written directly). So a panic=abort loses exactly the held
   tail, and stdout and stderr interleave as in Rust. `lust_print_out`
   gets one formatted string per print, where Rust writes piece by
   piece; the held bytes differ only when one partial line passes 1024
   bytes. SIGPIPE is ignored as in Rust, so a write to a closed pipe
   panics with Rust's message. */
#ifdef LUST_IMPL
static uint8_t lust_out_buf[1024];
static uint64_t lust_out_len;
/* io::Write on Stdout (sys.c) returns a write error where print! panics:
   in soft mode the first error lands in lust_out_err (errno, or EIO for
   a zero-byte write) and the held bytes are dropped. */
static int lust_out_soft, lust_out_err;

static void lust_out_raw(const uint8_t *p, uint64_t n) {
    while (n) {
        ssize_t w = write(1, p, n);
        if (w < 0 && errno == EINTR) continue;
        if (w <= 0) {
            int e = w < 0 ? errno : 0;
            if (lust_out_soft) {
                if (!lust_out_err) lust_out_err = e ? e : EIO;
                lust_out_len = 0;
                return;
            }
            lust_String s = lust_string_new();
            lust_string_push_cstr(&s, "failed printing to stdout: ");
            if (e == EPIPE) lust_string_push_cstr(&s, "Broken pipe (os error 32)");
            else if (e == EBADF) lust_string_push_cstr(&s, "Bad file descriptor (os error 9)");
            else if (e == ENOSPC) lust_string_push_cstr(&s, "No space left on device (os error 28)");
            else if (e == 0) lust_string_push_cstr(&s, "failed to write whole buffer");
            else { char b[32]; snprintf(b, sizeof b, " (os error %d)", e); lust_string_push_cstr(&s, strerror(e)); lust_string_push_cstr(&s, b); }
            lust_out_len = 0;
            lust_panic_at(s.ptr, s.len, LUST_STD_SRC "std/src/io/stdio.rs", 1168, 9);
        }
        p += w;
        n -= (uint64_t)w;
    }
}

static void lust_out_flush_buf(void) {
    uint64_t n = lust_out_len;
    lust_out_len = 0;
    if (n) lust_out_raw(lust_out_buf, n);
}
#endif

/* LineWriterShim::write_all: the complete lines (through the last
   newline) go out after any held bytes; the tail then takes the
   BufWriter::write_all path. */
void lust_print_out(const uint8_t *p, uint64_t n) LUST_BODY({
    uint64_t k = n;
    while (k && p[k - 1] != '\n') k--;
    if (k) {
        lust_out_flush_buf();
        lust_out_raw(p, k);
        p += k;
        n -= k;
    } else if (lust_out_len && lust_out_buf[lust_out_len - 1] == '\n') {
        lust_out_flush_buf();
    }
    if (lust_out_len + n > sizeof lust_out_buf) lust_out_flush_buf();
    if (n >= sizeof lust_out_buf) lust_out_raw(p, n);
    else { memcpy(lust_out_buf + lust_out_len, p, n); lust_out_len += n; }
})

/* Flushes stdout: at exit and `process::exit` (Rust's rt::cleanup). */
void lust_print_flush(void) LUST_BODY({ lust_out_flush_buf(); })

/* `io::Write` for Stdout (sys.c): the same LineWriter as print!, so the
   two interleave in program order; 0 or an errno instead of a panic. */
int32_t lust_stdout_write_soft(const uint8_t *p, uint64_t n) LUST_BODY({
    lust_out_soft = 1;
    lust_out_err = 0;
    lust_print_out(p, n);
    lust_out_soft = 0;
    return lust_out_err;
})
int32_t lust_stdout_flush_soft(void) LUST_BODY({
    lust_out_soft = 1;
    lust_out_err = 0;
    lust_out_flush_buf();
    lust_out_soft = 0;
    return lust_out_err;
})

/* ---------- Stack overflow ----------
   Rust puts a SIGSEGV/SIGBUS handler on an alternate stack: a fault in
   the guard region below the thread's stack prints
       \nthread 'main' (<os tid>) has overflowed its stack\nfatal runtime error: stack overflow, aborting\n
   and aborts (134); any other fault gets the default action. Linux only
   (the stack bounds come from pthread_getattr_np). The region counts 16
   MiB below the stack, as a tcc frame can step past one guard page. */
#if defined(LUST_IMPL) && defined(__linux__)
/* No <pthread.h>: sync.c declares pthread_create with its own types.
   pthread_attr_t is opaque here (56 bytes on x86_64 and aarch64 glibc). */
typedef union { char bytes[64]; long align; } lust_pthread_attr;
unsigned long pthread_self(void);
int pthread_getattr_np(unsigned long, void *);
int pthread_attr_getstack(const void *, void **, size_t *);
int pthread_attr_destroy(void *);
static uintptr_t lust_guard_lo, lust_guard_hi;
static char lust_alt_stack[65536];

static void lust_segv(int sig, siginfo_t *info, void *ctx) {
    (void)ctx;
    uintptr_t a = (uintptr_t)info->si_addr;
    if (a >= lust_guard_lo && a < lust_guard_hi) {
        char tid[24];
        int n = 0;
        unsigned long long t = lust_os_tid();
        do { tid[n++] = (char)('0' + t % 10); t /= 10; } while (t);
        char msg[160];
        int m = 0;
        const char *head = "\nthread 'main' (", *tail = ") has overflowed its stack\nfatal runtime error: stack overflow, aborting\n";
        while (*head) msg[m++] = *head++;
        while (n) msg[m++] = tid[--n];
        while (*tail) msg[m++] = *tail++;
        if (write(2, msg, (size_t)m) < 0) {}
        abort();
    }
    /* Not a stack overflow: the default action on return re-runs the fault. */
    signal(sig, SIG_DFL);
}

static void lust_stack_guard_init(void) {
    lust_pthread_attr at;
    void *addr;
    size_t size;
    if (pthread_getattr_np(pthread_self(), &at) != 0) return;
    int ok = pthread_attr_getstack(&at, &addr, &size) == 0;
    pthread_attr_destroy(&at);
    if (!ok) return;
    long page = sysconf(_SC_PAGESIZE);
    lust_guard_hi = (uintptr_t)addr + (uintptr_t)(page > 0 ? page : 4096);
    lust_guard_lo = (uintptr_t)addr > (16u << 20) ? (uintptr_t)addr - (16u << 20) : 0;
    stack_t ss;
    memset(&ss, 0, sizeof ss);
    ss.ss_sp = lust_alt_stack;
    ss.ss_size = sizeof lust_alt_stack;
    if (sigaltstack(&ss, NULL) != 0) return;
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_sigaction = lust_segv;
    sa.sa_flags = SA_SIGINFO | SA_ONSTACK;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGSEGV, &sa, NULL);
    sigaction(SIGBUS, &sa, NULL);
}
#elif defined(LUST_IMPL)
static void lust_stack_guard_init(void) {}
#endif

/* Runtime setup before main: Rust ignores SIGPIPE and reports a stack
   overflow (above). */
void lust_rt_init(void) LUST_BODY({
    signal(SIGPIPE, SIG_IGN);
    lust_stack_guard_init();
})

/* A print to stdout (`to_stderr` 0) or stderr whose fmt impl returned
   Err: Rust has already written the pieces before the failing one. */
void lust_print_failed(int to_stderr, lust_String *s) LUST_BODY({
    if (to_stderr) { if (s->len) fwrite(s->ptr, 1, s->len, stderr); fflush(stderr); }
    else lust_print_out(s->ptr, s->len);
    lust_panic_std("a formatting trait implementation returned an error when the underlying stream did not", "core/src/io/write.rs:411:17");
})
