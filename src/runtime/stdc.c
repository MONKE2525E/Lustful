#include <time.h>

/* One clock reading as the u128 the time intrinsics return. */
static lust_u128 lust_clock_read(clockid_t clock) {
    struct timespec ts;
    if (clock_gettime(clock, &ts) != 0) {
        abort();
    }
    lust_u128 r;
    r.lo = (uint64_t)(int64_t)ts.tv_sec;
    r.hi = (uint64_t)ts.tv_nsec;
    return r;
}

lust_u128 lust_clock_now_raw(void) {
    return lust_clock_read(CLOCK_MONOTONIC);
}

lust_u128 lust_system_time_raw(void) {
    return lust_clock_read(CLOCK_REALTIME);
}

uint32_t lust_fmt_align(lust_Formatter *f) {
    return f->align;
}
