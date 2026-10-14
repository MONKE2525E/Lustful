/* Bodies of the std platform intrinsics declared in sys.h (W-SHIM). */
#include <errno.h>

int64_t lust_sys_write_std(int32_t fd, const uint8_t *p, uint64_t len) {
    FILE *f = fd == 2 ? stderr : stdout;
    if (len == 0) return 0;
    size_t n = fwrite(p, 1, (size_t)len, f);
    if (n < len) {
        int e = errno ? errno : 5; /* EIO when stdio gives no reason */
        clearerr(f);
        if (n == 0) return -(int64_t)e;
    }
    if (fd == 2 && fflush(stderr) != 0) {
        int e = errno ? errno : 5;
        clearerr(stderr);
        return -(int64_t)e;
    }
    return (int64_t)n;
}

int32_t lust_sys_flush_std(int32_t fd) {
    FILE *f = fd == 2 ? stderr : stdout;
    if (fflush(f) != 0) {
        int e = errno ? errno : 5;
        clearerr(f);
        return e;
    }
    return 0;
}

void lust_sys_os_error_text(int32_t code, lust_String *out) {
    lust_string_push_cstr(out, strerror(code));
}

lust_Vec lust_sys_fmt_arguments_bytes(lust_String args) {
    lust_Vec v;
    v.ptr = args.ptr;
    v.len = args.len;
    v.cap = args.cap;
    return v;
}
