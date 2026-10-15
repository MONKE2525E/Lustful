/* The Unix calls behind the rustix adapter: see sysx.h. Included
   only under LUST_IMPL, after the runtime's own includes. */
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <poll.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <termios.h>
#include <unistd.h>

/* Appends `n` bytes to a Vec<u8> (the sysnet.c shape). */
static void lust_sysx_push(lust_Vec *out, const void *p, uint64_t n) {
    if (n == 0) return;
    lust_vec_reserve(out, n, 1, 1);
    memcpy((uint8_t *)out->ptr + out->len, p, (size_t)n);
    out->len += n;
}

/* Pushes one u64 to `out` little-endian. */
static void lust_sysx_u64(lust_Vec *out, uint64_t v) {
    uint8_t b[8];
    for (int k = 0; k < 8; k++) b[k] = (uint8_t)(v >> (8 * k));
    lust_sysx_push(out, b, 8);
}

/* A NUL-terminated copy of a (ptr, len) path, or NULL on OOM. */
static char *lust_sysx_path(const uint8_t *p, uint64_t len) {
    char *s = (char *)malloc(len + 1);
    if (!s) return NULL;
    memcpy(s, p, len);
    s[len] = 0;
    return s;
}

int32_t lust_sys_x_kill(int32_t pid, int32_t sig) {
    return kill((pid_t)pid, sig) == 0 ? 0 : errno;
}

int32_t lust_sys_x_getppid(void) {
    return (int32_t)getppid();
}

int32_t lust_sys_x_prctl_deathsig(int32_t sig) {
    return prctl(PR_SET_PDEATHSIG, (unsigned long)sig, 0, 0, 0) == 0 ? 0 : errno;
}

int32_t lust_sys_x_getrlimit(int32_t resource, lust_Vec *out) {
    struct rlimit rl;
    if (getrlimit((int)resource, &rl) != 0) return errno;
    lust_sysx_u64(out, (uint64_t)rl.rlim_cur);
    lust_sysx_u64(out, (uint64_t)rl.rlim_max);
    return 0;
}

int32_t lust_sys_x_setrlimit(int32_t resource, uint64_t current, uint64_t maximum) {
    struct rlimit rl;
    rl.rlim_cur = (rlim_t)current;
    rl.rlim_max = (rlim_t)maximum;
    return setrlimit((int)resource, &rl) == 0 ? 0 : errno;
}

int32_t lust_sys_x_openat(int32_t dirfd, const uint8_t *p, uint64_t len, int32_t flags, uint32_t mode) {
    char *s = lust_sysx_path(p, len);
    if (!s) return -ENOMEM;
    int fd = openat(dirfd, s, flags, (mode_t)mode);
    int e = errno;
    free(s);
    return fd < 0 ? -e : fd;
}

/* The 16-field stat record: dev, ino, nlink, mode, uid, gid,
   rdev, size, blksize, blocks, atime sec/nsec, mtime sec/nsec,
   ctime sec/nsec (signed fields cross as their u64 bits). */
static void lust_sysx_stat_rec(lust_Vec *out, const struct stat *st) {
    uint64_t f[16] = {(uint64_t)st->st_dev, (uint64_t)st->st_ino, (uint64_t)st->st_nlink,
                      (uint64_t)st->st_mode, (uint64_t)st->st_uid, (uint64_t)st->st_gid,
                      (uint64_t)st->st_rdev, (uint64_t)st->st_size, (uint64_t)st->st_blksize,
                      (uint64_t)st->st_blocks, (uint64_t)st->st_atim.tv_sec, (uint64_t)st->st_atim.tv_nsec,
                      (uint64_t)st->st_mtim.tv_sec, (uint64_t)st->st_mtim.tv_nsec,
                      (uint64_t)st->st_ctim.tv_sec, (uint64_t)st->st_ctim.tv_nsec};
    for (int i = 0; i < 16; i++) lust_sysx_u64(out, f[i]);
}

int32_t lust_sys_x_statat(int32_t dirfd, const uint8_t *p, uint64_t len, int32_t flags, lust_Vec *out) {
    char *s = lust_sysx_path(p, len);
    if (!s) return ENOMEM;
    struct stat st;
    int r = fstatat(dirfd, s, &st, flags);
    int e = errno;
    free(s);
    if (r != 0) return e;
    lust_sysx_stat_rec(out, &st);
    return 0;
}

int32_t lust_sys_x_fstat(int32_t fd, lust_Vec *out) {
    struct stat st;
    if (fstat(fd, &st) != 0) return errno;
    lust_sysx_stat_rec(out, &st);
    return 0;
}

/* The kernel's struct statx (stable ABI, 256 bytes), spelled
   out because tcc's headers do not expose glibc's. Field order
   is the kernel's: atime, btime, ctime, mtime. */
struct lust_statx_time {
    int64_t tv_sec;
    uint32_t tv_nsec;
    int32_t reserved;
};
struct lust_statx {
    uint32_t stx_mask;
    uint32_t stx_blksize;
    uint64_t stx_attributes;
    uint32_t stx_nlink;
    uint32_t stx_uid;
    uint32_t stx_gid;
    uint16_t stx_mode;
    uint16_t spare0[1];
    uint64_t stx_ino;
    uint64_t stx_size;
    uint64_t stx_blocks;
    uint64_t stx_attributes_mask;
    struct lust_statx_time stx_atime;
    struct lust_statx_time stx_btime;
    struct lust_statx_time stx_ctime;
    struct lust_statx_time stx_mtime;
    uint32_t stx_rdev_major;
    uint32_t stx_rdev_minor;
    uint32_t stx_dev_major;
    uint32_t stx_dev_minor;
    uint64_t stx_mnt_id;
    uint32_t stx_dio_mem_align;
    uint32_t stx_dio_offset_align;
    uint64_t spare3[12];
};
#ifndef SYS_statx
#define SYS_statx 332
#endif

/* The statx record: mask, blksize, attributes, nlink, uid, gid,
   mode, ino, size, blocks, atime sec/nsec, mtime sec/nsec,
   ctime sec/nsec, btime sec/nsec, rdev major/minor, dev
   major/minor. */
int32_t lust_sys_x_statx(int32_t dirfd, const uint8_t *p, uint64_t len, int32_t flags, uint32_t mask, lust_Vec *out) {
    char *s = lust_sysx_path(p, len);
    if (!s) return ENOMEM;
    struct lust_statx stx;
    long r = syscall(SYS_statx, dirfd, s, flags, mask, &stx);
    int e = errno;
    free(s);
    if (r != 0) return e;
    uint64_t f[23] = {stx.stx_mask, stx.stx_blksize, stx.stx_attributes, stx.stx_nlink,
                      stx.stx_uid, stx.stx_gid, stx.stx_mode, stx.stx_ino,
                      stx.stx_size, stx.stx_blocks, stx.stx_attributes_mask, (uint64_t)stx.stx_atime.tv_sec, stx.stx_atime.tv_nsec,
                      (uint64_t)stx.stx_mtime.tv_sec, stx.stx_mtime.tv_nsec, (uint64_t)stx.stx_ctime.tv_sec,
                      stx.stx_ctime.tv_nsec, (uint64_t)stx.stx_btime.tv_sec, stx.stx_btime.tv_nsec,
                      stx.stx_rdev_major, stx.stx_rdev_minor, stx.stx_dev_major, stx.stx_dev_minor};
    for (int i = 0; i < 23; i++) lust_sysx_u64(out, f[i]);
    return 0;
}

int32_t lust_sys_x_accessat(int32_t dirfd, const uint8_t *p, uint64_t len, int32_t mode, int32_t flags) {
    char *s = lust_sysx_path(p, len);
    if (!s) return ENOMEM;
#ifdef SYS_faccessat2
    long r = syscall(SYS_faccessat2, dirfd, s, mode, flags);
    int e = errno;
    if (r != 0 && e == ENOSYS) {
        r = faccessat(dirfd, s, mode, flags & AT_EACCESS);
        e = errno;
    }
#else
    long r = faccessat(dirfd, s, mode, flags & AT_EACCESS);
    int e = errno;
#endif
    free(s);
    return r == 0 ? 0 : e;
}

int32_t lust_sys_x_utimensat(int32_t dirfd, const uint8_t *p, uint64_t len, int64_t a_sec, int64_t a_nsec, int64_t m_sec, int64_t m_nsec, int32_t flags) {
    char *s = lust_sysx_path(p, len);
    if (!s) return ENOMEM;
    struct timespec ts[2] = {{(time_t)a_sec, (long)a_nsec}, {(time_t)m_sec, (long)m_nsec}};
    int r = utimensat(dirfd, s, ts, flags);
    int e = errno;
    free(s);
    return r == 0 ? 0 : e;
}

int32_t lust_sys_x_mknodat(int32_t dirfd, const uint8_t *p, uint64_t len, uint32_t mode, uint64_t dev) {
    char *s = lust_sysx_path(p, len);
    if (!s) return ENOMEM;
    int r = mknodat(dirfd, s, (mode_t)mode, (dev_t)dev);
    int e = errno;
    free(s);
    return r == 0 ? 0 : e;
}

int32_t lust_sys_x_fcntl_getfl(int32_t fd) {
    int r = fcntl(fd, F_GETFL);
    return r < 0 ? -errno : r;
}

int32_t lust_sys_x_fcntl_setfl(int32_t fd, int32_t flags) {
    return fcntl(fd, F_SETFL, flags) == 0 ? 0 : errno;
}

int32_t lust_sys_x_pipe(int32_t flags, lust_Vec *out) {
    int fds[2];
    if (pipe2(fds, flags) != 0) return errno;
    lust_sysx_u64(out, (uint64_t)(uint32_t)fds[0]);
    lust_sysx_u64(out, (uint64_t)(uint32_t)fds[1]);
    return 0;
}

int32_t lust_sys_x_dup2(int32_t oldfd, int32_t newfd) {
    int r = dup2(oldfd, newfd);
    return r < 0 ? -errno : r;
}

int32_t lust_sys_x_poll(lust_Vec *recs, int64_t sec, int64_t nsec) {
    uint64_t n = recs->len / 8;
    struct pollfd stack_fds[16];
    struct pollfd *fds = stack_fds;
    if (n > 16) {
        fds = (struct pollfd *)malloc((size_t)n * sizeof(struct pollfd));
        if (!fds) return -ENOMEM;
    }
    const uint8_t *bytes = (const uint8_t *)recs->ptr;
    for (uint64_t i = 0; i < n; i++) {
        uint64_t v = 0;
        for (int k = 0; k < 8; k++) v |= (uint64_t)bytes[i * 8 + k] << (8 * k);
        fds[i].fd = (int)(uint32_t)v;
        fds[i].events = (short)(v >> 32);
        fds[i].revents = 0;
    }
    int timeout_ms = -1;
    if (sec >= 0) {
        int64_t ms = sec * 1000 + nsec / 1000000 + (nsec % 1000000 != 0 ? 1 : 0);
        timeout_ms = ms > INT32_MAX ? INT32_MAX : (int)ms;
    }
    int r = poll(fds, (nfds_t)n, timeout_ms);
    int e = errno;
    if (r >= 0) {
        uint8_t *out = (uint8_t *)recs->ptr;
        for (uint64_t i = 0; i < n; i++) {
            uint16_t rev = (uint16_t)fds[i].revents;
            out[i * 8 + 6] = (uint8_t)(rev & 0xff);
            out[i * 8 + 7] = (uint8_t)(rev >> 8);
        }
    }
    if (fds != stack_fds) free(fds);
    return r < 0 ? -e : r;
}

int32_t lust_sys_x_winsize(int32_t fd, lust_Vec *out) {
    struct winsize ws;
    if (ioctl(fd, TIOCGWINSZ, &ws) != 0) return errno;
    uint16_t f[4] = {ws.ws_row, ws.ws_col, ws.ws_xpixel, ws.ws_ypixel};
    uint8_t b[8];
    for (int i = 0; i < 4; i++) {
        b[2 * i] = (uint8_t)(f[i] & 0xff);
        b[2 * i + 1] = (uint8_t)(f[i] >> 8);
    }
    lust_sysx_push(out, b, 8);
    return 0;
}
