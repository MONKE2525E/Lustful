/* Bodies of the fd and process intrinsics declared in sysio.h
   (W-SHIM phase 2). */
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <spawn.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

extern char **environ;

/* Appends `n` bytes to a Vec<u8>. */
static void lust_sysio_push(lust_Vec *out, const void *p, uint64_t n) {
    if (n == 0) return;
    lust_vec_reserve(out, n, 1, 1);
    memcpy((uint8_t *)out->ptr + out->len, p, (size_t)n);
    out->len += n;
}

/* One read into a fresh heap buffer, appended to the Vec. */
int64_t lust_sys_fd_read(int32_t fd, uint64_t max, lust_Vec *out) {
    if (max == 0) return 0;
    uint8_t *tmp = malloc((size_t)max);
    if (!tmp) lust_oom();
    ssize_t n = read(fd, tmp, (size_t)max);
    if (n < 0) {
        int e = errno;
        free(tmp);
        return -(int64_t)e;
    }
    lust_sysio_push(out, tmp, (uint64_t)n);
    free(tmp);
    return (int64_t)n;
}

int64_t lust_sys_fd_write(int32_t fd, const uint8_t *p, uint64_t len) {
    ssize_t n = write(fd, p, (size_t)len);
    if (n < 0) return -(int64_t)errno;
    return (int64_t)n;
}

int32_t lust_sys_fd_close(int32_t fd) { return close(fd) == 0 ? 0 : errno; }

int32_t lust_sys_fd_dup(int32_t fd) {
    int n = fcntl(fd, F_DUPFD_CLOEXEC, 0);
    return n < 0 ? -errno : n;
}

int32_t lust_sys_fd_sync(int32_t fd) { return fsync(fd) == 0 ? 0 : errno; }

int32_t lust_sys_fd_truncate(int32_t fd, uint64_t len) { return ftruncate(fd, (off_t)len) == 0 ? 0 : errno; }

int64_t lust_sys_fd_seek(int32_t fd, int64_t off, int32_t whence) {
    off_t r = lseek(fd, (off_t)off, whence == 0 ? SEEK_SET : whence == 1 ? SEEK_CUR : SEEK_END);
    return r < 0 ? -(int64_t)errno : (int64_t)r;
}

/* The stat fields of sys.c's lust_sys_stat, for an open fd. */
int32_t lust_sys_fd_stat(int32_t fd, lust_Vec *out) {
    struct stat st;
    if (fstat(fd, &st) != 0) return errno;
    uint64_t f[15] = {st.st_mode, (uint64_t)st.st_size, (uint64_t)st.st_mtim.tv_sec, (uint64_t)st.st_mtim.tv_nsec, st.st_uid, st.st_gid,
                      (uint64_t)st.st_nlink, (uint64_t)st.st_ino, (uint64_t)st.st_dev, (uint64_t)st.st_atim.tv_sec,
                      (uint64_t)st.st_atim.tv_nsec, (uint64_t)st.st_ctim.tv_sec, (uint64_t)st.st_ctim.tv_nsec, (uint64_t)st.st_blocks,
                      (uint64_t)st.st_blksize};
    for (int i = 0; i < 15; i++) {
        uint8_t b[8];
        for (int k = 0; k < 8; k++) b[k] = (uint8_t)(f[i] >> (8 * k));
        lust_sysio_push(out, b, 8);
    }
    return 0;
}

/* flags: bits 0-1 access (0 O_RDONLY, 1 O_WRONLY, 2 O_RDWR), bit 2
   O_CREAT, bit 3 O_TRUNC, bit 4 O_APPEND, bit 5 O_EXCL. Always
   O_CLOEXEC, mode 0666, as std opens files on Linux. */
int32_t lust_sys_fd_open(const uint8_t *p, uint64_t len, int32_t flags) {
    char *s = malloc(len + 1);
    if (!s) lust_oom();
    memcpy(s, p, len);
    s[len] = 0;
    int f = (flags & 3) | O_CLOEXEC;
    if (flags & 4) f |= O_CREAT;
    if (flags & 8) f |= O_TRUNC;
    if (flags & 16) f |= O_APPEND;
    if (flags & 32) f |= O_EXCL;
    int fd = open(s, f, 0666);
    int e = errno;
    free(s);
    return fd < 0 ? -e : fd;
}

/* Stdin: one process-wide buffer, as std's stdin. The buffer fills
   with a single read of up to 8192 bytes (std's stdin buffer size is
   also 8192 on Linux through BufReader::DEFAULT_BUF_SIZE, behind a
   line-read shim that only changes how much a terminal read asks
   for; byte streams see the same data in the same order). */
static uint8_t lust_sysio_stdin_buf[8192];
static uint64_t lust_sysio_stdin_pos, lust_sysio_stdin_cap;

int64_t lust_sys_stdin_read(uint64_t max, lust_Vec *out) {
    if (max == 0) return 0;
    if (lust_sysio_stdin_pos < lust_sysio_stdin_cap) {
        uint64_t avail = lust_sysio_stdin_cap - lust_sysio_stdin_pos;
        uint64_t n = avail < max ? avail : max;
        lust_sysio_push(out, lust_sysio_stdin_buf + lust_sysio_stdin_pos, n);
        lust_sysio_stdin_pos += n;
        return (int64_t)n;
    }
    lust_sysio_stdin_pos = lust_sysio_stdin_cap = 0;
    return lust_sys_fd_read(0, max, out);
}

int64_t lust_sys_stdin_fill(lust_Vec *out) {
    if (lust_sysio_stdin_pos >= lust_sysio_stdin_cap) {
        ssize_t n = read(0, lust_sysio_stdin_buf, sizeof lust_sysio_stdin_buf);
        if (n < 0) return -(int64_t)errno;
        lust_sysio_stdin_pos = 0;
        lust_sysio_stdin_cap = (uint64_t)n;
    }
    uint64_t avail = lust_sysio_stdin_cap - lust_sysio_stdin_pos;
    lust_sysio_push(out, lust_sysio_stdin_buf + lust_sysio_stdin_pos, avail);
    return (int64_t)avail;
}

void lust_sys_stdin_consume(uint64_t n) {
    uint64_t avail = lust_sysio_stdin_cap - lust_sysio_stdin_pos;
    lust_sysio_stdin_pos += n < avail ? n : avail;
}

/* Reads one fd that poll says is ready; appends one chunk. Returns 1
   at EOF, 0 on data, or errno. */
static int lust_sysio_read_chunk(int32_t fd, lust_Vec *out, uint8_t *tmp) {
    ssize_t n = read(fd, tmp, 65536);
    if (n < 0) return errno == EINTR ? 0 : errno;
    if (n == 0) return 1;
    lust_sysio_push(out, tmp, (uint64_t)n);
    return 0;
}

int32_t lust_sys_fd_read_both(int32_t fd1, lust_Vec *out1, int32_t fd2, lust_Vec *out2) {
    uint8_t *tmp = malloc(65536);
    if (!tmp) lust_oom();
    int err = 0, done1 = fd1 < 0, done2 = fd2 < 0;
    while (!done1 || !done2) {
        struct pollfd pf[2] = {{fd1, POLLIN, 0}, {fd2, POLLIN, 0}};
        if (done1) pf[0].fd = -1;
        if (done2) pf[1].fd = -1;
        if (poll(pf, 2, -1) < 0) {
            if (errno == EINTR) continue;
            err = errno;
            break;
        }
        for (int i = 0; i < 2; i++) {
            if (!(pf[i].revents & (POLLIN | POLLHUP | POLLERR))) continue;
            int r = lust_sysio_read_chunk(pf[i].fd, i == 0 ? out1 : out2, tmp);
            if (r == 1) {
                if (i == 0) done1 = 1; else done2 = 1;
            } else if (r != 0) {
                if (i == 0) done1 = 1; else done2 = 1;
                if (!err) err = r;
            }
        }
    }
    free(tmp);
    return err;
}

int64_t lust_sys_proc_wait(uint32_t pid, uint8_t block) {
    int st;
    for (;;) {
        pid_t r = waitpid((pid_t)pid, &st, block ? 0 : WNOHANG);
        if (r < 0 && errno == EINTR) continue;
        if (r < 0) return -(int64_t)errno;
        if (r == 0) return -2;
        return (int64_t)st;
    }
}

int32_t lust_sys_proc_kill(uint32_t pid) { return kill((pid_t)pid, SIGKILL) == 0 ? 0 : errno; }
