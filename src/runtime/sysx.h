/* The Unix calls behind the rustix adapter (w-cinterop2): the C
   behind the `sys_x_*` intrinsics of src/ty/lang.rs, called from
   library/deps/rustix. Paths cross as (ptr, len) byte strings and
   are copied to a NUL-terminated buffer here; an empty path with
   a real dirfd stays empty (AT_EMPTY_PATH callers pass the flag).
   OS errors return as errno (positive), or as -errno where the
   value is an fd or a flag word. Stat records are 8-byte
   little-endian fields appended to the out Vec (sysx.c lists
   them).

   Declarations here are in every unit; bodies (sysx.c) only in
   the runtime unit (LUST_IMPL), like sysnet.h. */
#ifndef LUST_RT_SYSX_H
#define LUST_RT_SYSX_H

/* kill(2): 0 or errno. */
int32_t lust_sys_x_kill(int32_t pid, int32_t sig);
/* getppid(2). */
int32_t lust_sys_x_getppid(void);
/* prctl(PR_SET_PDEATHSIG, sig): 0 or errno. */
int32_t lust_sys_x_prctl_deathsig(int32_t sig);
/* getrlimit: appends current and maximum as two u64 (RLIM_INFINITY
   is UINT64_MAX); 0 or errno. */
int32_t lust_sys_x_getrlimit(int32_t resource, lust_Vec *out);
/* setrlimit: 0 or errno. */
int32_t lust_sys_x_setrlimit(int32_t resource, uint64_t current, uint64_t maximum);
/* openat(2) with the raw Linux flags and mode: the fd or -errno. */
int32_t lust_sys_x_openat(int32_t dirfd, const uint8_t *p, uint64_t len, int32_t flags, uint32_t mode);
/* fstatat(2): appends the 16-field stat record; 0 or errno. */
int32_t lust_sys_x_statat(int32_t dirfd, const uint8_t *p, uint64_t len, int32_t flags, lust_Vec *out);
/* fstat(2): appends the 16-field stat record; 0 or errno. */
int32_t lust_sys_x_fstat(int32_t fd, lust_Vec *out);
/* statx(2): appends the 23-field statx record; 0 or errno. */
int32_t lust_sys_x_statx(int32_t dirfd, const uint8_t *p, uint64_t len, int32_t flags, uint32_t mask, lust_Vec *out);
/* faccessat2 (faccessat fallback without AT_EACCESS): 0 or errno. */
int32_t lust_sys_x_accessat(int32_t dirfd, const uint8_t *p, uint64_t len, int32_t mode, int32_t flags);
/* utimensat(2) with both times as (sec, nsec): 0 or errno. */
int32_t lust_sys_x_utimensat(int32_t dirfd, const uint8_t *p, uint64_t len, int64_t a_sec, int64_t a_nsec, int64_t m_sec, int64_t m_nsec, int32_t flags);
/* mknodat(2): 0 or errno. */
int32_t lust_sys_x_mknodat(int32_t dirfd, const uint8_t *p, uint64_t len, uint32_t mode, uint64_t dev);
/* fcntl(F_GETFL): the flags or -errno. */
int32_t lust_sys_x_fcntl_getfl(int32_t fd);
/* fcntl(F_SETFL): 0 or errno. */
int32_t lust_sys_x_fcntl_setfl(int32_t fd, int32_t flags);
/* ioctl(TIOCGWINSZ): appends row, col, xpixel, ypixel as u16
   little-endian pairs (8 bytes); 0 or errno. */
int32_t lust_sys_x_winsize(int32_t fd, lust_Vec *out);
/* pipe2(2) with the raw Linux flags: appends the two fds as 8-byte
   fields; 0 or errno. */
int32_t lust_sys_x_pipe(int32_t flags, lust_Vec *out);
/* dup2(2): the new fd or -errno. */
int32_t lust_sys_x_dup2(int32_t oldfd, int32_t newfd);
/* poll(2) over `recs`: one 8-byte field per fd (fd in the low 32
   bits, events at bit 32, revents at bit 48), revents written
   back in place. Returns the ready count or -errno. A timeout
   of (sec, nsec) with sec<0 waits without a limit. */
int32_t lust_sys_x_poll(lust_Vec *recs, int64_t sec, int64_t nsec);

#ifdef LUST_IMPL
#include "sysx.c"
#endif

#endif
