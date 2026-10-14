/* The std platform crate's runtime (docs/ARCH.md sections 3.1 and 3.7,
   package W-SHIM): the C behind the `sys_*` intrinsics of src/ty/lang.rs,
   called from library/std/src/platform.rs and its modules. A `&[u8]`
   argument (SigTy::Bytes) arrives as a pointer and a length; `&mut
   String` and `&mut Vec<u8>` arrive as pointers to the runtime structs.
   OS errors return as errno values, as std's `io::Error::last_os_error`
   reads them.

   Declarations here are in every unit; bodies (sys.c) only in the
   runtime unit (LUST_IMPL), like deps.h. */
#ifndef LUST_RT_SYS_H
#define LUST_RT_SYS_H

/* Standard streams: writes go through the C stdio streams `print!` and
   `eprint!` use (stderr is flushed after each write, as Rust's stderr
   is unbuffered). */
int64_t lust_sys_write_std(int32_t fd, const uint8_t *p, uint64_t len);
int32_t lust_sys_flush_std(int32_t fd);

/* A `fmt::Arguments` value is its formatted text (a lust_String, see
   cgen's fmt_ctype); its bytes as a Vec<u8> take over the buffer. */
lust_Vec lust_sys_fmt_arguments_bytes(lust_String args);

/* The OS text of an error code, as std's `error_string` (strerror). */
void lust_sys_os_error_text(int32_t code, lust_String *out);

#ifdef LUST_IMPL
#include "sys.c"
#endif

#endif
