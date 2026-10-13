/* Lust C runtime. Every compilation unit includes this text.
   - With LUST_IMPL defined (one unit per program): full function definitions.
   - Without it (all other units): declarations only, so those units stay small and parse fast.
   Rules: wrapping math is done in uint64_t, so C integer promotion never makes signed overflow;
   every check that Rust does in debug builds is done here and panics the same way. */
#include <stdint.h>
#include <stddef.h>
#ifdef LUST_IMPL
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#define LUST_BODY(...) __VA_ARGS__
#else
void free(void *);
void abort(void);
#define LUST_BODY(...) ;
#endif

/* 128-bit integers. tcc has no __int128 (spike K3-13), so codegen uses a
   two-word struct; _Alignas on the first member gives the type the
   16-byte alignment Rust u128/i128 have (spike K3-21), which a type-level
   aligned attribute cannot do in tcc. `lo` is the low word. Size 16. */
typedef struct { _Alignas(16) uint64_t lo; uint64_t hi; } lust_u128;
typedef struct { _Alignas(16) uint64_t lo; uint64_t hi; } lust_i128;

/* Rust `()`: a zero-sized C form, so aggregates with a direct unit
   field have the exact Rust size. Size 0 (GNU empty struct, in tcc
   as in gcc), align 1. */
typedef struct { } lust_Unit;
_Static_assert(sizeof(lust_Unit) == 0 && _Alignof(lust_Unit) == 1, "unit layout");

typedef struct { uint8_t *ptr; uint64_t len; } lust_str;
typedef struct { uint8_t *ptr; uint64_t len; uint64_t cap; } lust_String;
typedef struct { void *ptr; uint64_t len; uint64_t cap; } lust_Vec;
/* `vec::IntoIter<T>`: the moved-in Vec buffer; elements `front..len` are still owned. */
typedef struct { void *ptr; uint64_t len; uint64_t cap; uint64_t front; } lust_VecIter;
typedef struct { uint64_t n; } lust_Args;
/* `&dyn Trait` and `&mut dyn Trait` (ARCH 2.8): the data pointer and the
   vtable, an array of words: drop glue, size, align, one super vtable per
   supertrait, then one entry per method (see src/check/object.rs). */
typedef struct { void *data; const void *const *vt; } lust_dyn;

/* Program globals, defined in the runtime unit and set by main. */
extern int lust_argc;
extern const char *lust_file;

/* Every function is called through this table (see cgen.rs). */
typedef void (*lust_fnptr)(void);
extern lust_fnptr lust_fns[];
/* One slot trampoline per slot (ARCH 4.5): stable addresses that
   forward through lust_fns, stored in fn pointer values. */
extern lust_fnptr lust_tramps[];
/* Entry for a `main` that returns `Result<(), E>`: set by the unit
   that holds main when it registers; NULL for a `()` main. */
extern int (*lust_main_entry_p)(void);
void lust_base_init(void);

/* A source location: (function id << 32) | (line within the function << 12) | column. Lines are
   relative to each function's first line (lust_fn_line), so the code for an unchanged function
   stays valid when code above it moves. */
typedef uint64_t lust_loc;
extern const uint32_t *lust_fn_line;
#ifdef LUST_IMPL
int lust_argc;
const char *lust_file;
const uint32_t *lust_fn_line;
#endif

