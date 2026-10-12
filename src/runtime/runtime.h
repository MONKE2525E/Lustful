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

typedef struct { uint8_t *ptr; uint64_t len; } lust_str;
typedef struct { uint8_t *ptr; uint64_t len; uint64_t cap; } lust_String;
typedef struct { void *ptr; uint64_t len; uint64_t cap; } lust_Vec;
typedef struct { uint64_t n; } lust_Args;

/* Program globals, defined in the runtime unit and set by main. */
extern int lust_argc;
extern const char *lust_file;

/* Every function is called through this table (see cgen.rs). */
typedef void (*lust_fnptr)(void);
extern lust_fnptr lust_fns[];
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

