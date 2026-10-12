/* ---------- Panics ---------- */

void lust_panic(lust_String *msg, lust_loc loc) LUST_BODY({
    fflush(stdout);
    fprintf(stderr, "\nthread 'main' panicked at %s:%u:%u:\n%.*s\nnote: run with `RUST_BACKTRACE=1` environment variable to display a backtrace\n",
            lust_file, (unsigned)(lust_fn_line[loc >> 32] + ((loc >> 12) & 0xFFFFF)), (unsigned)(loc & 0xFFF), (int)msg->len, (const char *)msg->ptr);
    fflush(stderr);
    abort();
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

