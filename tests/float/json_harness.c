#define LUST_IMPL 1
#include "../../src/runtime/runtime.h"
#include "../../src/runtime/core.c"
#include <stdio.h>
int main(void) {
    unsigned long long raw;
    while (scanf("%llx", &raw) == 1) {
        double value;
        uint64_t bits = (uint64_t)raw;
        char buf[32];
        memcpy(&value, &bits, 8);
        uint64_t len = lust_fmt_json_f64_buf(buf, value);
        printf("%016llx\t", raw);
        fwrite(buf, 1, len, stdout);
        putchar('\n');
    }
    return ferror(stdin) || ferror(stdout);
}
