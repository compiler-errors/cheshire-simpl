#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

struct empty_t {} empty;

void* _cheshire_malloc_array(uint64_t sz, uint64_t no) {
    return (uint8_t*) malloc(sz * no);
}

void* _cheshire_malloc(uint64_t sz) {
    return malloc(sz);
}

void _cheshire_assert(bool cond) {
    if (!cond) {
        printf("Cheshire assert condition failed!");
        exit(-1);
    }
}

struct empty_t println() {
    printf("\n");
    return empty;
}

struct empty_t print_uint(uint64_t i) {
    printf("%llu", i);
    return empty;
}

struct empty_t print_int(int64_t i) {
    printf("%lld", i);
    return empty;
}

struct empty_t print_string(char* s) {
    printf("%s", s);
    return empty;
}

#ifdef __cplusplus
}
#endif
