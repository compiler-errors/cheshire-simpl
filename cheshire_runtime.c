#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

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

#ifdef __cplusplus
}
#endif
