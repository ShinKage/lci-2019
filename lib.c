#include <stdint.h>
#include <stdio.h>

int32_t read_int() {
    int32_t x = 0;
    scanf("%d", &x);
    return x;
}

int8_t read_bool() {
    int8_t x = 0;
    scanf("%c", &x);
    return x;
}

int8_t *read_unit() {
    return NULL;
}
