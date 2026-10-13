#include <stddef.h>
#include <stdint.h>

/**
 * Word-wise memcpy() and memset(). The newlib-nano versions selected by nano.specs move one byte per loop pass (a
 * 4 kB memset takes 0.7 ms), and the SPI and RF callbacks, which cannot preempt each other, copy and clear buffers of
 * that size. The Cortex-M4 reads and writes unaligned words.
 */

typedef uint32_t __attribute__((may_alias, aligned(1))) unaligned_word_t;

// Keeps GCC from turning the loops below back into calls of memcpy() and memset().
#define NO_LOOP_IDIOMS __attribute__((optimize("no-tree-loop-distribute-patterns")))

NO_LOOP_IDIOMS void *memcpy(void *restrict dest, const void *restrict src, size_t n) {
    uint8_t *d = (uint8_t *)dest;
    const uint8_t *s = (const uint8_t *)src;
    while (n >= 16) {
        ((unaligned_word_t *)d)[0] = ((const unaligned_word_t *)s)[0];
        ((unaligned_word_t *)d)[1] = ((const unaligned_word_t *)s)[1];
        ((unaligned_word_t *)d)[2] = ((const unaligned_word_t *)s)[2];
        ((unaligned_word_t *)d)[3] = ((const unaligned_word_t *)s)[3];
        d += 16;
        s += 16;
        n -= 16;
    }
    while (n >= 4) {
        *(unaligned_word_t *)d = *(const unaligned_word_t *)s;
        d += 4;
        s += 4;
        n -= 4;
    }
    while (n > 0) {
        *d++ = *s++;
        n--;
    }
    return dest;
}

NO_LOOP_IDIOMS void *memset(void *dest, int value, size_t n) {
    uint8_t *d = (uint8_t *)dest;
    uint32_t word = (uint8_t)value * 0x01010101u;
    while (n >= 16) {
        ((unaligned_word_t *)d)[0] = word;
        ((unaligned_word_t *)d)[1] = word;
        ((unaligned_word_t *)d)[2] = word;
        ((unaligned_word_t *)d)[3] = word;
        d += 16;
        n -= 16;
    }
    while (n >= 4) {
        *(unaligned_word_t *)d = word;
        d += 4;
        n -= 4;
    }
    while (n > 0) {
        *d++ = (uint8_t)value;
        n--;
    }
    return dest;
}
