/* Enumerate NPN equivalence class representatives of 5-variable Boolean
 * functions (input permutations x input flips x output complement).
 * Expected class count: 616,126.  Output: binary file of uint32 reps
 * (the minimum truth table of each orbit).
 *
 *   cc -O2 -o npn5 npn5.c && ./npn5 npn5_reps.bin
 *
 * Method: iterate truth tables 0..2^32-1; unseen f starts a new orbit; apply
 * all 3840 input transforms (byte-sliced lookup tables) and complement, mark
 * every image in a 512 MB bitmap, record the orbit minimum.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define NV 5
#define SIZE 32
#define NMAPS 3840          /* 5! * 2^5 */

static uint32_t T[NMAPS][4][256];   /* byte-sliced transform tables */
static uint8_t *seen;

static void build_maps(void) {
    int perm[NV] = {0, 1, 2, 3, 4};
    int idx = 0;
    /* iterate permutations via Heap's algorithm, materialized simply: */
    int perms[120][NV], np = 0;
    int a[NV] = {0, 1, 2, 3, 4}, c[NV] = {0, 0, 0, 0, 0};
    memcpy(perms[np++], a, sizeof a);
    for (int i = 0; i < NV;) {
        if (c[i] < i) {
            int j = (i % 2) ? c[i] : 0, t = a[j];
            a[j] = a[i]; a[i] = t;
            memcpy(perms[np++], a, sizeof a);
            c[i]++; i = 0;
        } else c[i++] = 0;
    }
    (void)perm;
    for (int p = 0; p < 120; p++)
        for (int flips = 0; flips < 32; flips++, idx++) {
            int map[SIZE];
            for (int x = 0; x < SIZE; x++) {
                int y = x ^ flips, z = 0;
                for (int i = 0; i < NV; i++)
                    z |= ((y >> perms[p][i]) & 1) << i;
                map[x] = z;   /* g(x) = f(map[x]) : bit x of g = bit map[x] of f */
            }
            /* byte-sliced: for byte b of f, precompute contribution to g:
               T[idx][b][v] = OR over x with map[x] in byte b and bit set in v */
            memset(T[idx], 0, sizeof T[idx]);
            for (int x = 0; x < SIZE; x++) {
                int src = map[x], byte = src >> 3, bit = src & 7;
                for (int v = 0; v < 256; v++)
                    if ((v >> bit) & 1)
                        T[idx][byte][v] |= (uint32_t)1 << x;
            }
        }
}

static inline uint32_t apply(int m, uint32_t f) {
    return T[m][0][f & 255] | T[m][1][(f >> 8) & 255] |
           T[m][2][(f >> 16) & 255] | T[m][3][f >> 24];
}

int main(int argc, char **argv) {
    if (argc != 2) { fprintf(stderr, "usage: %s out.bin\n", argv[0]); return 1; }
    build_maps();
    seen = calloc(1u << 29, 1);          /* 2^32 bits = 512 MB */
    if (!seen) { fprintf(stderr, "alloc failed\n"); return 1; }
    FILE *out = fopen(argv[1], "wb");
    uint64_t nclasses = 0, total = 0;
    for (uint64_t f0 = 0; f0 < (1ull << 32); f0++) {
        if (seen[f0 >> 3] & (1u << (f0 & 7))) continue;
        uint32_t f = (uint32_t)f0, mn = f;
        uint64_t orbit = 0;
        for (int m = 0; m < NMAPS; m++) {
            uint32_t g = apply(m, f), gc = ~g;
            if (!(seen[g >> 3] & (1u << (g & 7)))) { seen[g >> 3] |= 1u << (g & 7); orbit++; }
            if (!(seen[gc >> 3] & (1u << (gc & 7)))) { seen[gc >> 3] |= 1u << (gc & 7); orbit++; }
            if (g < mn) mn = g;
            if (gc < mn) mn = gc;
        }
        fwrite(&mn, 4, 1, out);
        nclasses++; total += orbit;
        if ((nclasses & 0xFFFF) == 0)
            fprintf(stderr, "classes %llu, covered %llu\n",
                    (unsigned long long)nclasses, (unsigned long long)total);
    }
    fclose(out);
    printf("NPN classes: %llu (expected 616126), functions covered: %llu "
           "(expected 4294967296)\n",
           (unsigned long long)nclasses, (unsigned long long)total);
    return 0;
}
