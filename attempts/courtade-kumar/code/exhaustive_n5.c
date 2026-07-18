/* Exhaustive Courtade-Kumar check at n=5 over a Gray-code range of functions.
 *
 * Enumerates Boolean functions f: {0,1}^5 -> {0,1} as 32-bit masks in Gray-code
 * order of an index range [start, end) with mask = gray(i) = i ^ (i >> 1).
 * Restricting i < 2^31 covers exactly the half with f(11111) = 0; the other half
 * consists of the complements 1-f, which have identical mutual information.
 *
 * For each f computes I(f(X);Y) exactly (X uniform, Y = BSC(alpha)^5 output),
 * maintaining the joint law P(f(X)=1, Y=y) incrementally (one input flips per
 * step). Reports the top two distinct MI values in the range with exact counts
 * and up to 16 example masks each.
 *
 *   cc -O3 -o exhaustive_n5 exhaustive_n5.c -lm
 *   ./exhaustive_n5 <alpha> <start> <end>
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define N 5
#define SIZE 32
#define MAXEX 16
#define TOL 1e-9

int main(int argc, char **argv) {
    if (argc != 4) { fprintf(stderr, "usage: %s alpha start end\n", argv[0]); return 1; }
    double alpha = atof(argv[1]);
    unsigned long long start = strtoull(argv[2], 0, 10);
    unsigned long long end = strtoull(argv[3], 0, 10);

    double R[SIZE][SIZE], py[SIZE];      /* R[x][y] = P(X=x, Y=y) */
    double px = 1.0 / SIZE;
    for (int x = 0; x < SIZE; x++)
        for (int y = 0; y < SIZE; y++) {
            int d = __builtin_popcount(x ^ y);
            R[x][y] = px * pow(alpha, d) * pow(1 - alpha, N - d);
        }
    for (int y = 0; y < SIZE; y++) {
        double s = 0;
        for (int x = 0; x < SIZE; x++) s += R[x][y];
        py[y] = s;
    }

    unsigned int mask = (unsigned int)(start ^ (start >> 1));
    double p1[SIZE];
    memset(p1, 0, sizeof p1);
    double pf1 = 0;
    for (int x = 0; x < SIZE; x++)
        if ((mask >> x) & 1) {
            for (int y = 0; y < SIZE; y++) p1[y] += R[x][y];
            pf1 += px;
        }

    double best = -1, second = -2;
    long long nbest = 0, nsecond = 0;
    unsigned int exb[MAXEX], exs[MAXEX];
    int neb = 0, nes = 0;

    for (unsigned long long i = start;;) {
        double mi = 0;
        if (pf1 > 1e-12 && pf1 < 1 - 1e-12) {
            double q0 = 1 - pf1;
            for (int y = 0; y < SIZE; y++) {
                double q = p1[y], r = py[y] - q;
                if (q > 0) mi += q * log2(q / (pf1 * py[y]));
                if (r > 0) mi += r * log2(r / (q0 * py[y]));
            }
        }
        if (mi > best + TOL) {
            second = best; nsecond = nbest; memcpy(exs, exb, sizeof exs); nes = neb;
            best = mi; nbest = 1; exb[0] = mask; neb = 1;
        } else if (mi > best - TOL) {
            nbest++;
            if (neb < MAXEX) exb[neb++] = mask;
        } else if (mi > second + TOL) {
            second = mi; nsecond = 1; exs[0] = mask; nes = 1;
        } else if (mi > second - TOL) {
            nsecond++;
            if (nes < MAXEX) exs[nes++] = mask;
        }
        if (++i >= end) break;
        int b = __builtin_ctzll(i);
        double sign = ((mask >> b) & 1) ? -1.0 : 1.0;
        mask ^= 1u << b;
        const double *row = R[b];
        for (int y = 0; y < SIZE; y++) p1[y] += sign * row[y];
        pf1 += sign * px;
    }

    printf("best %.12f count %lld masks", best, nbest);
    for (int k = 0; k < neb; k++) printf(" %08x", exb[k]);
    printf("\nsecond %.12f count %lld masks", second, nsecond);
    for (int k = 0; k < nes; k++) printf(" %08x", exs[k]);
    printf("\n");
    return 0;
}
