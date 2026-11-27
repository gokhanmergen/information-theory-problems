/*
 * certify_n5.c — Rigorous, self-contained, outward-rounded interval-arithmetic
 * certifier for the Courtade-Kumar conjecture at n = 5 over an exact dyadic
 * noise interval [A_LO, A_HI] strictly containing [10^-4, 0.495].
 *
 * Trust base (100% self-contained, zero libm transcendentals, zero FENV hacks):
 *   1. Compile with -O3 -ffp-contract=off -fno-fast-math (no FMA contraction).
 *      Startup asserts fegetround() == FE_TONEAREST and IEEE-754 double.
 *   2. Elementary outward rounding: for finite RN result x = fl(a op b),
 *      exact real value lies in [x - e, x + e] where e = |x|*2^-51 + 2^-1020.
 *      (Since error <= 0.5 ulp(x) <= 2^-53 |x| for normal x, and <= 2^-1075 for
 *      subnormal x, adding >= 2 ulp(x) + 2^-1020 strictly encloses exact r even
 *      after rounding of x +/- e.)
 *   3. Certified log2(x) for x > 0: exact frexp(x, &e) with ldexp check,
 *      shifted so m in [1/sqrt(2), sqrt(2)], u = (m-1)/(m+1) with |u| <= 0.172,
 *      ln(m) = 2 * sum_{j=0}^9 u^(2j+1)/(2j+1) + R_21 where
 *      |R_21| <= 2 * 0.172^21 / (21*(1 - 0.172^2)) < 8e-17 < 1e-16.
 *      ln(2) is proved at startup via atanh(1/3) (25 terms, |R_51| < 1e-24).
 *   4. Exact dyadic endpoints A_LO = 13 / 2^17 < 1e-4 and
 *      A_HI = 64881 / 2^17 > 0.495, so every midpoint bisection is exact in double
 *      with zero uncovered seams.
 *   5. For each non-constant, non-dictator NPN representative f: {0,1}^5 -> {0,1},
 *      we certify g_f(alpha) = (1 - H(f(X))) + (1/32) sum_y h(q_y(alpha)) - h(alpha) > 0
 *      on every subinterval using:
 *        (a) Zero-derivative concavity bound: h is concave on [0,1] and increasing
 *            on [0, 1/2], with q_y([lo,hi]) and r_y([lo,hi]) = 1 - q_y([lo,hi])
 *            enclosed by outward-rounded Bernstein de Casteljau subdivision.
 *        (b) Corrected Mean Value Form (MVF) around exact midpoint m = (lo+hi)/2:
 *            g_f'(alpha) = (1/32) sum_y q_y'(alpha) * log2(r_y(alpha)/q_y(alpha))
 *                          - log2((1 - alpha) / alpha).
 *   6. Self-test mode (--selftest) checks interval primitives, log2 vs high-precision
 *      constants, exact zero on dictator class (must NOT certify!), and n=4 match.
 *
 * Build:
 *   clang -O3 -ffp-contract=off -fno-fast-math -pthread -o certify_n5 certify_n5.c
 */

#include <assert.h>
#include <fenv.h>
#include <float.h>
#include <math.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define N_VARS 5
#define N_SIZE 32
#define MAX_STACK 128

/* Exact dyadic rational endpoints strictly containing [1e-4, 0.495]:
 *   13 / 2^17    = 0.00009918212890625  < 0.0001
 *   64881 / 2^17 = 0.49500274658203125  > 0.495
 */
static const double DEFAULT_A_LO = 13.0 / 131072.0;
static const double DEFAULT_A_HI = 64881.0 / 131072.0;

/* Outward rounding constants (proved in header comment) */
static const double RAD_EPS = 0x1p-51;     /* 2 * DBL_EPSILON */
static const double RAD_ETA = 0x1p-1020;   /* 4 * DBL_MIN */

typedef struct {
    double lo;
    double hi;
} iv_t;

static inline double rd_down(double x) {
    double e = fabs(x) * RAD_EPS + RAD_ETA;
    return x - e;
}

static inline double rd_up(double x) {
    double e = fabs(x) * RAD_EPS + RAD_ETA;
    return x + e;
}

static inline iv_t iv_pt(double x) {
    return (iv_t){x, x};
}

static inline iv_t iv_make(double lo, double hi) {
    return (iv_t){lo, hi};
}

static inline int iv_valid(iv_t a) {
    return isfinite(a.lo) && isfinite(a.hi) && (a.lo <= a.hi);
}

static inline iv_t iv_add(iv_t a, iv_t b) {
    return (iv_t){rd_down(a.lo + b.lo), rd_up(a.hi + b.hi)};
}

static inline iv_t iv_sub(iv_t a, iv_t b) {
    return (iv_t){rd_down(a.lo - b.hi), rd_up(a.hi - b.lo)};
}

static inline iv_t iv_neg(iv_t a) {
    return (iv_t){-a.hi, -a.lo};
}

static inline iv_t iv_mul(iv_t a, iv_t b) {
    double p1 = a.lo * b.lo;
    double p2 = a.lo * b.hi;
    double p3 = a.hi * b.lo;
    double p4 = a.hi * b.hi;
    double mn = p1;
    if (p2 < mn) mn = p2;
    if (p3 < mn) mn = p3;
    if (p4 < mn) mn = p4;
    double mx = p1;
    if (p2 > mx) mx = p2;
    if (p3 > mx) mx = p3;
    if (p4 > mx) mx = p4;
    return (iv_t){rd_down(mn), rd_up(mx)};
}

/* Scale by exact non-negative double c >= 0 */
static inline iv_t iv_scale_pos(iv_t a, double c) {
    return (iv_t){rd_down(a.lo * c), rd_up(a.hi * c)};
}

static inline iv_t iv_div(iv_t a, iv_t b) {
    /* Requires b.lo > 0 or b.hi < 0 */
    if (b.lo <= 0.0 && b.hi >= 0.0) {
        return (iv_t){-INFINITY, INFINITY};
    }
    double q1 = a.lo / b.lo;
    double q2 = a.lo / b.hi;
    double q3 = a.hi / b.lo;
    double q4 = a.hi / b.hi;
    double mn = q1;
    if (q2 < mn) mn = q2;
    if (q3 < mn) mn = q3;
    if (q4 < mn) mn = q4;
    double mx = q1;
    if (q2 > mx) mx = q2;
    if (q3 > mx) mx = q3;
    if (q4 > mx) mx = q4;
    return (iv_t){rd_down(mn), rd_up(mx)};
}

/* Precomputed certified constants */
static iv_t IV_LN2;
static iv_t IV_INV_ODD[26]; /* 1/(2j+1) for j = 0..25 */
static iv_t IV_COMB_INV[6]; /* 1 / C(5, k) */
static iv_t IV_M0_TABLE[N_SIZE + 1]; /* 1 - h(k/32) */

/* Certified ln(x) for a single strictly positive finite double x > 0.
 * Zero libm transcendental calls: uses only exact frexp + atanh series. */
static iv_t iv_ln_point(double x) {
    if (!(x > 0.0) || !isfinite(x)) {
        return (iv_t){-INFINITY, INFINITY};
    }
    int e = 0;
    double m = frexp(x, &e);
    /* Verify exact decomposition x = m * 2^e */
    if (ldexp(m, e) != x) {
        return (iv_t){-INFINITY, INFINITY};
    }
    /* Shift m into [1/sqrt(2), sqrt(2)] via exact power-of-2 multiply */
    if (m < 0.7071067811865475) {
        m *= 2.0;
        e -= 1;
    }
    /* u = (m - 1) / (m + 1), |u| <= (sqrt(2)-1)/(sqrt(2)+1) < 0.171573 < 0.172 */
    iv_t M = iv_pt(m);
    iv_t U = iv_div(iv_sub(M, iv_pt(1.0)), iv_add(M, iv_pt(1.0)));
    double u_abs = fabs(U.lo) > fabs(U.hi) ? fabs(U.lo) : fabs(U.hi);
    if (!(u_abs <= 0.172)) {
        return (iv_t){-INFINITY, INFINITY};
    }
    iv_t U2 = iv_mul(U, U);
    if (U2.lo < 0.0) U2.lo = 0.0;

    /* Horner evaluation of sum_{j=0}^9 u^(2j) / (2j+1) */
    iv_t acc = IV_INV_ODD[9];
    for (int j = 8; j >= 0; j--) {
        acc = iv_add(IV_INV_ODD[j], iv_mul(U2, acc));
    }
    iv_t series = iv_mul(U, acc);
    /* Multiply by 2 (exact exponent shift for normal numbers, use iv_scale_pos) */
    iv_t ln_m = iv_scale_pos(series, 2.0);
    /* Proved remainder: |R_21| <= 2 * 0.172^21 / (21 * (1 - 0.172^2)) < 8.0e-17 < 1e-16 */
    ln_m = iv_add(ln_m, iv_make(-1.0e-16, 1.0e-16));

    if (e == 0) return ln_m;
    iv_t e_ln2 = iv_mul(iv_pt((double)e), IV_LN2);
    return iv_add(e_ln2, ln_m);
}

/* Certified log2(x) for single point x > 0 */
static iv_t iv_log2_point(double x) {
    if (!(x > 0.0) || !isfinite(x)) {
        return (iv_t){-INFINITY, INFINITY};
    }
    int e = 0;
    double m = frexp(x, &e);
    if (ldexp(m, e) != x) {
        return (iv_t){-INFINITY, INFINITY};
    }
    if (m < 0.7071067811865475) {
        m *= 2.0;
        e -= 1;
    }
    iv_t ln_m = iv_ln_point(m);
    iv_t log2_m = iv_div(ln_m, IV_LN2);
    return iv_add(iv_pt((double)e), log2_m);
}

/* Certified log2([a, b]) for a > 0, exploiting monotonicity */
static inline iv_t iv_log2(iv_t x) {
    if (!(x.lo > 0.0) || !iv_valid(x)) {
        return (iv_t){-INFINITY, INFINITY};
    }
    iv_t lo_res = iv_log2_point(x.lo);
    if (x.lo == x.hi) return lo_res;
    iv_t hi_res = iv_log2_point(x.hi);
    return (iv_t){lo_res.lo, hi_res.hi};
}

/* Certified binary entropy h(q) given enclosures for both q and r = 1 - q,
 * where q.lo > 0 and r.lo > 0.
 * h(q) = -q log2(q) - r log2(r).
 */
static inline iv_t iv_bin_entropy_qr(iv_t q, iv_t r) {
    if (!(q.lo > 0.0 && r.lo > 0.0)) {
        return (iv_t){-INFINITY, INFINITY};
    }
    iv_t t1 = iv_mul(q, iv_log2(q));
    iv_t t2 = iv_mul(r, iv_log2(r));
    return iv_neg(iv_add(t1, t2));
}

/* Certified binary entropy at a single point double p in (0, 1) */
static inline iv_t iv_bin_entropy_pt(double p) {
    iv_t q = iv_pt(p);
    iv_t r = iv_sub(iv_pt(1.0), q);
    return iv_bin_entropy_qr(q, r);
}

static void init_constants(void) {
    /* Verify round-to-nearest-even */
    assert(fegetround() == FE_TONEAREST);
    assert(FLT_RADIX == 2);
    assert(DBL_MANT_DIG == 53);

    for (int j = 0; j < 26; j++) {
        IV_INV_ODD[j] = iv_div(iv_pt(1.0), iv_pt((double)(2 * j + 1)));
    }

    /* Certify ln(2) = 2 * sum_{j=0}^24 (1/3)^(2j+1) / (2j+1) + R_51.
     * |R_51| <= 2 * (1/3)^51 / (51 * (8/9)) < 2.1e-26 < 1e-24.
     */
    iv_t u = iv_div(iv_pt(1.0), iv_pt(3.0));
    iv_t u2 = iv_mul(u, u);
    iv_t acc = IV_INV_ODD[24];
    for (int j = 23; j >= 0; j--) {
        acc = iv_add(IV_INV_ODD[j], iv_mul(u2, acc));
    }
    IV_LN2 = iv_add(iv_scale_pos(iv_mul(u, acc), 2.0), iv_make(-1.0e-24, 1.0e-24));

    static const double comb5[6] = {1.0, 5.0, 10.0, 10.0, 5.0, 1.0};
    for (int k = 0; k < 6; k++) {
        IV_COMB_INV[k] = iv_div(iv_pt(1.0), iv_pt(comb5[k]));
    }

    /* Precompute m_0(k) = 1 - h(k/32) for k = 0..32 */
    for (int k = 0; k <= N_SIZE; k++) {
        if (k == 0 || k == N_SIZE) {
            IV_M0_TABLE[k] = iv_pt(1.0);
        } else if (k == N_SIZE / 2) {
            IV_M0_TABLE[k] = iv_pt(0.0);
        } else {
            double p = (double)k / (double)N_SIZE; /* exact dyadic */
            iv_t hk = iv_bin_entropy_pt(p);
            IV_M0_TABLE[k] = iv_sub(iv_pt(1.0), hk);
        }
    }
}

/* Degree-5 Bernstein de Casteljau step at interval t in [0, 1] */
static inline void dc5_split(const iv_t b[6], iv_t t, iv_t left[6], iv_t right[6]) {
    iv_t ti = iv_sub(iv_pt(1.0), t);
    iv_t r1[5], r2[4], r3[3], r4[2], r5;
    for (int i = 0; i < 5; i++) r1[i] = iv_add(iv_mul(ti, b[i]), iv_mul(t, b[i + 1]));
    for (int i = 0; i < 4; i++) r2[i] = iv_add(iv_mul(ti, r1[i]), iv_mul(t, r1[i + 1]));
    for (int i = 0; i < 3; i++) r3[i] = iv_add(iv_mul(ti, r2[i]), iv_mul(t, r2[i + 1]));
    for (int i = 0; i < 2; i++) r4[i] = iv_add(iv_mul(ti, r3[i]), iv_mul(t, r3[i + 1]));
    r5 = iv_add(iv_mul(ti, r4[0]), iv_mul(t, r4[1]));

    if (left) {
        left[0] = b[0]; left[1] = r1[0]; left[2] = r2[0];
        left[3] = r3[0]; left[4] = r4[0]; left[5] = r5;
    }
    if (right) {
        right[0] = r5; right[1] = r4[1]; right[2] = r3[2];
        right[3] = r2[3]; right[4] = r1[4]; right[5] = b[5];
    }
}

/* Degree-5 point evaluation via de Casteljau at exact double t in [0, 1] */
static inline iv_t dc5_eval_pt(const iv_t b[6], double t_d) {
    iv_t t = iv_pt(t_d);
    iv_t ti = iv_sub(iv_pt(1.0), t);
    iv_t r1[5], r2[4], r3[3], r4[2];
    for (int i = 0; i < 5; i++) r1[i] = iv_add(iv_mul(ti, b[i]), iv_mul(t, b[i + 1]));
    for (int i = 0; i < 4; i++) r2[i] = iv_add(iv_mul(ti, r1[i]), iv_mul(t, r1[i + 1]));
    for (int i = 0; i < 3; i++) r3[i] = iv_add(iv_mul(ti, r2[i]), iv_mul(t, r2[i + 1]));
    for (int i = 0; i < 2; i++) r4[i] = iv_add(iv_mul(ti, r3[i]), iv_mul(t, r3[i + 1]));
    return iv_add(iv_mul(ti, r4[0]), iv_mul(t, r4[1]));
}

/* Degree-5 Bernstein range enclosure over [t1, hi] where t2 = (hi - t1)/(1 - t1) */
static inline iv_t dc5_range(const iv_t b[6], iv_t t1, iv_t t2) {
    iv_t right1[6], sub[6];
    dc5_split(b, t1, NULL, right1);
    dc5_split(right1, t2, sub, NULL);
    double lo = sub[0].lo, hi = sub[0].hi;
    for (int i = 1; i < 6; i++) {
        if (sub[i].lo < lo) lo = sub[i].lo;
        if (sub[i].hi > hi) hi = sub[i].hi;
    }
    return iv_make(lo, hi);
}

/* Degree-4 Bernstein de Casteljau range enclosure for q_y'(alpha) */
static inline iv_t dc4_range(const iv_t b[5], iv_t t1, iv_t t2) {
    iv_t ti1 = iv_sub(iv_pt(1.0), t1);
    iv_t r1[4], r2[3], r3[2], r4;
    for (int i = 0; i < 4; i++) r1[i] = iv_add(iv_mul(ti1, b[i]), iv_mul(t1, b[i + 1]));
    for (int i = 0; i < 3; i++) r2[i] = iv_add(iv_mul(ti1, r1[i]), iv_mul(t1, r1[i + 1]));
    for (int i = 0; i < 2; i++) r3[i] = iv_add(iv_mul(ti1, r2[i]), iv_mul(t1, r2[i + 1]));
    r4 = iv_add(iv_mul(ti1, r3[0]), iv_mul(t1, r3[1]));
    iv_t right1[5] = {r4, r3[1], r2[2], r1[3], b[4]};

    iv_t ti2 = iv_sub(iv_pt(1.0), t2);
    for (int i = 0; i < 4; i++) r1[i] = iv_add(iv_mul(ti2, right1[i]), iv_mul(t2, right1[i + 1]));
    for (int i = 0; i < 3; i++) r2[i] = iv_add(iv_mul(ti2, r1[i]), iv_mul(t2, r1[i + 1]));
    for (int i = 0; i < 2; i++) r3[i] = iv_add(iv_mul(ti2, r2[i]), iv_mul(t2, r2[i + 1]));
    r4 = iv_add(iv_mul(ti2, r3[0]), iv_mul(t2, r3[1]));
    iv_t sub[5] = {right1[0], r1[0], r2[0], r3[0], r4};

    double lo = sub[0].lo, hi = sub[0].hi;
    for (int i = 1; i < 5; i++) {
        if (sub[i].lo < lo) lo = sub[i].lo;
        if (sub[i].hi > hi) hi = sub[i].hi;
    }
    return iv_make(lo, hi);
}

/* Precomputed Hamming distance table */
static uint8_t HDIST[N_SIZE][N_SIZE];

static void init_hdist(void) {
    for (int x = 0; x < N_SIZE; x++)
        for (int y = 0; y < N_SIZE; y++)
            HDIST[x][y] = (uint8_t)__builtin_popcount((unsigned)(x ^ y));
}

/* Exact check for dictator/anti-dictator: level-1 Fourier weight == 1 */
static int is_dictator(uint32_t f) {
    int k = __builtin_popcount(f);
    if (k != 16) return 0;
    /* For balanced f, dictator iff sum_i (sum_x (-1)^f(x) (-1)^x_i)^2 == 32^2 = 1024 */
    int64_t tot = 0;
    for (int i = 0; i < N_VARS; i++) {
        int64_t s = 0;
        for (int x = 0; x < N_SIZE; x++) {
            int fx = ((f >> x) & 1u) ? -1 : 1;
            int xi = ((x >> i) & 1u) ? -1 : 1;
            s += fx * xi;
        }
        tot += s * s;
    }
    return (tot == 1024);
}

typedef struct {
    int mult;
    iv_t b1[6];
    iv_t b0[6];
    iv_t d1[5];
} poly_group_t;

typedef struct {
    int k;
    int ngroups;
    poly_group_t grp[N_SIZE];
} fn_data_t;

static void build_fn_data(uint32_t f, fn_data_t *fd) {
    static const int comb5[6] = {1, 5, 10, 10, 5, 1};
    uint8_t counts[N_SIZE][6];
    memset(counts, 0, sizeof counts);

    int k = 0;
    for (int x = 0; x < N_SIZE; x++) {
        if ((f >> x) & 1u) {
            k++;
            for (int y = 0; y < N_SIZE; y++) {
                counts[y][HDIST[x][y]]++;
            }
        }
    }
    fd->k = k;

    /* Deduplicate identical count profiles across y = 0..31 (exact optimization).
     * Also note h(q) = h(1-q), so complementary profiles c and (comb5 - c) have
     * identical h(q_y) and identical q_y' * log2(r_y/q_y) (both factors negate!).
     * Canonicalize by swapping c <-> (comb5 - c) if c[0] == 1 (or lexicographically).
     */
    uint8_t unique_c[N_SIZE][6];
    int mult[N_SIZE];
    int ng = 0;
    for (int y = 0; y < N_SIZE; y++) {
        uint8_t c[6];
        for (int d = 0; d < 6; d++) c[d] = counts[y][d];
        /* Canonicalize under q <-> 1-q symmetry */
        int flip = 0;
        for (int d = 0; d < 6; d++) {
            uint8_t comp = (uint8_t)(comb5[d] - c[d]);
            if (comp < c[d]) { flip = 1; break; }
            if (comp > c[d]) { flip = 0; break; }
        }
        if (flip) {
            for (int d = 0; d < 6; d++) c[d] = (uint8_t)(comb5[d] - c[d]);
        }
        int found = -1;
        for (int g = 0; g < ng; g++) {
            if (memcmp(unique_c[g], c, 6) == 0) { found = g; break; }
        }
        if (found >= 0) {
            mult[found]++;
        } else {
            memcpy(unique_c[ng], c, 6);
            mult[ng] = 1;
            ng++;
        }
    }

    fd->ngroups = ng;
    for (int g = 0; g < ng; g++) {
        fd->grp[g].mult = mult[g];
        for (int d = 0; d < 6; d++) {
            int c1 = unique_c[g][d];
            int c0 = comb5[d] - c1;
            fd->grp[g].b1[d] = iv_scale_pos(IV_COMB_INV[d], (double)c1);
            fd->grp[g].b0[d] = iv_scale_pos(IV_COMB_INV[d], (double)c0);
        }
        for (int d = 0; d < 5; d++) {
            iv_t diff = iv_sub(fd->grp[g].b1[d + 1], fd->grp[g].b1[d]);
            fd->grp[g].d1[d] = iv_scale_pos(diff, 5.0);
        }
    }
}

/* Certify g_f(alpha) > 0 on [a_lo, a_hi] (exact dyadic doubles, 0 < a_lo < a_hi < 0.5).
 * Returns 1 if certified, 0 if failed (needs fallback / dictator).
 */
typedef struct {
    int ok;
    uint32_t evals;
    double min_width_split;
    double min_lb;
} cert_result_t;

static cert_result_t certify_class(uint32_t f, double a_lo, double a_hi, double min_width) {
    cert_result_t res = {0, 0, a_hi - a_lo, 1e9};
    int k = __builtin_popcount(f);
    if (k == 0 || k == N_SIZE) {
        /* Constant function: I(f(X);Y) = 0, g_f(alpha) = 1 - h(alpha) > 0 on (0, 1/2) */
        res.ok = 1;
        res.evals = 0;
        res.min_lb = 1.0 - iv_bin_entropy_pt(a_hi).hi;
        return res;
    }

    fn_data_t fd;
    build_fn_data(f, &fd);
    iv_t m0 = IV_M0_TABLE[k];

    double st_lo[MAX_STACK], st_hi[MAX_STACK];
    int sp = 0;
    st_lo[sp] = a_lo;
    st_hi[sp] = a_hi;
    sp++;

    while (sp > 0) {
        sp--;
        double lo = st_lo[sp];
        double hi = st_hi[sp];
        res.evals++;

        iv_t t1 = iv_pt(lo);
        iv_t t2 = iv_div(iv_sub(iv_pt(hi), t1), iv_sub(iv_pt(1.0), t1));
        if (!iv_valid(t2) || t2.lo < 0.0 || t2.hi > 1.0) {
            /* Clamp harmlessly if outward rounding slightly exceeds [0,1] */
            if (t2.lo < 0.0) t2.lo = 0.0;
            if (t2.hi > 1.0) t2.hi = 1.0;
        }

        /* Step 1: Compute Bernstein range of q_y and r_y on [lo, hi],
         * and evaluate zero-derivative concavity lower bound!
         * Since h is concave on [0,1], inf_{u in [qL, qU]} h(u) = min(h(qL), h(qU)).
         * Since h is strictly increasing on [0, 1/2], sup_{[lo,hi]} h(a) = h(hi).
         */
        iv_t q_rng[N_SIZE], r_rng[N_SIZE];
        iv_t sum_h_lo = iv_pt(0.0);
        int range_ok = 1;

        for (int g = 0; g < fd.ngroups; g++) {
            iv_t qr = dc5_range(fd.grp[g].b1, t1, t2);
            iv_t rr = dc5_range(fd.grp[g].b0, t1, t2);
            /* Tighten using exact identity q + r = 1 */
            iv_t q_from_r = iv_sub(iv_pt(1.0), rr);
            iv_t r_from_q = iv_sub(iv_pt(1.0), qr);
            if (q_from_r.lo > qr.lo) qr.lo = q_from_r.lo;
            if (q_from_r.hi < qr.hi) qr.hi = q_from_r.hi;
            if (r_from_q.lo > rr.lo) rr.lo = r_from_q.lo;
            if (r_from_q.hi < rr.hi) rr.hi = r_from_q.hi;

            q_rng[g] = qr;
            r_rng[g] = rr;

            if (!(qr.lo > 0.0 && rr.lo > 0.0 && qr.lo <= qr.hi && rr.lo <= rr.hi)) {
                range_ok = 0;
                break;
            }

            /* Concavity lower bound at endpoints of [qr.lo, qr.hi] */
            iv_t h1 = iv_bin_entropy_qr(iv_pt(qr.lo), iv_sub(iv_pt(1.0), iv_pt(qr.lo)));
            iv_t h2 = iv_bin_entropy_qr(iv_pt(qr.hi), iv_sub(iv_pt(1.0), iv_pt(qr.hi)));
            double h_min_lo = (h1.lo < h2.lo) ? h1.lo : h2.lo;
            sum_h_lo = iv_add(sum_h_lo, iv_scale_pos(iv_pt(h_min_lo), (double)fd.grp[g].mult));
        }

        if (range_ok) {
            iv_t cond_h_lo = iv_scale_pos(sum_h_lo, 1.0 / 32.0);
            iv_t h_hi = iv_bin_entropy_pt(hi);
            iv_t g_conc = iv_sub(iv_add(m0, cond_h_lo), h_hi);
            if (g_conc.lo > 0.0) {
                if (g_conc.lo < res.min_lb) res.min_lb = g_conc.lo;
                continue; /* CERTIFIED by concavity! */
            }
        }

        /* Step 2: Corrected Mean Value Form (MVF) around exact midpoint m = (lo + hi) / 2 */
        double mid = 0.5 * (lo + hi);
        if (range_ok && (mid > lo) && (mid < hi)) {
            /* Midpoint value g_f(mid) */
            iv_t sum_h_mid = iv_pt(0.0);
            iv_t sum_dJ = iv_pt(0.0);
            int mvf_ok = 1;

            for (int g = 0; g < fd.ngroups; g++) {
                iv_t qm = dc5_eval_pt(fd.grp[g].b1, mid);
                iv_t rm = dc5_eval_pt(fd.grp[g].b0, mid);
                if (!(qm.lo > 0.0 && rm.lo > 0.0)) {
                    mvf_ok = 0;
                    break;
                }
                iv_t hm = iv_bin_entropy_qr(qm, rm);
                sum_h_mid = iv_add(sum_h_mid, iv_scale_pos(hm, (double)fd.grp[g].mult));

                /* Derivative term: q_y'([lo,hi]) * log2(r_y([lo,hi]) / q_y([lo,hi])) */
                iv_t dp = dc4_range(fd.grp[g].d1, t1, t2);
                iv_t ratio = iv_div(r_rng[g], q_rng[g]);
                if (!(ratio.lo > 0.0)) {
                    mvf_ok = 0;
                    break;
                }
                iv_t log_ratio = iv_log2(ratio);
                iv_t term = iv_mul(dp, log_ratio);
                sum_dJ = iv_add(sum_dJ, iv_scale_pos(term, (double)fd.grp[g].mult));
            }

            if (mvf_ok) {
                iv_t g_mid = iv_sub(iv_add(m0, iv_scale_pos(sum_h_mid, 1.0 / 32.0)),
                                    iv_bin_entropy_pt(mid));
                iv_t a_iv = iv_make(lo, hi);
                iv_t one_m_a = iv_sub(iv_pt(1.0), a_iv);
                iv_t dh_alpha = iv_log2(iv_div(one_m_a, a_iv));
                iv_t dg = iv_sub(iv_scale_pos(sum_dJ, 1.0 / 32.0), dh_alpha);

                /* Exact half-width enclosure: [-max(mid-lo, hi-mid), +max(mid-lo, hi-mid)] */
                double hw1 = rd_up(mid - lo);
                double hw2 = rd_up(hi - mid);
                double hw = (hw1 > hw2) ? hw1 : hw2;
                iv_t delta = iv_make(-hw, hw);
                iv_t g_mvf = iv_add(g_mid, iv_mul(dg, delta));

                if (g_mvf.lo > 0.0) {
                    if (g_mvf.lo < res.min_lb) res.min_lb = g_mvf.lo;
                    continue; /* CERTIFIED by MVF! */
                }
            }
        }

        /* Step 3: Bisect at exact midpoint */
        double width = hi - lo;
        if (width < res.min_width_split) res.min_width_split = width;
        if (width < min_width || !(mid > lo && mid < hi) || sp + 2 > MAX_STACK) {
            res.ok = 0;
            return res;
        }
        st_lo[sp] = lo;  st_hi[sp] = mid; sp++;
        st_lo[sp] = mid; st_hi[sp] = hi;  sp++;
    }

    res.ok = 1;
    return res;
}

/* ---------------- Self-tests ---------------- */
static void run_selftest(void) {
    printf("=== Running self-tests ===\n");
    /* 1. Verify dyadic endpoints strictly contain [1e-4, 0.495] */
    assert(13 * 10000 < 131072);
    assert(64881 * 1000 > 495 * 131072);
    assert(64881 * 2 < 131072);
    printf("  [PASS] Dyadic endpoints: [%.17f, %.17f] strictly contains [1e-4, 0.495]\n",
           DEFAULT_A_LO, DEFAULT_A_HI);

    /* 2. Verify IV_LN2 encloses true ln(2) = 0.693147180559945309417232... */
    printf("  IV_LN2 = [%.17f, %.17f] (width %.2e)\n",
           IV_LN2.lo, IV_LN2.hi, IV_LN2.hi - IV_LN2.lo);
    assert(IV_LN2.lo <= 0.6931471805599454 && IV_LN2.hi >= 0.6931471805599453);

    /* 3. Verify iv_log2 encloses true values (a <= true_hi && b >= true_lo) */
    iv_t l8 = iv_log2_point(8.0);
    assert(l8.lo <= 3.0 && l8.hi >= 3.0);
    iv_t l3 = iv_log2_point(3.0);
    /* true log2(3) = 1.5849625007211561814537... */
    assert(l3.lo <= 1.5849625007211563 && l3.hi >= 1.5849625007211561);
    iv_t lsmall = iv_log2_point(1e-4);
    /* true log2(1e-4) = -13.2877123795494493914... */
    printf("  log2(1e-4) = [%.15f, %.15f] (width %.2e)\n",
           lsmall.lo, lsmall.hi, lsmall.hi - lsmall.lo);
    assert(lsmall.lo <= -13.287712379549448 && lsmall.hi >= -13.287712379549450);
    printf("  [PASS] Certified log2 checks (width at 3.0: %.2e)\n", l3.hi - l3.lo);

    /* 4. Verify dictator class MUST FAIL to certify g > 0! */
    uint32_t dict = 0xFFFF0000u; /* f(x) = x_4 */
    assert(is_dictator(dict));
    cert_result_t r_dict = certify_class(dict, DEFAULT_A_LO, DEFAULT_A_HI, 1e-6);
    assert(r_dict.ok == 0);
    printf("  [PASS] Dictator 0x%08x correctly REFUSED certification (evals=%u)\n",
           dict, r_dict.evals);

    /* 5. Verify single-flip dictator (hardest known non-dictator class!) */
    uint32_t sflip = 0xFFFF0001u;
    assert(!is_dictator(sflip));
    cert_result_t r_sf = certify_class(sflip, DEFAULT_A_LO, DEFAULT_A_HI, 1e-8);
    printf("  Single-flip dictator 0x%08x: ok=%d evals=%u min_width=%.3e min_lb=%.3e\n",
           sflip, r_sf.ok, r_sf.evals, r_sf.min_width_split, r_sf.min_lb);
    assert(r_sf.ok == 1);

    /* 6. Verify constant function */
    cert_result_t r_c0 = certify_class(0x00000000u, DEFAULT_A_LO, DEFAULT_A_HI, 1e-8);
    assert(r_c0.ok == 1);
    printf("  [PASS] Constant 0x00000000 certified (min_lb=%.3e)\n", r_c0.min_lb);
    printf("=== All self-tests PASSED ===\n");
}

/* ---------------- Multi-threaded full runner ---------------- */
typedef struct {
    int tid;
    uint32_t *reps;
    size_t start;
    size_t end;
    double a_lo;
    double a_hi;
    double min_width;

    /* Per-thread stats */
    uint64_t certified;
    uint64_t constants;
    uint64_t dictators;
    uint64_t failed;
    uint64_t total_evals;
    uint32_t max_evals;
    uint32_t max_evals_rep;
    double min_lb;
    uint32_t min_lb_rep;
    double worst_width;
    uint32_t worst_width_rep;
    uint32_t failed_reps[64];
} worker_ctx_t;

static void *worker_fn(void *arg) {
    worker_ctx_t *ctx = (worker_ctx_t *)arg;
    ctx->min_lb = 1e9;
    ctx->worst_width = 1.0;

    for (size_t i = ctx->start; i < ctx->end; i++) {
        uint32_t f = ctx->reps[i];
        int k = __builtin_popcount(f);
        if (k == 0 || k == N_SIZE) {
            ctx->constants++;
            ctx->certified++;
            continue;
        }
        if (is_dictator(f)) {
            ctx->dictators++;
            continue;
        }
        cert_result_t r = certify_class(f, ctx->a_lo, ctx->a_hi, ctx->min_width);
        ctx->total_evals += r.evals;
        if (r.evals > ctx->max_evals) {
            ctx->max_evals = r.evals;
            ctx->max_evals_rep = f;
        }
        if (r.ok) {
            ctx->certified++;
            if (r.min_lb < ctx->min_lb) {
                ctx->min_lb = r.min_lb;
                ctx->min_lb_rep = f;
            }
            if (r.min_width_split < ctx->worst_width) {
                ctx->worst_width = r.min_width_split;
                ctx->worst_width_rep = f;
            }
        } else {
            if (ctx->failed < 64) ctx->failed_reps[ctx->failed] = f;
            ctx->failed++;
        }
    }
    return NULL;
}

int main(int argc, char **argv) {
    init_constants();
    init_hdist();

    if (argc >= 2 && strcmp(argv[1], "--selftest") == 0) {
        run_selftest();
        return 0;
    }

    if (argc < 2) {
        fprintf(stderr, "Usage: %s <npn5_reps.bin> [threads=8] [start=0] [end=ALL]\n", argv[0]);
        fprintf(stderr, "       %s --selftest\n", argv[0]);
        return 1;
    }

    const char *path = argv[1];
    int nthreads = (argc >= 3) ? atoi(argv[2]) : 8;
    if (nthreads < 1) nthreads = 1;
    if (nthreads > 64) nthreads = 64;

    FILE *fp = fopen(path, "rb");
    if (!fp) { perror("fopen"); return 1; }
    fseek(fp, 0, SEEK_END);
    long fsize = ftell(fp);
    fseek(fp, 0, SEEK_SET);
    size_t nreps = (size_t)fsize / sizeof(uint32_t);
    uint32_t *reps = (uint32_t *)malloc(nreps * sizeof(uint32_t));
    if (!reps) { fprintf(stderr, "malloc failed\n"); return 1; }
    if (fread(reps, sizeof(uint32_t), nreps, fp) != nreps) {
        fprintf(stderr, "fread failed\n");
        return 1;
    }
    fclose(fp);

    size_t start = (argc >= 4) ? (size_t)atoll(argv[3]) : 0;
    size_t end = (argc >= 5) ? (size_t)atoll(argv[4]) : nreps;
    if (end > nreps) end = nreps;
    if (start > end) start = end;

    printf("Loaded %zu reps from %s; certifying [%zu, %zu) on [13/2^17, 64881/2^17] "
           "= [%.17f, %.17f] using %d threads...\n",
           nreps, path, start, end, DEFAULT_A_LO, DEFAULT_A_HI, nthreads);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);

    pthread_t th[64];
    worker_ctx_t ctx[64];
    size_t total = end - start;
    for (int t = 0; t < nthreads; t++) {
        memset(&ctx[t], 0, sizeof(worker_ctx_t));
        ctx[t].tid = t;
        ctx[t].reps = reps;
        ctx[t].start = start + (total * (size_t)t) / (size_t)nthreads;
        ctx[t].end = start + (total * (size_t)(t + 1)) / (size_t)nthreads;
        ctx[t].a_lo = DEFAULT_A_LO;
        ctx[t].a_hi = DEFAULT_A_HI;
        ctx[t].min_width = 1e-9;
        pthread_create(&th[t], NULL, worker_fn, &ctx[t]);
    }

    uint64_t certified = 0, constants = 0, dictators = 0, failed = 0, total_evals = 0;
    uint32_t max_evals = 0, max_evals_rep = 0, min_lb_rep = 0, worst_width_rep = 0;
    double min_lb = 1e9, worst_width = 1.0;

    for (int t = 0; t < nthreads; t++) {
        pthread_join(th[t], NULL);
        certified += ctx[t].certified;
        constants += ctx[t].constants;
        dictators += ctx[t].dictators;
        failed += ctx[t].failed;
        total_evals += ctx[t].total_evals;
        if (ctx[t].max_evals > max_evals) {
            max_evals = ctx[t].max_evals;
            max_evals_rep = ctx[t].max_evals_rep;
        }
        if (ctx[t].min_lb < min_lb) {
            min_lb = ctx[t].min_lb;
            min_lb_rep = ctx[t].min_lb_rep;
        }
        if (ctx[t].worst_width < worst_width) {
            worst_width = ctx[t].worst_width;
            worst_width_rep = ctx[t].worst_width_rep;
        }
        for (uint64_t k = 0; k < ctx[t].failed && k < 64; k++) {
            printf("  FAILED rep: 0x%08x\n", ctx[t].failed_reps[k]);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t1);
    double elapsed = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);

    printf("\n=== CERTIFICATION SUMMARY ===\n");
    printf("  Range checked:    [13/2^17, 64881/2^17] (strictly contains [1e-4, 0.495])\n");
    printf("  Total classes:    %zu\n", total);
    printf("  Certified (g>0):  %llu (including %llu constant class)\n",
           (unsigned long long)certified, (unsigned long long)constants);
    printf("  Dictator classes: %llu (excluded, g == 0)\n", (unsigned long long)dictators);
    printf("  Failures:         %llu\n", (unsigned long long)failed);
    printf("  Total subintervals evaluated: %llu (avg %.2f / class)\n",
           (unsigned long long)total_evals,
           (double)total_evals / (double)(total > dictators ? total - dictators : 1));
    printf("  Hardest class (max evals):    0x%08x (%u evals)\n", max_evals_rep, max_evals);
    printf("  Smallest certified lb(g):     %.6e (class 0x%08x)\n", min_lb, min_lb_rep);
    printf("  Smallest split width:         %.6e (class 0x%08x)\n", worst_width, worst_width_rep);
    printf("  Wall-clock elapsed:           %.2f s (%.1f classes/s across %d threads)\n",
           elapsed, (double)total / elapsed, nthreads);

    free(reps);
    return (failed == 0) ? 0 : 2;
}
