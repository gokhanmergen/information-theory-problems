#!/usr/bin/env python3
"""Non-rigorous numerical cross-checks for
attempts/gaussian-relay-channel-capacity/2026-11-26-claude-opus-5-5-time-sharing-catalog-error.md

Nothing labelled [proved] in the attempt depends on this file (see certify_catalog_error.py).
Sections (all seeds fixed; total runtime about 2-4 minutes on one core):

  N1  Direct numerical optimisation of the Lean hybrid rate (grid + Nelder-Mead over
      alpha, gamma, theta, c with beta = 1 - alpha - gamma) at random parameters, compared
      with the closed-form CF rate.  Cross-checks Lemma 1 (equality when g12^2 <= g13^2)
      and shows the hybrid can be strictly larger than CF when g12^2 > g13^2.
  N2  Unit gains, P1 = P2 = P: threshold below which bursting improves CF (hence, by
      Lemma 1, the Lean Statement fails).
  N3  Low-SNR slopes (t -> 0, powers (t, kappa t), unit gains) of
        - the concave envelope of R_CF (grid dual: a lower estimate of the envelope slope),
        - single-burst CF,
        - single-burst EMZ Example 1 linear relaying.
  N5  BPSK (hard-decision and soft) versions of EMZ Example 1: slopes on the diagonal.
  N4  Low-SNR slope of Gaussian CF with a *coded* time-sharing variable Q
      (rate constraints averaged over Q), unit gains, P1 = P2 = t; multistart Nelder-Mead.

Usage: python3 numerics.py [N1|N2|N3|N4|N5 ...]   (default: all)
"""
import sys
import numpy as np
from scipy.optimize import minimize

LN2 = np.log(2.0)


def C(s):
    return 0.5 * np.log1p(s) / LN2


# ----------------------------------------------------------------------------- N1
def hyb_val(x, g12, g13, g23, P1, P2):
    """max R1+R2 for fixed (alpha, gamma, theta, c), beta = 1-alpha-gamma; -1 if infeasible."""
    al, ga, th, c = x
    be = max(0.0, 1 - al - ga)
    A = C(g12**2 * be * P1 / (1 + g12**2 * ga * P1))
    B1 = C(g13**2 * ga * P1 + g12**2 * ga * P1 * c / (1 + c))
    B2 = C(g13**2 * ga * P1 + g23**2 * (1 - th) * P2) - C(c)
    S = C(g13**2 * P1 + g23**2 * P2 + 2 * abs(g13 * g23) * np.sqrt(max(al * th, 0) * P1 * P2)) - C(c)
    B = min(B1, B2)
    if B < 0 or S < 0:
        return -1.0
    return min(A + B, S)


def best_c(al, ga, th, *p):
    g12, g13, g23, P1, P2 = p
    cmax = g13**2 * P1 + g23**2 * P2 + 2 * abs(g13 * g23) * np.sqrt(P1 * P2)  # S < 0 beyond
    cs = np.concatenate([[0.0], np.geomspace(1e-9, cmax, 300)])
    v = [hyb_val((al, ga, th, c), *p) for c in cs]
    i = int(np.argmax(v))
    lo, hi = cs[max(i - 1, 0)], cs[min(i + 1, len(cs) - 1)]
    for _ in range(60):
        m1, m2 = lo + (hi - lo) / 3, hi - (hi - lo) / 3
        if hyb_val((al, ga, th, m1), *p) < hyb_val((al, ga, th, m2), *p):
            lo = m1
        else:
            hi = m2
    c = (lo + hi) / 2
    return max(v[i], hyb_val((al, ga, th, c), *p)), c


def R_hyb_numeric(g12, g13, g23, P1, P2, n=8):
    p = (g12, g13, g23, P1, P2)
    best = (-1.0, None)
    grid = np.linspace(0, 1, n)
    for al in grid:
        for ga in grid:
            if al + ga > 1 + 1e-12:
                continue
            for th in grid:
                v, c = best_c(al, ga, th, *p)
                if v > best[0]:
                    best = (v, (al, ga, th, c))

    def f(x):
        if x[0] + x[1] <= 1 and min(x) >= 0 and x[2] <= 1:
            return -hyb_val(tuple(x), *p)
        return 1.0

    r = minimize(f, np.array(best[1]), method="Nelder-Mead",
                 options={"xatol": 1e-12, "fatol": 1e-16, "maxiter": 20000})
    if -r.fun > best[0]:
        best = (-r.fun, tuple(r.x))
    return best


def R_CF(g12, g13, g23, P1, P2):
    a, b, d = g13**2 * P1, g12**2 * P1, g23**2 * P2
    return C(a + b * d / (1 + a + b + d))


def bursty_CF(g12, g13, g23, P1, P2):
    lams = np.geomspace(1e-4, 1, 20001)
    v = lams * R_CF(g12, g13, g23, P1 / lams, P2 / lams)
    i = int(np.argmax(v))
    return v[i], lams[i]


def N1():
    print("N1: numeric hybrid optimum vs closed-form CF (Lemma 1 cross-check)")
    rng = np.random.default_rng(1)
    for k in range(12):
        g13 = 1.0
        g12 = rng.uniform(0.2, 1.0) if k < 8 else rng.uniform(1.2, 3.0)
        g23 = rng.uniform(0.3, 5)
        P1, P2 = 10 ** rng.uniform(-3, 1), 10 ** rng.uniform(-3, 1)
        h = R_hyb_numeric(g12, g13, g23, P1, P2)[0]
        c = R_CF(g12, g13, g23, P1, P2)
        print(f"  g12={g12:.3f} g23={g23:.3f} P1={P1:.4g} P2={P2:.4g}  hyb_num={h:.10f} CF={c:.10f} diff={h - c:+.2e}")
    h = R_hyb_numeric(1, 1, 3, 0.05, 0.05)
    b = bursty_CF(1, 1, 3, 0.05, 0.05)
    print(f"  coordinator point (1,1,3,.05,.05): hyb_num={h[0]:.8f} at {np.round(h[1], 6)}, best burst={b[0]:.8f} at lambda={b[1]:.4f}")


def N2():
    print("N2: unit gains, P1=P2=P: largest P where some burst lambda<1 beats CF")
    lo, hi = 0.01, 1.0
    for _ in range(50):
        mid = (lo + hi) / 2
        lams = np.linspace(0.5, 1 - 1e-9, 200001)
        v = lams * R_CF(1, 1, 1, mid / lams, mid / lams)
        if v.max() > R_CF(1, 1, 1, mid, mid) * (1 + 1e-13):
            lo = mid
        else:
            hi = mid
    print(f"  threshold P* ~ {lo:.5f}")
    for P in [1e-3, 1e-2, 0.05, 0.1]:
        b = bursty_CF(1, 1, 1, P, P)
        print(f"  P={P}: CF={R_CF(1, 1, 1, P, P):.8g} best burst={b[0]:.8g} (lambda={b[1]:.4f}) ratio={b[0] / R_CF(1, 1, 1, P, P):.5f}")


# ----------------------------------------------------------------------------- N3
def rL_unit(x1, x2, nb=400):
    """EMZ Example 1 rate (unit gains), maximised over beta on a grid."""
    be = np.linspace(1e-4, 1, nb)
    d2 = 2 * x2 / (2 * be * x1 + 1)
    snr = 2 * be * x1 * (1 + (np.sqrt((1 - be) / be) + np.sqrt(d2)) ** 2 / (1 + d2))
    return np.max(0.5 * C(snr))


def N3():
    print("N3: low-SNR slopes along (t, kappa t), unit gains  [direct = %.5f, cutset = %.5f]" % (1 / (2 * LN2), 1 / LN2))
    X1 = np.geomspace(1e-4, 1e2, 250)
    X2 = np.geomspace(1e-4, 1e4, 300)
    G1, G2 = np.meshgrid(X1, X2, indexing="ij")
    FCF = R_CF(1, 1, 1, G1, G2)
    FL = np.vectorize(rL_unit)(G1, G2)

    def dual_slope(Fv, kappa):  # grid-restricted dual => lower estimate of the true envelope slope
        best = np.inf
        for mu1 in np.linspace(0, 3, 3001):
            mu2 = max(0.0, np.max((Fv - mu1 * G1) / G2))
            best = min(best, mu1 + kappa * mu2)
        return best

    def one_burst(Fv, kappa):
        return np.max(Fv / np.maximum(G1, G2 / kappa))

    for kappa in [0.1, 1, 10, 100, 1000]:
        print(f"  kappa={kappa:>6}: CF-envelope(grid dual)={dual_slope(FCF, kappa):.4f}  "
              f"CF 1-burst={one_burst(FCF, kappa):.4f}  ExampleI 1-burst={one_burst(FL, kappa):.4f}")


# ----------------------------------------------------------------------------- N4
def N4(trials=(40, 40, 30)):
    print("N4: low-SNR slope of CF with coded time-sharing Q (P1=P2=t->0, unit gains)")
    rng = np.random.default_rng(0)

    def B1(a, b, c):
        return C(a + a * c / (1 + c))

    def B2(a, b, c):
        return C(a + b) - C(c)

    for k, T in zip([1, 2, 3], trials):
        best, bz = 0.0, None
        for _ in range(T):
            x0 = np.concatenate([rng.uniform(-4, 1, k), rng.uniform(-4, 1, k),
                                 rng.uniform(-4, 1, k), rng.uniform(-1, 2, k)])

            def obj(z):
                zz = np.clip(z, -30, 30)
                a, b, c, w = (np.exp(zz[:k]), np.exp(zz[k:2 * k]),
                              np.exp(zz[2 * k:3 * k]), np.exp(zz[3 * k:]))
                w = w / max(np.dot(w, a), np.dot(w, b))
                return -min(np.dot(w, B1(a, b, c)), np.dot(w, B2(a, b, c)))

            r = minimize(obj, x0, method="Nelder-Mead",
                         options={"maxiter": 8000, "xatol": 1e-9, "fatol": 1e-12})
            if -r.fun > best:
                best, bz = -r.fun, r.x
        zz = np.clip(bz, -30, 30)
        print(f"  |Q|={k}: slope ~ {best:.5f}  a={np.exp(zz[:k])} b={np.exp(zz[k:2 * k])} c={np.exp(zz[2 * k:3 * k])}")


# ----------------------------------------------------------------------------- N5
def N5():
    """EMZ Example 1 with BPSK inputs, unit gains, diagonal P1 = P2 = x:
    hard decisions (BSC) vs unquantised binary-input AWGN (Gauss-Hermite)."""
    from scipy.stats import norm
    print("N5: BPSK versions of EMZ Example 1 (diagonal, unit gains), slopes rate/x")

    def h2(p):
        return -(p * np.log2(p) + (1 - p) * np.log2(1 - p))

    def snrL(x1, x2, be):
        d2 = 2 * x2 / (2 * be * x1 + 1)
        c = np.sqrt((1 - be) / be) + np.sqrt(d2)
        return 2 * be * x1 * (1 + c * c / (1 + d2))

    X = np.geomspace(1e-3, 50, 1500)[:, None]
    B = np.linspace(0.01, 1, 300)[None, :]
    S = snrL(X, X, B)
    r = 0.5 * (1 - h2(norm.sf(np.sqrt(S))))
    i = np.unravel_index(np.argmax(r / X), r.shape)
    print(f"  hard-decision: sup slope ~ {(r / X)[i]:.4f} at x={X[i[0], 0]:.4f}, beta={B[0, i[1]]:.3f}")
    d = r - R_CF(1, 1, 1, X, X)
    print(f"  hard-decision: max over grid of (rate - R_CF) = {d.max():+.3e}  (negative: never beats CF)")
    gx, gw = np.polynomial.hermite_e.hermegauss(200)
    gw = gw / gw.sum()

    def biawgn(s):
        y = gx + np.sqrt(s)
        return 1 - np.sum(gw * np.logaddexp(0, -2 * np.sqrt(s) * y)) / LN2

    best = (0,)
    for x in np.geomspace(1e-2, 3, 300):
        for be in np.linspace(0.2, 1, 81):
            v = 0.5 * biawgn(snrL(x, x, be)) / x
            if v > best[0]:
                best = (v, x, be)
    print(f"  soft BPSK: sup slope ~ {best[0]:.4f} at x={best[1]:.4f}, beta={best[2]:.3f}  (Gaussian input: 0.8849)")


if __name__ == "__main__":
    which = sys.argv[1:] or ["N1", "N2", "N3", "N4", "N5"]
    for w in which:
        globals()[w]()
