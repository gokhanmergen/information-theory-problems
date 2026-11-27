# Reviewer check (2026-11-27, non-rigorous): differential evolution on the raw Lean hybrid formula vs
# R_CF (Claim 2), the Claim-4 tangency point, the Claim-6 float grid and EMZ Fig. 3 comparisons.
# Run: python3 numeric_checks.py
# Runtime: about 15 s. Needs numpy, scipy.
"""Independent (non-rigorous) numerical checks by the reviewer."""
import numpy as np
from scipy.optimize import differential_evolution, brentq, minimize_scalar

LN2 = np.log(2.0)
m = 1 / (2 * LN2)


def C(s):
    return 0.5 * np.log1p(s) / LN2


def lean_hybrid_obj(x, g12, g13, g23, P1, P2):
    """Lean gaussianHybridDFCFRate inner value for (alpha, gamma, theta, c), beta = 1-alpha-gamma
    (beta only enters the R1 bound, monotonically).  Returns -inf if infeasible."""
    al, ga, th, lc = x
    c = np.expm1(lc)  # c = e^lc - 1 >= 0 range
    if al + ga > 1:
        return -np.inf
    be = 1 - al - ga
    A = C(g12**2 * be * P1 / (1 + g12**2 * ga * P1))
    B1 = C(g13**2 * ga * P1 + (g12**2 * ga * P1) * c / (1 + c))
    B2 = C(g13**2 * ga * P1 + g23**2 * (1 - th) * P2) - C(c)
    S = C(g13**2 * P1 + g23**2 * P2 + 2 * abs(g13 * g23) * np.sqrt(al * th * P1 * P2)) - C(c)
    B = min(B1, B2)
    if B < 0 or S < 0:
        return -np.inf
    return min(A + B, S)


def lean_hybrid(g12, g13, g23, P1, P2, seed=0):
    f = lambda x: -lean_hybrid_obj(x, g12, g13, g23, P1, P2) if np.isfinite(lean_hybrid_obj(x, g12, g13, g23, P1, P2)) else 1.0
    r = differential_evolution(f, [(0, 1), (0, 1), (0, 1), (0, 6)], seed=seed, tol=1e-14,
                               maxiter=3000, popsize=40, polish=True)
    return -r.fun, r.x


def RCF(g12, g13, g23, P1, P2):
    a, b, d = g13**2 * P1, g12**2 * P1, g23**2 * P2
    return C(a + b * d / (1 + a + b + d))


print("== Lemma 1 cross-check (differential evolution on the Lean formula) ==")
rng = np.random.default_rng(12345)
pts = [(1, 1, 1, 1e-3, 1e-1), (1, 1, 1, 0.1, 0.1), (1, 1, 3, 0.05, 0.05)]
for k in range(6):
    g13 = rng.uniform(0.5, 2)
    g12 = g13 * rng.uniform(0.05, 1.0)
    pts.append((g12, g13, rng.uniform(0.2, 4), 10 ** rng.uniform(-3, 1.5), 10 ** rng.uniform(-3, 1.5)))
for k in range(3):
    g13 = rng.uniform(0.5, 2)
    g12 = g13 * rng.uniform(1.3, 3.0)
    pts.append((g12, g13, rng.uniform(0.2, 4), 10 ** rng.uniform(-2, 1), 10 ** rng.uniform(-2, 1)))
for p in pts:
    h, x = lean_hybrid(*p)
    cf = RCF(*p)
    tag = "g12^2<=g13^2" if p[0] ** 2 <= p[1] ** 2 else "g12^2>g13^2"
    print("  %s g=(%.3f,%.3f,%.3f) P=(%.4g,%.4g): hyb_DE=%.12f  R_CF=%.12f  diff=%+.2e  x=%s"
          % (tag, p[0], p[1], p[2], p[3], p[4], h, cf, h - cf, np.round(x, 4)))

print("== EMZ Example 1: log-det (EMZ eq.14) vs MRC formula ==")


def rL_logdet(P1, P2, beta, a=1.0, b=1.0, N=1.0):
    d = np.sqrt(2 * P2 / (2 * a**2 * beta * P1 + N))
    Sig = 2 * P1 * np.array([[beta, np.sqrt(beta * (1 - beta))], [np.sqrt(beta * (1 - beta)), 1 - beta]])
    D = np.array([[0, 0], [d, 0]])
    I = np.eye(2)
    T = I + a * b * D
    num = np.linalg.det(T @ Sig @ T.T + N * (I + b**2 * D @ D.T))
    den = np.linalg.det(N * (I + b**2 * D @ D.T))
    relay_power = np.trace(a**2 * D @ Sig @ D.T + N * D @ D.T)
    return np.log2(num / den) / 4, relay_power


def rL_mrc(P1, P2, beta):
    d2 = 2 * P2 / (2 * beta * P1 + 1)
    c = np.sqrt((1 - beta) / beta) + np.sqrt(d2)
    return np.log2(1 + 2 * beta * P1 * (1 + c * c / (1 + d2))) / 4


v1, rp = rL_logdet(0.1, 0.1, 2 / 3)
print("  logdet r_L = %.13f (relay energy per 2 symbols %.6f = 2*P2?)  MRC r_L = %.13f" % (v1, rp, rL_mrc(0.1, 0.1, 2 / 3)))
rb = minimize_scalar(lambda be: -rL_mrc(0.1, 0.1, be), bounds=(1e-6, 1), method="bounded")
print("  best beta at (0.1,0.1): beta=%.4f r_L=%.10f ; R_hyb=%.10f" % (rb.x, -rb.fun, RCF(1, 1, 1, 0.1, 0.1)))

print("== 2D grid check of supporting line R_CF(x1,x1,x2) <= m x1 + x2/20 (unit gains) ==")
x1 = np.concatenate([np.geomspace(1e-8, 1e4, 1500)])
x2 = np.concatenate([[0.0], np.geomspace(1e-8, 1e5, 1500)])
X1, X2 = np.meshgrid(x1, x2)
G = C(X1 + X1 * X2 / (1 + 2 * X1 + X2)) - m * X1 - X2 / 20
i = np.unravel_index(np.argmax(G), G.shape)
print("  max of R_CF - m x1 - x2/20 on grid = %.3e at x1=%.3g x2=%.3g" % (G[i], X1[i], X2[i]))
# relative slack away from origin
mask = (X1 > 0.01)
print("  max over x1>0.01: %.3e" % G[mask].max())

print("== Claim 4 threshold: unit gains P1=P2=P; largest P where bursting improves R_CF ==")


def f(t):
    return RCF(1, 1, 1, t, t)


def burst_gain(P):
    lams = np.geomspace(1e-5, 1, 200001)
    v = lams * f(P / lams)
    return v.max() - f(P)


Ps = np.geomspace(1e-4, 1, 400)
g = np.array([burst_gain(P) for P in Ps])
pos = Ps[g > 1e-15]
print("  bursting helps for P up to ~ %.4f (grid)" % pos.max())
# tangent-from-origin: f(P) = P f'(P)
h = 1e-7
tang = lambda P: f(P) - P * (f(P + h) - f(P - h)) / (2 * h)
print("  tangency point P* = %.5f" % brentq(tang, 0.02, 0.5))
print("  relative gain at P=1e-3: %.4f" % (burst_gain(1e-3) / f(1e-3)))

print("== EMZ Fig. 3 setting: a=1, sqrt(gamma) b = 2 (Lean: g12=g13=1, g23^2 P2 = 4 P) ==")
for P in [0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.4, 0.5]:
    P2 = 4 * P  # g23 = 1, P2 = gamma P with gamma b^2 = 4
    rl = max(rL_mrc(P, P2, be) for be in np.linspace(0.01, 1, 991))
    cf = RCF(1, 1, 1, P, P2)
    lams = np.linspace(1e-3, 1, 2000)
    bcf = max(l * RCF(1, 1, 1, P / l, P2 / l) for l in lams)
    print("  P=%.2f  linear(Ex1)=%.5f  CF eq7=%.5f  bursty CF eq8=%.5f  direct/DF=%.5f  Ex1>eq7:%s Ex1>eq8:%s"
          % (P, rl, cf, bcf, C(P), rl > cf, rl > bcf))
