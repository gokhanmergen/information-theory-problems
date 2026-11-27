# Reviewer check (2026-11-27, Claim 4 and the fable-baseline correction): direct CF optimiser
# (Nelder-Mead over pi and |U| = 4 test channels, 30 restarts, seed 0) and the DF-corner tangent slope.
# Run: python3 cf_direct.py [R0,R0,...]   (default R0 list = the run in cf_direct.out)
# Runtime: about 2-4 min. Needs numpy, scipy.
"""Independent numerical CF rate for the primitive BSC relay (p1 dest, p2 relay):
direct optimization of the min-form over (pi, T: Yr -> U, |U| = 4) with SLSQP and random
restarts (no Lagrange dual, no theta grid).  Then the upper concave envelope of
max(DF, CF) in R0, evaluated at R0 = 0.4 (fable baseline correction check).
Floating point; numerical evidence only."""
import sys
import numpy as np
from scipy.optimize import minimize

p1, p2 = 0.2, 0.1
W1 = np.array([[1 - p1, p1], [p1, 1 - p1]])   # [x, y]
W2 = np.array([[1 - p2, p2], [p2, 1 - p2]])   # [x, yr]


def H(P):
    P = P.ravel()
    P = P[P > 1e-300]
    return float(-(P * np.log2(P)).sum())


def softmax_rows(z, k):
    z = z.reshape(2, k)
    z = z - z.max(1, keepdims=True)
    e = np.exp(z)
    return e / e.sum(1, keepdims=True)


def terms(pi, T):
    px = np.array([1 - pi, pi])
    J = px[:, None, None, None] * W1[:, :, None, None] * W2[:, None, :, None] * T[None, None, :, :]
    # axes x, y, yr, u
    Ixy = H(J.sum((1, 2, 3))) + H(J.sum((0, 2, 3))) - H(J.sum((2, 3)))
    Ix_yu = H(J.sum((1, 2, 3))) + H(J.sum((0, 2))) - H(J.sum(2))       # I(X; Y,U)
    # I(U; Yr | X, Y) = H(X,Y,U) + H(X,Y,Yr) - H(X,Y,Yr,U) - H(X,Y)
    Iu_yr_xy = H(J.sum(2)) + H(J.sum(3)) - H(J) - H(J.sum((2, 3)))
    return Ix_yu, Ixy, Iu_yr_xy


def cf(R0, k=4, restarts=30, seed=0):
    rng = np.random.default_rng(seed)
    best = -1.0
    bestx = None

    def unpack(x):
        pi = 0.5 / (1 + np.exp(-x[0])) + 1e-9   # pi in (0, 0.5]; symmetric
        return pi, softmax_rows(x[1:], k)

    def negobj(x):
        pi, T = unpack(x)
        b1, Ixy, c = terms(pi, T)
        return -min(b1, Ixy + R0 - c)

    for r in range(restarts):
        x0 = rng.normal(0, 3, 1 + 2 * k)
        res = minimize(negobj, x0, method='Nelder-Mead',
                       options={'maxiter': 20000, 'xatol': 1e-10, 'fatol': 1e-13})
        res = minimize(negobj, res.x, method='Nelder-Mead',
                       options={'maxiter': 20000, 'xatol': 1e-11, 'fatol': 1e-14})
        if -res.fun > best:
            best, bestx = -res.fun, res.x
    pi, T = unpack(bestx)
    return best, pi, T


if __name__ == '__main__':
    from math import log2
    h = lambda q: -(q * log2(q) + (1 - q) * log2(1 - q))
    D = h(p1) - h(p2)
    top = 1 - h(p2)
    Rs = [float(r) for r in sys.argv[1].split(',')] if len(sys.argv) > 1 else \
        [0.3, 0.4, 0.5, 0.6, 0.7, 0.75, 0.8, 0.81, 0.82, 0.83]
    pts = []
    for R in Rs:
        v, pi, T = cf(R)
        df = min(1 - h(p1) + R, top)
        pts.append((R, v))
        print(f'R0={R:.3f} CF={v:.7f} pi={pi:.4f} DF={df:.6f}  slope from DF corner={(v - top) / (R - D):.6f}',
              flush=True)
    s = max((v - top) / (R - D) for R, v in pts if R > D)
    print('best slope from DF corner', s, ' envelope at 0.4 >=', top + s * (0.4 - D))
