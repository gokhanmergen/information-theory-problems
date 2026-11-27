#!/usr/bin/env python3
"""
Floating-point (NON-rigorous) evaluator of the BSSC sum-rate envelope formulas, used for the
[heuristic] claims of
attempts/binary-skew-symmetric-bc/2026-11-26-claude-opus-5-5-certified-bounds.md
(parameter optimisation, grid-sensitivity of the published values, ternary auxiliary receivers).
Upper concave envelopes are computed with scipy's Qhull on a sin^2 grid (or a uniform grid);
a grid hull UNDER-estimates the true envelope, so these numbers are lower estimates of the
formulas.  Rigorous values come from bssc_certify.py.

Conventions as in bssc_certify.py: t = P(X=1), I_Y(t) = h(t/2) - t, I_Z(t) = h((1-t)/2) - (1-t),
binary auxiliary receiver (a0, a1) = (P(J=0|X=0), P(J=0|X=1)).

Usage:  python bssc_float_explore.py {values|grid|optJ|optGK|ternary}
"""
import sys
import numpy as np
from scipy.spatial import ConvexHull
from scipy.optimize import minimize, minimize_scalar


def h(p):
    p = np.clip(p, 0, 1)
    out = np.zeros_like(p, dtype=float)
    m = (p > 0) & (p < 1)
    q = p[m]
    out[m] = -(q * np.log2(q) + (1 - q) * np.log2(1 - q))
    return out


def hs(x):
    return float(h(np.array([x]))[0])


class Grid:
    def __init__(self, N, kind="sin2"):
        if kind == "sin2":
            th = np.linspace(0, np.pi / 2, N)
            t = np.sin(th) ** 2
            t[0], t[-1] = 0.0, 1.0
            t[(N - 1) // 2] = 0.5
        else:
            t = np.linspace(0, 1, N)
        self.t, self.mid = t, (N - 1) // 2
        self.IY = h(t / 2) - t
        self.IZ = h((1 - t) / 2) - (1 - t)

    def hull(self, f):
        t = self.t
        lo = f.min() - 10
        P = np.vstack([np.column_stack([t, f]), [[0, lo], [1, lo]]])
        H = ConvexHull(P)
        v = np.array(sorted([i for i in H.vertices if i < len(t)], key=lambda i: t[i]))
        return np.interp(t, t[v], f[v])

    def IJ(self, a0, a1):
        t = self.t
        return h((1 - t) * a0 + t * a1) - (1 - t) * hs(a0) - t * hs(a1)

    def eta_I(self, r0, r1):
        """I(X;G) for a G with arbitrary output alphabet, rows r0 (x=0), r1 (x=1)."""
        t = self.t

        def eta(q):
            q = np.clip(q, 0, 1)
            o = np.zeros_like(q)
            m = q > 0
            o[m] = -q[m] * np.log2(q[m])
            return o
        Hrow = lambda r: float(sum(-x * np.log2(x) for x in r if x > 0))
        HG = sum(eta((1 - t) * r0[j] + t * r1[j]) for j in range(len(r0)))
        return HG - (1 - t) * Hrow(r0) - t * Hrow(r1)

    def UV(self):
        F = 0.5 * self.IY + 0.5 * self.IZ + 0.5 * self.hull(self.IY - self.IZ) + 0.5 * self.hull(self.IZ - self.IY)
        return F[self.mid]

    def marton(self):
        F = 0.5 * self.IY + 0.5 * self.IZ + 0.5 * self.hull(np.abs(self.IY - self.IZ))
        return F[self.mid]

    def J(self, a0, a1, sig=1.0, gam=0.5, Jfun=None):
        J = self.IJ(a0, a1) if Jfun is None else Jfun
        A = self.hull(self.hull(sig * J - self.IY) + sig * gam * (self.IY - J))
        B = self.hull(self.hull(sig * J - self.IZ) + sig * (1 - gam) * (self.IZ - J))
        F = (1 - sig * gam) * self.IY + (1 - sig * (1 - gam)) * self.IZ + A + B
        return F.max()   # max over t (valid for a fixed J)

    def GK(self, G, K):
        IY, IZ, hull = self.IY, self.IZ, self.hull
        A = hull(0.5 * (IY - G) + hull(G - IY))
        B = hull(0.5 * (IZ - K) + hull(K - IZ))
        F = 0.5 * IY + 0.5 * IZ + A + B + 0.5 * hull(G - K) + 0.5 * hull(K - G)
        return F.max()

    def GKbin(self, g0, g1):
        """G = (g0, g1) paired with Y, K = skew mirror (1-g1, 1-g0)."""
        return self.GK(self.IJ(g0, g1), self.IJ(1 - g1, 1 - g0))


GENG_ALPHA = 0.189986556858845
GLN_K_AS_Y = (0.173670782688446, 0.793595839081043)   # GLN's T_K, paired with our Y


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "values"
    if mode == "values":
        g = Grid(200001)
        print("UV  (18): %.12f" % g.UV())
        print("Marton (17, with C restored): %.12f" % g.marton())
        print("J at Geng's BSC: %.12f" % g.J(1 - GENG_ALPHA, GENG_ALPHA))
        print("GK at GLN's (G,K): %.12f" % g.GKbin(*GLN_K_AS_Y))
    elif mode == "grid":
        for N in [101, 201, 501, 1001, 2001, 10001, 100001]:
            g = Grid(N, "uniform")
            print(N, "J %.15f" % g.J(1 - GENG_ALPHA, GENG_ALPHA), "GK %.15f" % g.GKbin(*GLN_K_AS_Y))
    elif mode == "optJ":
        g = Grid(40001)
        r = minimize_scalar(lambda a: g.J(1 - a, a), bracket=(0.185, 0.19, 0.195), tol=1e-10)
        print("BSC opt alpha=%.12f  J=%.15f" % (r.x, r.fun), flush=True)
        obj = lambda z: g.J(z[0], z[1], 1.0, z[2]) if (0 < z[0] < 1 and 0 < z[1] < 1 and 0 <= z[2] <= 1) else 1.0
        rr = minimize(obj, [1 - r.x, r.x, 0.5], method='Nelder-Mead',
                      options={'xatol': 1e-8, 'fatol': 1e-13, 'maxiter': 600})
        print("general binary J and gamma:", rr.x, "%.15f" % rr.fun)
    elif mode == "optGK":
        g = Grid(20001)
        obj = lambda z: g.GKbin(*z) if (0 < z[0] < 1 and 0 < z[1] < 1) else 1.0
        rr = minimize(obj, list(GLN_K_AS_Y), method='Nelder-Mead',
                      options={'xatol': 1e-7, 'fatol': 1e-13, 'maxiter': 250})
        print("GK skew-symmetric opt:", repr(rr.x), "%.15f" % rr.fun)
        print("refined (N=200001): %.15f" % Grid(200001).GKbin(*rr.x))
    elif mode == "ternary":
        g = Grid(10001)
        sm = lambda z: np.exp(z - z.max()) / np.exp(z - z.max()).sum()
        obj = lambda z: g.GK(g.eta_I(sm(z[:3]), sm(z[3:])), g.eta_I(sm(z[3:]), sm(z[:3])))
        G0 = (0.17311456, 0.79310944)
        print("binary reference: %.12f" % g.GKbin(*G0))
        rng = np.random.default_rng(1)
        for trial in range(4):
            r0 = np.array([G0[0], 1 - G0[0], 1e-3])
            r1 = np.array([G0[1], 1 - G0[1], 1e-3])
            z0 = np.concatenate([np.log(r0 / r0.sum()), np.log(r1 / r1.sum())])
            z0 = z0 + rng.normal(size=6) * (0.0 if trial == 0 else 0.5)
            r = minimize(obj, z0, method='Nelder-Mead', options={'maxiter': 300, 'xatol': 1e-7, 'fatol': 1e-12})
            print("ternary trial", trial, "%.12f" % r.fun, np.round(sm(r.x[:3]), 6), np.round(sm(r.x[3:]), 6))
