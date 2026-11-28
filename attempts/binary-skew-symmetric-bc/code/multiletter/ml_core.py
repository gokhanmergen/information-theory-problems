#!/usr/bin/env python3
"""
Core routines: one-letter vs two-letter Marton *dual* functionals for binary-input BCs.

Attempt file: attempts/binary-skew-symmetric-bc/2026-11-27-claude-opus-5-5-binary-input-multiletter.md

Everything is in BITS.  A binary-input BC is given by its two marginals
    TY : 2 x kY row-stochastic,   TZ : 2 x kZ row-stochastic
(the Marton sum rate depends only on the marginals).

Dual functional (HLL arXiv:2608.19869 eq. (4); Gohari-Liu-Nair ISIT 2025):
    G_T(P_UVX; alpha, a) = -alpha H(Y) - (1-alpha) H(Z) + I(U;Y) + I(V;Z) - I(U;V) + E a(X)
                         = (1-alpha) H(Y) + alpha H(Z) - H(U,Y) - H(V,Z) + H(U,V) + E a(X)
    B_T(alpha, a) = max_{P_UVX} G_T.
Cardinality/determinism reduction (Anantharam-Gohari-Nair, IEEE TIT 2019; used by HLL):
    it suffices to take X = f(U,V) deterministic and |U| + |V| <= |X| + 1.
  * one letter, |X| = 2:  |U|+|V| <= 3, so (U = X, V const) or (U const, V = X):
        B_1(alpha,a) = max_q max{ psi_Y(q), psi_Z(q) },
        psi_Y(q) = -alpha H_Y(q) - (1-alpha) H_Z(q) + I_Y(q) + a.q   (and Y <-> Z for psi_Z).
    This is a 1-D problem, solved here to ~1e-13 by grid + golden section.
  * two letters, T^{(x)2} with |X| = 4:  (|U|,|V|) in {(1,4),(4,1),(2,3),(3,2)} (smaller
    alphabets are faces of these), X = f(U,V) for a map f : [nu] x [nv] -> {0,1}^2.
        B_2(alpha,a) = B_{T(x)T}(alpha, a(+)a),  (a(+)a)(x1,x2) = a(x1) + a(x2).
    Searched by batched multistart mirror ascent over all maps (up to relabelling of U and V
    symbols), followed by L-BFGS polish of the best candidates.  This is a NUMERICAL search:
    it gives lower bounds on B_2 (each value is attained by an explicit distribution) but no
    upper bound.

Always B_2 >= 2 B_1 (product of one-letter maximisers).  B_2 > 2 B_1 ("dual non-additivity",
Gohari-Liu-Nair Conjecture 1 failing) is NECESSARY for a fixed-input two-letter Marton gain;
see Claim 2 of the attempt file.
"""
import itertools
import numpy as np
from scipy.optimize import minimize

LOG2 = np.log(2.0)


def ent(p, axis=-1):
    q = np.where(p > 0, p, 1.0)
    return -(p * np.log2(q)).sum(axis=axis)


def hb(x):
    return ent(np.stack([x, 1 - x], -1))


# ----------------------------------------------------------------------------------------
# channels
# ----------------------------------------------------------------------------------------
def bssc():
    TY = np.array([[1.0, 0.0], [0.5, 0.5]])     # 0 -> 0, 1 -> Unif
    TZ = np.array([[0.5, 0.5], [0.0, 1.0]])     # 0 -> Unif, 1 -> 1
    return TY, TZ


def product2(T):
    """Two-letter product of a 2 x k channel; input index x = 2*x1 + x2."""
    return np.kron(T, T)


# ----------------------------------------------------------------------------------------
# one-letter dual (exact up to 1-D optimisation tolerance)
# ----------------------------------------------------------------------------------------
def psi_branches(q, TY, TZ, alpha, a):
    q = np.asarray(q, dtype=float)
    P = np.stack([1 - q, q], -1)
    HY, HZ = ent(P @ TY), ent(P @ TZ)
    HYx, HZx = ent(TY), ent(TZ)
    IY = HY - P @ HYx
    IZ = HZ - P @ HZx
    base = -alpha * HY - (1 - alpha) * HZ + P @ np.asarray(a, float)
    return base + IY, base + IZ


def B1(TY, TZ, alpha, a, n=200001, return_arg=False):
    best = (-np.inf, None, None)
    for br in (0, 1):
        f = lambda q: psi_branches(q, TY, TZ, alpha, a)[br]
        qs = np.linspace(0, 1, n)
        v = f(qs)
        i = int(np.argmax(v))
        lo, hi = qs[max(i - 1, 0)], qs[min(i + 1, n - 1)]
        g = (np.sqrt(5) - 1) / 2
        x1, x2 = hi - g * (hi - lo), lo + g * (hi - lo)
        f1, f2 = f(x1), f(x2)
        for _ in range(200):
            if f1 < f2:
                lo, x1, f1 = x1, x2, f2
                x2 = lo + g * (hi - lo)
                f2 = f(x2)
            else:
                hi, x2, f2 = x2, x1, f1
                x1 = hi - g * (hi - lo)
                f1 = f(x1)
        cand = [(v[i], qs[i]), (f1, x1), (f2, x2), (f(0.0), 0.0), (f(1.0), 1.0)]
        val, arg = max(cand, key=lambda t: t[0])
        if val > best[0]:
            best = (float(val), float(arg), "UX" if br == 0 else "VX")
    return best if return_arg else best[0]


# ----------------------------------------------------------------------------------------
# two-letter dual: batched evaluation for maps f : [nu] x [nv] -> [4]
# ----------------------------------------------------------------------------------------
def canonical_maps(nu, nv, nx=4):
    """All maps up to permutations of U-labels and V-labels; drop maps not using all U or V
    'meaningfully' is NOT done (degenerate maps are harmless, they reproduce faces)."""
    seen, out = set(), []
    perms_u = list(itertools.permutations(range(nu)))
    perms_v = list(itertools.permutations(range(nv)))
    for f in itertools.product(range(nx), repeat=nu * nv):
        F = np.array(f).reshape(nu, nv)
        key = min(tuple(F[np.ix_(pu, pv)].ravel()) for pu in perms_u for pv in perms_v)
        if key in seen:
            continue
        seen.add(key)
        out.append(np.array(key).reshape(nu, nv))
    return out


class TwoLetterDual:
    """G for X = f(U,V) on the product channel, batched over (map, start)."""

    def __init__(self, TY, TZ, alpha, a, maps):
        self.TY2, self.TZ2 = product2(TY), product2(TZ)
        a = np.asarray(a, float)
        self.a2 = np.array([a[x1] + a[x2] for x1 in (0, 1) for x2 in (0, 1)])
        self.alpha = alpha
        self.maps = np.array(maps)                       # (M, nu, nv)
        M, nu, nv = self.maps.shape
        self.nu, self.nv = nu, nv
        # per-map channel rows: (M, nu, nv, kY2) etc.
        self.WY = self.TY2[self.maps]
        self.WZ = self.TZ2[self.maps]
        self.A = self.a2[self.maps]                      # (M, nu, nv)

    def value_grad(self, P):
        """P: (M, B, nu, nv) -> G (M,B), dG/dP (M,B,nu,nv) (up to an additive constant)."""
        al = self.alpha
        WY, WZ = self.WY[:, None], self.WZ[:, None]      # (M,1,nu,nv,k)
        PUY = np.einsum('mbuv,mbuvy->mbuy', P, np.broadcast_to(WY, P.shape + (WY.shape[-1],)))
        PVZ = np.einsum('mbuv,mbuvz->mbvz', P, np.broadcast_to(WZ, P.shape + (WZ.shape[-1],)))
        pY, pZ = PUY.sum(2), PVZ.sum(2)
        G = ((1 - al) * ent(pY) + al * ent(pZ) - ent(PUY.reshape(*PUY.shape[:2], -1))
             - ent(PVZ.reshape(*PVZ.shape[:2], -1)) + ent(P.reshape(*P.shape[:2], -1))
             + (P * self.A[:, None]).sum((2, 3)))
        lg = lambda x: np.log2(np.where(x > 0, x, 1e-300))
        lpY, lpZ, lPUY, lPVZ = lg(pY), lg(pZ), lg(PUY), lg(PVZ)
        g = (-(1 - al) * np.einsum('mbuvy,mby->mbuv', np.broadcast_to(WY, P.shape + (WY.shape[-1],)), lpY)
             - al * np.einsum('mbuvz,mbz->mbuv', np.broadcast_to(WZ, P.shape + (WZ.shape[-1],)), lpZ)
             + np.einsum('mbuvy,mbuy->mbuv', np.broadcast_to(WY, P.shape + (WY.shape[-1],)), lPUY)
             + np.einsum('mbuvz,mbvz->mbuv', np.broadcast_to(WZ, P.shape + (WZ.shape[-1],)), lPVZ)
             - lg(P) + self.A[:, None])
        return G, g

    def single(self, m, p):
        P = np.asarray(p, float).reshape(1, 1, self.nu, self.nv)
        sub = TwoLetterDual.__new__(TwoLetterDual)
        sub.__dict__ = dict(self.__dict__)
        sub.WY, sub.WZ, sub.A = self.WY[m:m + 1], self.WZ[m:m + 1], self.A[m:m + 1]
        return sub.value_grad(P)[0][0, 0]


def mirror_ascent(D, B, iters, rng, eta=0.5, conc=None):
    """Exponentiated-gradient ascent on the simplex, batched over all maps of D."""
    M, nu, nv = D.maps.shape
    n = nu * nv
    if conc is None:
        conc = rng.choice([0.2, 0.5, 1.0, 3.0], size=(M, B, 1))
    P = rng.gamma(np.broadcast_to(conc, (M, B, n)))
    P = (P / P.sum(-1, keepdims=True)).reshape(M, B, nu, nv)
    P = np.maximum(P, 1e-12)
    P /= P.sum((2, 3), keepdims=True)
    for it in range(iters):
        G, g = D.value_grad(P)
        g = g - (P * g).sum((2, 3), keepdims=True)
        step = eta / (1.0 + 0.002 * it)
        P = P * np.exp(np.clip(step * g, -30, 30))
        P = np.maximum(P, 1e-300)
        P /= P.sum((2, 3), keepdims=True)
    G, _ = D.value_grad(P)
    return G, P


def polish(D, m, p0):
    """L-BFGS in softmax coordinates for one map; returns (value, P)."""
    th0 = np.log(np.maximum(np.asarray(p0, float).ravel(), 1e-14))

    def obj(th):
        e = np.exp(th - th.max())
        P = e / e.sum()
        sub = TwoLetterDual.__new__(TwoLetterDual)
        sub.__dict__ = dict(D.__dict__)
        sub.WY, sub.WZ, sub.A = D.WY[m:m + 1], D.WZ[m:m + 1], D.A[m:m + 1]
        G, g = sub.value_grad(P.reshape(1, 1, D.nu, D.nv))
        g = g.ravel()
        gt = P * (g - P @ g)
        return -G[0, 0], -gt
    r = minimize(obj, th0, jac=True, method='L-BFGS-B',
                 options={'maxiter': 5000, 'ftol': 1e-16, 'gtol': 1e-13})
    e = np.exp(r.x - r.x.max())
    return -r.fun, e / e.sum()


def full_x_branches(TY, TZ, alpha, a, rng, starts=200):
    """(U const, V = X) and (U = X, V const) on the 4-ary product input."""
    TY2, TZ2 = product2(TY), product2(TZ)
    a = np.asarray(a, float)
    a2 = np.array([a[x1] + a[x2] for x1 in (0, 1) for x2 in (0, 1)])
    HY2x, HZ2x = ent(TY2), ent(TZ2)
    out = {}
    for name, (Tm, Hm) in (("U=X", (TY2, HY2x)), ("V=X", (TZ2, HZ2x))):
        def f(th):
            e = np.exp(th - th.max())
            p = e / e.sum()
            HY, HZ = ent(p @ TY2), ent(p @ TZ2)
            I = ent(p @ Tm) - p @ Hm
            return -(-alpha * HY - (1 - alpha) * HZ + I + p @ a2)
        best = -np.inf
        for s in range(starts):
            r = minimize(f, rng.normal(size=4) * 2, method='Nelder-Mead',
                         options={'xatol': 1e-12, 'fatol': 1e-15, 'maxiter': 4000})
            best = max(best, -r.fun)
        out[name] = best
    return out


def B2_search(TY, TZ, alpha, a, rng, maps23=None, maps32=None, B=48, iters=1500,
              npolish=6, verbose=False, branch_starts=30):
    """Numerical lower bound on B_2 = B_{T(x)T}(alpha, a(+)a); returns (value, info)."""
    if maps23 is None:
        maps23 = canonical_maps(2, 3)
    if maps32 is None:
        maps32 = canonical_maps(3, 2)
    best = (-np.inf, None)
    info = {}
    for tag, maps in (("23", maps23), ("32", maps32)):
        D = TwoLetterDual(TY, TZ, alpha, a, maps)
        G, P = mirror_ascent(D, B, iters, rng)
        flat = np.argsort(-G.ravel())
        done = 0
        tried = set()
        for idx in flat:
            m, b = divmod(int(idx), G.shape[1])
            if m in tried:
                continue
            tried.add(m)
            v, p = polish(D, m, P[m, b])
            v = max(v, G[m, b])
            if v > best[0]:
                best = (v, (tag, D.maps[m].tolist(), p.reshape(D.nu, D.nv).tolist()))
            done += 1
            if done >= npolish:
                break
        info[tag] = float(G.max())
    fb = full_x_branches(TY, TZ, alpha, a, rng, starts=branch_starts)
    info.update(fb)
    for k, v in fb.items():
        if v > best[0]:
            best = (v, (k, None, None))
    return best[0], best[1], info
