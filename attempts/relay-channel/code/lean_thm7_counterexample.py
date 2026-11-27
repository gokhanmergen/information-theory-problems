#!/usr/bin/env python3
"""Counterexample to the frozen Lean statement InfoTheory.Problems.RelayChannel.Statement.

Channel ("noise-observing relay + binary adder"):
    X  = (X1, X2) in {0,1}^2         (source input, |X| = 4)
    Xr in {0,1}                        (relay input)
    Yr = Z,   Z ~ Bern(1/2)            (relay observes only the noise)
    Y  = (Y1, Y2),  Y1 = X1 xor Z,  Y2 = X2 + Xr in {0,1,2}

Facts checked here (exact rational/closed-form values, double precision):
  (A) The Lean functional `coverElGamalTheorem7Rate` (two constraints r1, r2,
      arbitrary joint P(u,x,xr), test channel Q(yh|u,xr,yr)) attains log2(3)
      with U trivial, X1 ~ Bern(1/2) independent, (X2,Xr) correlated as
      [[1/3,1/6],[1/6,1/3]], and Yh = Yr.  r1 = 1 + h(1/3), r2 = log2 3.
  (B) For independent binary X2, Xr:  max H(X2 + Xr) = 1.5 (binary erasure
      MAC sum capacity); grid check.  This is the single-letter constant in the
      converse C <= 1.5 (proof in the attempt file).
  (C) The faithful Cover-El Gamal Theorem 7 (Chong-Motani 2011 Lemma 2 form,
      three constraints, p(w)p(u|w)p(x|u)p(xr|w)p(v|u,xr,yr)) attains 1.5 with
      U=W=const, V=Yr, uniform independent inputs; a random search over small
      auxiliary alphabets never exceeds 1.5 (sanity check that the excess in
      (A) is an artefact of the Lean transcription, not of the channel).

Reproduce:  python3 lean_thm7_counterexample.py      (numpy only, < 1 min)
"""
import itertools
import math

import numpy as np

LOG2 = math.log(2.0)


def H(p):
    """Shannon entropy in bits of an array of probabilities (any shape)."""
    p = np.asarray(p, dtype=float).ravel()
    p = p[p > 0]
    return float(-(p * np.log2(p)).sum())


def marg(J, keep):
    """Marginal of joint array J onto the axes in `keep` (tuple, order kept)."""
    drop = tuple(i for i in range(J.ndim) if i not in keep)
    M = J.sum(axis=drop) if drop else J
    # reorder to the order given in keep
    kept_sorted = sorted(keep)
    perm = [kept_sorted.index(k) for k in keep]
    return np.transpose(M, perm)


def Hm(J, axes):
    return H(marg(J, tuple(sorted(axes))))


def cmi(J, A, B, C):
    """I(A;B|C) = H(A,C) + H(B,C) - H(A,B,C) - H(C), exactly as Lean's condMutualInfo."""
    A, B, C = set(A), set(B), set(C)
    hc = Hm(J, C) if C else 0.0
    return Hm(J, A | C) + Hm(J, B | C) - Hm(J, A | B | C) - hc


# ------------------------------------------------------------------ channel
# axes:  x in 0..3 (x = 2*x1 + x2), xr in 0..1, y in 0..5 (y = 3*y1 + y2), yr in 0..1
def channel():
    Wt = np.zeros((4, 2, 6, 2))
    for x1, x2, xr, z in itertools.product(range(2), range(2), range(2), range(2)):
        x = 2 * x1 + x2
        y1 = x1 ^ z
        y2 = x2 + xr
        y = 3 * y1 + y2
        Wt[x, xr, y, z] += 0.5
    assert np.allclose(Wt.sum(axis=(2, 3)), 1.0)
    return Wt


W = channel()


# ------------------------------------------------- (A) Lean functional value
def lean_rate(P_uxxr, Qc):
    """Lean coverElGamalTheorem7Rate integrand min(r1, r2).

    P_uxxr: array (kU, 4, 2);  Qc: array (kU, 2, 2[yr], kYh) = Q(yh | u, xr, yr).
    Joint axes: 0=u, 1=x, 2=xr, 3=y, 4=yr, 5=yh.
    """
    J = (P_uxxr[:, :, :, None, None, None]
         * W[None, :, :, :, :, None]
         * Qc[:, None, :, None, :, :])
    assert abs(J.sum() - 1) < 1e-12
    U, X, XR, Y, YR, YH = 0, 1, 2, 3, 4, 5
    r1 = cmi(J, {U}, {YR}, {XR}) + cmi(J, {X}, {Y, YH}, {U, XR})
    r2 = cmi(J, {X, XR}, {Y}, set()) - cmi(J, {YR}, {YH}, {U, X, XR, Y})
    return r1, r2, min(r1, r2)


def part_A():
    P = np.zeros((1, 4, 2))
    pair = np.array([[1 / 3, 1 / 6], [1 / 6, 1 / 3]])  # P(x2, xr)
    for x1 in range(2):
        for x2 in range(2):
            for xr in range(2):
                P[0, 2 * x1 + x2, xr] = 0.5 * pair[x2, xr]
    Qc = np.zeros((1, 2, 2, 2))
    for xr in range(2):
        for yr in range(2):
            Qc[0, xr, yr, yr] = 1.0  # Yh = Yr
    r1, r2, r = lean_rate(P, Qc)
    h13 = -(1 / 3) * math.log2(1 / 3) - (2 / 3) * math.log2(2 / 3)
    print("(A) Lean functional at the correlated CF point:")
    print(f"    r1 = {r1:.12f}   (1 + h(1/3) = {1 + h13:.12f})")
    print(f"    r2 = {r2:.12f}   (log2 3     = {math.log2(3):.12f})")
    print(f"    min(r1, r2) = {r:.12f}  >  1.5  by {r - 1.5:.6f} bits")
    assert abs(r1 - (1 + h13)) < 1e-12 and abs(r2 - math.log2(3)) < 1e-12
    # same functional with independent (X2, Xr): must give 1.5
    P2 = np.full((1, 4, 2), 1 / 8)
    _, _, rind = lean_rate(P2, Qc)
    print(f"    (same, independent uniform inputs: {rind:.12f})")
    return r


# ------------------------------------------------ (B) binary adder constant
def part_B(n=2001):
    p = np.linspace(0, 1, n)
    P, Q = np.meshgrid(p, p, indexing="ij")
    p0 = (1 - P) * (1 - Q)
    p1 = P * (1 - Q) + Q * (1 - P)
    p2 = P * Q
    def ent(t):
        with np.errstate(divide="ignore", invalid="ignore"):
            return np.where(t > 0, -t * np.log2(np.where(t > 0, t, 1)), 0.0)
    Hs = ent(p0) + ent(p1) + ent(p2)
    i, j = np.unravel_index(np.argmax(Hs), Hs.shape)
    print(f"(B) max_(p,q) H(Bern(p)+Bern(q)) on {n}x{n} grid = {Hs[i, j]:.12f} "
          f"at p={p[i]:.4f}, q={p[j]:.4f}")
    # crude Lipschitz-free check: entropy gradient bounded away from corners;
    # the analytic value 1.5 is the textbook binary-erasure-MAC sum capacity.
    assert Hs.max() <= 1.5 + 1e-12
    return Hs.max()


# ------------------------------------- (C) faithful Theorem 7 (CM11 Lemma 2)
def thm7_faithful(pw, pu_w, px_u, pxr_w, pv_uxryr):
    """Three-constraint Cover-El Gamal Theorem 7 (Q = const).

    pw (kW,), pu_w (kW,kU), px_u (kU,4), pxr_w (kW,2), pv_uxryr (kU,2,2,kV).
    Axes: 0=w,1=u,2=x,3=xr,4=y,5=yr,6=v.
    R <= I(X,Xr;Y) - I(Yr;V|U,X,Xr,Y)
    R <= I(X;V,Y|U,Xr) + I(U;Yr|W,Xr)
    R <= I(X;V,Y|U,Xr) + I(U;Yr|W,Xr) + I(Xr;Y|W) - I(Yr;V|U,Xr,Y)
    """
    J = (pw[:, None, None, None, None, None, None]
         * pu_w[:, :, None, None, None, None, None]
         * px_u[None, :, :, None, None, None, None]
         * pxr_w[:, None, None, :, None, None, None]
         * W[None, None, :, :, :, :, None]
         * pv_uxryr[None, :, None, :, None, :, :])
    Wv, U, X, XR, Y, YR, V = range(7)
    c1 = cmi(J, {X, XR}, {Y}, set()) - cmi(J, {YR}, {V}, {U, X, XR, Y})
    base = cmi(J, {X}, {V, Y}, {U, XR}) + cmi(J, {U}, {YR}, {Wv, XR})
    c2 = base
    c3 = base + cmi(J, {XR}, {Y}, {Wv}) - cmi(J, {YR}, {V}, {U, XR, Y})
    return min(c1, c2, c3)


def rand_simplex(rng, shape):
    g = rng.gamma(0.3, size=shape)
    return g / g.sum(axis=-1, keepdims=True)


def part_C(trials=3000, seed=1):
    # explicit point achieving 1.5
    pw = np.ones(1)
    pu_w = np.ones((1, 1))
    px_u = np.full((1, 4), 0.25)
    pxr_w = np.full((1, 2), 0.5)
    pv = np.zeros((1, 2, 2, 2))
    for xr in range(2):
        for yr in range(2):
            pv[0, xr, yr, yr] = 1.0
    val = thm7_faithful(pw, pu_w, px_u, pxr_w, pv)
    print(f"(C) faithful Theorem 7 at U=W=const, V=Yr, uniform inputs: {val:.12f}")
    rng = np.random.default_rng(seed)
    best = val
    for _ in range(trials):
        kW, kU, kV = 2, 3, 2
        pw = rand_simplex(rng, (kW,))
        pu_w = rand_simplex(rng, (kW, kU))
        px_u = rand_simplex(rng, (kU, 4))
        pxr_w = rand_simplex(rng, (kW, 2))
        pv = rand_simplex(rng, (kU, 2, 2, kV))
        best = max(best, thm7_faithful(pw, pu_w, px_u, pxr_w, pv))
    print(f"    random search ({trials} draws, |W|=2,|U|=3,|V|=2): max = {best:.12f}")
    assert best <= 1.5 + 1e-9
    return best


# ------------------------------------- (D) primitive-BSC time-sharing check
def hb(p):
    return 0.0 if p <= 0 or p >= 1 else -p * math.log2(p) - (1 - p) * math.log2(1 - p)


def hinv(y):
    lo, hi = 0.0, 0.5
    for _ in range(200):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if hb(mid) < y else (lo, mid)
    return (lo + hi) / 2


def bsc_relay_channel(pd=0.2, pr=0.1, link=0.3):
    """DM relay channel with orthogonal receiver components:
    Y1 = X xor N1 (BSC(pd)), Yr = X xor N2 (BSC(pr)), Y2 = Xr xor N3 (BSC(q)),
    1 - h(q) = link.  Axes x(2), xr(2), y=(y1,y2) -> 2*y1+y2 (4), yr(2)."""
    q = hinv(1 - link)
    Wt = np.zeros((2, 2, 4, 2))
    for x, xr, y1, y2, yr in itertools.product(range(2), repeat=5):
        p1 = 1 - pd if y1 == x else pd
        p2 = 1 - q if y2 == xr else q
        pr_ = 1 - pr if yr == x else pr
        Wt[x, xr, 2 * y1 + y2, yr] = p1 * p2 * pr_
    assert np.allclose(Wt.sum(axis=(2, 3)), 1.0)
    return Wt, q


def lean_rate_general(Wt, P_uxxr, Qc):
    J = (P_uxxr[:, :, :, None, None, None] * Wt[None, :, :, :, :, None]
         * Qc[:, None, :, None, :, :])
    U, X, XR, Y, YR, YH = 0, 1, 2, 3, 4, 5
    r1 = cmi(J, {U}, {YR}, {XR}) + cmi(J, {X}, {Y, YH}, {U, XR})
    r2 = cmi(J, {X, XR}, {Y}, set()) - cmi(J, {YR}, {YH}, {U, X, XR, Y})
    return r1, r2, min(r1, r2)


def part_D():
    Wt, q = bsc_relay_channel()
    best = (0, None)
    for lam1 in np.linspace(0, 0.2, 2001):          # P(CF phase)
        # U in {0,1} = DF phase carrying X;  U = 2 = CF phase.  X, Xr uniform indep.
        P = np.zeros((3, 2, 2))
        for x in range(2):
            for xr in range(2):
                P[x, x, xr] = (1 - lam1) * 0.25      # U = X in DF phase
                P[2, x, xr] = lam1 * 0.25
        Qc = np.zeros((3, 2, 2, 2))
        Qc[0:2, :, :, 0] = 1.0                       # DF phase: Yh constant
        for xr in range(2):
            for yr in range(2):
                Qc[2, xr, yr, yr] = 1.0              # CF phase: Yh = Yr
        r = lean_rate_general(Wt, P, Qc)[2]
        if r > best[0]:
            best = (r, lam1)
    print(f"(D) DM relay channel BSC(0.2) direct, BSC(0.1) relay, orthogonal BSC(q={q:.6f}) link "
          f"of capacity 0.3:\n    Lean functional with U = (coin, X|DF) reaches {best[0]:.6f} at "
          f"P(CF phase) = {best[1]:.4f}  (time-sharing value 0.539568; DF alone 0.531004)")
    assert best[0] > 0.5395
    # Ponniah (arXiv:2609.15709) C-CF / U-CF feasibility-constrained rates on the same
    # channel: random correlated p(xs,xr) and test channels T(yh|yr,xr), |Yh| in {2,3};
    # feasible (I(Yh;Yr|Xr) < I(Yh,Xr;Y)) rates must stay <= 1-h(0.2)+0.8*0.3.
    rng = np.random.default_rng(7)
    bound = 1 - hb(0.2) + 0.8 * 0.3
    worst = -1.0
    for _ in range(20000):
        kh = int(rng.integers(2, 4))
        pxx = rng.dirichlet(np.full(4, 0.4)).reshape(2, 2)
        T = rng.dirichlet(np.full(kh, 0.3), size=(2, 2))          # T[xr, yr, yh]
        J = pxx[:, :, None, None, None] * Wt[:, :, :, :, None] * T[None, :, None, :, :]
        X, XR, Y, YR, YH = 0, 1, 2, 3, 4
        rate = cmi(J, {X}, {YH, Y}, {XR})
        if cmi(J, {YH}, {YR}, {XR}) < cmi(J, {YH, XR}, {Y}, set()):
            worst = max(worst, rate - bound)
    print(f"    Ponniah C-CF-type feasible rates (20000 random draws): max(rate - {bound:.6f}) = {worst:.6f}")
    assert worst <= 1e-12
    return best[0]


if __name__ == "__main__":
    rA = part_A()
    cB = part_B()
    bC = part_C()
    dD = part_D()
    print()
    print(f"Summary: Lean functional >= {rA:.6f} = log2 3;  capacity <= {cB:.6f};"
          f"  faithful Thm 7 (searched) <= {bC:.6f}.")
