#!/usr/bin/env python3
"""
Independent numerical re-check of the explicit numbers in
  M. Huang, Y. Liu, Y. Liu, "Sub-optimality of Marton's inner bound for the two-receiver
  broadcast channel", arXiv:2608.19869v1 (20 Aug 2026)  [HLL]
for its ternary base channel (eqs. (14)-(19), (22)-(28), (44)-(46), Appendix A).

All quantities in NATS (as in HLL).  Written from the paper's text only (HLL's own code was
NOT used), so this is an independent implementation.

What is checked
  1. G_T at HLL's one-letter optimiser (19) reproduces F_T({a},alpha) of (18), and the induced
     input marginal is p* of (16).
  2. UB(p*) of (23)/(25) (= value of the dual bound on M_T(p*)) reproduces 0.09165088339...
  3. The two-letter component values A_q, B_q of (44) and the mixture value gamma of (46),
     recomputed from the Appendix-A rational table (exact rationals -> 50-digit mpmath).
  4. (falsification test, NOT a proof) multistart local maximisation of G_T over P_{UVX}
     with |U|,|V| in {2,3,4} and randomised X|(U,V): any value above F_T would refute (25).
  5. (structured near-exhaustive search, NOT a proof) the cases HLL say suffice by the
     cardinality bound |U|+|V| <= |X|+1 with X = f(U,V) deterministic: all 81 maps
     f:{0,1}^2 -> {0,1,2} with P_UV on a simplex grid (step 1/60) + Nelder-Mead polish, and the
     edge cases (U const, V = X) and (U = X, V const) with p_X on a simplex grid + polish.

Usage:  python hll_check.py [n_starts]
"""
import sys
from fractions import Fraction as Fr
import numpy as np
from mpmath import mp, mpf, log
from scipy.optimize import minimize

mp.dps = 50

TY = [["0.385361043864", "0.358548005177", "0.256090950959"],
      ["0.790302113033", "0.091025394735", "0.118672492232"],
      ["0.113168779849", "0.520687239901", "0.366143980250"]]
TZ = [["0.390396602690", "0.207292393713", "0.402311003597"],
      ["0.293627666338", "0.040944965497", "0.665427368165"],
      ["0.396880111705", "0.507497881167", "0.095622007128"]]
PSTAR = ["0.704504835923", "0.172563088231", "0.122932075846"]
ALPHA = "0.546388044486"
AVEC = ["0", "-0.393210549796", "-0.149290191142"]
MU = "0.28950945961978169531"

TABLE = [  # (q, wc, u, v, "x1x2", numerator / 10^12), HLL Appendix A
    (0, 0, 0, 0, "11", 2),
    (0, 0, 0, 1, "01", 1384478680),
    (0, 0, 0, 2, "10", 1384478680),
    (0, 0, 0, 3, "11", 15902736192),
    (0, 0, 1, 0, "10", 16),
    (0, 0, 1, 1, "00", 10209427117),
    (0, 0, 1, 2, "12", 23193325149),
    (0, 0, 1, 3, "10", 117244957226),
    (0, 0, 2, 0, "01", 16),
    (0, 0, 2, 1, "21", 23193325149),
    (0, 0, 2, 2, "00", 10209427117),
    (0, 0, 2, 3, "01", 117244957226),
    (0, 0, 3, 0, "00", 55),
    (0, 0, 3, 1, "20", 81553873546),
    (0, 0, 3, 2, "02", 81553873546),
    (0, 0, 3, 3, "00", 411998751962),
    (0, 1, 0, 0, "00", 732352219),
    (0, 1, 0, 3, "11", 14837590966),
    (0, 1, 1, 0, "22", 42),
    (0, 1, 1, 3, "00", 166),
    (0, 1, 2, 0, "22", 18),
    (0, 1, 2, 3, "00", 70),
    (0, 1, 3, 0, "22", 18184877091),
    (0, 1, 3, 3, "00", 71171567749),
    (1, 0, 0, 0, "11", 3),
    (1, 0, 0, 1, "01", 1422792872),
    (1, 0, 0, 2, "10", 1422792872),
    (1, 0, 0, 3, "11", 16393806593),
    (1, 0, 1, 0, "10", 25),
    (1, 0, 1, 1, "00", 10187677513),
    (1, 0, 1, 2, "12", 23143812089),
    (1, 0, 1, 3, "10", 117357754072),
    (1, 0, 2, 0, "01", 25),
    (1, 0, 2, 1, "21", 23143812089),
    (1, 0, 2, 2, "00", 10187677513),
    (1, 0, 2, 3, "01", 117357754072),
    (1, 0, 3, 0, "00", 88),
    (1, 0, 3, 1, "20", 81614505516),
    (1, 0, 3, 2, "02", 81614505516),
    (1, 0, 3, 3, "00", 413588568366),
    (1, 1, 0, 0, "00", 720151199),
    (1, 1, 0, 2, "11", 18),
    (1, 1, 0, 3, "11", 14244922559),
    (1, 1, 1, 0, "22", 45),
    (1, 1, 1, 3, "00", 171),
    (1, 1, 2, 0, "22", 26),
    (1, 1, 2, 3, "00", 100),
    (1, 1, 3, 0, "22", 18173758170),
    (1, 1, 3, 1, "00", 1),
    (1, 1, 3, 2, "00", 88),
    (1, 1, 3, 3, "00", 69425708399),
]

TYf = np.array([[float(x) for x in r] for r in TY])
TZf = np.array([[float(x) for x in r] for r in TZ])


def H(p):
    return -sum(x * log(x) for x in p if x > 0)


def mutual(joint):
    """I(A;B) for a dict {(a,b): prob} (mpf)."""
    pa, pb = {}, {}
    for (a, b), v in joint.items():
        pa[a] = pa.get(a, 0) + v
        pb[b] = pb.get(b, 0) + v
    return H(pa.values()) + H(pb.values()) - H(joint.values())


def check_rows():
    for M in (TY, TZ):
        for r in M:
            s = sum(Fr(x) for x in r)
            print("   row sum", s, "== 1" if s == 1 else "!= 1 (difference %s)" % (s - 1))


def one_letter():
    al = mpf(ALPHA)
    a = [mpf(x) for x in AVEC]
    ty = [[mpf(x) for x in r] for r in TY]
    tz = [[mpf(x) for x in r] for r in TZ]
    # optimiser (19): X = f(U,V) with f = [[0,1],[2,0]], P_UV = [[p00,p01],[p10,p11]]
    f = [[0, 1], [2, 0]]
    PUV = [[mpf("0.013502132210"), mpf("0.172563088231")],
           [mpf("0.122932075846"), mpf("0.691002703713")]]
    px = [mpf(0)] * 3
    for u in range(2):
        for v in range(2):
            px[f[u][v]] += PUV[u][v]
    py = [sum(px[x] * ty[x][y] for x in range(3)) for y in range(3)]
    pz = [sum(px[x] * tz[x][z] for x in range(3)) for z in range(3)]
    jUY, jVZ, jUV = {}, {}, {}
    for u in range(2):
        for v in range(2):
            x = f[u][v]
            jUV[(u, v)] = PUV[u][v]
            for y in range(3):
                jUY[(u, y)] = jUY.get((u, y), 0) + PUV[u][v] * ty[x][y]
                jVZ[(v, y)] = jVZ.get((v, y), 0) + PUV[u][v] * tz[x][y]
    G = (-al * H(py) - (1 - al) * H(pz) + mutual(jUY) + mutual(jVZ) - mutual(jUV)
         + sum(px[x] * a[x] for x in range(3)))
    marton_val = mutual(jUY) + mutual(jVZ) - mutual(jUV)
    print("1. induced p_X =", [mp.nstr(x, 13) for x in px], " (p* =", PSTAR, ")")
    print("   G_T at (19)  = %s   (HLL (18): -1.06471340944277385029...)" % mp.nstr(G, 25))
    # UB(p*) with F replaced by G at the optimiser
    pst = [mpf(x) for x in PSTAR]
    pys = [sum(pst[x] * ty[x][y] for x in range(3)) for y in range(3)]
    pzs = [sum(pst[x] * tz[x][z] for x in range(3)) for z in range(3)]
    UB = al * H(pys) + (1 - al) * H(pzs) + G - sum(pst[x] * a[x] for x in range(3))
    print("2. UB(p*) using F_T := G_T(19) = %s   (HLL (25): <= 0.0916508833913554746710)" % mp.nstr(UB, 22))
    print("   I(U;Y)+I(V;Z)-I(U;V) at (19) = %s" % mp.nstr(marton_val, 22))
    return G, UB


def two_letter():
    ty = [[mpf(x) for x in r] for r in TY]
    tz = [[mpf(x) for x in r] for r in TZ]
    res = {}
    for q in (0, 1):
        rows = [r for r in TABLE if r[0] == q]
        tot = sum(r[5] for r in rows)
        assert tot == 10 ** 12, tot
        P = {}
        for (_, wc, u, v, xx, num) in rows:
            P[(wc, u, v, int(xx[0]), int(xx[1]))] = mpf(num) / mpf(10) ** 12
        # joint with Y^2 and Z^2
        jWY, jWZ, jUWY, jVWZ, jUVW = {}, {}, {}, {}, {}
        for (wc, u, v, x1, x2), pr in P.items():
            jUVW[(wc, u, v)] = jUVW.get((wc, u, v), 0) + pr
            for y1 in range(3):
                for y2 in range(3):
                    py = pr * ty[x1][y1] * ty[x2][y2]
                    pz = pr * tz[x1][y1] * tz[x2][y2]
                    k = (y1, y2)
                    jWY[(wc, k)] = jWY.get((wc, k), 0) + py
                    jWZ[(wc, k)] = jWZ.get((wc, k), 0) + pz
                    jUWY[((u, wc), k)] = jUWY.get(((u, wc), k), 0) + py
                    jVWZ[((v, wc), k)] = jVWZ.get(((v, wc), k), 0) + pz
        IWY = mutual(jWY)
        IWZ = mutual(jWZ)
        IUY_W = mutual(jUWY) - IWY          # I(U,W;Y) - I(W;Y)
        IVZ_W = mutual(jVWZ) - IWZ
        # I(U;V|W) = sum_w p(w) I(U;V|W=w)
        pw = {}
        for (wc, u, v), pr in jUVW.items():
            pw[wc] = pw.get(wc, 0) + pr
        IUV_W = 0
        for w0 in pw:
            sub = {(u, v): pr / pw[w0] for (wc, u, v), pr in jUVW.items() if wc == w0}
            IUV_W += pw[w0] * mutual(sub)
        Jq = IUY_W + IVZ_W - IUV_W
        A, B = IWY + Jq, IWZ + Jq
        res[q] = (A, B)
        print("3. q=%d: A_q = %s  B_q = %s" % (q, mp.nstr(A, 22), mp.nstr(B, 22)))
    mu = mpf(MU)
    gA = mu * res[0][0] + (1 - mu) * res[1][0]
    gB = mu * res[0][1] + (1 - mu) * res[1][1]
    print("   mu*A0+(1-mu)A1 = %s ; mu*B0+(1-mu)B1 = %s   (HLL (46): 0.183304594320655224901767...)"
          % (mp.nstr(gA, 22), mp.nstr(gB, 22)))
    return min(gA, gB)


# ---------------- falsification search for F_T({a}, alpha) ----------------
def G_float(theta, nu, nv, al, a):
    P = np.exp(theta - theta.max())
    P = P.reshape(nu, nv, 3)
    P /= P.sum()
    px = P.sum(axis=(0, 1))
    puv = P.sum(axis=2)
    pu, pv = puv.sum(1), puv.sum(0)
    pUy = np.einsum('uvx,xy->uy', P, TYf)
    pVz = np.einsum('uvx,xz->vz', P, TZf)
    py, pz = pUy.sum(0), pVz.sum(0)

    def ent(p):
        p = p[p > 1e-300]
        return -(p * np.log(p)).sum()
    HYgU = ent(pUy.ravel()) - ent(pu)
    HZgV = ent(pVz.ravel()) - ent(pv)
    IUV = ent(pu) + ent(pv) - ent(puv.ravel())
    return (1 - al) * ent(py) + al * ent(pz) - HYgU - HZgV - IUV + px @ a


def search(n_starts, seed=0):
    rng = np.random.default_rng(seed)
    al = float(ALPHA)
    a = np.array([float(x) for x in AVEC])
    best = -np.inf
    for (nu, nv) in [(2, 2), (2, 3), (3, 2), (3, 3), (4, 4)]:
        bloc = -np.inf
        for s in range(n_starts):
            th0 = rng.normal(size=nu * nv * 3) * 3
            r = minimize(lambda th: -G_float(th, nu, nv, al, a), th0, method='L-BFGS-B',
                         options={'maxiter': 3000, 'ftol': 1e-15, 'gtol': 1e-11})
            bloc = max(bloc, -r.fun)
        print("4. |U|=%d |V|=%d: best G found over %d starts = %.15f" % (nu, nv, n_starts, bloc), flush=True)
        best = max(best, bloc)
    return best


def explicit_instance(UB_ours):
    """Recompute HLL (40), (42), (43) for the explicit channel (M = 2e6, N = 2^M)."""
    lam = mpf(99999977198527428838942) / mpf(10) ** 23
    d0 = mpf(20970790337007940) / mpf(10) ** 23
    d1 = mpf(1830682234153118) / mpf(10) ** 23
    L = 2000000 * log(2)
    p0, p1 = mpf(PSTAR[0]), mpf(PSTAR[1])
    h2 = lambda p: -(p * log(p) + (1 - p) * log(1 - p))
    eps = mpf("1.846843880121467e-17")
    print("6. lambda+delta0+delta1 =", lam + d0 + d1)
    for name, UB in [("printed (25)", mpf("0.0916508833913554746710")), ("recomputed", UB_ours)]:
        up = lam * UB + d0 * (h2(p0) + p0 * L) + d1 * (h2(p1) + p1 * L) + eps
        print("   (40) with UB %s: M_T~ <= %s   (HLL: 0.30084186609915448)" % (name, mp.nstr(up, 20)))
    Ms = mpf("0.1833045943206552249020")
    low = lam ** 2 * Ms + 2 * L * (d0 * p0 + d1 * p1) - (1 - lam ** 2) * log(4)
    print("   (42): M_T~^2 >= %s   (HLL: 0.60168561432394163)" % mp.nstr(low, 20))
    print("   (43) with printed (40): gap >= %s" % mp.nstr(low - 2 * mpf("0.30084186609915448"), 12))


def G_det_batch(P, f, al, a):
    """G_T for X = f(U,V), U,V binary; P: (B,2,2) batch of P_UV."""
    B = P.shape[0]
    fx = np.array(f).reshape(2, 2)
    px = np.zeros((B, 3))
    pUy = np.zeros((B, 2, 3))
    pVz = np.zeros((B, 2, 3))
    for u in range(2):
        for v in range(2):
            x = fx[u, v]
            px[:, x] += P[:, u, v]
            pUy[:, u, :] += P[:, u, v][:, None] * TYf[x][None, :]
            pVz[:, v, :] += P[:, u, v][:, None] * TZf[x][None, :]

    def ent(q, axes):
        q = np.where(q > 0, q, 1.0)
        return -(q * np.log(q)).sum(axis=axes)
    pu, pv = P.sum(2), P.sum(1)
    py, pz = pUy.sum(1), pVz.sum(1)
    G = ((1 - al) * ent(py, 1) + al * ent(pz, 1) - (ent(pUy, (1, 2)) - ent(pu, 1))
         - (ent(pVz, (1, 2)) - ent(pv, 1)) - (ent(pu, 1) + ent(pv, 1) - ent(P, (1, 2)))
         + px @ a)
    return G


def simplex_grid(k, n):
    pts = []
    import itertools
    for c in itertools.product(range(n + 1), repeat=k - 1):
        if sum(c) <= n:
            pts.append(list(c) + [n - sum(c)])
    return np.array(pts, dtype=float) / n


def structured_search():
    import itertools
    al = float(ALPHA)
    a = np.array([float(x) for x in AVEC])
    grid = simplex_grid(4, 60)
    best = (-np.inf, None)
    allmaps = list(itertools.product(range(3), repeat=4))
    for f in allmaps:
        P = grid.reshape(-1, 2, 2)
        G = G_det_batch(P, f, al, a)
        idx = np.argsort(-G)[:3]
        for i in idx:
            z0 = np.log(np.maximum(grid[i], 1e-9))
            obj = lambda z: -G_det_batch((np.exp(z - z.max()) / np.exp(z - z.max()).sum()).reshape(1, 2, 2), f, al, a)[0]
            r = minimize(obj, z0, method='Nelder-Mead', options={'maxiter': 4000, 'xatol': 1e-12, 'fatol': 1e-16})
            if -r.fun > best[0]:
                best = (-r.fun, f)
    print("5. best over all 81 deterministic maps (|U|=|V|=2): %.15f  map f(00,01,10,11)=%s" % best, flush=True)
    # edge cases: (U const, V = X) and (U = X, V const)
    g3 = simplex_grid(3, 600)

    def ent(q):
        q = np.where(q > 0, q, 1.0)
        return -(q * np.log(q)).sum(axis=-1)
    HYx = np.array([ent(TYf[x]) for x in range(3)])
    HZx = np.array([ent(TZf[x]) for x in range(3)])
    for name, extra in [("U const, V=X", lambda p: ent(p @ TZf) - p @ HZx),
                        ("U=X, V const", lambda p: ent(p @ TYf) - p @ HYx)]:
        G = -al * ent(g3 @ TYf) - (1 - al) * ent(g3 @ TZf) + extra(g3) + g3 @ a
        i = int(np.argmax(G))
        obj = lambda z: -(lambda p: -al * ent(p @ TYf) - (1 - al) * ent(p @ TZf) + extra(p) + p @ a)(np.exp(z - z.max()) / np.exp(z - z.max()).sum())
        r = minimize(obj, np.log(np.maximum(g3[i], 1e-9)), method='Nelder-Mead', options={'xatol': 1e-12, 'fatol': 1e-16})
        print("5. %s: best G = %.15f" % (name, -r.fun), flush=True)
        best = max(best, (-r.fun, name), key=lambda x: x[0])
    return best[0]


if __name__ == "__main__":
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 40
    print("0. channel row sums (exact decimal arithmetic):")
    check_rows()
    G, UB = one_letter()
    g2 = two_letter()
    print("   two-letter value - 2*UB(p*) = %s nats  (HLL: >= 2.8275e-6)" % mp.nstr(g2 - 2 * UB, 12))
    explicit_instance(UB)
    best = search(n)
    print("   search max - F_T(19) = %.3e  (positive => (25) would be refuted)" % (best - float(G)))
    sb = structured_search()
    print("   structured max - F_T(19) = %.3e  (positive => (25) would be refuted)" % (sb - float(G)))
