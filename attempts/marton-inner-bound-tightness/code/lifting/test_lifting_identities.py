#!/usr/bin/env python3
"""Brute-force sanity tests (float64; NOT part of any proof) of the analytic steps of HLL
(arXiv:2608.19869v1) Prop. 3, eq. (9), eq. (11)/(12) and the two-letter bound (51), on small
random instances of the receiver-revealed mixture  T~  with label alphabet [N], N small.

The mixture channel is built EXPLICITLY, output symbol by output symbol (tag, value), and every
Marton quantity is computed from the full joint law; nothing uses the decompositions being tested.

Tests (each over many random instances):
  T1  (10): M_{T~}(P) == lam*M_T(P_WUVX) + sum_i d_i M_{G_i}(P), and the same for L_t, t in [0,1].
  T2  (9) : H(G_i) == h2(p_i) + p_i H(K|X=i) <= h2(p_i) + p_i ln N.
  T3  (11): M_{G_i}(P) == I(WUV;G_i) - I(U;V|W,G_i) <= H(G_i).
  T4  (12) chain: M_{T~}(P) <= lam*M_T(P_WUVX) + sum_i d_i [h2(p_i) + p_i ln N].
  T5  (51): for the lifted seed (W~ = (W,K1,K2), K_l uniform, independent), for t in a grid,
            L_t,T~(x)2 >= lam^2 L_t,T(x)2(P*) + L sum_i d_i (q1(i)+q2(i)) - (1-lam^2) I(U;V|W).
  NEG negative control: crediting 1.5x the label term in T5 must fail on some instance.

Usage: python -I test_lifting_identities.py [n_instances] [seed]
"""
import itertools
import math
import sys

import numpy as np


def H(p):
    p = np.asarray(p, dtype=float).ravel()
    p = p[p > 0]
    return float(-(p * np.log(p)).sum())


def marg(J, keep):
    """J: dict tuple->prob; keep: tuple of indices."""
    out = {}
    for k, v in J.items():
        kk = tuple(k[i] for i in keep)
        out[kk] = out.get(kk, 0.0) + v
    return out


def Hd(J, keep):
    return H(list(marg(J, keep).values()))


def I(J, a, b, c=()):
    """I(A;B|C) for index tuples a, b, c of joint dict J."""
    return Hd(J, a + c) + Hd(J, b + c) - Hd(J, a + b + c) - (Hd(J, c) if c else 0.0)


def marton_parts(JY, JZ, w, u, v, y, z):
    """Return (IWY, IWZ, rest) with rest = I(U;Y|W)+I(V;Z|W)-I(U;V|W)."""
    IWY, IWZ = I(JY, w, y), I(JZ, w, z)
    rest = I(JY, u, y, w) + I(JZ, v, z, w) - I(JY, u, v, w)
    return IWY, IWZ, rest


def Lt(parts, t):
    IWY, IWZ, rest = parts
    return (1 - t) * IWY + t * IWZ + rest


def Mval(parts):
    IWY, IWZ, rest = parts
    return min(IWY, IWZ) + rest


def rand_channel(rng, nx, ny):
    T = rng.dirichlet(np.ones(ny) * 0.7, size=nx)
    return T


def one_letter_instance(rng, N=3, nx=3, nw=2, nu=2, nv=2):
    TY, TZ = rand_channel(rng, nx, 3), rand_channel(rng, nx, 3)
    shp = [i for i in range(nx) if i != nx - 1]          # shaping on all but r = last
    wts = rng.dirichlet(np.ones(len(shp) + 1))
    lam, d = wts[0], {i: wts[1 + j] for j, i in enumerate(shp)}
    # random sparse-ish P_{W U V X K}
    cells = list(itertools.product(range(nw), range(nu), range(nv), range(nx), range(N)))
    pr = rng.dirichlet(np.ones(len(cells)) * 0.3)
    P = {c: p for c, p in zip(cells, pr)}
    # explicit mixture outputs: tilde-Y = (tag, val); tag 0 base, tag i+1 shaping G_i (val 'e' or k)
    JY, JZ = {}, {}
    for (w, u, v, x, k), p in P.items():
        for y in range(3):
            key = (w, u, v, (0, y))
            JY[key] = JY.get(key, 0.0) + p * lam * TY[x][y]
            key = (w, u, v, (0, y))
            JZ[key] = JZ.get(key, 0.0) + p * lam * TZ[x][y]
        for i in shp:
            g = k if x == i else "e"
            key = (w, u, v, (i + 1, g))
            JY[key] = JY.get(key, 0.0) + p * d[i]
            JZ[key] = JZ.get(key, 0.0) + p * d[i]
    full = marton_parts(JY, JZ, (0,), (1,), (2,), (3,), (3,))
    # base channel functional on the marginal P_WUVX (K ignored)
    bY, bZ = {}, {}
    for (w, u, v, x, k), p in P.items():
        for y in range(3):
            bY[(w, u, v, y)] = bY.get((w, u, v, y), 0.0) + p * TY[x][y]
            bZ[(w, u, v, y)] = bZ.get((w, u, v, y), 0.0) + p * TZ[x][y]
    base = marton_parts(bY, bZ, (0,), (1,), (2,), (3,), (3,))
    # shaping components alone
    Gp, HG, extra = {}, {}, {}
    px = [sum(p for c, p in P.items() if c[3] == x) for x in range(nx)]
    for i in shp:
        J = {}
        for (w, u, v, x, k), p in P.items():
            g = k if x == i else "e"
            J[(w, u, v, g)] = J.get((w, u, v, g), 0.0) + p
        Gp[i] = marton_parts(J, J, (0,), (1,), (2,), (3,), (3,))
        HG[i] = Hd(J, (3,))
        pk = [sum(p for c, p in P.items() if c[3] == i and c[4] == kk) for kk in range(N)]
        HKgX = H(np.array(pk) / px[i]) if px[i] > 0 else 0.0
        hb = H([px[i], 1 - px[i]])
        extra[i] = dict(HKgX=HKgX, h2=hb, IWUV_G=I(J, (0, 1, 2), (3,)), IUV_WG=I(J, (1,), (2,), (0, 3)))
    return dict(lam=lam, d=d, shp=shp, full=full, base=base, Gp=Gp, HG=HG, extra=extra, px=px, N=N)


def two_letter_instance(rng, N=2, nx=3, nw=2, nu=2, nv=2):
    TY, TZ = rand_channel(rng, nx, 2), rand_channel(rng, nx, 2)
    shp = [i for i in range(nx) if i != nx - 1]
    wts = rng.dirichlet(np.ones(len(shp) + 1))
    lam, d = wts[0], {i: wts[1 + j] for j, i in enumerate(shp)}
    cells = list(itertools.product(range(nw), range(nu), range(nv), range(nx), range(nx)))
    pr = rng.dirichlet(np.ones(len(cells)) * 0.3)
    Pst = {c: p for c, p in zip(cells, pr) if p > 1e-14}
    # per-letter tilde output law given (x,k):  list of (symbol, prob)
    def outs(T, x, k):
        o = [((0, y), lam * T[x][y]) for y in range(T.shape[1])]
        for i in shp:
            o.append(((i + 1, k if x == i else "e"), d[i]))
        return o
    # lifted law: W~ = (w, k1, k2)
    JY, JZ = {}, {}
    for (w, u, v, x1, x2), p in Pst.items():
        for k1 in range(N):
            for k2 in range(N):
                pk = p / (N * N)
                for (T, J) in ((TY, JY), (TZ, JZ)):
                    for s1, a1 in outs(T, x1, k1):
                        for s2, a2 in outs(T, x2, k2):
                            key = ((w, k1, k2), u, v, (s1, s2))
                            J[key] = J.get(key, 0.0) + pk * a1 * a2
    lifted = marton_parts(JY, JZ, (0,), (1,), (2,), (3,), (3,))
    bY, bZ = {}, {}
    for (w, u, v, x1, x2), p in Pst.items():
        for (T, J) in ((TY, bY), (TZ, bZ)):
            for y1 in range(T.shape[1]):
                for y2 in range(T.shape[1]):
                    key = (w, u, v, (y1, y2))
                    J[key] = J.get(key, 0.0) + p * T[x1][y1] * T[x2][y2]
    base = marton_parts(bY, bZ, (0,), (1,), (2,), (3,), (3,))
    C = I(bY, (1,), (2,), (0,))
    q1 = [sum(p for c, p in Pst.items() if c[3] == x) for x in range(nx)]
    q2 = [sum(p for c, p in Pst.items() if c[4] == x) for x in range(nx)]
    return dict(lam=lam, d=d, shp=shp, lifted=lifted, base=base, C=C, q1=q1, q2=q2, L=math.log(N))


def main():
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 200
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 20261127
    rng = np.random.default_rng(seed)
    tol = 1e-10
    worst = dict(T1=0.0, T2eq=0.0, T2ub=-np.inf, T3eq=0.0, T3ub=-np.inf, T4=-np.inf, T5=-np.inf, NEG=-np.inf)
    for _ in range(n):
        R = one_letter_instance(rng)
        lam, d, shp = R["lam"], R["d"], R["shp"]
        pred_M = lam * Mval(R["base"]) + sum(d[i] * Mval(R["Gp"][i]) for i in shp)
        worst["T1"] = max(worst["T1"], abs(Mval(R["full"]) - pred_M))
        for t in (0.0, 0.25, 0.5, 1.0):
            pred = lam * Lt(R["base"], t) + sum(d[i] * Lt(R["Gp"][i], t) for i in shp)
            worst["T1"] = max(worst["T1"], abs(Lt(R["full"], t) - pred))
        bound = lam * Mval(R["base"])
        for i in shp:
            e, p = R["extra"][i], R["px"][i]
            worst["T2eq"] = max(worst["T2eq"], abs(R["HG"][i] - (e["h2"] + p * e["HKgX"])))
            worst["T2ub"] = max(worst["T2ub"], R["HG"][i] - (e["h2"] + p * math.log(R["N"])))
            worst["T3eq"] = max(worst["T3eq"], abs(Mval(R["Gp"][i]) - (e["IWUV_G"] - e["IUV_WG"])))
            worst["T3ub"] = max(worst["T3ub"], Mval(R["Gp"][i]) - R["HG"][i])
            bound += d[i] * (e["h2"] + p * math.log(R["N"]))
        worst["T4"] = max(worst["T4"], Mval(R["full"]) - bound)
    for _ in range(max(1, n // 4)):
        R = two_letter_instance(rng)
        lam, d, shp = R["lam"], R["d"], R["shp"]
        lab = R["L"] * sum(d[i] * (R["q1"][i] + R["q2"][i]) for i in shp)
        for t in np.linspace(0, 1, 11):
            rhs = lam ** 2 * Lt(R["base"], t) + lab - (1 - lam ** 2) * R["C"]
            worst["T5"] = max(worst["T5"], rhs - Lt(R["lifted"], t))
        rhsM = lam ** 2 * Mval(R["base"]) + lab - (1 - lam ** 2) * R["C"]
        worst["T5"] = max(worst["T5"], rhsM - Mval(R["lifted"]))
        # negative control: a label credit of 1.5x (i.e. claiming more than q(i) L per shaping use)
        # must be violated on some instance, otherwise T5 has no power.
        worst["NEG"] = max(worst["NEG"], rhsM + 0.5 * lab - Mval(R["lifted"]))
    print(f"instances: {n} one-letter (N=3, |X|=3, |W|=|U|=|V|=2), {max(1, n // 4)} two-letter (N=2); seed {seed}")
    print(f"T1 (10) identity, max |lhs-rhs| over M and L_t       : {worst['T1']:.3e}")
    print(f"T2 (9) identity  H(G)=h2+pH(K|X=i), max |diff|        : {worst['T2eq']:.3e}")
    print(f"T2 (9) bound     max H(G) - (h2 + p ln N)  (<= 0)      : {worst['T2ub']:.3e}")
    print(f"T3 (11) identity M_G = I(WUV;G)-I(U;V|WG), max |diff| : {worst['T3eq']:.3e}")
    print(f"T3 (11) bound    max M_G - H(G)            (<= 0)      : {worst['T3ub']:.3e}")
    print(f"T4 (12) chain    max M_T~ - [lam M_T + sum d(h2+pL)] (<= 0): {worst['T4']:.3e}")
    print(f"T5 (51)/(52)     max rhs - lhs             (<= 0)      : {worst['T5']:.3e}")
    print(f"NEG control: 1.5x label credit, max rhs - lhs (must be > 0): {worst['NEG']:.3e}")
    ok = (worst["NEG"] > 0 and worst["T1"] < tol and worst["T2eq"] < tol and worst["T2ub"] < tol and worst["T3eq"] < tol
          and worst["T3ub"] < tol and worst["T4"] < tol and worst["T5"] < tol)
    print("ALL TESTS PASSED" if ok else "SOME TEST FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
