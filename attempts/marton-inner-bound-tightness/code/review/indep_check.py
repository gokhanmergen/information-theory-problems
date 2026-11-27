#!/usr/bin/env python3
# Reviewer check (2026-11-27): independent 60-digit re-check of the HLL (arXiv:2608.19869v1) numbers:
# marginals (26), A_q, B_q, mu, gamma, G_T(19), I(U;V|X), gradient shaping (36)/(39), (40), (42), (43).
# Run: python3 indep_check.py [hll.txt [author_hll_check.py]]   (default author file ../hll_check.py)
# Runtime: about 1 s. Needs mpmath. Output of the full run in indep_check.out.
# Part A compares the Appendix-A table parsed from a pdftotext extract of the arXiv PDF (hll.txt, not
# committed: paper text) with the author's TABLE. Without hll.txt it uses the author's 51 rows instead.
"""Reviewer's independent re-check of HLL (arXiv:2608.19869v1) numbers.

Written from the paper text only (table parsed from pdftotext output of the arXiv PDF);
does not import the attempt's hll_check.py nor HLL's repo code.
Usage: python -I indep_check.py [<hll.txt> [<author_hll_check.py>]]
"""
import os
import re
import sys
from fractions import Fraction as F
from mpmath import mp, mpf, log

mp.dps = 60

TY = [["0.385361043864", "0.358548005177", "0.256090950959"],
      ["0.790302113033", "0.091025394735", "0.118672492232"],
      ["0.113168779849", "0.520687239901", "0.366143980250"]]
TZ = [["0.390396602690", "0.207292393713", "0.402311003597"],
      ["0.293627666338", "0.040944965497", "0.665427368165"],
      ["0.396880111705", "0.507497881167", "0.095622007128"]]
PST = ["0.704504835923", "0.172563088231", "0.122932075846"]
AL = "0.546388044486"
AV = ["0", "-0.393210549796", "-0.149290191142"]


def parse_table(txt_path):
    rows = []
    pat = re.compile(r"^\s+([01])\s+([01])\s+([0-3])\s+([0-3])\s+([0-2])([0-2])\s+([0-9,]+)\s*$")
    for line in open(txt_path, encoding="utf-8"):
        m = pat.match(line)
        if m:
            q, wc, u, v, x1, x2 = (int(m.group(i)) for i in range(1, 7))
            rows.append((q, wc, u, v, x1, x2, int(m.group(7).replace(",", ""))))
    return rows


def parse_author_table(py_path):
    rows = []
    pat = re.compile(r'^\s*\((\d), (\d), (\d), (\d), "(\d)(\d)", (\d+)\),')
    for line in open(py_path, encoding="utf-8"):
        m = pat.match(line)
        if m:
            rows.append(tuple(int(m.group(i)) for i in range(1, 8)))
    return rows


def H(vals):
    s = mpf(0)
    for p in vals:
        if p > 0:
            s -= p * log(p)
    return s


def marg(joint, keyf):
    out = {}
    for k, v in joint.items():
        kk = keyf(k)
        out[kk] = out.get(kk, 0) + v
    return out


def main(txt_path, author_py):
    ty = [[mpf(x) for x in r] for r in TY]
    tz = [[mpf(x) for x in r] for r in TZ]
    arows = parse_author_table(author_py)
    if txt_path:
        rows = parse_table(txt_path)
        print("A. parsed rows from PDF:", len(rows), " author rows:", len(arows),
              " identical:", sorted(rows) == sorted(arows))
    else:  # no paper text supplied: fall back to the author's table
        rows = arows
        print("A. skipped (no pdftotext extract given); using the author's TABLE:", len(arows), "rows")
    pst_int = [int(F(x) * 10**12) for x in PST]
    comps = {}
    for q in (0, 1):
        R = [r for r in rows if r[0] == q]
        tot = sum(r[6] for r in R)
        m1 = [sum(r[6] for r in R if r[4] == x) for x in range(3)]
        m2 = [sum(r[6] for r in R if r[5] == x) for x in range(3)]
        print("B. q=%d total=%d  X1-marg=%s X2-marg=%s  p*·1e12=%s  exact match: %s %s"
              % (q, tot, m1, m2, pst_int, m1 == pst_int, m2 == pst_int))
        comps[q] = {(r[1], r[2], r[3], r[4], r[5]): mpf(r[6]) / mpf(10)**12 for r in R}
    # two-letter endpoint values via entropies
    res = {}
    for q in (0, 1):
        P = comps[q]
        jY, jZ = {}, {}   # (wc,u,v,y1,y2) joint
        for (wc, u, v, x1, x2), p in P.items():
            for a in range(3):
                for b in range(3):
                    jY[(wc, u, v, a, b)] = jY.get((wc, u, v, a, b), 0) + p * ty[x1][a] * ty[x2][b]
                    jZ[(wc, u, v, a, b)] = jZ.get((wc, u, v, a, b), 0) + p * tz[x1][a] * tz[x2][b]
        def Hm(j, f):
            return H(marg(j, f).values())
        # I(Wc;Y2)=H(Y2)-H(Y2|Wc); H(Y2|Wc)=H(Wc,Y2)-H(Wc)
        HWc = Hm(jY, lambda k: k[0])
        HY = Hm(jY, lambda k: (k[3], k[4])); HZ = Hm(jZ, lambda k: (k[3], k[4]))
        HWY = Hm(jY, lambda k: (k[0], k[3], k[4])); HWZ = Hm(jZ, lambda k: (k[0], k[3], k[4]))
        HWU = Hm(jY, lambda k: (k[0], k[1])); HWV = Hm(jY, lambda k: (k[0], k[2]))
        HWUY = Hm(jY, lambda k: (k[0], k[1], k[3], k[4])); HWVZ = Hm(jZ, lambda k: (k[0], k[2], k[3], k[4]))
        HWUV = Hm(jY, lambda k: (k[0], k[1], k[2]))
        IWY = HY - (HWY - HWc); IWZ = HZ - (HWZ - HWc)
        IUY_W = (HWY - HWc) - (HWUY - HWU)
        IVZ_W = (HWZ - HWc) - (HWVZ - HWV)
        IUV_W = (HWU - HWc) + (HWV - HWc) - (HWUV - HWc)
        J = IUY_W + IVZ_W - IUV_W
        res[q] = (IWY + J, IWZ + J)
        print("C. q=%d A=%s B=%s" % (q, mp.nstr(res[q][0], 25), mp.nstr(res[q][1], 25)))
    (A0, B0), (A1, B1) = res[0], res[1]
    mu = (B1 - A1) / ((A0 - A1) - (B0 - B1))
    gam = mu * A0 + (1 - mu) * A1
    print("C. equalising mu =", mp.nstr(mu, 22), " (HLL 0.28950945961978169531)")
    print("C. gamma =", mp.nstr(gam, 25), " (HLL (46) 0.183304594320655224901767...)")
    # mixed X1X2 marginal (28)
    mix = {}
    for q, w in ((0, mu), (1, 1 - mu)):
        for (wc, u, v, x1, x2), p in comps[q].items():
            mix[(x1, x2)] = mix.get((x1, x2), 0) + w * p
    print("C. P*_X1X2 row0:", [mp.nstr(mix[(0, j)], 15) for j in range(3)],
          " symmetric:", all(abs(mix[(i, j)] - mix[(j, i)]) < mpf(10)**-40 for i in range(3) for j in range(3)))

    # one-letter at (19)
    al = mpf(AL); a = [mpf(x) for x in AV]
    f = {(0, 0): 0, (0, 1): 1, (1, 0): 2, (1, 1): 0}
    PUV = {(0, 0): mpf("0.013502132210"), (0, 1): mpf("0.172563088231"),
           (1, 0): mpf("0.122932075846"), (1, 1): mpf("0.691002703713")}
    px = [sum(p for k, p in PUV.items() if f[k] == x) for x in range(3)]
    pY = [sum(px[x] * ty[x][y] for x in range(3)) for y in range(3)]
    pZ = [sum(px[x] * tz[x][z] for x in range(3)) for z in range(3)]
    jUY = {}; jVZ = {}
    for (u, v), p in PUV.items():
        for y in range(3):
            jUY[(u, y)] = jUY.get((u, y), 0) + p * ty[f[(u, v)]][y]
            jVZ[(v, y)] = jVZ.get((v, y), 0) + p * tz[f[(u, v)]][y]
    HU = H(marg(PUV, lambda k: k[0]).values()); HV = H(marg(PUV, lambda k: k[1]).values())
    IUY = H(pY) - (H(jUY.values()) - HU)
    IVZ = H(pZ) - (H(jVZ.values()) - HV)
    IUV = HU + HV - H(PUV.values())
    G = -al * H(pY) - (1 - al) * H(pZ) + IUY + IVZ - IUV + sum(px[x] * a[x] for x in range(3))
    # I(U;V|X)
    IUVgX = mpf(0)
    for x in range(3):
        sub = {k: p for k, p in PUV.items() if f[k] == x}
        tot = sum(sub.values())
        cond = {k: p / tot for k, p in sub.items()}
        IUVgX += tot * (H(marg(cond, lambda k: k[0]).values()) + H(marg(cond, lambda k: k[1]).values()) - H(cond.values()))
    print("D. induced p_X == p*:", [mp.nstr(t, 13) for t in px], px == [mpf(x) for x in PST])
    print("D. G_T(19) =", mp.nstr(G, 30))
    print("D. primal I(U;Y)+I(V;Z)-I(U;V) at (19) =", mp.nstr(IUY + IVZ - IUV, 25))
    print("D. I(U;V|X) at (19) =", mp.nstr(IUVgX, 20), " (HLL 0.06676808506814671821...)")
    UB_print = mpf("0.0916508833913554746710")
    print("D. printed (25) - primal(19) =", mp.nstr(UB_print - (IUY + IVZ - IUV), 10))

    # gradient of UB(p) = al H_p(Y) + (1-al) H_p(Z) + B - sum p a, at p*
    p = [mpf(x) for x in PST]
    pY = [sum(p[x] * ty[x][y] for x in range(3)) for y in range(3)]
    pZ = [sum(p[x] * tz[x][z] for x in range(3)) for z in range(3)]
    g = [-al * sum(ty[x][y] * (log(pY[y]) + 1) for y in range(3))
         - (1 - al) * sum(tz[x][z] * (log(pZ[z]) + 1) for z in range(3)) - a[x] for x in range(3)]
    print("E. grad UB(p*) differences g1-g0 =", mp.nstr(g[1] - g[0], 22), " (HLL b1 0.26533808894270830145)")
    print("E.                         g2-g0 =", mp.nstr(g[2] - g[0], 22), " (HLL b2 0.29071676800873404161)")
    lam = mpf(99999977198527428838942) / mpf(10)**23
    d0 = mpf(20970790337007940) / mpf(10)**23
    d1 = mpf(1830682234153118) / mpf(10)**23
    L = 2000000 * log(2)
    print("E. lambda+d0+d1 - 1 =", lam + d0 + d1 - 1)
    gphi = [lam * g[0] + d0 * (L + log((1 - p[0]) / p[0])),
            lam * g[1] + d1 * (L + log((1 - p[1]) / p[1])),
            lam * g[2]]
    rng = max(gphi) - min(gphi)
    print("E. range of grad Phi(p*) =", mp.nstr(rng, 10), " (HLL (39): < 1.846843880121467e-17)")
    h2 = lambda t: -(t * log(t) + (1 - t) * log(1 - t))
    # (40): one-letter upper (sup over simplex of concave Phi <= Phi(p*) + range * max|p-p*|_1/2 <= Phi(p*)+range)
    one = lam * UB_print + d0 * (h2(p[0]) + p[0] * L) + d1 * (h2(p[1]) + p[1] * L) + rng
    Ms = mpf("0.1833045943206552249020")
    two = lam**2 * Ms + 2 * L * (d0 * p[0] + d1 * p[1]) - (1 - lam**2) * log(4)
    print("F. (40) recomputed =", mp.nstr(one, 20), " (HLL <= 0.30084186609915448)")
    print("F. (42) recomputed =", mp.nstr(two, 20), " (HLL >= 0.60168561432394163)")
    print("F. (43) gap two - 2*one =", mp.nstr(two - 2 * one, 15), " (HLL > 1.8821256327185490e-6)")
    print("F. with gamma (46) instead of (27) and UB=primal(19):",
          mp.nstr(lam**2 * gam + 2 * L * (d0 * p[0] + d1 * p[1]) - (1 - lam**2) * log(4)
                  - 2 * (lam * (IUY + IVZ - IUV) + d0 * (h2(p[0]) + p[0] * L) + d1 * (h2(p[1]) + p[1] * L) + rng), 12))


if __name__ == "__main__":
    HERE = os.path.dirname(os.path.abspath(__file__))
    main(sys.argv[1] if len(sys.argv) > 1 else None,
         sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, '..', 'hll_check.py'))
