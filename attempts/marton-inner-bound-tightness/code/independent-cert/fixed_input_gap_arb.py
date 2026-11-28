#!/usr/bin/env python3
"""Rigorous (python-flint arb) closing of HLL's fixed-input inequality (27):

    M_{T⊗2}(P*)  >=  V_lo  >  2 * UB(p*)  >=  2 M_T(p*),

with UB(p*) = alpha H_{p*}(Y) + abar H_{p*}(Z) + B - a.p*  and B any certified upper bound on
B_T = max G (from bnb_rigorous.py).  Two-letter side: the explicit rational law of HLL Appendix A
(51 rows, denominators 10^12; reused from ../hll_check.py TABLE), W = (Q, Wc), P(Q=0) = mu with mu
HLL's printed decimal 0.28950945961978169531 read as an exact rational (any mu in [0,1] gives a
valid lower bound, since I(Q,Wc;Y) >= I(Wc;Y|Q) and the conditional terms average exactly over Q):
    M_{T⊗2}(P*) >= min( sum_q mu_q A_q , sum_q mu_q B_q ),
    A_q = I(Wc;Y^2|Q=q) + J_q,  B_q = I(Wc;Z^2|Q=q) + J_q,
    J_q = I(U;Y^2|Wc,Q=q) + I(V;Z^2|Wc,Q=q) - I(U;V|Wc,Q=q).
Also re-checks HLL (26) exactly: both coordinate marginals of each component equal p*.

Usage: python -I fixed_input_gap_arb.py
"""
import os
import re
import sys
from fractions import Fraction as Fr

from flint import arb, ctx, fmpq

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import model as M  # noqa: E402

ctx.prec = 200


def A(q):
    q = Fr(q)
    return arb(fmpq(q.numerator, q.denominator))


def H(vals):
    s = arb(0)
    for t in vals:
        if t != 0:
            s += -(t * t.log())
    return s


def marg(j, key):
    out = {}
    for k, v in j.items():
        kk = key(k)
        out[kk] = out.get(kk, 0) + v
    return out


def load_table():
    rows = []
    pat = re.compile(r'^\s*\((\d), (\d), (\d), (\d), "(\d)(\d)", (\d+)\),')
    for line in open(os.path.join(HERE, "..", "hll_check.py"), encoding="utf-8"):
        m = pat.match(line)
        if m:
            rows.append(tuple(int(m.group(i)) for i in range(1, 8)))
    assert len(rows) == 51
    return rows


def main(B_str=None):
    rows = load_table()
    pst = [x * 10**12 for x in M.PSTAR]
    comp = {}
    for q in (0, 1):
        R = [r for r in rows if r[0] == q]
        assert sum(r[6] for r in R) == 10**12
        m1 = [sum(r[6] for r in R if r[4] == x) for x in range(3)]
        m2 = [sum(r[6] for r in R if r[5] == x) for x in range(3)]
        assert m1 == pst and m2 == pst, (m1, m2)
        comp[q] = R
    print("(26) exact: both coordinate marginals of both components equal p*  -> OK")
    TY = [[A(x) for x in r] for r in M.TY]
    TZ = [[A(x) for x in r] for r in M.TZ]
    vals = {}
    for q in (0, 1):
        jY, jZ = {}, {}
        for (_, wc, u, v, x1, x2, n) in comp[q]:
            p = A(Fr(n, 10**12))
            for a in range(3):
                for b in range(3):
                    k = (wc, u, v, a, b)
                    jY[k] = jY.get(k, arb(0)) + p * TY[x1][a] * TY[x2][b]
                    jZ[k] = jZ.get(k, arb(0)) + p * TZ[x1][a] * TZ[x2][b]
        Hm = lambda j, f: H(marg(j, f).values())
        HW = Hm(jY, lambda k: k[0])
        HY, HZ = Hm(jY, lambda k: k[3:]), Hm(jZ, lambda k: k[3:])
        HWY, HWZ = Hm(jY, lambda k: (k[0],) + k[3:]), Hm(jZ, lambda k: (k[0],) + k[3:])
        HWU, HWV = Hm(jY, lambda k: k[:2]), Hm(jY, lambda k: (k[0], k[2]))
        HWUY = Hm(jY, lambda k: k[:2] + k[3:])
        HWVZ = Hm(jZ, lambda k: (k[0], k[2]) + k[3:])
        HWUV = Hm(jY, lambda k: k[:3])
        IWY, IWZ = HY - (HWY - HW), HZ - (HWZ - HW)
        J = ((HWY - HW) - (HWUY - HWU)) + ((HWZ - HW) - (HWVZ - HWV)) - ((HWU - HW) + (HWV - HW) - (HWUV - HW))
        vals[q] = (IWY + J, IWZ + J)
        print(f"q={q}: A_q = {vals[q][0].str(25)}  B_q = {vals[q][1].str(25)}")
    mu = A(Fr("0.28950945961978169531"))
    LA = mu * vals[0][0] + (1 - mu) * vals[1][0]
    LB = mu * vals[0][1] + (1 - mu) * vals[1][1]
    Vlo = min(LA.lower(), LB.lower(), key=lambda x: x.mid())
    print("mixture endpoints:", LA.str(25), LB.str(25))
    print("V_lo (rigorous lower bound on M_{T⊗2}(P*)) =", Vlo.str(25))
    pY = [sum(M.PSTAR[x] * M.TY[x][y] for x in range(3)) for y in range(3)]
    pZ = [sum(M.PSTAR[x] * M.TZ[x][z] for x in range(3)) for z in range(3)]
    ap = sum(M.AVEC[x] * M.PSTAR[x] for x in range(3))
    base = A(M.ALPHA) * H([A(t) for t in pY]) + A(M.ABAR) * H([A(t) for t in pZ]) - A(ap)
    import bnb_rigorous as BR
    T5 = BR.compute_target()
    for label, B in [("B = T5 (HLL-level target, bnb_rigorous default)", T5),
                     ("B = G(19)+1e-12 (sharpened run)", Fr(-10647134094417738503, 10**19))]:
        UB = (base + A(B)).upper()
        gap = (Vlo - 2 * UB)
        print(f"{label}: UB(p*) <= {UB.str(22)} ; V_lo - 2 UB >= {gap.lower().str(15)}  positive: {gap.lower() > 0}")


if __name__ == "__main__":
    main()
