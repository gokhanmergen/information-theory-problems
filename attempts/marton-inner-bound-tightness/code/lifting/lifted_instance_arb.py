#!/usr/bin/env python3
"""Rigorous re-certification of the explicit lifted instance of Huang-Liu-Liu [HLL],
arXiv:2608.19869v1, Sec. III-D, eqs. (30)-(43).

Every decision below is either an exact-rational (fractions.Fraction) identity/inequality or a
comparison of python-flint/Arb balls (``a < b`` is True only if it holds for every point of both
balls).  Floats never enter a decision.  All quantities are in nats.

What is certified (numbering = HLL's):
  (30)/(32)  lambda + delta0 + delta1 = 1 exactly, all positive; N = 2^M, L = M ln 2 = ln N.
  (36)/(37)  the gradient of UB at p* equals b + nu*1 + rho with range(rho) < 4.692109048907095e-22.
  (39)       range of grad Phi(p*) (Phi of (38), weights (32)) < 1.846843880121467e-17;
             we compute grad Phi(p*) directly, not via b.
  (40)       M_{T~} <= lambda*U + delta0[h2(p0)+p0 L] + delta1[h2(p1)+p1 L] + eps
             <= 0.30084186609915448, for U = printed (25), and for U = f_T(p*) with
             T in {T5, T12} the certified upper bounds on B_T (independent-cert/results_*.json).
  (42)       lambda^2 M* + 2L(delta0 p0 + delta1 p1) - (1-lambda^2) ln 4 >= 0.60168561432394163,
             with M* >= our own exact evaluation of M_{T(x)2}(P*) (W = (Q,Wc) as one variable).
  (43)       the gap >= 1.88e-6 (and the printed 1.8821256327185490e-6), both in the
             "direct" form (huge L-terms present) and in the L-free cancelled form.
  Also: the same chain with the exact C = I(U;V|W) in place of ln 4 (a sharper, still valid
  bound), and the ideal Theorem-2 weights for comparison with the rational weights (32).

Mathematical justification of each inequality: see the attempt file
attempts/marton-inner-bound-tightness/2026-11-27-claude-opus-5-5-lifting-verification.md.

Usage:  python -I lifted_instance_arb.py
"""
import json
import os
import re
import sys
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))
CERT = os.path.join(HERE, "..", "independent-cert")
sys.path.insert(0, CERT)
import model as MD  # noqa: E402  exact constants of HLL (14)-(17), cross-checked with hll_check.py
import fixed_input_gap_arb as FG  # noqa: E402  (only load_table: the 51-row Appendix-A table)

from flint import arb, ctx, fmpq  # noqa: E402

ctx.prec = 320   # set after importing FG (which sets 200 at import time)

FAILS = []


def check(cond, msg):
    """cond must be a Python bool produced by exact Fraction logic or an Arb ball comparison."""
    assert isinstance(cond, bool)
    print(("PASS  " if cond else "FAIL  ") + msg)
    if not cond:
        FAILS.append(msg)


def A(q):
    q = Fr(q)
    return arb(fmpq(q.numerator, q.denominator))


def ln(q):
    """Arb enclosure of ln(q) for an exact positive rational q."""
    q = Fr(q)
    assert q > 0
    return A(q).log()


def H(probs):
    """Entropy (nats) of a list of exact nonnegative rationals, as an Arb ball."""
    s = arb(0)
    for t in probs:
        t = Fr(t)
        assert t >= 0
        if t:
            s -= A(t) * ln(t)
    return s


def h2(p):
    return H([Fr(p), 1 - Fr(p)])


def up(x):
    return x.upper()


def lo(x):
    return x.lower()


def s(x, n=25):
    return x.str(n, radius=True)


# ----------------------------------------------------------------------------- constants
# HLL (30): M = 2,000,000, N = 2^M, L = M log 2.
MEXP = 2_000_000
# HLL (32): exact rational weights, common denominator 10^23.
LAM = Fr(99999977198527428838942, 10**23)
D0 = Fr(20970790337007940, 10**23)
D1 = Fr(1830682234153118, 10**23)
# HLL (36), (37), (39), (40), (42), (43) printed values.
B1 = Fr("0.26533808894270830145")
B2 = Fr("0.29071676800873404161")
RHO_RANGE_37 = Fr("4.692109048907095e-22")
EPS_39 = Fr("1.846843880121467e-17")
UB40 = Fr("0.30084186609915448")
LB42 = Fr("0.60168561432394163")
GAP43 = Fr("1.8821256327185490e-6")
GAP43_ABSTRACT = Fr("1.88e-6")
UB25 = Fr(MD.UB25_S)
MU = Fr("0.28950945961978169531")   # HLL's printed mu, read as an exact rational (any mu in [0,1] is valid)

T5_CONST = Fr(-532356454721386925147158010951, 5 * 10**29)
T12_CONST = Fr(-10647134094417738503, 10**19)


def crosscheck_hll_check():
    """Reuse: the weights (32) and the mu used here equal those in ../hll_check.py."""
    src = open(os.path.join(HERE, "..", "hll_check.py"), encoding="utf-8").read()
    lam = int(re.search(r"lam = mpf\((\d+)\) / mpf\(10\) \*\* 23", src).group(1))
    d0 = int(re.search(r"d0 = mpf\((\d+)\) / mpf\(10\) \*\* 23", src).group(1))
    d1 = int(re.search(r"d1 = mpf\((\d+)\) / mpf\(10\) \*\* 23", src).group(1))
    mu = re.search(r'MU = "([0-9.]+)"', src).group(1)
    return Fr(lam, 10**23) == LAM and Fr(d0, 10**23) == D0 and Fr(d1, 10**23) == D1 and Fr(mu) == MU


def load_target(fname, expect):
    d = json.load(open(os.path.join(CERT, fname), encoding="utf-8"))
    T = Fr(d["T"])
    jobs = d["results"]
    ok = (T == expect and len(jobs) == 29 and all(j["certified"] for j in jobs)
          and len({j["job"] for j in jobs}) == 29)
    return T, ok


# ----------------------------------------------------------------------------- two-letter side
def two_letter_values():
    """Our own exact evaluation of the HLL Appendix-A law with W = (Q, Wc) as ONE variable.

    Returns Arb balls (M*, C, V_mix) with
      M* = min{I(W;Y^2), I(W;Z^2)} + I(U;Y^2|W) + I(V;Z^2|W) - I(U;V|W)   (exact functional (2)),
      C  = I(U;V|W),
      V_mix = HLL's mixture lower bound min_t sum_q mu_q L_t(P_q)  (drops I(Q;Y^2), I(Q;Z^2)).
    Joint probabilities are exact rationals; Arb is used only for logarithms.
    """
    rows = FG.load_table()
    pq = {0: MU, 1: 1 - MU}
    # exact checks: each component sums to 1; HLL (26): both coordinate marginals equal p*
    margs_ok = True
    for q in (0, 1):
        R = [r for r in rows if r[0] == q]
        if sum(Fr(r[6], 10**12) for r in R) != 1:
            margs_ok = False
        for c in (4, 5):
            m = [sum(Fr(r[6], 10**12) for r in R if r[c] == x) for x in range(3)]
            if m != MD.PSTAR:
                margs_ok = False
    check(margs_ok, "Appendix-A components are probability laws with both X-marginals = p* exactly (HLL (26) => (13))")

    def joint(T):
        """exact joint of (q, wc, u, v, y1, y2) under channel T on both coordinates."""
        j = {}
        for (q, wc, u, v, x1, x2, n) in rows:
            p = pq[q] * Fr(n, 10**12)
            for a in range(3):
                for b in range(3):
                    k = (q, wc, u, v, a, b)
                    j[k] = j.get(k, 0) + p * T[x1][a] * T[x2][b]
        return j

    def Hm(j, f, cond=None):
        m = {}
        for k, v in j.items():
            if cond is not None and k[0] != cond:
                continue
            kk = f(k)
            m[kk] = m.get(kk, 0) + v
        tot = sum(m.values())
        return H([v / tot for v in m.values()])

    jY, jZ = joint(MD.TY), joint(MD.TZ)
    # W = (q, wc)  -> key[:2];  U -> key[2];  V -> key[3];  output -> key[4:]
    W = lambda k: k[:2]
    HW = Hm(jY, W)
    IWY = Hm(jY, lambda k: k[4:]) + HW - Hm(jY, lambda k: k[:2] + k[4:])
    IWZ = Hm(jZ, lambda k: k[4:]) + HW - Hm(jZ, lambda k: k[:2] + k[4:])
    HWU, HWV = Hm(jY, lambda k: k[:3]), Hm(jY, lambda k: k[:2] + (k[3],))
    HWUV = Hm(jY, lambda k: k[:4])
    IUY_W = (Hm(jY, lambda k: k[:2] + k[4:]) - HW) - (Hm(jY, lambda k: k[:3] + k[4:]) - HWU)
    IVZ_W = (Hm(jZ, lambda k: k[:2] + k[4:]) - HW) - (Hm(jZ, lambda k: k[:2] + (k[3],) + k[4:]) - HWV)
    C = HWU + HWV - HWUV - HW
    rest = IUY_W + IVZ_W - C
    LY, LZ = IWY + rest, IWZ + rest            # L_0 and L_1 of (3) at P*
    Mstar_lo = min(lo(LY), lo(LZ), key=lambda x: x.mid())

    # HLL's mixture bound: per-component A_q, B_q, then mu-mixture (eq. (49))
    comp = {}
    for q in (0, 1):
        Wc = lambda k: k[1]
        hW = Hm(jY, Wc, q)
        iwy = Hm(jY, lambda k: k[4:], q) + hW - Hm(jY, lambda k: (k[1],) + k[4:], q)
        iwz = Hm(jZ, lambda k: k[4:], q) + hW - Hm(jZ, lambda k: (k[1],) + k[4:], q)
        hwu, hwv = Hm(jY, lambda k: k[1:3], q), Hm(jY, lambda k: (k[1], k[3]), q)
        hwuv = Hm(jY, lambda k: k[1:4], q)
        iuy = (Hm(jY, lambda k: (k[1],) + k[4:], q) - hW) - (Hm(jY, lambda k: k[1:3] + k[4:], q) - hwu)
        ivz = (Hm(jZ, lambda k: (k[1],) + k[4:], q) - hW) - (Hm(jZ, lambda k: (k[1], k[3]) + k[4:], q) - hwv)
        cq = hwu + hwv - hwuv - hW
        comp[q] = (iwy + iuy + ivz - cq, iwz + iuy + ivz - cq, cq, iwy, iwz)
    VA = A(MU) * comp[0][0] + A(1 - MU) * comp[1][0]
    VB = A(MU) * comp[0][1] + A(1 - MU) * comp[1][1]
    Vmix_lo = min(lo(VA), lo(VB), key=lambda x: x.mid())
    Cmix = A(MU) * comp[0][2] + A(1 - MU) * comp[1][2]
    return dict(LY=LY, LZ=LZ, Mstar_lo=Mstar_lo, C=C, Cmix=Cmix, comp=comp, Vmix_lo=Vmix_lo,
                IWY=IWY, IWZ=IWZ)


# ----------------------------------------------------------------------------- main
def main():
    print(f"python-flint Arb, working precision {ctx.prec} bits; all logs natural (nats)\n")
    print("== exact-rational checks ==")
    check(MD.CROSSCHECKED, "HLL (14)-(17) constants identical to ../hll_check.py (model.py cross-check)")
    check(crosscheck_hll_check(), "weights (32) and mu identical to ../hll_check.py")
    check(LAM + D0 + D1 == 1, "(32): lambda + delta0 + delta1 == 1 exactly")
    check(LAM > 0 and D0 > 0 and D1 > 0 and LAM < 1, "(32): 0 < lambda < 1, delta0 > 0, delta1 > 0")
    check(sum(MD.PSTAR) == 1 and min(MD.PSTAR) > 0, "(16): p* is a probability vector with full support (relative interior)")
    check(all(sum(r) == 1 and min(r) > 0 for M in (MD.TY, MD.TZ) for r in M),
          "(14),(15): every channel row sums to 1 exactly and is strictly positive")
    T5, ok5 = load_target("results_T5.json", T5_CONST)
    T12, ok12 = load_target("results_1e-12.json", T12_CONST)
    check(ok5, f"independent-cert/results_T5.json: 29/29 jobs certified, T = {T5}")
    check(ok12, f"independent-cert/results_1e-12.json: 29/29 jobs certified, T = {T12}")

    p0, p1, p2 = MD.PSTAR
    al, ab, a = MD.ALPHA, MD.ABAR, MD.AVEC
    qY = [sum(MD.PSTAR[x] * MD.TY[x][y] for x in range(3)) for y in range(3)]
    qZ = [sum(MD.PSTAR[x] * MD.TZ[x][z] for x in range(3)) for z in range(3)]
    ap = sum(a[x] * MD.PSTAR[x] for x in range(3))

    print("\n== L = M ln 2 = ln N, N = 2^M, M = 2,000,000 ==")
    L = arb(MEXP) * arb(2).log()
    print("   L =", s(L, 30))
    Aw = {0: L + ln((1 - p0) / p0), 1: L + ln((1 - p1) / p1)}
    check(lo(Aw[0]) > 0 and lo(Aw[1]) > 0, "A_i(L) = L + ln((1-p_i)/p_i) > 0 for i = 0,1 (Thm 2 'L large enough')")

    print("\n== gradient of UB at p* (HLL (36)-(37)) ==")
    # UB(p) = al*H(T_Y^T p) + ab*H(T_Z^T p) + B - a.p ;  dH(T^T p)/dp_x = -sum_y T[x][y] (1 + ln q_y)
    lnqY, lnqZ = [ln(t) for t in qY], [ln(t) for t in qZ]
    g = []
    for x in range(3):
        gx = arb(0)
        for y in range(3):
            gx -= A(al) * A(MD.TY[x][y]) * (1 + lnqY[y])
            gx -= A(ab) * A(MD.TZ[x][y]) * (1 + lnqZ[y])
        g.append(gx - A(a[x]))
    for x in range(3):
        print(f"   dUB/dp_{x} = {s(g[x], 30)}")
    rho = [g[0] - 0, g[1] - A(B1), g[2] - A(B2)]          # = nu*1 + rho, nu := g_0
    rr = max(up(rho[i] - rho[j]) for i in range(3) for j in range(3) if i != j)
    print("   range(grad UB - b) <=", s(rr, 16))
    check(rr < A(RHO_RANGE_37), "(37): max rho - min rho < 4.692109048907095e-22")
    check(g[2] - g[1] > 0 and g[1] - g[0] > 0, "(36): coordinate 2 carries the largest supergradient entry (r = 2)")

    print("\n== Theorem-2 ideal weights from the exact gradient (comparison only) ==")
    gr = [g[2] - g[0], g[2] - g[1]]
    lam_id = 1 / (1 + gr[0] / Aw[0] + gr[1] / Aw[1])
    d_id = [lam_id * gr[0] / Aw[0], lam_id * gr[1] / Aw[1]]
    print("   lambda_L =", s(lam_id, 25), "  (32):", s(A(LAM), 25))
    print("   delta0_L =", s(d_id[0], 25), "  (32):", s(A(D0), 25))
    print("   delta1_L =", s(d_id[1], 25), "  (32):", s(A(D1), 25))

    print("\n== gradient range of Phi at p* (HLL (38)-(39)), computed directly ==")
    gphi = [A(LAM) * g[0] + A(D0) * Aw[0], A(LAM) * g[1] + A(D1) * Aw[1], A(LAM) * g[2]]
    eps = max(up(gphi[i] - gphi[j]) for i in range(3) for j in range(3) if i != j)
    for x in range(3):
        print(f"   dPhi/dp_{x} = {s(gphi[x], 30)}")
    print("   eps_ours := range(grad Phi(p*)) <=", s(eps, 16))
    check(eps < A(EPS_39), "(39): range of grad Phi(p*) < 1.846843880121467e-17")
    check(eps > 0, "eps_ours is a (positive) upper bound; used in place of (39) below")

    print("\n== one-letter side (HLL (40)) ==")
    base = A(al) * H(qY) + A(ab) * H(qZ) - A(ap)           # UB(p*) - B_T
    shaping = A(D0) * (h2(p0) + A(p0) * L) + A(D1) * (h2(p1) + A(p1) * L)
    Us = {}
    for lab, T in (("T5", T5), ("T12", T12)):
        Us[lab] = up(base + A(T))
        print(f"   f_{lab}(p*) = alpha H(Y*) + abar H(Z*) + {lab} - a.p* <= {s(Us[lab], 25)}")
    check(Us["T5"] <= A(UB25), "UB(p*) <= f_T5(p*) <= printed (25)  [B_T < T5 is independent-cert Claim 2]")
    U1 = {}
    for lab, U in (("(25)", A(UB25)), ("T5", Us["T5"]), ("T12", Us["T12"])):
        U1[lab] = up(A(LAM) * U + shaping + eps)
        print(f"   U = {lab:5s}: M_T~ <= lambda U + shaping + eps <= {s(U1[lab], 22)}")
    check(U1["(25)"] <= A(UB40), "(40): M_T~ <= 0.30084186609915448 with U = printed (25)")
    check(U1["T5"] <= A(UB40), "(40): M_T~ <= 0.30084186609915448 with U = f_T5(p*)")
    print(f"   [eps_ours vs printed eps (39): bound with printed eps = "
          f"{s(up(A(LAM) * A(UB25) + shaping + A(EPS_39)), 22)}]")

    print("\n== two-letter side (HLL (41)-(42)) ==")
    tl = two_letter_values()
    print("   exact functional at P*: L_0 =", s(tl["LY"]), " L_1 =", s(tl["LZ"]))
    print("   M*  = M_{T(x)2}(P*) >=", s(tl["Mstar_lo"]))
    print("   HLL mixture bound (49), gamma >=", s(tl["Vmix_lo"]))
    IQY = tl["IWY"] - (A(MU) * tl["comp"][0][3] + A(1 - MU) * tl["comp"][1][3])
    IQZ = tl["IWZ"] - (A(MU) * tl["comp"][0][4] + A(1 - MU) * tl["comp"][1][4])
    print("   I(Q;Y^2) =", s(IQY, 8), "  I(Q;Z^2) =", s(IQZ, 8), " (dropped by HLL (49))")
    print("   C = I(U;V|W) =", s(tl["C"]), "  (mixture of components:", s(tl["Cmix"]), ")")
    check(tl["Mstar_lo"] >= tl["Vmix_lo"], "exact M_{T(x)2}(P*) >= HLL's mixture bound gamma (dropping I(Q;.) >= 0)")
    check(tl["Vmix_lo"] > A(Fr("0.183304594320655224901767")) - A(Fr(1, 10**24)) and
          tl["Vmix_lo"] < A(Fr("0.183304594320655224901768")),
          "mixture bound reproduces HLL (46) gamma = 0.183304594320655224901767...")
    check(up(tl["C"]) < ln(4), "C = I(U;V|W) <= ln 4 (|U| = |V| = 4), as used in (41)")
    Mst = tl["Mstar_lo"]
    lam2 = A(LAM) ** 2
    labels = 2 * L * (A(D0) * A(p0) + A(D1) * A(p1))
    R2 = lo(lam2 * Mst + labels - (1 - lam2) * ln(4))
    R2g = lo(lam2 * tl["Vmix_lo"] + labels - (1 - lam2) * ln(4))
    R2C = lo(lam2 * Mst + labels - (1 - lam2) * tl["C"])
    print("   (42) with M* (ours), ln 4  : M_T~(x)2 >=", s(R2, 22))
    print("   (42) with gamma (HLL), ln 4: M_T~(x)2 >=", s(R2g, 22))
    print("   (42) with M*, exact C      : M_T~(x)2 >=", s(R2C, 22))
    check(R2g >= A(LB42), "(42): lambda^2 gamma + 2L(d0 p0 + d1 p1) - (1-lambda^2) ln 4 >= 0.60168561432394163")
    check(R2 >= A(LB42), "(42) also with our exact M*")

    print("\n== the gap (HLL (43)) ==")
    rows = []
    for lab_u in ("(25)", "T5", "T12"):
        for lab_l, R in (("gamma,ln4", R2g), ("M*,ln4", R2), ("M*,C", R2C)):
            gap = lo(R - 2 * U1[lab_u])
            rows.append((lab_u, lab_l, gap))
            print(f"   U = {lab_u:5s}, two-letter = {lab_l:9s}: M_T~(x)2 - 2 M_T~ >= {s(gap, 20)}")
    # L-free cancelled form for the HLL chain (U = (25), gamma, ln 4)
    canc = lo(lam2 * tl["Vmix_lo"] - 2 * A(LAM) * A(UB25) - 2 * A(D0) * h2(p0) - 2 * A(D1) * h2(p1)
              - (1 - lam2) * ln(4) - 2 * eps)
    print("   cancelled form (53) [no L terms], U = (25), gamma, ln 4: gap >=", s(canc, 20))
    g_hll = rows[0][2]
    check(g_hll > A(GAP43_ABSTRACT), "(43): gap > 1.88e-6 (HLL's chain: U = (25), gamma, ln 4, our eps)")
    check(canc > A(GAP43_ABSTRACT), "(43) via the L-free cancelled form")
    print("   |direct - cancelled| =", s(abs(canc - g_hll), 5))
    check(g_hll > A(GAP43), "(43): gap > 1.8821256327185490e-6 exactly as printed (with our smaller eps)")
    gap_printed_eps = lo(R2g - 2 * (A(LAM) * A(UB25) + shaping + A(EPS_39)))
    print("   with HLL's printed eps (39) instead of eps_ours: gap >=", s(gap_printed_eps, 20))
    check(gap_printed_eps > A(GAP43_ABSTRACT), "(43) > 1.88e-6 also with printed eps (39)")
    print("   printed (42) - 2 * printed (40) =", s(A(LB42) - 2 * A(UB40), 20),
          " (note: below printed (43) by ~4.6e-17; (43) was computed from unrounded values)")
    check(min(r[2] for r in rows) > A(GAP43_ABSTRACT), "all nine (U, two-letter) combinations give gap > 1.88e-6")

    print()
    if FAILS:
        print(f"{len(FAILS)} FAILURE(S):")
        for f in FAILS:
            print("   ", f)
        sys.exit(1)
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()
