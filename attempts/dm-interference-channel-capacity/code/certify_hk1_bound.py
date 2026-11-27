"""Computer-assisted certificate:  max_{R_HK^(1)} (2 R1 + R2) < 1.10803 for the NXY binary CZI channel.

Chain (see the attempt file, Claim D3):
  max_{R_HK}(2R1+R2) <= max_{p,q} [ g(p,q) + E(p,q) ],  where
  g(p,q) = I(X1,X2;Y1) = hb(s) - p(1-q),  s = q + (1-q)p/2,
  E(p,.) = any concave majorant of f(p,.)  (NXY Lemma 1; we use the NXY Lemma 2 envelope,
           whose correctness is re-proved in the attempt: f_qq sign + exact tangency identity).
On {p >= 1/2} or {q >= 1-2p}:   g + E = F_f := 2 hb(s) + (2p-1) hb(q) - 2p hb((1+q)/2).
For p <= 1/2 and all q:          g + E <= F_l := hb(s) - p(1-q) + hb(p/2) - p + q*slope(p),
   slope(p) = -phi(p)/2 - phi(1-2p) + (p-1) + 2(p-1)log2(1-p) + (1-p/2)log2(2-p),  phi(x) = -x log2 x
   (F_l uses the tangent line at q = 1-2p, which majorises the concave E everywhere).
Interval arithmetic: mpmath.iv (outward rounding); hb and phi are bounded via their exact monotone pieces.
Branch-and-bound on boxes of [0,1]^2 (split at p = 1/2) until every box has upper bound < TARGET.
"""
import heapq
import sys
import time
import mpmath as mp
from mpmath import iv

iv.dps = 30
mp.mp.dps = 30
LN2 = iv.log(iv.mpf(2))
TARGET = mp.mpf(sys.argv[1]) if len(sys.argv) > 1 else mp.mpf("1.10803")


def log2i(x):
    return iv.log(x) / LN2


def phi_pt(x):
    """-x log2 x at a point (x given as an mpf in [0,1]); returns an iv interval."""
    if x <= 0:
        return iv.mpf(0)
    X = iv.mpf(x)
    return -X * log2i(X)


INV_E_LO, INV_E_HI = mp.mpf("0.3678"), mp.mpf("0.3679")   # 1/e = 0.367879...
PHI_MAX = iv.mpf(1) / (iv.e * LN2)                          # max of phi = 1/(e ln 2)


def phi_rng(a, b):
    """Rigorous enclosure of {-x log2 x : x in [a,b]}, 0 <= a <= b <= 1."""
    A, B = phi_pt(a), phi_pt(b)
    if b <= INV_E_LO:           # increasing
        return iv.mpf([A.a, B.b])
    if a >= INV_E_HI:           # decreasing
        return iv.mpf([B.a, A.b])
    return iv.mpf([min(A.a, B.a), PHI_MAX.b])


def hb_pt(x):
    return phi_pt(x) + phi_pt(1 - x) if 0 < x < 1 else iv.mpf(0)


def hb_rng(a, b):
    """Rigorous enclosure of hb on [a,b] (increasing on [0,1/2], decreasing on [1/2,1])."""
    A, B = hb_pt(a), hb_pt(b)
    if b <= 0.5:
        return iv.mpf([A.a, B.b])
    if a >= 0.5:
        return iv.mpf([B.a, A.b])
    return iv.mpf([min(A.a, B.a), 1])


def s_pt(p, q):
    return q + (1 - q) * p / 2      # exact in mpf up to rounding; widened below


def s_rng(pl, ph, ql, qh):
    # s is nondecreasing in p and increasing in q on [0,1]^2
    lo = iv.mpf(ql) + (1 - iv.mpf(ql)) * iv.mpf(pl) / 2
    hi = iv.mpf(qh) + (1 - iv.mpf(qh)) * iv.mpf(ph) / 2
    return max(mp.mpf(0), lo.a), min(mp.mpf(1), hi.b)


def ub_Ff(pl, ph, ql, qh):
    P = iv.mpf([pl, ph]);
    sl, sh = s_rng(pl, ph, ql, qh)
    t1 = 2 * hb_rng(sl, sh)
    t2 = (2 * P - 1) * hb_rng(ql, qh)
    rl = (1 + iv.mpf(ql)) / 2; rh = (1 + iv.mpf(qh)) / 2
    t3 = -2 * P * hb_rng(rl.a, min(mp.mpf(1), rh.b))
    return (t1 + t2 + t3).b


def slope_rng(pl, ph):
    P = iv.mpf([pl, ph])
    t = -phi_rng(pl, ph) / 2
    ul = 1 - 2 * iv.mpf(ph); uh = 1 - 2 * iv.mpf(pl)
    t = t - phi_rng(max(mp.mpf(0), ul.a), min(mp.mpf(1), uh.b))
    t = t + (P - 1) + 2 * (P - 1) * log2i(1 - P) + (1 - P / 2) * log2i(2 - P)
    return t


def ub_Fl(pl, ph, ql, qh):
    P = iv.mpf([pl, ph]); Q = iv.mpf([ql, qh])
    sl, sh = s_rng(pl, ph, ql, qh)
    t = hb_rng(sl, sh) - P * (1 - Q)
    hl = iv.mpf(pl) / 2; hh = iv.mpf(ph) / 2
    t = t + hb_rng(hl.a, hh.b) - P + Q * slope_rng(pl, ph)
    return t.b


def ub_box(pl, ph, ql, qh):
    if pl >= 0.5:
        return ub_Ff(pl, ph, ql, qh)
    # here ph <= 1/2 (initial split at p = 1/2)
    fl = ub_Fl(pl, ph, ql, qh)
    if ql >= 1 - 2 * pl:              # whole box inside {q >= 1-2p}: E = f there
        return min(fl, ub_Ff(pl, ph, ql, qh))
    return fl


def F_point(p, q):
    """Float-ish point value of g+E (lower bound bookkeeping only)."""
    p = mp.mpf(p); q = mp.mpf(q)
    P = iv.mpf(p); Q = iv.mpf(q)
    if p >= 0.5 or q >= 1 - 2 * p:
        return mp.mpf((2 * hb_pt(s_pt(p, q)) + (2 * P - 1) * hb_pt(q) - 2 * P * hb_pt((1 + q) / 2)).mid)
    return mp.mpf((hb_pt(s_pt(p, q)) - P * (1 - Q) + hb_pt(p / 2) - P
                   + Q * slope_rng(p, p)).mid)


def main():
    t0 = time.time()
    half = mp.mpf("0.5")
    heap = []
    for (pl, ph) in [(mp.mpf(0), half), (half, mp.mpf(1))]:
        heapq.heappush(heap, (-ub_box(pl, ph, mp.mpf(0), mp.mpf(1)), pl, ph, mp.mpf(0), mp.mpf(1)))
    nbox = 0
    best_lb = mp.mpf(0)
    while True:
        negub, pl, ph, ql, qh = heapq.heappop(heap)
        ub = -negub
        if ub < TARGET:
            heapq.heappush(heap, (negub, pl, ph, ql, qh))
            break
        nbox += 1
        pm = (pl + ph) / 2; qm = (ql + qh) / 2
        best_lb = max(best_lb, F_point(pm, qm))
        if (ph - pl) >= (qh - ql):
            kids = [(pl, pm, ql, qh), (pm, ph, ql, qh)]
        else:
            kids = [(pl, ph, ql, qm), (pl, ph, qm, qh)]
        for k in kids:
            heapq.heappush(heap, (-ub_box(*k), *k))
        if nbox % 20000 == 0:
            print(f"  boxes split: {nbox}, current max UB = {mp.nstr(-heap[0][0], 10)}, "
                  f"best point value = {mp.nstr(best_lb, 10)}, live boxes = {len(heap)}, "
                  f"{time.time()-t0:.0f}s", flush=True)
    print(f"CERTIFIED: max_(p,q) [g+E] <= {mp.nstr(-heap[0][0], 12)} < TARGET = {TARGET}")
    print(f"  boxes split: {nbox}; live boxes: {len(heap)}; best point value found = {mp.nstr(best_lb, 12)}; "
          f"time {time.time()-t0:.1f}s")


if __name__ == "__main__":
    # consistency check of the rewritten slope against the direct derivative formula
    import numpy as np
    from czi_common import fq_at_tangent, F as Ffloat
    for p in [0.05, 0.2, 0.33, 0.45]:
        a = float(slope_rng(mp.mpf(p), mp.mpf(p)).mid); b = fq_at_tangent(p)
        print(f"slope check p={p}: {a:.12f} vs {b:.12f}")
    for (p, q) in [(0.3, 0.1), (0.3, 0.7), (0.6, 0.4), (0.50785, 0.43655)]:
        print(f"F check {p},{q}: {float(F_point(p, q)):.12f} vs {Ffloat(p, q):.12f}")
    main()
