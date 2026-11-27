# Reviewer check (2026-11-27, Claim 7): independent interval B&B certifying max (g+E) < TARGET
# for the NXY channel (mpmath.iv, 20 digits). Logs: bnb_110803.log, bnb_11078.log.
# Run: python3 indep_bnb.py [TARGET]   (default 1.10803; the note also quotes TARGET = 1.1078)
# Runtime: about 30-45 s (1.10803) and 60-70 s (1.1078). Needs mpmath.
"""Reviewer's independent interval branch-and-bound for  max_{p,q} [g(p,q) + E(p,q)]  (NXY channel).

Written from scratch (does not import the author's code).  Differences from certify_hk1_bound.py:
 * uses the exact piecewise g+E (line branch only where q <= 1-2p, f-branch where q >= 1-2p,
   max of both enclosures on straddling boxes) instead of the tangent line on all of p <= 1/2;
 * entropy enclosures: point values computed in interval arithmetic on X and 1-X, combined by
   monotonicity of h on [0,1/2],[1/2,1] and of phi(x) = -x log2 x on [0,1/e],[1/e,1];
 * every comparison that decides a monotone piece is done on exact mpf/dyadic numbers or falls
   back to the conservative branch.
g(p,q)   = h(s) - p(1-q),  s = q + (1-q) p/2
f(p,q)   = (2p-1) h(q) - 2p h((1+q)/2) + h(s) + p(1-q)
E(p,q)   = f(p,q)                          if p >= 1/2 or q >= 1-2p
         = f(p,0) + q*sigma(p)             otherwise, f(p,0) = h(p/2) - p, sigma(p) = f_q(p,1-2p)
sigma(p) = -phi(p)/2 - phi(1-2p) + (p-1) + 2(p-1)log2(1-p) + (1-p/2)log2(2-p)
Usage: python indep_bnb.py TARGET
"""
import heapq
import sys
import time
import mpmath as mp
from mpmath import iv

iv.dps = 20
mp.mp.dps = 20
LN2 = iv.log(2)
HALF = mp.mpf(1) / 2
TARGET = mp.mpf(sys.argv[1]) if len(sys.argv) > 1 else mp.mpf("1.10803")
E_LO, E_HI = mp.mpf("0.36787"), mp.mpf("0.36788")   # 1/e = 0.3678794...
assert E_LO < 1 / mp.e < E_HI
PHIMAX = 1 / (iv.e * LN2)


def lo_(x):
    return x.a if isinstance(x, iv.mpf) else x


def hi_(x):
    return x.b if isinstance(x, iv.mpf) else x


def phi_at(x):  # x an mpf/ivmpf point (possibly degenerate interval); returns interval
    X = iv.mpf(x)
    if X.b <= 0:
        return iv.mpf(0)
    if X.a <= 0:
        # tiny interval touching 0: phi in [0, phi(X.b)] if X.b < 1/e
        assert X.b < E_LO
        return iv.mpf([0, (-iv.mpf(X.b) * iv.log(iv.mpf(X.b)) / LN2).b])
    return -X * iv.log(X) / LN2


def phi_enc(a, b):
    """enclosure of phi on [a,b] (a,b points, possibly degenerate intervals)."""
    A, B = phi_at(a), phi_at(b)
    if iv.mpf(b).b <= E_LO:          # increasing piece
        return iv.mpf([A.a, B.b])
    if iv.mpf(a).a >= E_HI:          # decreasing piece
        return iv.mpf([B.a, A.b])
    return iv.mpf([min(A.a, B.a), PHIMAX.b])


def h_at(x):
    X = iv.mpf(x)
    return phi_at(X) + phi_at(1 - X)


def h_enc(a, b):
    """enclosure of h on [a,b], 0<=a<=b<=1 (a,b may be degenerate intervals)."""
    a = iv.mpf(a).a if iv.mpf(a).a > 0 else iv.mpf(0)
    b = iv.mpf(b).b if iv.mpf(b).b < 1 else iv.mpf(1)
    A, B = h_at(a), h_at(b)
    if iv.mpf(b).b <= HALF:
        return iv.mpf([A.a, B.b])
    if iv.mpf(a).a >= HALF:
        return iv.mpf([B.a, A.b])
    return iv.mpf([min(A.a, B.a), 1])


def s_enc(pl, ph, ql, qh):
    lo = iv.mpf(ql) + (1 - iv.mpf(ql)) * iv.mpf(pl) / 2
    hi = iv.mpf(qh) + (1 - iv.mpf(qh)) * iv.mpf(ph) / 2
    return lo.a, hi.b


def Ff_ub(pl, ph, ql, qh):
    """upper bound of g+f = 2h(s) + (2p-1)h(q) - 2p h((1+q)/2) on the box."""
    P = iv.mpf([pl, ph])
    sa, sb = s_enc(pl, ph, ql, qh)
    r_lo = ((1 + iv.mpf(ql)) / 2).a
    r_hi = ((1 + iv.mpf(qh)) / 2).b
    val = 2 * h_enc(sa, sb) + (2 * P - 1) * h_enc(ql, qh) - 2 * P * h_enc(r_lo, r_hi)
    return val.b


def sigma_enc(pl, ph):
    P = iv.mpf([pl, ph])
    u_lo = (1 - 2 * iv.mpf(ph)).a
    u_hi = (1 - 2 * iv.mpf(pl)).b
    u_lo = u_lo if u_lo > 0 else iv.mpf(0)
    return (-phi_enc(pl, ph) / 2 - phi_enc(u_lo, u_hi) + (P - 1)
            + 2 * (P - 1) * iv.log(1 - P) / LN2 + (1 - P / 2) * iv.log(2 - P) / LN2)


def L_ub(pl, ph, ql, qh):
    """upper bound of g + f(p,0) + q sigma(p) on the box (p <= 1/2)."""
    P = iv.mpf([pl, ph]); Q = iv.mpf([ql, qh])
    sa, sb = s_enc(pl, ph, ql, qh)
    val = (h_enc(sa, sb) - P * (1 - Q) + h_enc((iv.mpf(pl) / 2).a, (iv.mpf(ph) / 2).b) - P
           + Q * sigma_enc(pl, ph))
    return val.b


def ub(pl, ph, ql, qh):
    if pl >= HALF:
        return Ff_ub(pl, ph, ql, qh)
    assert ph <= HALF
    # region q >= 1-2p  <=> E = f ;  q <= 1-2p <=> E = line
    if ql >= 1 - 2 * pl:            # whole box in f-branch
        return Ff_ub(pl, ph, ql, qh)
    if qh <= 1 - 2 * ph:            # whole box in line-branch
        return L_ub(pl, ph, ql, qh)
    return max(Ff_ub(pl, ph, ql, qh), L_ub(pl, ph, ql, qh))


def main():
    t0 = time.time()
    heap = []
    for (pl, ph) in [(mp.mpf(0), HALF), (HALF, mp.mpf(1))]:
        u = ub(pl, ph, mp.mpf(0), mp.mpf(1))
        heapq.heappush(heap, (-u, pl, ph, mp.mpf(0), mp.mpf(1)))
    n = 0
    while True:
        negu, pl, ph, ql, qh = heap[0]
        if -negu < TARGET:
            break
        heapq.heappop(heap)
        n += 1
        if ph - pl >= qh - ql:
            m = (pl + ph) / 2
            kids = [(pl, m, ql, qh), (m, ph, ql, qh)]
        else:
            m = (ql + qh) / 2
            kids = [(pl, ph, ql, m), (pl, ph, m, qh)]
        for kb in kids:
            u = ub(*kb)
            heapq.heappush(heap, (-u, *kb))
        if n % 20000 == 0:
            print(f"  split {n}, max UB {mp.nstr(-heap[0][0], 12)}, live {len(heap)}, {time.time()-t0:.0f}s",
                  flush=True)
        if n > 3_000_000:
            print("giving up"); return
    print(f"CERTIFIED (reviewer B&B): max g+E <= {mp.nstr(-heap[0][0], 15)} < {TARGET}; "
          f"splits {n}, live {len(heap)}, {time.time()-t0:.0f}s")


if __name__ == "__main__":
    # point sanity versus float formula
    import math
    def hb(x):
        return 0.0 if x in (0.0, 1.0) else -x * math.log2(x) - (1 - x) * math.log2(1 - x)
    def gE(p, q):
        s = q + (1 - q) * p / 2
        g = hb(s) - p * (1 - q)
        if p >= 0.5 or q >= 1 - 2 * p:
            f = (2 * p - 1) * hb(q) - 2 * p * hb((1 + q) / 2) + hb(s) + p * (1 - q)
        else:
            sig = ((2 * p - 1) * math.log2(2 * p / (1 - 2 * p)) - p * math.log2(p / (1 - p))
                   + (1 - p / 2) * math.log2(p * (2 - p) / (1 - p) ** 2) - p)
            f = hb(p / 2) - p + q * sig
        return g + f
    for (p, q) in [(0.507829413, 0.436538150), (0.3, 0.2), (0.3, 0.6), (0.1, 0.05)]:
        e = mp.mpf(1) / 10 ** 9
        P_, Q_ = mp.mpf(p), mp.mpf(q)
        u = ub(P_, P_ + e, Q_, Q_ + e)
        print(f"  ({p},{q}): float g+E = {gE(p, q):.10f}, tiny-box UB = {mp.nstr(u, 12)}")
    main()
