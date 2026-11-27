"""Certify  max-sum-rate(R_CL^(1)(W)) < max-sum-rate(R_CL^(2)(W))  for the Bross-Lapidoth binary MAC W_q.

(1) k=2 LOWER bound: the saved k=2 distribution (from opt_cl.py) is re-normalised exactly and
    its A1, A2, B are evaluated in 40-digit mpmath arithmetic; min(A1+A2, B)/2 is an achievable
    sum-rate of R_CL^(2)(W) (it is a point of the region by definition).
(2) k=1 UPPER bound: weak-duality certificate of cert_cl1.py (alpha, L, r found by LP; the
    majorisation psi <= L + EPS verified on [0,1]^2 by interval bisection).
Usage: python certify_gap.py Q [EPS]     (reported run: python certify_gap.py 0.5 4e-3)
"""
import sys
import time
import numpy as np
import mpmath as mp
from mac_cl import super_channel, bross_lapidoth_mac
import cert_cl1 as C

mp.mp.dps = 40
qq = float(sys.argv[1]) if len(sys.argv) > 1 else 0.5
qstr = sys.argv[1] if len(sys.argv) > 1 else "0.5"
EPS = sys.argv[2] if len(sys.argv) > 2 else "4e-3"   # majorisation slack verified by interval B&B
D = np.load(f"opt_q{qq}.npz")
W = bross_lapidoth_mac(qq)
qm = mp.mpf(qstr)

# ---------------- (1) exact k=2 evaluation
S1, S2, _ = super_channel(W, 2)
def Wm(x1, x2, y):
    p1 = qm * (x1 + x2)
    return p1 if y == 1 else 1 - p1
ys = [(a, b) for a in range(2) for b in range(2)]
Vm = [[[None] * 4 for _ in S2] for _ in S1]
for a, s1 in enumerate(S1):
    for b, s2 in enumerate(S2):
        for c, y in enumerate(ys):
            pr = mp.mpf(1)
            for i in range(2):
                pref = y[:i]
                pr *= Wm(s1[i][pref], s2[i][pref], y[i])
            Vm[a][b][c] = pr

def to_mp(v):
    v = [mp.mpf(repr(float(x))) for x in v]
    s = mp.fsum(v); return [x / s for x in v]
pu = to_mp(D["pu2"]); P1 = [to_mp(r) for r in D["P12"]]; P2 = [to_mp(r) for r in D["P22"]]
nu, n1, n2 = len(pu), len(S1), len(S2)

def Hm(v):
    return -mp.fsum([x * mp.log(x, 2) for x in v if x > 0])

HV = [[Hm(Vm[a][b]) for b in range(n2)] for a in range(n1)]
Hcond = mp.fsum(pu[u] * P1[u][a] * P2[u][b] * HV[a][b] for u in range(nu) for a in range(n1) for b in range(n2))
H_Y_S2U = mp.mpf(0); H_Y_S1U = mp.mpf(0)
for u in range(nu):
    for b in range(n2):
        out = [mp.fsum(P1[u][a] * Vm[a][b][c] for a in range(n1)) for c in range(4)]
        H_Y_S2U += pu[u] * P2[u][b] * Hm(out)
    for a in range(n1):
        out = [mp.fsum(P2[u][b] * Vm[a][b][c] for b in range(n2)) for c in range(4)]
        H_Y_S1U += pu[u] * P1[u][a] * Hm(out)
py = [mp.fsum(pu[u] * P1[u][a] * P2[u][b] * Vm[a][b][c] for u in range(nu) for a in range(n1) for b in range(n2))
      for c in range(4)]
A1 = H_Y_S2U - Hcond; A2 = H_Y_S1U - Hcond; B = Hm(py) - Hcond
lb2 = min(A1 + A2, B) / 2
print(f"q={qstr}: k=2 point: A1/2={mp.nstr(A1/2, 12)}, A2/2={mp.nstr(A2/2, 12)}, B/2={mp.nstr(B/2, 12)}")
print(f"   => sum-rate of R_CL^(2) >= {mp.nstr(lb2, 15)}  (40-digit arithmetic)", flush=True)

# ---------------- (2) certified k=1 upper bound
t0 = time.time()
alphas = np.linspace(0.30, 0.95, 27)
pu1, P11, P21 = D["pu1"], D["P11"], D["P21"]
pbar = np.einsum("u,ua,ub->ab", pu1, P11, P21).ravel()
r0 = pbar @ W.reshape(4, -1)
t, al, L, r = C.search(W, alphas, r0, rounds=5, grid=121)
# refine alpha locally
for al2 in np.linspace(max(0, al - 0.03), min(1, al + 0.03), 13):
    t2, a2, L2, rr2 = C.search(W, [al2], r, rounds=5, grid=161)
    if t2 < t:
        t, al, L, r = t2, a2, L2, rr2
print(f"   LP (grid) bound for k=1: {t:.8f} at alpha={al:.4f}, r={r}, L={L.ravel()}  [{time.time()-t0:.0f}s]",
      flush=True)
print("   certificate parameters (exact decimal strings used below):")
print("     alpha =", repr(float(al)))
print("     L[x1,x2] =", [repr(float(x)) for x in L.ravel()], "(order 00,01,10,11)")
print("     r =", [repr(float(x)) for x in r], flush=True)
Wex = {(x1, x2): [1 - qm * (x1 + x2), qm * (x1 + x2)] for x1 in range(2) for x2 in range(2)}
ub1, eps, nbox = C.certified_bound(Wex, al, L, r, EPS)
print(f"   CERTIFIED k=1 sum-rate <= {mp.nstr(ub1, 12)}   (psi <= L + {mp.nstr(eps, 6)} verified on [0,1]^2, {nbox} boxes)  "
      f"[{time.time()-t0:.0f}s]")
print(f"   numerical k=1 optimum found: {float(D['v1']):.10f}")
print(f"RESULT: certified gap  {mp.nstr(lb2, 12)} - {mp.nstr(ub1, 12)} = {mp.nstr(lb2 - ub1, 6)}  "
      f"({'STRICT INCLUSION R_CL^(1) < R_CL^(2) CERTIFIED' if lb2 > ub1 else 'not certified'})")
