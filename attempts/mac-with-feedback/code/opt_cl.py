"""Careful numerical optimisation of the max sum-rate of R_CL^(1) and R_CL^(2) for one channel.
Soft-min continuation (beta = 1e2 -> 1e3 -> 1e4) on softmax-parametrised p(u)p(s1|u)p(s2|u);
k=2 warm-started from the k=1 optimum embedded as feedback-ignoring product strategies.
Saves the best distributions to an .npz file.   Usage: python opt_cl.py Q RESTARTS NU1 NU2
"""
import sys
import time
import numpy as np
from scipy.optimize import minimize
from mac_cl import super_channel, cl_quantities, unpack, bross_lapidoth_mac

qq = float(sys.argv[1]) if len(sys.argv) > 1 else 0.4
RESTARTS = int(sys.argv[2]) if len(sys.argv) > 2 else 6
NU1 = int(sys.argv[3]) if len(sys.argv) > 3 else 4
NU2 = int(sys.argv[4]) if len(sys.argv) > 4 else 4
W = bross_lapidoth_mac(qq)


def smin(a, b, beta):
    m = min(a, b)
    return m - np.log(np.exp(-beta * (a - m)) + np.exp(-beta * (b - m))) / beta


def run(V, k, nu, z0, betas=(1e2, 1e3, 1e4)):
    n1, n2, _ = V.shape
    z = z0
    for beta in betas:
        def obj(zz):
            pu, P1, P2 = unpack(zz, nu, n1, n2)
            A1, A2, B = cl_quantities(pu, P1, P2, V)
            return -smin(A1 + A2, B, beta) / k
        res = minimize(obj, z, method="L-BFGS-B", options=dict(maxiter=5000, maxfun=10 ** 6))
        z = res.x
    pu, P1, P2 = unpack(z, nu, n1, n2)
    A1, A2, B = cl_quantities(pu, P1, P2, V)
    return min(A1 + A2, B) / k, z, (A1, A2, B)


def best_of(V, k, nu, inits):
    best = (-1, None, None)
    for z0 in inits:
        v, z, q = run(V, k, nu, z0)
        if v > best[0]:
            best = (v, z, q)
    return best


rng = np.random.default_rng(12345)
t0 = time.time()
S1a, S2a, V1 = super_channel(W, 1)
inits = [rng.normal(scale=2.0, size=NU1 * (1 + 2 + 2)) for _ in range(RESTARTS)]
v1, z1, q1 = best_of(V1, 1, NU1, inits)
pu1, P11, P21 = unpack(z1, NU1, 2, 2)
print(f"q={qq}: CL k=1 sum-rate ~ {v1:.8f}  (A1+A2={q1[0]+q1[1]:.8f}, B={q1[2]:.8f})  [{time.time()-t0:.0f}s]",
      flush=True)
print("   pu =", np.round(pu1, 5), "\n   P1 =", np.round(P11, 5).tolist(), "\n   P2 =", np.round(P21, 5).tolist())

S1, S2, V2 = super_channel(W, 2)
n1, n2 = len(S1), len(S2)
# embed k=1 optimum: U' = (u, u'), s = (x0, constant x1)
idx1 = {}
for a, s in enumerate(S1):
    x0 = s[0][()]; f = s[1]
    if f[(0,)] == f[(1,)]:
        idx1[(x0, f[(0,)])] = a
idx2 = {}
for b, s in enumerate(S2):
    x0 = s[0][()]; f = s[1]
    if f[(0,)] == f[(1,)]:
        idx2[(x0, f[(0,)])] = b
nuE = NU1 * NU1
puE = np.zeros(nuE); P1E = np.full((nuE, n1), 1e-9); P2E = np.full((nuE, n2), 1e-9)
for u in range(NU1):
    for v in range(NU1):
        j = u * NU1 + v
        puE[j] = pu1[u] * pu1[v]
        for x0 in range(2):
            for x1 in range(2):
                P1E[j, idx1[(x0, x1)]] += P11[u, x0] * P11[v, x1]
                P2E[j, idx2[(x0, x1)]] += P21[u, x0] * P21[v, x1]
P1E /= P1E.sum(1, keepdims=True); P2E /= P2E.sum(1, keepdims=True)
A1, A2, B = cl_quantities(puE, P1E, P2E, V2)
print(f"   embedded k=1 optimum evaluated as k=2: {min(A1+A2, B)/2:.8f}", flush=True)
zE = np.concatenate([np.log(puE + 1e-12), np.log(P1E).ravel(), np.log(P2E).ravel()])
inits2 = [zE + rng.normal(scale=0.3, size=zE.size) for _ in range(max(2, RESTARTS // 2))]
vE, zEo, qE = best_of(V2, 2, nuE, inits2)
print(f"   k=2 from embedded start (nu={nuE}): {vE:.8f}  [{time.time()-t0:.0f}s]", flush=True)
inits3 = [rng.normal(scale=2.0, size=NU2 * (1 + n1 + n2)) for _ in range(RESTARTS)]
vR, zR, qR = best_of(V2, 2, NU2, inits3)
print(f"   k=2 random starts (nu={NU2}): {vR:.8f}  [{time.time()-t0:.0f}s]", flush=True)
if vE >= vR:
    v2, z2, nu2 = vE, zEo, nuE
else:
    v2, z2, nu2 = vR, zR, NU2
pu2, P12, P22 = unpack(z2, nu2, n1, n2)
print(f"q={qq}: CL k=2 sum-rate >= {v2:.8f};  gain over k=1 numerics: {v2 - v1:.3e}", flush=True)
np.savez(f"opt_q{qq}.npz", q=qq, pu1=pu1, P11=P11, P21=P21, pu2=pu2, P12=P12, P22=P22, v1=v1, v2=v2)
