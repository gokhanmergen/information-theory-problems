"""
Fast tests for two-channel Multiple Descriptions (MD):
1. BSS with D_0 > 0 (excess-rate regime): exact general EGC vs ZB (|U_0|=2).
2. Skewed binary source X ~ Bern(0.3) at D_0 = 0: 1-letter EGC vs 1-letter ZB vs 2-letter ZB.
3. Exact check of whether ZB(D_0=0) at D=0.10 is beaten by ANY 2-letter ZB with |U_0|=1 (i.e. 2-letter EGC!)
   or general |U_0|=2!
   WAIT: Checking 2-letter EGC (|U_0|=1) vs 1-letter EGC vs 1-letter ZB is SUPER enlightening:
   2-letter EGC already has 16*16? No, for (Xh1^2, Xh2^2) in {0..3}^2 given X^2 in {0..3}: 4*16 = 64 vars!
"""

import numpy as np
from scipy.optimize import minimize

def h2(p):
    p = np.clip(p, 1e-15, 1.0 - 1e-15)
    return -p * np.log2(p) - (1.0 - p) * np.log2(1.0 - p)

def ent(p):
    p = np.asarray(p, dtype=float).ravel()
    p = p[p > 1e-15]
    return float(-np.sum(p * np.log2(p)))

def mi_2d(pxy):
    return ent(pxy.sum(axis=1)) + ent(pxy.sum(axis=0)) - ent(pxy)

def cond_mi_3d(pxyz):
    pz = pxyz.sum(axis=(0, 1))
    pxz = pxyz.sum(axis=1)
    pyz = pxyz.sum(axis=0)
    return ent(pxz) + ent(pyz) - ent(pz) - ent(pxyz)

# ---------------------------------------------------------------------------
# 1. BSS at D_0 > 0: General EGC vs ZB (|U_0|=2)
#    Note: for BSS with D_0 > 0, given (x, u, xh1, xh2), Xh0 is an extra binary variable.
#    For general EGC: P(x, xh0, xh1, xh2) has 16 entries (8 for X=0, 8 for X=1).
#    For ZB with symmetric binary U_0 (P(u=0)=P(u=1)=0.5, bit-flip invariant):
#      P0[x, xh0, xh1, xh2] for u=0 has 16 entries summing to 1!
#      Wait: bit-flip invariance of u=0 <-> u=1 automatically gives P(X=0)=P(X=1)=0.5!
# ---------------------------------------------------------------------------
def egc_bss_pos_d0(D0, D):
    # P[x, a, b, c] (16 vars)
    def eval_P(v):
        P = v.reshape(2, 2, 2, 2)
        d0 = P[0, 1].sum() + P[1, 0].sum()
        d1 = P[0, :, 1].sum() + P[1, :, 0].sum()
        d2 = P[0, :, :, 1].sum() + P[1, :, :, 0].sum()
        r1 = mi_2d(P.sum(axis=(1, 3)))
        r2 = mi_2d(P.sum(axis=(1, 2)))
        ix_012 = mi_2d(P.reshape(2, 8))
        i12 = mi_2d(P.sum(axis=(0, 1)))
        return max(r1, r2, 0.5 * (ix_012 + i12)), d0, d1, d2

    bounds = [(0.0, 1.0)] * 16
    cons = [
        {"type": "eq", "fun": lambda v: v[:8].sum() - 0.5},
        {"type": "eq", "fun": lambda v: v[8:].sum() - 0.5},
        {"type": "ineq", "fun": lambda v: D0 - (v.reshape(2,2,2,2)[0,1].sum() + v.reshape(2,2,2,2)[1,0].sum())},
        {"type": "ineq", "fun": lambda v: D - (v.reshape(2,2,2,2)[0,:,1].sum() + v.reshape(2,2,2,2)[1,:,0].sum())},
        {"type": "ineq", "fun": lambda v: D - (v.reshape(2,2,2,2)[0,:,:,1].sum() + v.reshape(2,2,2,2)[1,:,:,0].sum())},
    ]
    rng = np.random.default_rng(11)
    best = 10.0
    for _ in range(25):
        v0 = np.concatenate([0.5 * rng.dirichlet(np.ones(8)), 0.5 * rng.dirichlet(np.ones(8))])
        res = minimize(lambda v: eval_P(v)[0], v0, method="SLSQP", bounds=bounds, constraints=cons,
                       options={"ftol": 1e-10, "maxiter": 400})
        v = np.clip(res.x, 0.0, 1.0)
        v[:8] *= 0.5 / v[:8].sum()
        v[8:] *= 0.5 / v[8:].sum()
        r, d0, d1, d2 = eval_P(v)
        if d0 <= D0 + 1e-6 and d1 <= D + 1e-6 and d2 <= D + 1e-6 and r < best:
            best = r
    return best

def zb_bss_pos_d0(D0, D):
    # Symmetric binary U_0: P0[x, a, b, c] for u=0 (16 vars, sum = 1), u=1 is bit-flip!
    # Marginal on X is automatically (0.5, 0.5).
    def eval_P0(v):
        P0 = v.reshape(2, 2, 2, 2)
        d0 = P0[0, 1].sum() + P0[1, 0].sum()
        d1 = P0[0, :, 1].sum() + P0[1, :, 0].sum()
        d2 = P0[0, :, :, 1].sum() + P0[1, :, :, 0].sum()
        px = P0.sum(axis=(1, 2, 3))
        ixu = 1.0 - ent(px)
        # I(X; U_0, Xh1) = 1 - H(X | U_0=0, Xh1)
        px1 = P0.sum(axis=(1, 3))
        r1 = 1.0 - (ent(px1) - ent(px1.sum(axis=0)))
        px2 = P0.sum(axis=(1, 2))
        r2 = 1.0 - (ent(px2) - ent(px2.sum(axis=0)))
        # I(X; Xh0, Xh1, Xh2 | U_0) = I(x; (a,b,c)) under P0
        ix_012_gu = mi_2d(P0.reshape(2, 8))
        # I(Xh1; Xh2 | U_0) = I(b; c) under P0
        i12_gu = mi_2d(P0.sum(axis=(0, 1)))
        rsum = 2.0 * ixu + ix_012_gu + i12_gu
        return max(r1, r2, 0.5 * rsum), d0, d1, d2, ixu, i12_gu

    bounds = [(0.0, 1.0)] * 16
    cons = [
        {"type": "eq", "fun": lambda v: v.sum() - 1.0},
        {"type": "ineq", "fun": lambda v: D0 - (v.reshape(2,2,2,2)[0,1].sum() + v.reshape(2,2,2,2)[1,0].sum())},
        {"type": "ineq", "fun": lambda v: D - (v.reshape(2,2,2,2)[0,:,1].sum() + v.reshape(2,2,2,2)[1,:,0].sum())},
        {"type": "ineq", "fun": lambda v: D - (v.reshape(2,2,2,2)[0,:,:,1].sum() + v.reshape(2,2,2,2)[1,:,:,0].sum())},
    ]
    rng = np.random.default_rng(22)
    best = (10.0, 0.0, 0.0)
    for _ in range(30):
        v0 = rng.dirichlet(np.ones(16))
        res = minimize(lambda v: eval_P0(v)[0], v0, method="SLSQP", bounds=bounds, constraints=cons,
                       options={"ftol": 1e-10, "maxiter": 400})
        v = np.clip(res.x, 0.0, 1.0)
        v /= v.sum()
        r, d0, d1, d2, ixu, i12 = eval_P0(v)
        if d0 <= D0 + 1e-6 and d1 <= D + 1e-6 and d2 <= D + 1e-6 and r < best[0]:
            best = (r, ixu, i12)
    return best

# ---------------------------------------------------------------------------
# 2. 2-letter EGC (|U_0|=1) on BSS at D_0 = 0, D = 0.10!
#    Does 2-letter EGC already strictly beat 1-letter EGC (0.628213)?!
#    WAIT A SECOND! Think about that!
#    In 2-letter EGC, Xh1^2 and Xh2^2 can encode a 2-letter common bit implicitly?!
#    NO — in 2-letter EGC, R_1+R_2 >= (1/2)*(2 + I(Xh1^2; Xh2^2))!
#    Let's CHECK whether 2-letter EGC beats 1-letter EGC at D=0.10!
# ---------------------------------------------------------------------------
def test_2letter_egc_bss(D=0.10):
    pop = np.array([[bin(x ^ y).count('1') * 0.5 for y in range(4)] for x in range(4)])
    def eval_P(v):
        P = v.reshape(4, 4, 4) # P[x^2, b^2, c^2], each x^2 slice sums to 0.25
        pxb = P.sum(axis=2)
        pxc = P.sum(axis=1)
        pbc = P.sum(axis=0)
        d1 = np.sum(pxb * pop)
        d2 = np.sum(pxc * pop)
        r1 = 0.5 * mi_2d(pxb)
        r2 = 0.5 * mi_2d(pxc)
        i12 = mi_2d(pbc)
        return max(r1, r2, 0.25 * (2.0 + i12)), d1, d2

    bounds = [(0.0, 0.25)] * 64
    cons = [
        {"type": "eq", "fun": lambda v, x=x: v.reshape(4,4,4)[x].sum() - 0.25} for x in range(4)
    ] + [
        {"type": "ineq", "fun": lambda v: D - np.sum(v.reshape(4,4,4).sum(axis=2) * pop)},
        {"type": "ineq", "fun": lambda v: D - np.sum(v.reshape(4,4,4).sum(axis=1) * pop)},
    ]
    rng = np.random.default_rng(99)
    best = 10.0
    for _ in range(15):
        v0 = np.concatenate([0.25 * rng.dirichlet(np.ones(16)) for _ in range(4)])
        res = minimize(lambda v: eval_P(v)[0], v0, method="SLSQP", bounds=bounds, constraints=cons,
                       options={"ftol": 1e-9, "maxiter": 300})
        v = np.clip(res.x, 0.0, 1.0).reshape(4, 4, 4)
        for x in range(4):
            v[x] *= 0.25 / v[x].sum()
        r, d1, d2 = eval_P(v.ravel())
        if d1 <= D + 1e-6 and d2 <= D + 1e-6 and r < best:
            best = r
    return best

def main():
    print("=== BSS AT D_0 > 0: GENERAL EGC vs ZB (|U_0|=2) ===")
    print(f"{'D0':>5} {'D':>5} | {'0.5*R(D0)':>9} | {'R(D)':>9} | {'EGC':>9} | {'ZB_u2':>9} | {'EGC-ZB':>9} | {'I(X;U0)':>8}")
    print("-" * 78)
    for D0, D in [(0.02, 0.10), (0.02, 0.15), (0.05, 0.15), (0.05, 0.20),
                  (0.05, 0.25), (0.08, 0.20), (0.10, 0.20), (0.10, 0.25)]:
        r_egc = egc_bss_pos_d0(D0, D)
        r_zb, ixu, i12 = zb_bss_pos_d0(D0, D)
        print(f"{D0:5.2f} {D:5.2f} | {0.5*(1-h2(D0)):9.6f} | {1-h2(D):9.6f} | {r_egc:9.6f} | {r_zb:9.6f} | {r_egc-r_zb:9.6f} | {ixu:8.5f}")

    r2_egc = test_2letter_egc_bss(0.10)
    print(f"\n=== 2-LETTER EGC TEST AT D_0 = 0, D = 0.10 ===")
    print(f"1-letter EGC = 0.628213, 2-letter EGC = {r2_egc:.6f}, 1-letter ZB = 0.602850")

if __name__ == "__main__":
    main()
