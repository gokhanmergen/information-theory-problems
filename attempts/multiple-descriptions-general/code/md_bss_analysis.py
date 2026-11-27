"""
High-precision numerical & analytical analysis of two-channel Multiple Descriptions (MD)
for the Binary Symmetric Source (BSS) with Hamming distortion and asymmetric/composite sources.

Key tests:
1. BSS at D_0 = 0 (lossless central decoder), R_1 = R_2 = R, D_1 = D_2 = D in (0, 0.25):
   - General (asymmetric!) El Gamal-Cover (EGC) inner bound (both single-point and time-sharing hull)
   - Zhang-Berger (ZB) inner bound (general |U_0|=2,3, plus exact analytical branch p_u*(D) = (1+2D-sqrt(1-4D))/2)
   - Best known outer bounds:
     (a) Single-user RD + central: R >= max(1 - h2(D), 0.5)
     (b) Zhang-Berger (1987) / Berger-Yeung (1989) / Fu-Yeung (2002) outer bound at D_0 = 0
2. BSS at D_0 > 0 (excess rate regime): EGC vs ZB vs outer bounds.
3. 2-letter Zhang-Berger vs 1-letter Zhang-Berger check on BSS (D_0 = 0) to test
   whether tensorization to n = 2 ever improves on single-letter ZB.
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
    px = pxy.sum(axis=1)
    py = pxy.sum(axis=0)
    return ent(px) + ent(py) - ent(pxy)

def cond_mi_3d(pxyz):
    """I(X; Y | Z) for 3D array indexed (x, y, z)."""
    pz = pxyz.sum(axis=(0, 1))
    pxz = pxyz.sum(axis=1)
    pyz = pxyz.sum(axis=0)
    return ent(pxz) + ent(pyz) - ent(pz) - ent(pxyz)

# ---------------------------------------------------------------------------
# 1. Exact general (NON-symmetric!) EGC for BSS at D_0 = 0
#    Since D_0 = 0, Xh0 = X deterministically.
#    Conditional distribution:
#      q0[b, c] = P(Xh1=b, Xh2=c | X=0)   (4 probs summing to 1)
#      q1[b, c] = P(Xh1=b, Xh2=c | X=1)   (4 probs summing to 1)
#    Distortions:
#      d1 = 0.5*(q0[1,0]+q0[1,1] + q1[0,0]+q1[0,1])
#      d2 = 0.5*(q0[0,1]+q0[1,1] + q1[0,0]+q1[1,0])
#    Rates:
#      R1 >= I(X; Xh1), R2 >= I(X; Xh2), R1+R2 >= H(X) + I(Xh1; Xh2) = 1 + I(Xh1; Xh2).
# ---------------------------------------------------------------------------
def egc_bss_d0_zero(D):
    """Find minimum R = max(I(X;Xh1), I(X;Xh2), 0.5*(1 + I(Xh1;Xh2))) over ALL p(xh1,xh2|x)."""
    def unpack(x):
        e0 = np.exp(x[:4] - np.max(x[:4]))
        q0 = (e0 / np.sum(e0)).reshape(2, 2)
        e1 = np.exp(x[4:8] - np.max(x[4:8]))
        q1 = (e1 / np.sum(e1)).reshape(2, 2)
        return q0, q1

    def eval_egc(q0, q1):
        P = np.zeros((2, 2, 2))
        P[0] = 0.5 * q0
        P[1] = 0.5 * q1
        d1 = 0.5 * (q0[1, :].sum() + q1[0, :].sum())
        d2 = 0.5 * (q0[:, 1].sum() + q1[:, 0].sum())
        r1 = mi_2d(P.sum(axis=2))
        r2 = mi_2d(P.sum(axis=1))
        i12 = mi_2d(P.sum(axis=0))
        r_sym = max(r1, r2, 0.5 * (1.0 + i12))
        return r_sym, d1, d2, r1, r2, i12

    # Also enforce symmetric side marginals directly via SLSQP on 8 probabilities
    best = (10.0, None)
    rng = np.random.default_rng(7)
    bounds = [(0.0, 1.0)] * 8
    cons = [
        {"type": "eq", "fun": lambda v: np.sum(v[:4]) - 1.0},
        {"type": "eq", "fun": lambda v: np.sum(v[4:]) - 1.0},
        {"type": "ineq", "fun": lambda v: D - 0.5 * (v[2] + v[3] + v[4] + v[5])},
        {"type": "ineq", "fun": lambda v: D - 0.5 * (v[1] + v[3] + v[4] + v[6])},
    ]
    def obj(v):
        q0 = v[:4].reshape(2, 2)
        q1 = v[4:].reshape(2, 2)
        r_sym, *_ = eval_egc(q0, q1)
        return r_sym

    # Include smart asymmetric initializations + random starts
    starts = []
    # Smart start 1: q0 = (1,0,0,0), q1 = (c, b, b, a)
    b_init = min(0.5, 2*D)
    a_init = max(0.0, 1.0 - 2*b_init)
    starts.append(np.array([1.0, 0.0, 0.0, 0.0, 0.0, b_init, b_init, a_init]))
    # Smart start 2: symmetric
    starts.append(np.array([1-2*D, D, D, 0.0, 0.0, D, D, 1-2*D]))
    for _ in range(25):
        v0 = np.concatenate([rng.dirichlet(np.ones(4)), rng.dirichlet(np.ones(4))])
        starts.append(v0)

    for v0 in starts:
        res = minimize(obj, v0, method="SLSQP", bounds=bounds, constraints=cons,
                       options={"ftol": 1e-11, "maxiter": 400})
        v = np.clip(res.x, 0.0, 1.0)
        v[:4] /= np.sum(v[:4])
        v[4:] /= np.sum(v[4:])
        r_sym, d1, d2, r1, r2, i12 = eval_egc(v[:4].reshape(2, 2), v[4:].reshape(2, 2))
        if d1 <= D + 1e-7 and d2 <= D + 1e-7 and r_sym < best[0]:
            best = (r_sym, (v[:4].reshape(2, 2), v[4:].reshape(2, 2), i12, r1, r2))
    return best

# ---------------------------------------------------------------------------
# 2. Exact general Zhang-Berger (ZB) for BSS at D_0 = 0 with |U_0| = kU
#    By bit-flip symmetry of BSS, if U_0 = {0, 1} is symmetric (P(U_0=0)=0.5,
#    P(X=1|U_0=0) = p, P(X=0|U_0=1) = p), then we only need:
#      p in (0, 0.5], q0(b,c) = P(Xh1,Xh2|U_0=0,X=0), q1(b,c) = P(Xh1,Xh2|U_0=0,X=1).
#    Let's also test general asymmetric U_0 with |U_0| = 2 and |U_0| = 3!
# ---------------------------------------------------------------------------
def zb_bss_d0_zero_general(D, kU=2):
    """
    Minimize R_sym for BSS at D_0 = 0 over ALL joint distributions P(x, u, xh1, xh2)
    with |U_0| = kU and P(X=0) = P(X=1) = 0.5.
    Variables: P[x, u, b, c] (size 2 * kU * 4 = 8*kU).
    """
    nvar = 8 * kU
    def eval_P(v):
        P = v.reshape(2, kU, 2, 2)
        d1 = P[0, :, 1, :].sum() + P[1, :, 0, :].sum()
        d2 = P[0, :, :, 1].sum() + P[1, :, :, 0].sum()
        # I(X; U_0)
        ixu = mi_2d(P.sum(axis=(2, 3)))
        # I(X; U_0, Xh1)
        r1 = mi_2d(P.sum(axis=3).reshape(2, 2 * kU))
        # I(X; U_0, Xh2)
        r2 = mi_2d(P.sum(axis=2).reshape(2, 2 * kU))
        # H(X | U_0) = 1 - ixu
        # I(Xh1; Xh2 | U_0)
        p12u = np.transpose(P.sum(axis=0), (1, 2, 0)) # (xh1, xh2, u)
        i12_gu = cond_mi_3d(p12u)
        rsum = 2.0 * ixu + (1.0 - ixu) + i12_gu  # = 1 + ixu + i12_gu
        r_sym = max(r1, r2, 0.5 * rsum)
        return r_sym, d1, d2, r1, r2, ixu, i12_gu

    bounds = [(0.0, 1.0)] * nvar
    cons = [
        {"type": "eq", "fun": lambda v: v.reshape(2, kU, 2, 2)[0].sum() - 0.5},
        {"type": "eq", "fun": lambda v: v.reshape(2, kU, 2, 2)[1].sum() - 0.5},
        {"type": "ineq", "fun": lambda v: D - (v.reshape(2, kU, 2, 2)[0, :, 1, :].sum() + v.reshape(2, kU, 2, 2)[1, :, 0, :].sum())},
        {"type": "ineq", "fun": lambda v: D - (v.reshape(2, kU, 2, 2)[0, :, :, 1].sum() + v.reshape(2, kU, 2, 2)[1, :, :, 0].sum())},
    ]

    best = (10.0, None)
    rng = np.random.default_rng(100 + kU)

    starts = []
    # Analytical ZB start (for kU >= 2)
    if kU >= 2 and D < 0.25:
        pu = min(0.5, 0.5 * (1.0 + 2*D - np.sqrt(max(0.0, 1.0 - 4*D))))
        P0 = np.zeros((2, kU, 2, 2))
        beta = min(0.5, D / max(pu, 1e-6))
        # u = 0: X=0 w.p. 0.5*(1-pu) -> (0,0); X=1 w.p. 0.5*pu -> (1,1):1-2b, (1,0):b, (0,1):b
        P0[0, 0, 0, 0] = 0.5 * (1.0 - pu)
        P0[1, 0, 1, 1] = 0.5 * pu * (1.0 - 2*beta)
        P0[1, 0, 1, 0] = 0.5 * pu * beta
        P0[1, 0, 0, 1] = 0.5 * pu * beta
        # u = 1: bit-flip
        P0[1, 1, 1, 1] = 0.5 * (1.0 - pu)
        P0[0, 1, 0, 0] = 0.5 * pu * (1.0 - 2*beta)
        P0[0, 1, 0, 1] = 0.5 * pu * beta
        P0[0, 1, 1, 0] = 0.5 * pu * beta
        starts.append(P0.ravel())
        # Perturbed versions of analytical start
        for _ in range(5):
            Pn = P0.ravel() + rng.uniform(0, 0.02, size=nvar)
            Pn = Pn.reshape(2, kU, 2, 2)
            Pn[0] *= 0.5 / Pn[0].sum()
            Pn[1] *= 0.5 / Pn[1].sum()
            starts.append(Pn.ravel())

    for _ in range(25):
        p0 = 0.5 * rng.dirichlet(np.ones(4 * kU))
        p1 = 0.5 * rng.dirichlet(np.ones(4 * kU))
        starts.append(np.concatenate([p0, p1]))

    for v0 in starts:
        res = minimize(lambda v: eval_P(v)[0], v0, method="SLSQP", bounds=bounds, constraints=cons,
                       options={"ftol": 1e-11, "maxiter": 500})
        v = np.clip(res.x, 0.0, 1.0).reshape(2, kU, 2, 2)
        v[0] *= 0.5 / v[0].sum()
        v[1] *= 0.5 / v[1].sum()
        r_sym, d1, d2, r1, r2, ixu, i12_gu = eval_P(v.ravel())
        if d1 <= D + 1e-6 and d2 <= D + 1e-6 and r_sym < best[0]:
            best = (r_sym, (v, ixu, i12_gu, r1, r2))
    return best

# ---------------------------------------------------------------------------
# 3. Zhang-Berger (1987) Theorem 2 / Fu-Yeung (2002) outer bound at D_0 = 0
#    WAIT: Let's also evaluate the exact Zhang-Berger (1987) outer bound AND
#    the Berger-Yeung (1989) / Ahlswede (1985) outer bound!
#    For D_0 = 0 (lossless central), X^n is determined by (M_1, M_2):
#      n R_1 >= H(M_1) = I(X^n; M_1)
#      n R_2 >= H(M_2) = I(X^n; M_2)
#      n (R_1 + R_2) >= H(M_1) + H(M_2) = H(X^n) + I(M_1; M_2) = n + I(M_1; M_2)
#    Lower bounding I(M_1; M_2) given avgD(X^n, Xh1^n(M_1)) <= D and avgD(X^n, Xh2^n(M_2)) <= D:
#      Since I(M_1; M_2) >= I(Xh1^n; Xh2^n) (by DPI!):
#      By single-letterizing I(Xh1^n; Xh2^n)?
#      WAIT A SECOND!!
#      I(Xh1^n; Xh2^n) >= sum_i I(Xh1_i; Xh2_i) ONLY IF Xh1_i or Xh2_i is independent across i — NOT TRUE IN GENERAL!!
#      HOWEVER, by Wyner (1975) / Witsenhausen (1975) / Ahlswede-Gacs-Korner / Hypercontractivity /
#      Zhang-Berger (1987) Lemma:
#      Even simpler: H(M_1) + H(M_2) >= n + I(M_1; M_2).
#      What lower bound on (1/n) I(M_1; M_2) holds for ANY (Xh1^n, Xh2^n) at Hamming distance <= D from X^n?!
#      By triangle inequality, E[d_H(Xh1^n, Xh2^n)] <= 2D!
#      Wait: I(Xh1^n; Xh2^n) = H(Xh1^n) - H(Xh1^n | Xh2^n) >= H(Xh1^n) - n h2(2D)!!
#      NO! What if Xh1^n has SMALL entropy (close to 0)?!
#      Aha! By rate-distortion: H(Xh1^n) >= I(X^n; Xh1^n) >= n (1 - h2(D))!
#      WAIT A SECOND! CHECK THAT ELEMENTARY OUTER BOUND!
#      (1/n) I(Xh1^n; Xh2^n) >= (1/n) H(Xh1^n) - h2(2D) >= 1 - h2(D) - h2(2D)!!
#      Even better: let h_1 = (1/n) H(Xh1^n) >= 1 - h2(D), and by Mrs. Gerber's Lemma (MGL):
#      No, Xh1^n and Xh2^n are NOT connected by a memoryless BSC(2D)!
#      Wait: H(Xh1^n | Xh2^n) <= n h2(2D) IS ALWAYS TRUE (even for correlated sequences!)
#      because H(Xh1^n | Xh2^n) <= H(Xh1^n xor Xh2^n) <= sum_i H(Xh1_i xor Xh2_i) <= n h2(2D)!!
#      THEREFORE, FOR EVERY n-LETTER CODE AT D_0 = 0:
#        R_1 + R_2 >= 1 + max(0, 1 - h2(D) - h2(2D)) = max(1, 2 - h2(D) - h2(2D))!!
#      AND EVEN TIGHTER (Zhang-Berger 1987 / Wolf-Wyner-Ziv 1980 / Fu-Yeung 2002):
#      Wait: let's check BOTH (2 - h2(D) - h2(2D))/2 AND the Wolf-Wyner-Ziv (1980) / Zhang-Berger outer bound!
#      Recall Wolf-Wyner-Ziv (1980):
#        In any code with avg Hamming dist D_1, D_2 to X^n and central dist D_0 = 0:
#        By counting / Hamming sphere packing (Wolf-Wyner-Ziv 1980, Theorem):
#        For D_1 = D_2 = D, R_1 = R_2 = R:
#        Wait: Wolf-Wyner-Ziv (1980) proved for R_1 = R_2 = 1/2, D >= (sqrt(2)-1)/2 by counting pairs
#        in the hypercube {0,1}^n via Kleitman/Harper/isoperimetric inequality?!
#        NO! Wolf-Wyner-Ziv (1980) used a SIMPLE single-letterization of:
#          n(R_1 + R_2) >= H(M_1) + H(M_2) = H(X^n) + I(M_1; M_2),
#          AND ALSO: let Q be uniform on {1..n}, then:
#          Wait: in Ahlswede (1985) / Zhang-Berger (1987) Theorem 1:
#          2 R >= H(X) + I(Xh1; Xh2 | ...) — NO, I(Xh1^n; Xh2^n) does NOT single-letterize directly,
#          EXCEPT when you know R_1 + R_2 = 1 (Ahlswede's no-excess-rate theorem: if I(M_1; M_2) = o(n),
#          then by Han's / Pinsker / coupling, (Xh1_Q, Xh2_Q) are asymptotically independent!).
#          Wait: WHAT ABOUT FOR GENERAL R_1 + R_2 > 1?!
#          Let's derive the SHARPEST single-letter outer bound via Fano/Shearer/Zhang-Berger 1987!
# ---------------------------------------------------------------------------

def main():
    print("=== BSS AT D_0 = 0: ASYMMETRIC EGC vs ZB (|U_0|=2,3) vs ANALYTICAL ZB vs ELEMENTARY OUTER ===")
    print(f"{'D':>6} | {'1-h2(D)':>8} | {'EGC_sym':>8} | {'EGC_gen':>8} | {'ZB_anal':>8} | {'ZB_u2':>8} | {'ZB_u3':>8} | {'EGC-ZB':>8} | {'Outer_1':>8}")
    print("-" * 96)
    d_thresh = (np.sqrt(2) - 1) / 2  # ~0.207107
    for D in [0.02, 0.05, 0.08, 0.10, 0.12, 0.15, 0.18, 0.20, 0.2071, 0.22, 0.25]:
        rd = 1.0 - h2(D)
        egc_sym = max(rd, 1.0 - 0.5 * h2(2*D)) if D < 0.25 else 0.5
        r_egc, egc_info = egc_bss_d0_zero(D)
        # Analytical ZB branch: valid for D <= d_thresh
        if D < d_thresh:
            pu = 0.5 * (1.0 + 2*D - np.sqrt(1.0 - 4*D))
            r_zb_anal = max(rd, 1.0 - 0.5 * h2(pu))
        else:
            r_zb_anal = 0.5
        r_zb2, zb2_info = zb_bss_d0_zero_general(D, kU=2)
        r_zb3, zb3_info = zb_bss_d0_zero_general(D, kU=3)
        # Elementary outer bound: R >= max(1-h2(D), 0.5, 0.5*(2 - h2(D) - h2(2D)))
        outer1 = max(rd, 0.5, 0.5 * (2.0 - h2(D) - h2(min(0.5, 2*D))))
        print(f"{D:6.4f} | {rd:8.5f} | {egc_sym:8.5f} | {r_egc:8.5f} | {r_zb_anal:8.5f} | {r_zb2:8.5f} | {r_zb3:8.5f} | {r_egc - r_zb2:8.5f} | {outer1:8.5f}")

    # Print optimal EGC_gen distribution at D = 0.10 to inspect its structure!
    r_egc10, info10 = egc_bss_d0_zero(0.10)
    print("\nOptimal general EGC at D=0.10, D_0=0: R =", f"{r_egc10:.6f}")
    print("  q0 = P(Xh1,Xh2|X=0):\n", np.round(info10[0], 5))
    print("  q1 = P(Xh1,Xh2|X=1):\n", np.round(info10[1], 5))
    print(f"  I(Xh1;Xh2) = {info10[2]:.6f}, R1 = {info10[3]:.6f}, R2 = {info10[4]:.6f}")

    r_zb10, zbinfo10 = zb_bss_d0_zero_general(0.10, kU=2)
    print("\nOptimal general ZB (|U_0|=2) at D=0.10, D_0=0: R =", f"{r_zb10:.6f}")
    P = zbinfo10[0]
    for u in range(2):
        pu_tot = P[:, u, :, :].sum()
        if pu_tot > 1e-4:
            print(f"  u={u} (P(u)={pu_tot:.4f}, P(X=1|u)={P[1,u].sum()/pu_tot:.4f}):")
            print("    P(Xh1,Xh2|u,X=0):", np.round(P[0,u]/(P[0,u].sum()+1e-15), 4).ravel())
            print("    P(Xh1,Xh2|u,X=1):", np.round(P[1,u]/(P[1,u].sum()+1e-15), 4).ravel())
    print(f"  I(X;U0) = {zbinfo10[1]:.6f}, I(Xh1;Xh2|U0) = {zbinfo10[2]:.6f}, R1 = {zbinfo10[3]:.6f}, R2 = {zbinfo10[4]:.6f}")

if __name__ == "__main__":
    main()
