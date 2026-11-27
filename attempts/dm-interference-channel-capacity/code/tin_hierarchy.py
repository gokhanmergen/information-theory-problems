"""k-letter treating-interference-as-noise (TIN) values on the NXY binary CZI channel, lambda = 2:
    V_k = max_{p(x1^k) p(x2^k)} (1/k) [ 2 I(X1^k;Y1^k) + H(X2^k) ]
(numerical LOWER bounds: any distribution found is an explicit achievable point of R_HK^(k) with
U1 = U2 = const, Q = const), and the single-letter OUTER bound
    max_C (2R1+R2) <= max_{p,q} [ I(X1X2;Y1) + H(X2|Y1,X1) + I(X1;Y1|X2) ]   (Claim D5).
Usage: python tin_hierarchy.py KMAX RESTARTS
"""
import sys
import time
import numpy as np
from scipy.optimize import minimize
from czi_common import joint_k, tin_value, H, hb

KMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 4
RESTARTS = int(sys.argv[2]) if len(sys.argv) > 2 else 10


def sm(v):
    v = v - v.max(); e = np.exp(v); return e / e.sum()


def blahut_arimoto(M, iters=400, p0=None):
    """max_p I(X;Y) for channel matrix M[x, y]; returns (p, value).  Warm start p0 (smoothed)."""
    n = M.shape[0]
    p = np.ones(n) / n if p0 is None else (0.999 * p0 + 0.001 / n)
    for _ in range(iters):
        q = p @ M
        with np.errstate(divide="ignore", invalid="ignore"):
            D = np.where(M > 0, M * np.log2(np.where(M > 0, M, 1) / np.where(q > 0, q, 1)), 0).sum(1)
        p = p * np.exp2(D); p /= p.sum()
    q = p @ M
    with np.errstate(divide="ignore", invalid="ignore"):
        D = np.where(M > 0, M * np.log2(np.where(M > 0, M, 1) / np.where(q > 0, q, 1)), 0).sum(1)
    return p, float(p @ D)


def optimise_k(k, restarts, seed=0, extra_inits=()):
    n = 2 ** k
    _, Wk = joint_k(np.ones(n) / n, np.ones(n) / n, k)
    rng = np.random.default_rng(seed)

    def val(p1, p2):
        return tin_value(p1, p2, k, Wk=Wk)[0]

    def obj(z):
        return -val(sm(z[:n]), sm(z[n:]))

    best = (-1, None, None)
    inits = []
    # structured init: product of the single-letter optimum (p, q) ~ (0.5078, 0.4365) plus noise
    p0, q0 = 0.5078, 0.4365
    prod1 = np.array([np.prod([p0 if b == '0' else 1 - p0 for b in format(s, f'0{k}b')]) for s in range(n)])
    prod2 = np.array([np.prod([q0 if b == '0' else 1 - q0 for b in format(s, f'0{k}b')]) for s in range(n)])
    rep1 = np.zeros(n); rep1[0] = p0; rep1[-1] = 1 - p0          # repetition code for X1
    structured = [np.concatenate([np.log(prod1 + 1e-12), np.log(prod2 + 1e-12)]),
                  np.concatenate([np.log(rep1 + 1e-9), np.log(prod2 + 1e-12)])]
    if k == 2:   # NXY Appendix structure: repetition on X1, correlated X2
        nxy2 = np.array([0.36 * q0, 0.64 * q0, 0.64 * q0, 1 - 1.64 * q0])
        structured.append(np.concatenate([np.log(rep1 + 1e-9), np.log(nxy2)]))
    structured += [np.concatenate([np.log(a + 1e-12), np.log(b + 1e-12)]) for a, b in extra_inits]
    for r in range(restarts + len(structured)):
        if r < len(structured):
            z0 = structured[r]
        else:
            z0 = rng.normal(scale=1.5, size=2 * n)
        res = minimize(obj, z0, method="L-BFGS-B", options=dict(maxiter=4000))
        p1, p2 = sm(res.x[:n]), sm(res.x[n:])
        # polish: alternate exact BA step for p1 with gradient step for p2
        v = val(p1, p2)
        for _ in range(60):     # polish; a step is accepted only if it improves the objective
            M = np.einsum("b,aby->ay", p2, Wk)
            p1n, _ = blahut_arimoto(M, iters=2000, p0=p1)
            res2 = minimize(lambda z: -val(p1n, sm(z)), np.log(p2 + 1e-15), method="L-BFGS-B",
                            options=dict(maxiter=2000))
            p2n = sm(res2.x)
            vn = val(p1n, p2n)
            if vn <= v + 1e-12:
                break
            p1, p2, v = p1n, p2n, vn
        if v > best[0]:
            best = (v, p1, p2)
    return best


if __name__ == "__main__":
    # single-letter outer bound (Claim D5), grid + refine
    def phi(p, q):
        s = q + (1 - q) * p / 2
        g = hb(s) - p * (1 - q)
        H2_given = hb(q) - (p * (hb((1 + q) / 2) - (1 - q)) + (1 - p) * hb(q))
        I1_given_x2 = (1 - q) * (hb(p / 2) - p)
        return g + H2_given + I1_given_x2
    G = np.linspace(0, 1, 1001)
    PP, QQ = np.meshgrid(G, G, indexing="ij")
    vals = phi(PP.ravel(), QQ.ravel()).reshape(PP.shape)
    i, j = np.unravel_index(np.argmax(vals), vals.shape)
    res = minimize(lambda z: -phi(np.clip(z[0], 0, 1), np.clip(z[1], 0, 1)), [G[i], G[j]],
                   method="Nelder-Mead", options=dict(xatol=1e-12, fatol=1e-15))
    print(f"single-letter outer bound on max_C(2R1+R2): {-res.fun:.6f} at (p,q)={res.x}", flush=True)

    best = {}
    for k in range(1, KMAX + 1):
        t0 = time.time()
        # nesting inits: products of optimisers found for divisors d | k (R^(d) in R^(k))
        extra = []
        for d in range(1, k):
            if k % d == 0 and d in best:
                a, b = best[d][1], best[d][2]
                A, B = a, b
                for _ in range(k // d - 1):
                    A = np.kron(A, a); B = np.kron(B, b)
                extra.append((A, B))
        v, p1, p2 = optimise_k(k, RESTARTS if k > 1 else 4, seed=k, extra_inits=extra)
        best[k] = (v, p1, p2)
        _, r1, r2 = tin_value(p1, p2, k)
        print(f"k={k}: V_k >= {v:.7f}   (R1={r1:.6f}, R2={r2:.6f})   [{time.time()-t0:.0f}s]", flush=True)
        np.set_printoptions(precision=5, suppress=True)
        print("    p(x1^k) =", p1)
        print("    p(x2^k) =", p2, flush=True)
