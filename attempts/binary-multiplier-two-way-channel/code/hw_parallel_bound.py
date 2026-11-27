#!/usr/bin/env python3
"""Hekstra-Willems (1989) dependence-balance bound WITH the adaptive parallel channel,
evaluated for the BMC at the equal-rate point.  Target: 0.64628 (HW 1989).

Source of the construction (we could not access HW 1989 itself): A.H.A. Bloemen,
"Discrete coding strategies for two-way channels", PhD thesis, TU Eindhoven, 1996,
Thm 6.3 and Table 6.2 (Sec. 6.4.3), DOI 10.6100/IR463500:

  R1 <= min[ I(X1; Y B | X2 U), I(X1; Y | X2) ],
  R2 <= min[ I(X2; Y B | X1 U), I(X2; Y | X1) ],
  0  <= I(X1; X2 | Y B U) - I(X1; X2 | U),
  p(u,x1,x2,y,b) = p(u,x1,x2) p(y|x1,x2) p_B(b|x1,x2,y),   |U| <= |X1||X2| + 2 = 6,

with the BMC parallel channel (Table 6.2), B in {*, 0, 1}:
  (x1,x2,y) = (0,0,0): P(B=0) = p, P(B=1) = 1-p
              (0,1,0): B = 1
              (1,0,0): B = 0
              (1,1,1): B = *
and p chosen per u as a function of p(x1,x2|u) (adaptive), Bloemen eq. (6.58).

Two facts used below (proved in the attempt file):
 (i)  I(X1; X2 | Y, B, U) = 0 identically (Y=1 fixes both inputs; Y=0,B=1 forces X1=0;
      Y=0,B=0 forces X2=0), so DB forces I(X1;X2|U) = 0: inputs are conditionally
      independent given U.  Write alpha_u = P(X1=1|u), beta_u = P(X2=1|u).
 (ii) With independent inputs,
      I(X1;YB|X2,u) = beta h(alpha) + (1-beta)[h((1-alpha)(1-p)) - (1-alpha) h(p)],
      I(X2;YB|X1,u) = alpha h(beta) + (1-alpha)[h((1-beta) p) - (1-beta) h(p)],
      and the leak sum is minimised at p = alpha(1-beta) / ((1-alpha)beta + alpha(1-beta)).
 I(X1;Y|X2) (no U) is H(Y|X2) of the mixture: P2 h(P11/P2), P2 = E beta, P11 = E alpha beta.

We maximise t <= all four terms with SLSQP over (w_u, alpha_u, beta_u), |U| = K,
with many random restarts.  Output values are attained by explicit parameters, i.e.
they are LOWER bounds on the HW functional; agreement with 0.64628 is the check.

Usage: python hw_parallel_bound.py KMAX RESTARTS SEED [p_mode]
  p_mode = 'hw' (default, leak-minimising p) or 'free' (p_u optimised adversarially is
  NOT allowed - the parallel channel must be fixed a priori; 'free' instead lets the
  maximiser pick p_u, giving an upper envelope used only as a sanity check).
"""
import sys
import json
import numpy as np
from scipy.optimize import minimize

EPS = 1e-12


def h(x):
    x = np.clip(x, EPS, 1 - EPS)
    return -(x * np.log2(x) + (1 - x) * np.log2(1 - x))


def p_hw(al, be):
    d = (1 - al) * be + al * (1 - be)
    return np.where(d > EPS, al * (1 - be) / np.maximum(d, EPS), 0.5)


def terms(w, al, be, p):
    r1 = be * h(al) + (1 - be) * (h((1 - al) * (1 - p)) - (1 - al) * h(p))
    r2 = al * h(be) + (1 - al) * (h((1 - be) * p) - (1 - be) * h(p))
    R1, R2 = w @ r1, w @ r2
    P1, P2, P11 = w @ al, w @ be, w @ (al * be)
    O1 = P2 * h(P11 / max(P2, EPS))
    O2 = P1 * h(P11 / max(P1, EPS))
    return np.array([R1, R2, O1, O2])


def solve(K, rng, mode):
    nv = 3 * K + (K if mode == "free" else 0)

    def unpack(x):
        w, al, be = x[:K], x[K:2 * K], x[2 * K:3 * K]
        p = x[3 * K:4 * K] if mode == "free" else p_hw(al, be)
        return w, al, be, p

    def cons_terms(z):
        x, t = z[:-1], z[-1]
        return terms(*unpack(x)) - t

    w0 = rng.dirichlet(np.ones(K))
    al0 = rng.uniform(0.3, 1.0, K)
    be0 = rng.uniform(0.3, 1.0, K)
    x0 = np.concatenate([w0, al0, be0] + ([rng.uniform(0, 1, K)] if mode == "free" else []))
    t0 = terms(*unpack(x0)).min()
    z0 = np.append(x0, t0)
    bounds = [(0, 1)] * nv + [(0, 1)]
    cons = [{"type": "ineq", "fun": cons_terms},
            {"type": "eq", "fun": lambda z: z[:K].sum() - 1}]
    r = minimize(lambda z: -z[-1], z0, method="SLSQP", bounds=bounds, constraints=cons,
                 options={"maxiter": 2000, "ftol": 1e-14})
    x = np.clip(r.x[:-1], 0, 1)
    w, al, be, p = unpack(x)
    w = w / w.sum()
    val = terms(w, al, be, p).min()     # exact re-evaluation at the returned point
    return val, w, al, be, p


def main():
    Kmax, restarts, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    mode = sys.argv[4] if len(sys.argv) > 4 else "hw"
    rng = np.random.default_rng(seed)
    out = {}
    for K in range(1, Kmax + 1):
        best = (-1,)
        for _ in range(restarts):
            res = solve(K, rng, mode)
            if res[0] > best[0]:
                best = res
        val, w, al, be, p = best
        keep = w > 1e-7
        out[K] = {"value": val, "w": w[keep].round(6).tolist(), "alpha": al[keep].round(6).tolist(),
                  "beta": be[keep].round(6).tolist(), "p": np.asarray(p)[keep].round(6).tolist(),
                  "terms": terms(w, al, be, p).round(7).tolist()}
        print(K, json.dumps(out[K]), flush=True)


if __name__ == "__main__":
    main()
