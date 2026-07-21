#!/usr/bin/env python3
"""Gohari-Nair (2022) Theorem 7 ("J version of the UV outer bound") evaluated on
the BSSC, private-message sum rate (R0 = 0).

Theorem 7 (Gohari-Nair, IEEE Trans. IT 68(2):701-736, 2022; transcribed from
the author-hosted final PDF, pp. 17-18, eqs. (18)-(20)): for any achievable
(R0,R1,R2) there is an input distribution p(x) such that for every auxiliary
channel T_{J|X,Y,Z} there exist auxiliaries with joint
    p_{U,V,W,X} p_{Wt,Ut,Vt|X} p_{Wh,Uh,Vh|X} T_{Y,Z|X} T_{J|X,Y,Z}
(t = tilde, h = hat) satisfying the rate constraints (18a)-(18i) and the
coupling constraints (19a)-(19c), (20a)-(20c) [see code below for all of them].

Evaluation used here (weaker but valid): fixing a single auxiliary channel T_J,
achievability still implies existence of p(x) and auxiliaries satisfying all
constraints at that T_J.  Hence for each fixed T_J,

  B7(T_J) = max { min[ min(18b,18c,18d) + min(18e,18f,18g), 18h, 18i ] :
                  auxiliaries satisfying (19a-c), (20a-c) }

is a valid upper bound on the private-message sum capacity, and so is the min
over any family of T_J's.

Key structural fact used: every mutual-information term in (18b)-(18i) and
(19)-(20) involves J only through joint distributions with X and the
auxiliaries, never jointly with Y or Z.  Therefore the bound depends on
T_{J|X,Y,Z} only through the induced channel q(j|x), and it suffices to sweep
channels q(j|x).

Constraint handling: quadratic penalty on the equality constraints (19a-c),
(20c) and hinge penalty on the inequalities (20a), (20b), with an increasing
penalty schedule; final feasibility residual is reported.  NOTE the error
directions: residual slack can only ENLARGE the feasible set (reported value
may slightly overestimate B7(T_J) -- the safe direction for an outer bound),
while under-optimization of the max UNDERestimates B7(T_J) (unsafe direction);
global-optimality claims are heuristic (restart concentration reported).

The diagonal identification (Wt,Ut,Vt)=(Wh,Uh,Vh)=(W,U,V) satisfies (19a-c)
identically, and (20c) holds automatically for distributions symmetric under
the BSSC swap symmetry, so the feasible set is nonempty and reachable.

Usage:
  python3 gohari_nair_thm7_bssc.py test
  python3 gohari_nair_thm7_bssc.py scan [restarts] [maxiter]

Requires numpy + scipy.  Sanity anchors: any reported value must lie in
[0.3616428 (Marton, achievable floor), ...]; (18i) alone equals the UV
sum-rate expression, so no value can exceed the UV bound estimate 0.3725562
by more than numerical slack.
"""
import sys

import numpy as np
from scipy.optimize import minimize

from gohari_nair_thm8_bssc import (W1, W2, MARTON, UV, entropy, softmax,
                                   make_H, cmi)


# ------------------------------------------------------------- family terms

def family_terms(q_xwuv, qJ):
    """Mutual-information terms for one auxiliary family p(x,w,u,v) combined
    with channels W1 (Y), W2 (Z) and qJ (J).  Returns a dict."""
    t = {}
    for s, ch in (("Y", W1), ("Z", W2), ("J", qJ)):
        # joint (x,w,u,v,s)
        j = np.einsum('xwuv,xs->xwuvs', q_xwuv, ch)
        H = make_H(j)
        X, W, U, V, S = 0, 1, 2, 3, 4
        t["W;" + s] = cmi(H, (W,), (S,))
        t["U;" + s + "|W"] = cmi(H, (U,), (S,), (W,))
        t["V;" + s + "|W"] = cmi(H, (V,), (S,), (W,))
        t["X;" + s + "|UW"] = cmi(H, (X,), (S,), (U, W))
        t["X;" + s + "|VW"] = cmi(H, (X,), (S,), (V, W))
        t["X;" + s] = cmi(H, (X,), (S,))
    return t


def unpack(theta, dims):
    """theta -> p(x), and the three conditionals p(w,u,v|x) (plain/tilde/hat).
    Returns joints q(x,w,u,v) for each family (all sharing p(x))."""
    kw, ku, kv = dims
    k = kw * ku * kv
    px = softmax(theta[:2])
    out = []
    o = 2
    for _fam in range(3):
        q = np.empty((2, kw, ku, kv))
        for x in range(2):
            q[x] = px[x] * softmax(theta[o:o + k]).reshape(kw, ku, kv)
            o += k
        out.append(q)
    return out  # [plain, tilde, hat]


def thm7_value_and_residuals(theta, dims, qJ):
    P, Pt, Ph = unpack(theta, dims)
    p = family_terms(P, qJ)    # plain: W,U,V
    a = family_terms(Pt, qJ)   # tilde: Wt,Ut,Vt
    b = family_terms(Ph, qJ)   # hat:   Wh,Uh,Vh

    iwy, iwz = p["W;Y"], p["W;Z"]
    d = min(iwy, iwz)
    # shared min-blocks of (18c)/(18g) and (18d)/(18f)
    mA = min(a["W;Z"] + min(0.0, iwy - iwz), a["W;J"] + b["W;Y"] - b["W;J"])
    mB = min(b["W;Y"] + min(0.0, iwz - iwy), b["W;J"] + a["W;Z"] - a["W;J"])

    A1 = d + p["U;Y|W"]                                          # (18b)
    A2 = mA + a["U;J|W"] + b["U;Y|W"] - b["U;J|W"]               # (18c)
    A3 = mB + b["U;Y|W"]                                         # (18d)
    B1 = d + p["V;Z|W"]                                          # (18e)
    B2 = mB + b["V;J|W"] + a["V;Z|W"] - a["V;J|W"]               # (18f)
    B3 = mA + a["V;Z|W"]                                         # (18g)
    S1 = (min(b["W;Y"] - b["W;J"], a["W;Z"] - a["W;J"]) + p["X;J"]
          + b["U;Y|W"] - b["U;J|W"] + a["V;Z|W"] - a["V;J|W"])   # (18h)
    S2 = d + min(p["V;Z|W"] + p["X;Y|VW"],
                 p["U;Y|W"] + p["X;Z|UW"])                       # (18i)
    S = min(min(A1, A2, A3) + min(B1, B2, B3), S1, S2)

    eq = [
        # (19a)
        (a["W;Z"] - a["W;J"]) + (b["W;J"] - b["W;Y"]) - (iwz - iwy),
        # (19b)
        (a["U;Z|W"] - a["U;J|W"]) + (b["U;J|W"] - b["U;Y|W"])
        - (p["U;Z|W"] - p["U;Y|W"]),
        # (19c)
        (a["V;Z|W"] - a["V;J|W"]) + (b["V;J|W"] - b["V;Y|W"])
        - (p["V;Z|W"] - p["V;Y|W"]),
        # (20c)
        (p["V;Z|W"] + p["X;Y|VW"]) - (p["U;Y|W"] + p["X;Z|UW"]),
    ]
    ineq = [  # each must be >= 0
        a["X;Z|UW"] - a["X;J|UW"],                                   # (20a) lo
        (a["V;Z|W"] - a["V;J|W"]) - (a["X;Z|UW"] - a["X;J|UW"]),     # (20a) hi
        b["X;Y|VW"] - b["X;J|VW"],                                   # (20b) lo
        (b["U;Y|W"] - b["U;J|W"]) - (b["X;Y|VW"] - b["X;J|VW"]),     # (20b) hi
    ]
    return S, np.array(eq), np.array(ineq)


def penalized(theta, dims, qJ, mu):
    S, eq, ineq = thm7_value_and_residuals(theta, dims, qJ)
    pen = (eq ** 2).sum() + (np.minimum(ineq, 0.0) ** 2).sum()
    return S - mu * pen


def max_violation(theta, dims, qJ):
    _, eq, ineq = thm7_value_and_residuals(theta, dims, qJ)
    return max(np.abs(eq).max(), -min(ineq.min(), 0.0))


def uv_warm_start(dims, qJ, rng):
    """Maximize (18i) alone (the UV sum-rate expression) over the plain
    family; returns the best (2+k)-logit vector.  Used as an init: the UV
    optimum is where the bound can plausibly sit, and penalties then repair
    (20a)-(20c) feasibility."""
    k = 2 * dims[0] * dims[1] * dims[2]

    def f(t):
        P = unpack(np.concatenate([t] + [t[2:]] * 2), dims)[0]
        p = family_terms(P, qJ)
        return min(p["W;Y"], p["W;Z"]) + min(p["V;Z|W"] + p["X;Y|VW"],
                                             p["U;Y|W"] + p["X;Z|UW"])
    best, arg = -1.0, None
    for _ in range(8):
        res = minimize(lambda t: -f(t), rng.normal(0, 3, 2 + k),
                       method="Nelder-Mead",
                       options={"maxiter": 8000, "xatol": 1e-10,
                                "fatol": 1e-13, "adaptive": True})
        if -res.fun > best:
            best, arg = -res.fun, res.x
    return arg


def evaluate_thm7(name, qJ, dims, restarts, maxiter, seed=0):
    k = 2 * dims[0] * dims[1] * dims[2]
    npar = 2 + 3 * k
    rng = np.random.default_rng(seed)
    uv0 = uv_warm_start(dims, qJ, rng)
    stage1 = []
    for r in range(restarts):
        if r % 3 == 0:      # UV-optimum diagonal init
            x0 = np.concatenate([uv0] + [uv0[2:]] * 2)
            x0 += rng.normal(0, 0.05 if r == 0 else 0.5, npar)
        elif r % 3 == 1:    # diagonal init: all three families equal, so the
            base = rng.normal(0, 3, 2 + k)          # (19) equalities vanish
            x0 = np.concatenate([base[:2]] + [base[2:]] * 3)
            x0 += rng.normal(0, 0.05, npar)
        else:
            x0 = rng.normal(0, 3, npar)
        res = minimize(lambda t: -penalized(t, dims, qJ, 300.0),
                       x0, method="Nelder-Mead",
                       options={"maxiter": maxiter, "xatol": 1e-10,
                                "fatol": 1e-13, "adaptive": True})
        stage1.append((-res.fun, res.x))
    stage1.sort(key=lambda r: -r[0])
    finals = []
    for _, x0 in stage1[:5]:
        x = x0
        for mu in (3000.0, 30000.0):
            res = minimize(lambda t: -penalized(t, dims, qJ, mu), x,
                           method="Nelder-Mead",
                           options={"maxiter": maxiter, "xatol": 1e-11,
                                    "fatol": 1e-14, "adaptive": True})
            x = res.x
        S, eq, ineq = thm7_value_and_residuals(x, dims, qJ)
        finals.append((S, max_violation(x, dims, qJ), x))
    feas = [f for f in finals if f[1] < 1e-4]
    pool = feas if feas else finals
    S, viol, x = max(pool, key=lambda r: r[0])
    near = sum(1 for s, v, _ in finals if s > S - 1e-5)
    flag = "  ** BELOW MARTON: under-optimized, not a usable estimate **" \
        if S < MARTON - 1e-4 else ""
    print(f"  {name:34s} dims={dims}  B7_hat = {S:.7f} bits "
          f"(maxviol {viol:.2e}) [{near}/5 finals within 1e-5]{flag}", flush=True)
    return S, viol, x


# ---------------------------------------------------------------- unit test

def unit_test():
    rng = np.random.default_rng(11)
    dims = (2, 2, 2)
    qJ = np.array([[1.0, 0.0], [0.25, 0.75]])
    ok = True
    # 1) diagonal identification makes (19a-c) vanish identically
    k = 2 * dims[0] * dims[1] * dims[2]
    for _ in range(100):
        base = rng.normal(0, 2, 2 + k)
        theta = np.concatenate([base[:2]] + [base[2:]] * 3)
        _, eq, _ = thm7_value_and_residuals(theta, dims, qJ)
        if max(abs(eq[0]), abs(eq[1]), abs(eq[2])) > 1e-10:
            ok = False
            print("diagonal (19) residual nonzero:", eq)
    # 2) (18i) must equal the independently coded UV sum-rate expression
    from gohari_nair_thm8_bssc import uv_sum_with_w
    for _ in range(100):
        theta = rng.normal(0, 2, 2 + 3 * k)
        P, _, _ = unpack(theta, dims)
        p = family_terms(P, qJ)
        s2 = min(p["W;Y"], p["W;Z"]) + min(p["V;Z|W"] + p["X;Y|VW"],
                                           p["U;Y|W"] + p["X;Z|UW"])
        if abs(s2 - uv_sum_with_w(P)) > 1e-9:
            ok = False
            print("18i vs UV mismatch", s2, uv_sum_with_w(P))
    print("unit test (diagonal feasibility + 18i==UV expression):",
          "PASS" if ok else "FAIL")
    return ok


# --------------------------------------------------------------------- main

def qj_const():
    return np.ones((2, 1))


def qj_identity():
    return np.eye(2)


def qj_bsc(delta):
    return np.array([[1 - delta, delta], [delta, 1 - delta]])


def qj_zch(t):
    """Z-channel-type enhancement of receiver Y: x=0 -> j=0; x=1 -> j=1 w.p.
    1-t.  t=0: J=X; t=0.5: J distributed like Y."""
    return np.array([[1.0, 0.0], [t, 1 - t]])


def qj_zch_mirror(t):
    return np.array([[1 - t, t], [0.0, 1.0]])


def qj_erase(e):
    return np.array([[1 - e, 0.0, e], [0.0, 1 - e, e]])


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "test"
    if mode == "test":
        sys.exit(0 if unit_test() else 1)
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    maxiter = int(sys.argv[3]) if len(sys.argv) > 3 else 12000
    configs = [
        ("J=const", qj_const()),
        ("J=X", qj_identity()),
        ("J=BSC(X,.05)", qj_bsc(0.05)),
        ("J=BSC(X,.1)", qj_bsc(0.1)),
        ("J=BSC(X,.2)", qj_bsc(0.2)),
        ("J=BSC(X,.3)", qj_bsc(0.3)),
        ("J=BSC(X,.4)", qj_bsc(0.4)),
        ("J=Zch(.1)", qj_zch(0.1)),
        ("J=Zch(.25)", qj_zch(0.25)),
        ("J=Zch(.4)", qj_zch(0.4)),
        ("J=Zch(.5) (~Y)", qj_zch(0.5)),
        ("J=Zch-mirror(.25)", qj_zch_mirror(0.25)),
        ("J=Zch-mirror(.5) (~Z)", qj_zch_mirror(0.5)),
        ("J=erase(X,.25)", qj_erase(0.25)),
        ("J=erase(X,.5)", qj_erase(0.5)),
        ("J=erase(X,.75)", qj_erase(0.75)),
    ]
    if mode == "scan":
        print(f"[thm7 scan] dims W=2 (all families), U=V=2, restarts={restarts}, "
              f"maxiter={maxiter}")
        print(f"targets: Marton {MARTON} (floor), UV {UV}")
        results = []
        for i, (name, qJ) in enumerate(configs):
            S, viol, _ = evaluate_thm7(name, qJ, (2, 2, 2), restarts, maxiter,
                                       seed=900 + i)
            results.append((S, name, viol))
        results.sort()
        print("\n[thm7 scan] sorted (smallest first — candidates for min over T_J):")
        for S, name, viol in results:
            tag = " (UNDER-OPT, ignore)" if S < MARTON - 1e-4 else ""
            print(f"  {S:.7f} (maxviol {viol:.1e})  {name}{tag}")
    elif mode == "final":
        picks = [("J=const", qj_const()), ("J=X", qj_identity()),
                 ("J=BSC(X,.1)", qj_bsc(0.1)), ("J=Zch(.25)", qj_zch(0.25)),
                 ("J=erase(X,.5)", qj_erase(0.5))]
        for dims in [(2, 2, 2), (3, 2, 2)]:
            print(f"[thm7 final] dims={dims}, restarts={restarts}, maxiter={maxiter}")
            for i, (name, qJ) in enumerate(picks):
                evaluate_thm7(name, qJ, dims, restarts, maxiter, seed=1500 + i)
    else:
        sys.exit(f"unknown mode {mode!r}")
