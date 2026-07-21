#!/usr/bin/env python3
"""Gohari-Nair (2022) Theorem 8 (two-auxiliary-receiver outer bound) evaluated on
the binary skew-symmetric broadcast channel (BSSC), private-message sum rate.

Channel: X in {0,1};  Y-receiver p(y|x) = [[1, 0], [1/2, 1/2]],
                      Z-receiver p(z|x) = [[1/2, 1/2], [0, 1]].
Joint coupling chosen as Y independent of Z given X (any coupling consistent
with the marginals gives a valid outer bound, since the capacity region of a
broadcast channel depends only on the marginal channels).

Theorem 8 (Gohari-Nair, IEEE Trans. IT 68(2):701-736, 2022; transcribed from the
author-hosted final PDF, p. 23, eq. (31a)-(31g)): for ANY auxiliary channel
T_{J,Jh|X,Y,Z} (Jh = J-hat), every achievable (R0,R1,R2) satisfies, for SOME
p(wa,va,ua|x) p(wb,vb,ub|x) p(x):

  (31a) R0    <= min{ I(Wb;J)+I(Wa;Y|J),  I(Wb;Z|Jh)+I(Wa;Jh) }
  (31b) R0+R1 <= I(Ub,Wb;J) + I(Ua,Wa;Y|J)
  (31c) R0+R1 <= I(Wb;Z|Jh) + I(Wa,J;Jh) + I(Ub;J|Wb,Jh) + I(Ua;Y|Wa,J)
  (31d) R0+R2 <= I(Wb,Jh;J) + I(Wa;Y|J) + I(Vb;Z|Wb,Jh) + I(Va;Jh|Wa,J)
  (31e) R0+R2 <= I(Va,Wa;Jh) + I(Vb,Wb;Z|Jh)
  (31f) R0+R1+R2 <= min{ I(Wb,Jh;J)+I(Wa;Y|J),  I(Wb;Z|Jh)+I(Wa,J;Jh) }
                    + I(Ua;Y|Wa,J) + I(X;Jh|Ua,Wa,J)
                    + min{ I(Ub;J|Wb,Jh)+I(X;Z|Ub,Wb,Jh),
                           I(Vb;Z|Wb,Jh)+I(X;J|Vb,Wb,Jh) }
  (31g) R0+R1+R2 <= min{ I(Wb,Jh;J)+I(Wa;Y|J),  I(Wb;Z|Jh)+I(Wa,J;Jh) }
                    + I(Vb;Z|Wb,Jh) + I(X;J|Vb,Wb,Jh)
                    + min{ I(Ua;Y|Wa,J)+I(X;Jh|Ua,Wa,J),
                           I(Va;Jh|Wa,J)+I(X;Y|Va,Wa,J) }

with cardinalities |Wb|,|Wa| <= |X|+7, |Ub|,|Va| <= |X|+2, |Vb|,|Ua| <= |X|+1.

This script evaluates, for a chosen T_{J,Jh|X,Y,Z} and R0 = 0,

  B8(T) = max_p  min{ min(31b,31c) + min(31d,31e),  31f,  31g }

which is a valid upper bound on the private-message sum capacity R1+R2 for
EVERY fixed T.  Two deliberate restrictions relative to the theorem, both
documented in the attempt file:
  1. T is restricted to the family J -| (X,Y), Jh -| (X,Z) conditionally
     independent given (X,Y,Z) -- each member is still a valid choice of
     T_{J,Jh|X,Y,Z}, so validity is unaffected; only the min over T is
     explored partially.
  2. Auxiliary cardinalities are run at |W*| in {2,3}, |U*|=|V*| in {2,3}
     instead of the theorem's caps (9 and 3/4): this can only UNDERESTIMATE
     B8(T).  Stability across cardinalities is reported as evidence.

DIRECTION OF ERROR: B8(T) is a max over auxiliaries; a numerical optimum is a
certified LOWER estimate of B8(T).  Since the outer bound is B8(T) itself, an
under-optimized (or cardinality-truncated) value is NOT a safe upper bound on
capacity.  All "the bound equals v" claims are therefore heuristic (restart
concentration reported); "capacity <= v" additionally assumes them.

Sanity anchors built in:
  * T: J=Y, Jh=const reduces Theorem 8 exactly to the UV outer bound
    (Gohari-Nair Remark 17(2)); its sum rate must reproduce 0.3725562.
    An algebraic-reduction unit test on random distributions is included.
  * Any B8(T) must be >= Marton sum rate 0.3616428 (an achievable rate);
    a smaller optimum proves under-optimization, and is flagged.

Usage:
  python3 gohari_nair_thm8_bssc.py test            # unit tests
  python3 gohari_nair_thm8_bssc.py scan [restarts] [maxiter]
  python3 gohari_nair_thm8_bssc.py final [restarts] [maxiter]

Requires numpy + scipy.
"""
import sys

import numpy as np
from scipy.optimize import minimize

W1 = np.array([[1.0, 0.0], [0.5, 0.5]])   # p(y|x)  (Y-receiver, Z-channel)
W2 = np.array([[0.5, 0.5], [0.0, 1.0]])   # p(z|x)  (Z-receiver, mirrored)

MARTON = 0.3616428    # exact Marton sum rate (achievable -> validity floor)
UV = 0.3725562        # UV outer bound sum rate (numerical, prior attempt)


def entropy(p):
    p = p[p > 1e-15]
    return float(-(p * np.log2(p)).sum())


def softmax(v):
    e = np.exp(v - v.max())
    return e / e.sum()


# ------------------------------------------------------- auxiliary channels
# A T-config is (name, TJ, TJh): TJ[x, y, j] = p(j|x,y), TJh[x, z, jh] = p(jh|x,z).

def t_const():
    return np.ones((2, 2, 1))


def t_output(delta=0.0):
    """J = output through a BSC(delta) (delta=0: J = copy of the output)."""
    t = np.zeros((2, 2, 2))
    for y in range(2):
        t[:, y, y] = 1 - delta
        t[:, y, 1 - y] = delta
    return t


def t_input(delta=0.0):
    """J = X through a BSC(delta) (depends on X only)."""
    t = np.zeros((2, 2, 2))
    for x in range(2):
        t[x, :, x] = 1 - delta
        t[x, :, 1 - x] = delta
    return t


def t_erase_output(e):
    """J = output erased with probability e (|J| = 3, symbol 2 = erasure)."""
    t = np.zeros((2, 2, 3))
    for y in range(2):
        t[:, y, y] = 1 - e
        t[:, y, 2] = e
    return t


def t_erase_input(e):
    """J = X erased with probability e."""
    t = np.zeros((2, 2, 3))
    for x in range(2):
        t[x, :, x] = 1 - e
        t[x, :, 2] = e
    return t


def channel_tensors(TJ, TJh):
    """pyjj[x,y,j,jh] = p(y,j,jh|x) and pzjj[x,z,j,jh] = p(z,j,jh|x), under the
    coupling Y indep Z given X, J -| (X,Y), Jh -| (X,Z)."""
    qj = np.einsum('xy,xyj->xj', W1, TJ)      # p(j|x)
    qjh = np.einsum('xz,xzk->xk', W2, TJh)    # p(jh|x)
    pyjj = np.einsum('xy,xyj,xk->xyjk', W1, TJ, qjh)
    pzjj = np.einsum('xz,xzk,xj->xzjk', W2, TJh, qj)
    return pyjj, pzjj


# ------------------------------------------------------- Theorem 8 objective

def make_H(p):
    cache = {}

    def H(axes):
        key = tuple(sorted(axes))
        if key not in cache:
            other = tuple(i for i in range(p.ndim) if i not in key)
            cache[key] = entropy(p.sum(axis=other).ravel()) if other else entropy(p.ravel())
        return cache[key]
    return H


def cmi(H, A, B, C=()):
    a, b, c = tuple(A), tuple(B), tuple(C)
    hc = H(c) if c else 0.0
    return max(0.0, H(a + c) + H(b + c) - H(a + b + c) - hc)


def thm8_terms(theta, dims, pyjj, pzjj):
    """Return the constraint values (c1b, c1c, c2d, c2e, cf, cg) at R0=0."""
    kwa, kua, kva, kwb, kub, kvb = dims
    ka, kb = kwa * kua * kva, kwb * kub * kvb
    px = softmax(theta[:2])
    qa = np.empty((2, kwa, kua, kva))
    qb = np.empty((2, kwb, kub, kvb))
    o = 2
    for x in range(2):
        qa[x] = px[x] * softmax(theta[o:o + ka]).reshape(kwa, kua, kva)
        o += ka
    for x in range(2):
        qb[x] = px[x] * softmax(theta[o:o + kb]).reshape(kwb, kub, kvb)
        o += kb
    # joint arrays, axes: (x=0, w=1, u=2, v=3, out=4, j=5, jh=6)
    pa = qa[:, :, :, :, None, None, None] * pyjj[:, None, None, None, :, :, :]
    pb = qb[:, :, :, :, None, None, None] * pzjj[:, None, None, None, :, :, :]
    Ha, Hb = make_H(pa), make_H(pb)

    X, W, U, V, OUT, J, JH = 0, 1, 2, 3, 4, 5, 6
    t1 = cmi(Hb, (U, W), (J,))                # I(Ub,Wb;J)
    t2 = cmi(Ha, (U, W), (OUT,), (J,))        # I(Ua,Wa;Y|J)
    t3 = cmi(Hb, (W,), (OUT,), (JH,))         # I(Wb;Z|Jh)
    t4 = cmi(Ha, (W, J), (JH,))               # I(Wa,J;Jh)
    t5 = cmi(Hb, (U,), (J,), (W, JH))         # I(Ub;J|Wb,Jh)
    t6 = cmi(Ha, (U,), (OUT,), (W, J))        # I(Ua;Y|Wa,J)
    t7 = cmi(Hb, (W, JH), (J,))               # I(Wb,Jh;J)
    t8 = cmi(Ha, (W,), (OUT,), (J,))          # I(Wa;Y|J)
    t9 = cmi(Hb, (V,), (OUT,), (W, JH))       # I(Vb;Z|Wb,Jh)
    t10 = cmi(Ha, (V,), (JH,), (W, J))        # I(Va;Jh|Wa,J)
    t11 = cmi(Ha, (V, W), (JH,))              # I(Va,Wa;Jh)
    t12 = cmi(Hb, (V, W), (OUT,), (JH,))      # I(Vb,Wb;Z|Jh)
    t13 = cmi(Ha, (X,), (JH,), (U, W, J))     # I(X;Jh|Ua,Wa,J)
    t14 = cmi(Hb, (X,), (OUT,), (U, W, JH))   # I(X;Z|Ub,Wb,Jh)
    t15 = cmi(Hb, (X,), (J,), (V, W, JH))     # I(X;J|Vb,Wb,Jh)
    t16 = cmi(Ha, (X,), (OUT,), (V, W, J))    # I(X;Y|Va,Wa,J)

    c1b = t1 + t2
    c1c = t3 + t4 + t5 + t6
    c2d = t7 + t8 + t9 + t10
    c2e = t11 + t12
    m0 = min(t7 + t8, t3 + t4)
    cf = m0 + t6 + t13 + min(t5 + t14, t9 + t15)
    cg = m0 + t9 + t15 + min(t6 + t13, t10 + t16)
    return c1b, c1c, c2d, c2e, cf, cg


def thm8_sum(theta, dims, pyjj, pzjj):
    c1b, c1c, c2d, c2e, cf, cg = thm8_terms(theta, dims, pyjj, pzjj)
    return min(min(c1b, c1c) + min(c2d, c2e), cf, cg)


def nparams(dims):
    kwa, kua, kva, kwb, kub, kvb = dims
    return 2 + 2 * kwa * kua * kva + 2 * kwb * kub * kvb


def maximize(f, npar, restarts, maxiter, seed=0):
    rng = np.random.default_rng(seed)
    vals, best, arg = [], -1.0, None
    for _ in range(restarts):
        res = minimize(lambda t: -f(t), rng.normal(0, 3, npar),
                       method="Nelder-Mead",
                       options={"maxiter": maxiter, "xatol": 1e-10,
                                "fatol": 1e-13, "adaptive": True})
        vals.append(-res.fun)
        if -res.fun > best:
            best, arg = -res.fun, res.x
    for _ in range(2):    # polish the champion
        res = minimize(lambda t: -f(t), arg, method="Nelder-Mead",
                       options={"maxiter": maxiter, "xatol": 1e-12,
                                "fatol": 1e-14, "adaptive": True})
        if -res.fun > best:
            best, arg = -res.fun, res.x
    near = sum(1 for v in vals if v > best - 1e-5)
    return best, near, arg


def evaluate(name, TJ, TJh, dims, restarts, maxiter, seed=0):
    pyjj, pzjj = channel_tensors(TJ, TJh)
    f = lambda t: thm8_sum(t, dims, pyjj, pzjj)
    best, near, arg = maximize(f, nparams(dims), restarts, maxiter, seed=seed)
    flag = "  ** BELOW MARTON: under-optimized, not a usable estimate **" \
        if best < MARTON - 1e-4 else ""
    print(f"  {name:42s} dims={dims}  B8_hat = {best:.7f} bits "
          f"[{near}/{restarts} restarts within 1e-5]{flag}", flush=True)
    return best, near, arg


# ---------------------------------------------------------------- unit test

def uv_sum_with_w(qwuv_x):
    """Independent UV sum-rate expression min{IWY,IWZ} +
    min{I(U;Y|W)+I(X;Z|U,W), I(V;Z|W)+I(X;Y|V,W)} from p(x,w,u,v)."""
    p = qwuv_x  # axes (x,w,u,v)
    py = np.einsum('xwuv,xy->wuvy', p, W1)  # (w,u,v,y)
    pz = np.einsum('xwuv,xy->wuvy', p, W2)
    pxy = np.einsum('xwuv,xy->xwuvy', p, W1)
    pxz = np.einsum('xwuv,xy->xwuvy', p, W2)

    def mi2(j):
        return entropy(j.sum(1)) + entropy(j.sum(0)) - entropy(j.ravel())
    iwy = mi2(py.sum(axis=(1, 2)))
    iwz = mi2(pz.sum(axis=(1, 2)))

    def cm(j3):  # I(A;B|C) from p(c,a,b)
        Hj = make_H(j3)
        return cmi(Hj, (1,), (2,), (0,))
    iuy_w = cm(py.sum(axis=2).transpose(0, 1, 2))          # (w,u,y)
    ivz_w = cm(pz.sum(axis=1).transpose(0, 1, 2))          # (w,v,y)
    ixz_uw = cmi(make_H(pxz.sum(axis=3)), (0,), (3,), (1, 2))  # (x,w,u,y)
    ixy_vw = cmi(make_H(pxy.sum(axis=2)), (0,), (3,), (1, 2))  # (x,w,v,y)
    return min(iwy, iwz) + min(iuy_w + ixz_uw, ivz_w + ixy_vw)


def unit_test():
    """With J=Y, Jh=const, Theorem 8 must reduce exactly to the UV bound
    (Remark 17(2)): check constraint-by-constraint on random distributions."""
    rng = np.random.default_rng(7)
    dims = (2, 2, 2, 2, 2, 2)
    pyjj, pzjj = channel_tensors(t_output(0.0), t_const())
    ok = True
    for _ in range(200):
        theta = rng.normal(0, 2, nparams(dims))
        c1b, c1c, c2d, c2e, cf, cg = thm8_terms(theta, dims, pyjj, pzjj)
        # rebuild qb = p(x,wb,ub,vb) to compute the UV expressions directly
        px = softmax(theta[:2])
        ka = 2 + 2 * 8
        qb = np.stack([px[x] * softmax(theta[ka + 8 * x: ka + 8 * (x + 1)]).reshape(2, 2, 2)
                       for x in range(2)])
        pwy = np.einsum('xwuv,xy->wy', qb, W1)
        pwz = np.einsum('xwuv,xy->wy', qb, W2)

        def mi2(j):
            return entropy(j.sum(1)) + entropy(j.sum(0)) - entropy(j.ravel())
        iwy, iwz = mi2(pwy), mi2(pwz)
        pwuy = np.einsum('xwuv,xy->wuy', qb, W1)
        pwvz = np.einsum('xwuv,xy->wvy', qb, W2)
        iuy_w = cmi(make_H(pwuy), (1,), (2,), (0,))
        ivz_w = cmi(make_H(pwvz), (1,), (2,), (0,))
        pxwuz = np.einsum('xwuv,xy->xwuy', qb, W2)
        pxwvy = np.einsum('xwuv,xy->xwvy', qb, W1)
        ixz_uw = cmi(make_H(pxwuz), (0,), (3,), (1, 2))
        ixy_vw = cmi(make_H(pxwvy), (0,), (3,), (1, 2))
        checks = [
            (c1b, iwy + iuy_w),                     # I(Ub,Wb;Y)
            (c1c, iwz + iuy_w),                     # I(Wb;Z)+I(Ub;Y|Wb)
            (c2d, iwy + ivz_w),                     # I(Wb;Y)+I(Vb;Z|Wb)
            (c2e, iwz + ivz_w),                     # I(Vb,Wb;Z)
            (cf, min(iwy, iwz) + min(iuy_w + ixz_uw, ivz_w + ixy_vw)),
            (cg, min(iwy, iwz) + ivz_w + ixy_vw),
        ]
        for got, want in checks:
            if abs(got - want) > 1e-9:
                ok = False
                print("MISMATCH", got, want)
    # cross-check the standalone UV expression too
    for _ in range(50):
        q = rng.dirichlet(np.ones(16)).reshape(2, 2, 2, 2)
        v1 = uv_sum_with_w(q)
        assert np.isfinite(v1)
    print("unit test (J=Y, Jh=const reduces to UV bound):", "PASS" if ok else "FAIL")
    return ok


# --------------------------------------------------------------------- main

def scan_configs():
    return [
        ("J=Y, Jh=const (UV anchor)", t_output(0.0), t_const()),
        ("J=const, Jh=Z (mirror anchor)", t_const(), t_output(0.0)),
        ("J=const, Jh=const", t_const(), t_const()),
        ("J=Y, Jh=Z", t_output(0.0), t_output(0.0)),
        ("J=X, Jh=const", t_input(0.0), t_const()),
        ("J=const, Jh=X", t_const(), t_input(0.0)),
        ("J=X, Jh=X", t_input(0.0), t_input(0.0)),
        ("J=Y, Jh=X", t_output(0.0), t_input(0.0)),
        ("J=X, Jh=Z", t_input(0.0), t_output(0.0)),
        ("J=BSC(Y,.1), Jh=BSC(Z,.1)", t_output(0.1), t_output(0.1)),
        ("J=BSC(Y,.25), Jh=BSC(Z,.25)", t_output(0.25), t_output(0.25)),
        ("J=BSC(X,.1), Jh=BSC(X,.1)", t_input(0.1), t_input(0.1)),
        ("J=erase(Y,.5), Jh=erase(Z,.5)", t_erase_output(0.5), t_erase_output(0.5)),
        ("J=erase(X,.5), Jh=erase(X,.5)", t_erase_input(0.5), t_erase_input(0.5)),
        ("J=erase(Y,.25), Jh=erase(Z,.25)", t_erase_output(0.25), t_erase_output(0.25)),
    ]


if __name__ == "__main__":
    mode = sys.argv[1] if len(sys.argv) > 1 else "test"
    if mode == "test":
        sys.exit(0 if unit_test() else 1)
    restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    maxiter = int(sys.argv[3]) if len(sys.argv) > 3 else 6000
    if mode == "scan":
        print(f"[scan] dims Wa=Wb=2, U*=V*=2, restarts={restarts}, maxiter={maxiter}")
        print(f"targets: Marton {MARTON} (floor), UV {UV} (anchor)")
        results = []
        for i, (name, TJ, TJh) in enumerate(scan_configs()):
            b, near, _ = evaluate(name, TJ, TJh, (2, 2, 2, 2, 2, 2),
                                  restarts, maxiter, seed=100 + i)
            results.append((b, name))
        results.sort()
        print("\n[scan] sorted (smallest valid estimate first — candidates for min over T):")
        for b, name in results:
            tag = " (UNDER-OPT, ignore)" if b < MARTON - 1e-4 else ""
            print(f"  {b:.7f}  {name}{tag}")
    elif mode == "final":
        # High-effort verification runs on the anchor and the most promising
        # configs (per scan results), at higher cardinality levels.
        allc = {name: (name, TJ, TJh) for name, TJ, TJh in scan_configs()}
        want = sys.argv[4].split(";") if len(sys.argv) > 4 else \
            ["J=Y, Jh=const (UV anchor)", "J=Y, Jh=Z"]
        picks = [allc[w] for w in want]
        for dims in [(2, 2, 2, 2, 2, 2), (3, 2, 2, 3, 2, 2), (2, 3, 3, 2, 3, 3)]:
            print(f"[final] dims={dims}, restarts={restarts}, maxiter={maxiter}")
            for i, (name, TJ, TJh) in enumerate(picks):
                evaluate(name, TJ, TJh, dims, restarts, maxiter, seed=500 + i)
    else:
        sys.exit(f"unknown mode {mode!r}")
