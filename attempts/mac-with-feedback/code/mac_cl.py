"""k-letter Cover-Leung (Kramer's generalized CL) region for a small DM-MAC with feedback.

Strategies: a k-step strategy for user j is s = (s_0, ..., s_{k-1}) with s_i : Y^i -> X_j
(exactly `MACFeedbackStrat k X Y` in lean/InfoTheory/Problems/MacWithFeedback.lean).
Super-channel V[s1, s2, y^k] = prod_i W(y_i | s1_i(y^{i-1}), s2_i(y^{i-1})).
For p(u) p(s1|u) p(s2|u):
   A1 = I(S1;Y^k|S2,U),  A2 = I(S2;Y^k|S1,U),  B = I(S1,S2;Y^k),
and the region is {R1 <= A1/k, R2 <= A2/k, R1+R2 <= B/k} (union, closure).
Max sum-rate of R_CL^(k) = sup min(A1+A2, B)/k.
"""
import itertools
import numpy as np
from scipy.optimize import minimize


def H_rows(P):
    """Entropy (bits) along the last axis."""
    P = np.asarray(P, dtype=float)
    with np.errstate(divide="ignore", invalid="ignore"):
        T = np.where(P > 0, -P * np.log2(np.where(P > 0, P, 1.0)), 0.0)
    return T.sum(axis=-1)


def strategies(k, nx, ny):
    """All k-step strategies as tuples of dicts: s[i][y_prefix] -> x."""
    per_step = []
    for i in range(k):
        prefixes = list(itertools.product(range(ny), repeat=i))
        per_step.append([dict(zip(prefixes, vals))
                         for vals in itertools.product(range(nx), repeat=len(prefixes))])
    return list(itertools.product(*per_step))


def super_channel(W, k):
    """W[x1, x2, y] -> (strategies1, strategies2, V[s1, s2, y^k index])."""
    nx1, nx2, ny = W.shape
    S1 = strategies(k, nx1, ny); S2 = strategies(k, nx2, ny)
    ys = list(itertools.product(range(ny), repeat=k))
    V = np.ones((len(S1), len(S2), len(ys)))
    for a, s1 in enumerate(S1):
        for b, s2 in enumerate(S2):
            for c, y in enumerate(ys):
                pr = 1.0
                for i in range(k):
                    pref = y[:i]
                    pr *= W[s1[i][pref], s2[i][pref], y[i]]
                V[a, b, c] = pr
    return S1, S2, V


def cl_quantities(pu, P1, P2, V):
    """pu: (nu,), P1: (nu, n1), P2: (nu, n2), V: (n1, n2, ny). Returns A1, A2, B (bits)."""
    HV = H_rows(V)                                           # (n1, n2)
    # H(Y | S1, S2, U) = sum_u pu sum p1 p2 HV
    Hcond = np.einsum("u,ua,ub,ab->", pu, P1, P2, HV)
    # H(Y | S2, U): for each (u, s2): output dist sum_a P1[u,a] V[a,b,:]
    Y_given_u_b = np.einsum("ua,aby->uby", P1, V)
    H_Y_S2U = np.einsum("u,ub,ub->", pu, P2, H_rows(Y_given_u_b))
    Y_given_u_a = np.einsum("ub,aby->uay", P2, V)
    H_Y_S1U = np.einsum("u,ua,ua->", pu, P1, H_rows(Y_given_u_a))
    py = np.einsum("u,ua,ub,aby->y", pu, P1, P2, V)
    A1 = H_Y_S2U - Hcond
    A2 = H_Y_S1U - Hcond
    B = H_rows(py) - Hcond
    return A1, A2, B


def unpack(z, nu, n1, n2):
    def sm(v):
        v = v - v.max(axis=-1, keepdims=True)
        e = np.exp(v)
        return e / e.sum(axis=-1, keepdims=True)
    i = 0
    pu = sm(z[i:i + nu]); i += nu
    P1 = sm(z[i:i + nu * n1].reshape(nu, n1)); i += nu * n1
    P2 = sm(z[i:i + nu * n2].reshape(nu, n2)); i += nu * n2
    return pu, P1, P2


def optimize_weighted(V, k, w=(1.0, 1.0), nu=3, restarts=20, seed=0, beta=200.0, maxiter=3000,
                      init=None):
    """Maximise min(w1*R1 + w2*R2) over the region, via the corner representation:
    for w = (1,1) this is the sum-rate  min(A1+A2, B)/k.  General w (w1 >= w2):
    max over pentagon of w1 R1 + w2 R2 = w2*min(A1+A2,B) + (w1-w2)*min(A1, B) ... handled by
    objective = (w2*min(A1+A2,B) + (w1-w2)*A1')/k with R1 = min(A1,B).  We use a soft-min."""
    n1, n2, _ = V.shape
    rng = np.random.default_rng(seed)
    w1, w2 = w

    def smin(a, b):
        m = min(a, b)
        return m - np.log(np.exp(-beta * (a - m)) + np.exp(-beta * (b - m))) / beta

    def obj(z):
        pu, P1, P2 = unpack(z, nu, n1, n2)
        A1, A2, B = cl_quantities(pu, P1, P2, V)
        if w1 >= w2:
            r1 = smin(A1, B)
            val = w2 * smin(A1 + A2, B) + (w1 - w2) * r1
        else:
            r2 = smin(A2, B)
            val = w1 * smin(A1 + A2, B) + (w2 - w1) * r2
        return -val / k

    best = (np.inf, None)
    dim = nu + nu * n1 + nu * n2
    for r in range(restarts):
        z0 = rng.normal(scale=2.0, size=dim) if (init is None or r > 0) else init
        res = minimize(obj, z0, method="L-BFGS-B", options=dict(maxiter=maxiter))
        if res.fun < best[0]:
            best = (res.fun, res.x)
    pu, P1, P2 = unpack(best[1], nu, n1, n2)
    A1, A2, B = cl_quantities(pu, P1, P2, V)
    return dict(pu=pu, P1=P1, P2=P2, A1=A1, A2=A2, B=B, z=best[1],
                sum_rate=min(A1 + A2, B) / k)


def nofb_sum_rate(W, grid=401):
    """No-feedback MAC sum capacity: max over product inputs of min(I1+I2... ) -> for the MAC without
    feedback the max sum-rate is max_{p1 p2} I(X1,X2;Y) (time-sharing does not help the sum)."""
    nx1, nx2, ny = W.shape
    assert nx1 == 2 and nx2 == 2
    best = 0
    for a in np.linspace(0, 1, grid):
        for b in np.linspace(0, 1, grid):
            p = np.outer([a, 1 - a], [b, 1 - b])
            py = np.einsum("ij,ijy->y", p, W)
            I = H_rows(py) - (p * H_rows(W)).sum()
            best = max(best, I)
    return best


def coop_sum_rate(W, iters=5000):
    """max_{p(x1,x2)} I(X1,X2;Y) via Blahut-Arimoto."""
    nx1, nx2, ny = W.shape
    Wf = W.reshape(nx1 * nx2, ny)
    p = np.ones(nx1 * nx2) / (nx1 * nx2)
    for _ in range(iters):
        q = p @ Wf
        with np.errstate(divide="ignore", invalid="ignore"):
            D = np.where(Wf > 0, Wf * np.log2(np.where(Wf > 0, Wf, 1) / q), 0).sum(1)
        p = p * np.exp2(D); p /= p.sum()
    q = p @ Wf
    with np.errstate(divide="ignore", invalid="ignore"):
        D = np.where(Wf > 0, Wf * np.log2(np.where(Wf > 0, Wf, 1) / q), 0).sum(1)
    return float(p @ D), float(D.max())   # lower and upper (dual) bounds


def bross_lapidoth_mac(qq):
    """Binary MAC from the Poisson example (Bross-Lapidoth 2005; Venkataramanan-Pradhan 2011, Sec. IV-C):
    P(Y=1|00)=0, P(Y=1|01)=P(Y=1|10)=q, P(Y=1|11)=2q."""
    W = np.zeros((2, 2, 2))
    for x1 in range(2):
        for x2 in range(2):
            p1 = qq * (x1 + x2)
            W[x1, x2] = [1 - p1, p1]
    return W
