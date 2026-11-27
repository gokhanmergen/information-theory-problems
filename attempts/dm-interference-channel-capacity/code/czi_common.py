"""Common definitions for the Nair-Xia-Yazdanpanah (NXY 2015) binary CZI example.

Channel (NXY arXiv:1502.02589, Table 1 row 1 / Appendix, Fig. 3):
    Y2 = X2 (clean), and q(y1 = 0 | x1, x2) is
        (x1,x2) = (0,0) -> 1      (0,1) -> 1/2
        (x1,x2) = (1,0) -> 1      (1,1) -> 0
i.e. X2 = 0 forces Y1 = 0; X2 = 1 turns X1 -> Y1 into a Z-channel (1 -> 1, 0 -> Bern(1/2)).
Notation: p = P(X1 = 0), q = P(X2 = 0). All logs base 2.
"""
import itertools
import numpy as np

# W1[x1, x2, y1]
W1 = np.zeros((2, 2, 2))
W1[0, 0] = [1.0, 0.0]
W1[0, 1] = [0.5, 0.5]
W1[1, 0] = [1.0, 0.0]
W1[1, 1] = [0.0, 1.0]


def hb(x):
    x = np.clip(x, 0.0, 1.0)
    out = np.zeros_like(np.asarray(x, dtype=float))
    m = (x > 0) & (x < 1)
    xm = np.asarray(x)[m]
    out[m] = -xm * np.log2(xm) - (1 - xm) * np.log2(1 - xm)
    return out if out.shape else float(out)


def H(pv):
    pv = np.asarray(pv, dtype=float).ravel()
    pv = pv[pv > 0]
    return float(-(pv * np.log2(pv)).sum())


def f_closed(p, q):
    """NXY eq. (13): f = H(X2) - I(X2;Y1|X1) + I(X1;Y1)  (lambda = 2)."""
    return ((2 * p - 1) * hb(q) - 2 * p * hb((1 + q) / 2)
            + hb(q + (1 - q) * p / 2) + p * (1 - q))


def g_closed(p, q):
    """I(X1,X2;Y1) = hb(q + p(1-q)/2) - p(1-q)."""
    return hb(q + (1 - q) * p / 2) - p * (1 - q)


def fq_at_tangent(p):
    """d f / d q at q = 1 - 2p (p in (0, 1/2)); slope of NXY Lemma 2 tangent line."""
    t1 = (2 * p - 1) * (np.log2(2 * p) - np.log2(1 - 2 * p)) if p < 0.5 else 0.0
    return (t1 - p * (np.log2(p) - np.log2(1 - p))
            + (1 - p / 2) * (np.log2(p * (2 - p)) - 2 * np.log2(1 - p)) - p)


def E_env(p, q):
    """Upper concave envelope in q of f(p, .) (NXY Lemma 2, re-proved in the attempt)."""
    if p >= 0.5 or q >= 1 - 2 * p:
        return f_closed(p, q)
    return f_closed(p, 0.0) + q * fq_at_tangent(p)


def F(p, q):
    return g_closed(p, q) + E_env(p, q)


# ---------- brute-force information quantities from the channel matrix ----------

def joint_k(px1, px2, k):
    """Joint pmf over (x1^k, x2^k, y1^k) for the k-fold product of W1.
    px1, px2: arrays of length 2^k indexed by the integer whose binary digits are the letters."""
    n = 2 ** k
    # per-sequence channel matrix  Wk[x1seq, x2seq, y1seq]
    Wk = np.ones((n, n, n))
    bits = np.array([[(s >> (k - 1 - i)) & 1 for i in range(k)] for s in range(n)])
    for a in range(n):
        for b in range(n):
            for c in range(n):
                pr = 1.0
                for i in range(k):
                    pr *= W1[bits[a, i], bits[b, i], bits[c, i]]
                Wk[a, b, c] = pr
    return px1[:, None, None] * px2[None, :, None] * Wk, Wk


def tin_value(px1, px2, k, lam=2.0, Wk=None):
    """(1/k)[lam * I(X1^k;Y1^k) + H(X2^k)] for the k-letter TIN scheme on the CZI channel."""
    if Wk is None:
        J, Wk = joint_k(px1, px2, k)
    else:
        J = px1[:, None, None] * px2[None, :, None] * Wk
    py = J.sum(axis=(0, 1))
    px1y = J.sum(axis=1)
    I1 = H(py) + H(px1) - H(px1y)
    return (lam * I1 + H(px2)) / k, I1 / k, H(px2) / k


if __name__ == "__main__":
    # sanity: closed forms vs brute force at random (p, q)
    rng = np.random.default_rng(0)
    for _ in range(5):
        p, q = rng.random(2)
        px1 = np.array([p, 1 - p]); px2 = np.array([q, 1 - q])
        J, _ = joint_k(px1, px2, 1)
        pxy = J  # (x1,x2,y1)
        Hy = H(J.sum((0, 1))); Hy_x1 = H(J.sum(1)) - H(px1)
        Hy_x1x2 = H(J) - H(px1[:, None] * px2[None, :])
        I_x1y = Hy - Hy_x1
        I_x2y_x1 = Hy_x1 - Hy_x1x2
        f_bf = H(px2) - I_x2y_x1 + I_x1y
        g_bf = Hy - Hy_x1x2
        print(f"p={p:.4f} q={q:.4f}  f: {f_bf:.12f} vs {f_closed(p,q):.12f}   g: {g_bf:.12f} vs {g_closed(p,q):.12f}")
