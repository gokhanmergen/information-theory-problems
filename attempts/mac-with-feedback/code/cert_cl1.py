"""Certified UPPER bound on the max sum-rate of the single-letter Cover-Leung region R_CL^(1)(W)
for a binary-input DM-MAC W (any finite output alphabet).

Lemma (Claim M6 in the attempt).  For alpha in [0,1], a real table L(x1,x2), an output pmf r, if
      psi(p1,p2) := I(X1;Y|X2) + I(X2;Y|X1)   (X1 ~ p1, X2 ~ p2 independent)
               <= sum_{x1,x2} p1(x1) p2(x2) L(x1,x2)      for ALL product inputs,
then   max sum-rate of R_CL^(1)(W)  <=  max_{x1,x2} [ alpha L(x1,x2) + (1-alpha) D(W(.|x1,x2) || r) ].
Proof: min(A,B) <= alpha A + (1-alpha) B;  A = sum_u p(u) psi(p1u,p2u) <= <pbar, L>;
       B = I(X1X2;Y) = sum_x pbar(x) D(W_x||pbar W) <= sum_x pbar(x) D(W_x||r).

Procedure: LP for L on a grid (given alpha, r), alternate with r-update; then RIGOROUSLY verify
psi(a,b) - L(a,b) <= eps on all of [0,1]^2 by interval bisection (mpmath.iv; function
verify_majorization), so that L + eps is a valid table, and report
UB = max_x [alpha (L(x)+eps) + (1-alpha) D(W_x||r)]  evaluated in interval arithmetic.
(certify_eps, a best-first variant that estimates the smallest eps, is kept but unused: it is
slow near the tangency points of psi and L.)
"""
import heapq
import numpy as np
from scipy.optimize import linprog, minimize
import mpmath as mp
from mpmath import iv

iv.dps = 30
LN2 = iv.log(iv.mpf(2))


# ----------------------------------------------------------------- float helpers
def Hv(P):
    P = np.asarray(P, float)
    with np.errstate(divide="ignore", invalid="ignore"):
        return np.where(P > 0, -P * np.log2(np.where(P > 0, P, 1)), 0).sum(-1)


def psi_float(W, a, b):
    """W[x1,x2,y]; a = P(X1=0), b = P(X2=0). Vectorised over arrays a, b."""
    a = np.asarray(a, float)[..., None]; b = np.asarray(b, float)[..., None]
    w00, w01, w10, w11 = W[0, 0], W[0, 1], W[1, 0], W[1, 1]
    # I(X1;Y|X2) and I(X2;Y|X1)
    I1 = (b[..., 0] * (Hv(a * w00 + (1 - a) * w10) - a[..., 0] * Hv(w00) - (1 - a[..., 0]) * Hv(w10))
          + (1 - b[..., 0]) * (Hv(a * w01 + (1 - a) * w11) - a[..., 0] * Hv(w01) - (1 - a[..., 0]) * Hv(w11)))
    I2 = (a[..., 0] * (Hv(b * w00 + (1 - b) * w01) - b[..., 0] * Hv(w00) - (1 - b[..., 0]) * Hv(w01))
          + (1 - a[..., 0]) * (Hv(b * w10 + (1 - b) * w11) - b[..., 0] * Hv(w10) - (1 - b[..., 0]) * Hv(w11)))
    return I1 + I2


def D_rows(W, r):
    Wf = W.reshape(4, -1)
    with np.errstate(divide="ignore", invalid="ignore"):
        return np.where(Wf > 0, Wf * np.log2(np.where(Wf > 0, Wf, 1) / r), 0).sum(1)


def bil(L, a, b):
    """sum p1 p2 L with p1 = (a, 1-a), p2 = (b, 1-b); L indexed [x1, x2]."""
    return a * b * L[0, 0] + a * (1 - b) * L[0, 1] + (1 - a) * b * L[1, 0] + (1 - a) * (1 - b) * L[1, 1]


def lp_L(W, alpha, r, grid=121):
    G = np.linspace(0, 1, grid)
    A, B = np.meshgrid(G, G, indexing="ij"); A = A.ravel(); B = B.ravel()
    ps = psi_float(W, A, B)
    D = D_rows(W, r)
    # variables: L00, L01, L10, L11, t ; minimise t
    c = np.array([0, 0, 0, 0, 1.0])
    # alpha L_x + (1-alpha) D_x <= t
    A1 = np.zeros((4, 5)); b1 = np.zeros(4)
    for i in range(4):
        A1[i, i] = alpha; A1[i, 4] = -1; b1[i] = -(1 - alpha) * D[i]
    # -(bilinear) <= -psi
    A2 = -np.stack([A * B, A * (1 - B), (1 - A) * B, (1 - A) * (1 - B), 0 * A], 1)
    b2 = -ps
    res = linprog(c, A_ub=np.vstack([A1, A2]), b_ub=np.concatenate([b1, b2]),
                  bounds=[(None, None)] * 5, method="highs")
    return res.x[:4].reshape(2, 2), res.x[4]


def best_r(W, alpha, L):
    ny = W.shape[2]
    def obj(z):
        r = np.exp(z - z.max()); r /= r.sum()
        return np.max(alpha * L.ravel() + (1 - alpha) * D_rows(W, r))
    best = None
    for z0 in [np.zeros(ny), np.random.default_rng(0).normal(size=ny)]:
        res = minimize(obj, z0, method="Nelder-Mead", options=dict(xatol=1e-12, fatol=1e-14, maxiter=20000))
        if best is None or res.fun < best.fun:
            best = res
    r = np.exp(best.x - best.x.max()); return r / r.sum()


def search(W, alphas, r0, rounds=6, grid=121):
    out = None
    for al in alphas:
        r = r0.copy()
        for _ in range(rounds):
            L, t = lp_L(W, al, r, grid)
            r = best_r(W, al, L)
        L, t = lp_L(W, al, r, grid)
        if out is None or t < out[0]:
            out = (t, al, L, r)
    return out


# ----------------------------------------------------------------- interval certification
INV_E_LO, INV_E_HI = mp.mpf("0.3678"), mp.mpf("0.3679")      # 1/e = 0.367879...
PHI_MAX = iv.mpf(1) / (iv.e * LN2)                               # max of -x log2 x


def _phi_at(x):
    """-x log2 x at an exact mpf point x in [0,1], as a rigorous interval."""
    if x <= 0:
        return iv.mpf(0)
    X = iv.mpf(x)
    return -X * iv.log(X) / LN2


def phi_iv(X):
    """Rigorous enclosure of {-x log2 x : x in X}, X an iv interval (clipped to [0,1])."""
    a = max(X.a, mp.mpf(0)); b = min(X.b, mp.mpf(1))
    A, B = _phi_at(a), _phi_at(b)
    if b <= INV_E_LO:
        return iv.mpf([A.a, B.b])
    if a >= INV_E_HI:
        return iv.mpf([B.a, A.b])
    return iv.mpf([min(A.a, B.a), PHI_MAX.b])


def H_iv(vec):
    """Enclosure of the entropy of a pmf whose entries lie in the given intervals."""
    return sum((phi_iv(iv.mpf(x)) for x in vec), iv.mpf(0))


def H_iv_point(v):
    return H_iv(v)


def Hmix_rng(a_lo, a_hi, w0, w1):
    """Enclosure of h(a) := H(a*w0 + (1-a)*w1) for a in [a_lo, a_hi] (w0, w1 output pmfs, mpf lists).
    h is concave in a, so min over the interval is at an endpoint, and h lies below the tangent
    line at each endpoint where the derivative h'(a) = sum_y (w1_y - w0_y) log2 m_y is finite."""
    def mix(a):
        A = iv.mpf(a)
        return [A * iv.mpf(x) + (1 - A) * iv.mpf(y) for x, y in zip(w0, w1)]
    def Hm(a):
        return H_iv(mix(a))
    lo = min(Hm(a_lo).a, Hm(a_hi).a)
    def dH(a):
        s = iv.mpf(0)
        for (x, y), m in zip(zip(w0, w1), mix(a)):
            if x != y:
                if m.a <= 0:
                    return None
                s += iv.mpf(y - x) * iv.log(m) / LN2
        return s
    cands = []
    dl, dh = dH(a_lo), dH(a_hi)
    width = iv.mpf(a_hi) - iv.mpf(a_lo)
    if dl is not None:
        cands.append(Hm(a_lo) + iv.mpf(max(dl.b, mp.mpf(0))) * width)
    if dh is not None:
        cands.append(Hm(a_hi) + iv.mpf(max((-dh).b, mp.mpf(0))) * width)
    if not cands:   # both endpoints on the boundary of the simplex: use the global bound log2(ny)
        hi = iv.log(iv.mpf(len(w0))) / LN2
        return iv.mpf([lo, hi.b])
    hi = min(c.b for c in cands)
    return iv.mpf([lo, hi])


def psi_minus_L_ub(Wm, L, al, ah, bl, bh):
    """Upper bound of psi(a,b) - bilinear_L(a,b) on the box (interval arithmetic)."""
    A = iv.mpf([al, ah]); B = iv.mpf([bl, bh])
    Hw = {k: H_iv_point(v) for k, v in Wm.items()}
    I1 = (B * (Hmix_rng(al, ah, Wm[(0, 0)], Wm[(1, 0)]) - A * Hw[(0, 0)] - (1 - A) * Hw[(1, 0)])
          + (1 - B) * (Hmix_rng(al, ah, Wm[(0, 1)], Wm[(1, 1)]) - A * Hw[(0, 1)] - (1 - A) * Hw[(1, 1)]))
    I2 = (A * (Hmix_rng(bl, bh, Wm[(0, 0)], Wm[(0, 1)]) - B * Hw[(0, 0)] - (1 - B) * Hw[(0, 1)])
          + (1 - A) * (Hmix_rng(bl, bh, Wm[(1, 0)], Wm[(1, 1)]) - B * Hw[(1, 0)] - (1 - B) * Hw[(1, 1)]))
    Lb = (A * B * L[0][0] + A * (1 - B) * L[0][1] + (1 - A) * B * L[1][0] + (1 - A) * (1 - B) * L[1][1])
    return (I1 + I2 - Lb).b


def certify_eps(Wm, L, tol, max_boxes=400000):
    """Rigorous upper bound on max_{[0,1]^2} (psi - L): B&B until max UB - best LB <= tol."""
    z, o = mp.mpf(0), mp.mpf(1)
    heap = [(-psi_minus_L_ub(Wm, L, z, o, z, o), z, o, z, o)]
    best_lb = mp.mpf(-10)
    n = 0
    while n < max_boxes:
        nub, al, ah, bl, bh = heapq.heappop(heap)
        ub = -nub
        am, bm = (al + ah) / 2, (bl + bh) / 2
        pt = psi_minus_L_ub(Wm, L, am, am, bm, bm)   # point value (upper end of tiny interval)
        best_lb = max(best_lb, pt)
        if ub - best_lb <= tol:
            heapq.heappush(heap, (nub, al, ah, bl, bh)); break
        n += 1
        if ah - al >= bh - bl:
            kids = [(al, am, bl, bh), (am, ah, bl, bh)]
        else:
            kids = [(al, ah, bl, bm), (al, ah, bm, bh)]
        for kk in kids:
            heapq.heappush(heap, (-psi_minus_L_ub(Wm, L, *kk), *kk))
    return -heap[0][0], best_lb, n


def verify_majorization(Wm, L, eps_target, min_width=mp.mpf("1e-9")):
    """Rigorously verify psi(a,b) - L(a,b) <= eps_target on [0,1]^2 by interval bisection.
    Returns (True, #boxes processed) or raises if some box of width < min_width cannot be verified."""
    z, o = mp.mpf(0), mp.mpf(1)
    stack = [(z, o, z, o)]
    n = 0
    while stack:
        al, ah, bl, bh = stack.pop()
        n += 1
        if n % 20000 == 0:
            print(f"      verify_majorization: {n} boxes processed, {len(stack)} pending", flush=True)
        if psi_minus_L_ub(Wm, L, al, ah, bl, bh) <= eps_target:
            continue
        if max(ah - al, bh - bl) < min_width:
            raise RuntimeError(f"cannot verify box [{al},{ah}]x[{bl},{bh}]")
        if ah - al >= bh - bl:
            am = (al + ah) / 2; stack += [(al, am, bl, bh), (am, ah, bl, bh)]
        else:
            bm = (bl + bh) / 2; stack += [(al, ah, bl, bm), (al, ah, bm, bh)]
    return True, n


def certified_bound(W_exact, alpha, L, r, eps_target):
    """W_exact: dict (x1,x2) -> list of mpf output probabilities.
    Verifies psi <= L + eps_target on [0,1]^2, then returns (UB, eps_target, #boxes) with
    UB = max_x [alpha (L(x) + eps_target) + (1 - alpha) D(W_x || r)] in interval arithmetic."""
    Lm = [[mp.mpf(repr(float(L[i, j]))) for j in range(2)] for i in range(2)]
    eps = mp.mpf(eps_target)
    ok, nbox = verify_majorization(W_exact, Lm, eps)
    al = iv.mpf(mp.mpf(repr(float(alpha))))
    rr = [iv.mpf(mp.mpf(repr(float(x)))) for x in r]
    s = sum(rr, iv.mpf(0))
    rr = [x / s for x in rr]
    vals = []
    for (x1, x2), w in W_exact.items():
        D = iv.mpf(0)
        for wy, ry in zip(w, rr):
            if wy > 0:
                D += iv.mpf(wy) * (iv.log(iv.mpf(wy)) - iv.log(ry)) / LN2
        vals.append(al * (Lm[x1][x2] + eps) + (1 - al) * D)
    return max(v.b for v in vals), eps, nbox
