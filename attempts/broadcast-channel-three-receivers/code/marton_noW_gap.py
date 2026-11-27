"""
Certified gap between the superposition-coding (capacity) region and Marton's
private-message region WITHOUT a superposition variable (time-sharing Q allowed)
for the degraded broadcast channel of Gohari--El Gamal--Anantharam
(arXiv:1006.5166v2, proof of Claim 1):

    X -> Y : BSC(0.3)
    Y -> Z : P(Z=0|Y=0)=0.6, P(Z=1|Y=0)=0.4, P(Z=0|Y=1)=0, P(Z=1|Y=1)=1.

Hence the marginal X -> Z channel is P(Z=0|X=0)=0.42, P(Z=0|X=1)=0.18.

Quantities (all in bits):
  F_alpha := max_{V -> X} I(X;Y|V) + alpha I(V;Z)               (capacity side)
  S_alpha := sup_{p(u,v,x)} I(U;Y) + alpha I(V;Z) - I(U;V)      (Marton without W)

The attempt file proves (analytically) that for alpha >= 1
  * S_alpha is attained with |U|,|V| <= |X| = 2 and X = f(U,V) deterministic;
  * the maps f that depend on a single variable or are constant are bounded
    analytically by max(C_Y, alpha*C_Z) (given alpha*eta_TV(X->Z) <= 1).
This script
  (1) computes a lower bound F_lo <= F_alpha from an explicit p(v,x) using
      mpmath interval arithmetic (rigorous);
  (2) certifies S_alpha <= tau < F_lo by simplicial branch and bound over the
      3-simplex of p(u,v) for the 7 orbit representatives of the 16 maps
      f:{0,1}^2 -> {0,1} under relabelling of U- and V-values (G is invariant),
      so all 16 maps are covered and the analytic bounds for the single-variable
      maps are cross-checked rather than relied upon;
      the bound on a simplex S with centroid c is
         max_{vertices w of S} [ sum_k a_k CE(q_k(w) || q_k(c)) + Psi(w) ],
      where the concave part Phi = sum_k a_k H(q_k(p)) (a_k >= 0, q_k linear in
      p) is bounded by its tangent plane at c (cross-entropy), and the convex
      part Psi = -H(UY) - alpha H(VZ) plus the linear tangent is convex, so its
      maximum over S is attained at a vertex;
  (3) re-verifies every accepted leaf simplex in mpmath interval arithmetic,
      so floating-point rounding cannot invalidate the certificate.

Usage:  python marton_noW_gap.py [alpha] [comma-separated orbit names]
        (default alpha = 2.4; all 7 orbit representatives)
"""
import sys, itertools, time
import numpy as np
from scipy.optimize import minimize
import mpmath
from mpmath import iv

ALPHA = float(sys.argv[1]) if len(sys.argv) > 1 else 2.4
LN2 = np.log(2.0)

# ---------------------------------------------------------------- channel
WY = np.array([[0.7, 0.3], [0.3, 0.7]])           # rows x, cols y
WZY = np.array([[0.6, 0.4], [0.0, 1.0]])          # rows y, cols z
WZ = WY @ WZY                                     # [[0.42,0.58],[0.18,0.82]]

def h2(t):
    t = np.clip(np.asarray(t, float), 1e-300, 1.0)
    s = np.clip(1.0 - t, 1e-300, 1.0)
    return -(t*np.log2(t) + s*np.log2(s))

# ------------------------------------------------- capacity side (float)
def cap_functional(alpha):
    """max over |V|=2 of I(X;Y|V)+alpha I(V;Z); returns (value, (a,s0,s1))
    with P(V=1)=a, P(X=1|V=v)=s_v.  |V|=2 suffices for this 1-D concave
    envelope (Caratheodory), but we only need a LOWER bound here anyway."""
    zy = lambda s: 0.3 + 0.4*s          # P(Y=1) = 0.3(1-s)+0.7 s
    zz = lambda s: 0.58 + 0.24*s        # P(Z=1)
    g = lambda s: h2(zy(s)) - alpha*h2(zz(s))
    def val(a, s0, s1):
        return (1-a)*g(s0) + a*g(s1) + alpha*h2(zz((1-a)*s0 + a*s1)) - h2(0.3)
    S = np.linspace(0, 1, 201)
    A = np.linspace(0, 1, 101)
    s0, s1, a = np.meshgrid(S, S, A, indexing='ij')
    V = val(a, s0, s1)
    i = np.unravel_index(np.argmax(V), V.shape)
    x0 = np.array([A[i[2]], S[i[0]], S[i[1]]])
    r = minimize(lambda z: -val(*np.clip(z, 0, 1)), x0, method='Nelder-Mead',
                 options=dict(xatol=1e-13, fatol=1e-15, maxiter=20000))
    z = np.clip(r.x, 0, 1)
    return float(val(*z)), tuple(float(t) for t in z)

def iv_H(ps):
    """interval entropy (bits) of a list of interval probabilities (>0 or exactly 0)."""
    out = iv.mpf(0)
    for p in ps:
        if p == 0:
            continue
        out -= p * iv.log(p)
    return out / iv.log(2)

def cap_lower_bound_interval(alpha, a, s0, s1):
    """Rigorous interval value of I(X;Y|V)+alpha I(V;Z) at the given rational point."""
    iv.prec = 80
    al = iv.mpf(str(alpha))
    one = iv.mpf(1)
    a, s0, s1 = iv.mpf(a), iv.mpf(s0), iv.mpf(s1)
    py = lambda s: iv.mpf('0.3') + iv.mpf('0.4')*s
    pz = lambda s: iv.mpf('0.58') + iv.mpf('0.24')*s
    HYgX = iv_H([iv.mpf('0.3'), iv.mpf('0.7')])
    HYgV = (one-a)*iv_H([py(s0), one-py(s0)]) + a*iv_H([py(s1), one-py(s1)])
    HZgV = (one-a)*iv_H([pz(s0), one-pz(s0)]) + a*iv_H([pz(s1), one-pz(s1)])
    sbar = (one-a)*s0 + a*s1
    HZ = iv_H([pz(sbar), one-pz(sbar)])
    return (HYgV - HYgX) + al*(HZ - HZgV), (HYgV - HYgX), (HZ - HZgV)

# --------------------------------------------- Marton-without-W objective
# p is a length-4 vector p[2u+v] = P(U=u, V=v);  map f given by bits f[2u+v].
def build_linear_maps(f):
    """Return the linear maps p -> distributions of Y, Z, V, (U,V), (U,Y), (V,Z)."""
    AX_u = np.zeros((2, 2, 4)); AX_v = np.zeros((2, 2, 4))   # p(u,x), p(v,x)
    for u, v in itertools.product(range(2), range(2)):
        k = 2*u + v; x = f[k]
        AX_u[u, x, k] += 1; AX_v[v, x, k] += 1
    AUY = np.einsum('uxk,xy->uyk', AX_u, WY).reshape(4, 4)   # rows (u,y)
    AVZ = np.einsum('vxk,xz->vzk', AX_v, WZ).reshape(4, 4)   # rows (v,z)
    AY = AUY.reshape(2, 2, 4).sum(0)
    AZ = AVZ.reshape(2, 2, 4).sum(0)
    AV = np.zeros((2, 4))
    for u, v in itertools.product(range(2), range(2)):
        AV[v, 2*u+v] = 1
    AUV = np.eye(4)
    return AY, AZ, AV, AUV, AUY, AVZ

def G_value(p, f, alpha):
    AY, AZ, AV, AUV, AUY, AVZ = build_linear_maps(f)
    def H(q):
        q = q[q > 0]; return -np.sum(q*np.log2(q))
    return (H(AY@p) + alpha*H(AZ@p) + (alpha-1)*H(AV@p) + H(AUV@p)
            - H(AUY@p) - alpha*H(AVZ@p))

class Bounder:
    """Float64 vectorized simplex bound (used to drive the search)."""
    def __init__(self, f, alpha):
        self.f = f; self.alpha = alpha
        AY, AZ, AV, AUV, AUY, AVZ = build_linear_maps(f)
        self.conc = [(1.0, AY), (alpha, AZ), (alpha-1.0, AV), (1.0, AUV)]
        self.conv = [(1.0, AUY), (alpha, AVZ)]

    def bound(self, W):
        """W: (4 vertices, 4 coords). Upper bound of G over conv(W)."""
        c = W.mean(0)
        tot = np.zeros(W.shape[0])
        for a, A in self.conc:
            if a == 0: continue
            qc = A @ c; qw = W @ A.T                 # (4 vertices, dim)
            lq = np.where(qc > 0, np.log2(np.where(qc > 0, qc, 1.0)), 0.0)
            tot += a * (-(qw * lq).sum(1))
        for a, A in self.conv:
            qw = W @ A.T
            ent = -np.where(qw > 0, qw*np.log2(np.where(qw > 0, qw, 1.0)), 0.0).sum(1)
            tot -= a * ent
        return tot.max()

def iv_bound(f, alpha, W):
    """Same bound as Bounder.bound but in interval arithmetic with exact
    (rational-dyadic) vertex coordinates -> rigorous upper bound."""
    al = iv.mpf(repr(alpha))          # interval enclosing the exact decimal alpha
    conc = [(iv.mpf(1), 'Y'), (al, 'Z'), (al - 1, 'V'), (iv.mpf(1), 'UV')]
    conv = [(iv.mpf(1), 'UY'), (al, 'VZ')]
    WYi = [[iv.mpf('0.7'), iv.mpf('0.3')], [iv.mpf('0.3'), iv.mpf('0.7')]]
    WZi = [[iv.mpf('0.42'), iv.mpf('0.58')], [iv.mpf('0.18'), iv.mpf('0.82')]]
    def dists(p):
        # p: list of 4 interval probs p[2u+v]
        pux = [[iv.mpf(0)]*2 for _ in range(2)]; pvx = [[iv.mpf(0)]*2 for _ in range(2)]
        for u, v in itertools.product(range(2), range(2)):
            k = 2*u+v; x = f[k]
            pux[u][x] += p[k]; pvx[v][x] += p[k]
        puy = [pux[u][0]*WYi[0][y] + pux[u][1]*WYi[1][y] for u in range(2) for y in range(2)]
        pvz = [pvx[v][0]*WZi[0][z] + pvx[v][1]*WZi[1][z] for v in range(2) for z in range(2)]
        py = [puy[0+y] + puy[2+y] for y in range(2)]
        pz = [pvz[0+z] + pvz[2+z] for z in range(2)]
        pv = [p[0+v] + p[2+v] for v in range(2)]
        # exact-zero bookkeeping: a coordinate is structurally zero iff it is
        # a sum of zero p-entries (channel entries are all > 0)
        return dict(Y=py, Z=pz, V=pv, UV=list(p), UY=puy, VZ=pvz)
    def is_zero(x):
        return x.a == 0 and x.b == 0
    def ent(q):
        s = iv.mpf(0)
        for t in q:
            if is_zero(t): continue
            s -= t*iv.log(t)
        return s/iv.log(2)
    def xent(q, r):
        s = iv.mpf(0)
        for t, rr in zip(q, r):
            if is_zero(t): continue
            if is_zero(rr): raise ValueError('support violation')
            s -= t*iv.log(rr)
        return s/iv.log(2)
    nv = len(W)
    Wiv = [[iv.mpf(mpmath.mpf(float(x))) for x in w] for w in W]   # exact dyadics
    cen = [sum(Wiv[i][k] for i in range(nv))/nv for k in range(4)]
    dc = dists(cen)
    best = None
    for w in Wiv:
        dw = dists(w)
        tot = iv.mpf(0)
        for a, key in conc:
            tot += a*xent(dw[key], dc[key])
        for a, key in conv:
            tot -= a*ent(dw[key])
        best = tot if best is None else iv.mpf([max(best.a, tot.a), max(best.b, tot.b)])
    return best.b   # upper end

def certify_map(f, alpha, tau, max_leaves=2_000_000, verify_iv=True):
    B = Bounder(f, alpha)
    root = np.eye(4)
    stack = [root]
    leaves = []; nbox = 0; worst = -np.inf
    while stack:
        S = stack.pop(); nbox += 1
        b = B.bound(S)
        if b <= tau - 1e-9:
            leaves.append(S); worst = max(worst, b)
            continue
        # bisect longest edge (midpoints of dyadic coordinates stay dyadic)
        best = (-1, None)
        for i in range(4):
            for j in range(i+1, 4):
                d = np.abs(S[i]-S[j]).sum()
                if d > best[0]: best = (d, (i, j))
        if best[0] < 1e-7:
            raise RuntimeError(f'map {f}: cannot certify near {S.mean(0)}, bound {b}')
        i, j = best[1]; m = 0.5*(S[i]+S[j])
        S1 = S.copy(); S1[i] = m
        S2 = S.copy(); S2[j] = m
        stack.append(S1); stack.append(S2)
        if nbox > max_leaves:
            raise RuntimeError('too many simplices')
    ivworst = None
    if verify_iv:
        iv.prec = 60
        ivworst = max(float(iv_bound(f, alpha, S)) for S in leaves)
        if not ivworst <= tau:
            raise RuntimeError(f'interval re-verification failed for map {f}: {ivworst}')
    return len(leaves), nbox, worst, ivworst

# Orbit representatives of the 16 maps f:{0,1}^2->{0,1} under relabelling of the
# values of U and of V (which leaves G unchanged: G(p, f o sigma) = G(p o sigma, f)).
# f is listed as (f(0,0), f(0,1), f(1,0), f(1,1)).
ORBIT_REPS = {
    'const0': (0, 0, 0, 0), 'const1': (1, 1, 1, 1),
    'X=U': (0, 0, 1, 1), 'X=V': (0, 1, 0, 1),
    'XOR': (0, 1, 1, 0), 'AND': (0, 0, 0, 1), 'OR': (0, 1, 1, 1),
}

def orbit_of(f):
    out = set()
    for su in (0, 1):
        for sv in (0, 1):
            out.add(tuple(f[2*(u ^ su) + (v ^ sv)] for u in range(2) for v in range(2)))
    return out

def capacity_side(alpha):
    F, (a, s0, s1) = cap_functional(alpha)
    # decimal strings: iv.mpf(str) gives an interval enclosing the exact decimal value
    ar, s0r, s1r = (str(round(t, 4)) for t in (a, s0, s1))
    val, R1, R2 = cap_lower_bound_interval(repr(alpha), ar, s0r, s1r)
    return F, (ar, s0r, s1r), val, R1, R2

if __name__ == '__main__':
    t0 = time.time()
    alpha = ALPHA
    which = sys.argv[2].split(',') if len(sys.argv) > 2 else list(ORBIT_REPS)
    assert set().union(*(orbit_of(f) for f in ORBIT_REPS.values())) == \
        {tuple((i >> k) & 1 for k in range(4)) for i in range(16)}
    print(f'alpha = {alpha};  W_Z = {WZ.tolist()}')
    CY = 1 - float(h2(0.3))
    s = np.linspace(0, 1, 1000001)
    IZ = h2(0.58 + 0.24*s) - ((1-s)*h2(0.58) + s*h2(0.82))
    CZ = float(IZ.max()); sz = float(s[IZ.argmax()])
    print(f'C_Y = {CY:.10f}, C_Z ~= {CZ:.10f} at P(X=1)={sz:.5f}, alpha*C_Z ~= {alpha*CZ:.10f}')
    F, (ar, s0r, s1r), val, R1, R2 = capacity_side(alpha)
    print(f'F_alpha (float search) = {F:.10f}')
    print(f'rational superposition point: P(V=1)={ar}, P(X=1|V=0)={s0r}, P(X=1|V=1)={s1r}')
    print(f'  R1 = I(X;Y|V)       in {R1}\n  R2 = I(V;Z)         in {R2}\n  R1 + alpha*R2       in {val}')
    F_lo = float(mpmath.mpf(val.a))
    tau = F_lo - 1e-7
    print(f'certifying G <= tau = {tau:.10f} on the 3-simplex for maps {which}')
    for name in which:
        f = ORBIT_REPS[name]
        t1 = time.time()
        n, nb, worst, ivw = certify_map(f, alpha, tau)
        print(f'  {name:6s} f={f} (orbit size {len(orbit_of(f))}): {n} leaf simplices '
              f'({nb} visited); max float bound {worst:.9f}; max interval bound {ivw:.9f}  '
              f'[{time.time()-t1:.0f}s]', flush=True)
    print(f'DONE: on the maps above, S_alpha <= {tau:.10f} < {F_lo:.10f} <= F_alpha '
          f'({time.time()-t0:.0f}s)')
