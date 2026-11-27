# Reviewer check (2026-11-27, items 5-6): independent box majorisation psi - bil(L) on N x N cells
# and the final UB1 in mpmath. The note's run used N = 8192 (log rev_k1_ub.log); the default is 8000.
# Run: python3 rev_k1_ub.py 8192
# Runtime: about 2 s at N = 8192. Needs numpy, mpmath.
"""Reviewer's independent check of the k=1 duality certificate for W_{1/2} (P(Y=1|x1,x2)=(x1+x2)/2).

Closed form (derived by the reviewer), a = P(X1=0), b = P(X2=0), g(t) = h(t/2) - t >= 0:
  psi(a,b) = I(X1;Y|X2) + I(X2;Y|X1) = b g(1-a) + (1-b) g(a) + a g(1-b) + (1-a) g(b).
Box bound (different method from cert_cl1.py): h(t/2) is increasing on [0,1], so on [a0,a1]x[b0,b1]
  g(a)   <= h(a1/2) - a0,          g(1-a) <= h((1-a0)/2) - (1-a1),   (same for b),
  all multipliers in [0,1] and bounded at the right end; bil(L) is bilinear => min at a corner.
h at grid nodes is computed in mpmath interval arithmetic (upper ends taken); the remaining
float64 arithmetic is a handful of operations per box, covered by a 1e-9 safety margin.
Then UB = max_x [alpha (L_x + eps) + (1-alpha) D(W_x||r)] in mpmath.
"""
import sys
import numpy as np
import mpmath as mp
from mpmath import iv

N = int(sys.argv[1]) if len(sys.argv) > 1 else 8000
EPS = 4e-3
alpha = mp.mpf("0.605")
L = {(0, 0): "0.30004610530312337", (0, 1): "0.9529406263243592",
     (1, 0): "0.9529406263243592", (1, 1): "0.3000500233786525"}
r = [mp.mpf("0.4999989600880894"), mp.mpf("0.5000010399119106")]
Lf = {k: float(v) for k, v in L.items()}

iv.dps = 30
def h_up(t):   # rigorous upper end of binary entropy h(t) (bits), t exact rational node
    if t <= 0 or t >= 1:
        return 0.0
    T = iv.mpf(t)
    v = (-(T * iv.log(T)) - (1 - T) * iv.log(1 - T)) / iv.log(2)
    return float(mp.mpf(v.b)) + 1e-15

nodes = [mp.mpf(i) / N for i in range(N + 1)]
hhalf = np.array([h_up(x / 2) for x in nodes])            # h(t/2) at t = i/N
hhalf_c = np.array([h_up((1 - x) / 2) for x in nodes])    # h((1-t)/2) at t = i/N
t = np.arange(N + 1) / N

worst = -1e9
lo, hi = t[:-1], t[1:]
# upper bounds of g(a), g(1-a) on each cell [lo_i, hi_i]
g_up = hhalf[1:] - lo                  # h(a1/2) - a0
gc_up = hhalf_c[:-1] - (1 - hi)        # h((1-a0)/2) - (1-a1)
for i in range(N):
    a0, a1 = lo[i], hi[i]
    b0, b1 = lo, hi
    psi_ub = (b1 * gc_up[i] + (1 - b0) * g_up[i] + a1 * gc_up + (1 - a0) * g_up)
    corners = []
    for aa in (a0, a1):
        for bb in (b0, b1):
            corners.append(aa * bb * Lf[(0, 0)] + aa * (1 - bb) * Lf[(0, 1)]
                           + (1 - aa) * bb * Lf[(1, 0)] + (1 - aa) * (1 - bb) * Lf[(1, 1)])
    bil_min = np.minimum(np.minimum(corners[0], corners[1]), np.minimum(corners[2], corners[3]))
    worst = max(worst, float(np.max(psi_ub - bil_min)))
print(f"N={N}: max over cells of (rigorous-ish) upper bound of psi - bil(L) = {worst:.6e}")
print("majorisation psi <= L + 4e-3 on [0,1]^2:", "VERIFIED" if worst + 1e-9 <= EPS else "NOT verified at this N")

# point estimate of the true max of psi - bil(L)
G = np.linspace(0, 1, 2001)
A, B = np.meshgrid(G, G, indexing="ij")
def h(x):
    x = np.clip(x, 1e-300, 1)
    return np.where((x > 0) & (x < 1), -x * np.log2(x) - (1 - x) * np.log2(np.clip(1 - x, 1e-300, 1)), 0.0)
g = lambda s: h(s / 2) - s
psi = B * g(1 - A) + (1 - B) * g(A) + A * g(1 - B) + (1 - A) * g(B)
bil = A * B * Lf[(0, 0)] + A * (1 - B) * Lf[(0, 1)] + (1 - A) * B * Lf[(1, 0)] + (1 - A) * (1 - B) * Lf[(1, 1)]
d = psi - bil
k = np.unravel_index(np.argmax(d), d.shape)
print(f"grid-2001 estimate of max(psi - bil(L)) = {d[k]:.3e} at a={G[k[0]]:.4f}, b={G[k[1]]:.4f}")

# final bound
Dx = {(0, 0): mp.log(1 / r[0], 2), (1, 1): mp.log(1 / r[1], 2),
      (0, 1): (mp.log(mp.mpf(1) / 2 / r[0], 2) + mp.log(mp.mpf(1) / 2 / r[1], 2)) / 2}
Dx[(1, 0)] = Dx[(0, 1)]
vals = {x: alpha * (mp.mpf(L[x]) + mp.mpf(EPS)) + (1 - alpha) * Dx[x] for x in L}
for x, v in vals.items():
    print("  x =", x, " alpha(L+eps)+(1-alpha)D =", mp.nstr(v, 15))
print("UB1 =", mp.nstr(max(vals.values()), 15))
