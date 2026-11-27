# Reviewer check (2026-11-27): coarse (sigma, gamma) grid for Geng's bound (GLN Thm 5, mu = 1) at
# J = BSC(0.189986556858845) on the BSSC; is sigma = 1, gamma = 1/2 the minimiser of max_p? Float, bits.
# Run: python3 geng_sigma.py
# Runtime: about 1 min (21 x 21 grid, pure-Python hulls). Needs numpy.
# Does the min over (sigma, gamma) in Geng's Theorem (GLN Thm 5, mu=1) go below the sigma=1, gamma=1/2
# specialisation (GLN eq. (15)) for the BSSC at J = BSC(0.189986556858845)?  float, bits.
import numpy as np
N = 40001
p = np.linspace(0, 1, N)


def h(q):
    q = np.clip(q, 1e-300, 1)
    r = np.clip(1 - q, 1e-300, 1)
    return -(q * np.log2(q) + r * np.log2(r))


IY = h((1 - p) * 0.5 + p) - (1 - p)
IZ = h(p * 0.5) - p


def uce(f):
    hull = []
    for i in range(N):
        while len(hull) >= 2:
            i1, i2 = hull[-2], hull[-1]
            if (f[i2] - f[i1]) * (p[i] - p[i1]) <= (f[i] - f[i1]) * (p[i2] - p[i1]):
                hull.pop()
            else:
                break
        hull.append(i)
    return np.interp(p, p[hull], f[hull])


d = 0.189986556858845
IJ = h(p * (1 - d) + (1 - p) * d) - h(np.full(N, d))


def val(s, g):
    gb = 1 - g
    return ((1 - s * g) * IY + (1 - s * gb) * IZ
            + uce(uce(s * IJ - IY) + s * g * (IY - IJ))
            + uce(uce(s * IJ - IZ) + s * gb * (IZ - IJ)))


best = None
for s in np.linspace(0.8, 1.0, 21):
    for g in np.linspace(0.3, 0.7, 21):
        v = val(s, g)
        m = v.max()
        if best is None or m < best[0]:
            best = (m, s, g, v[N // 2])
print("sigma=1,gamma=1/2: max_p %.9f" % val(1.0, 0.5).max())
print("min over grid of max_p (fixed sigma,gamma for all p): %.9f at sigma=%.3f gamma=%.3f (value at p=1/2: %.9f)" % best)
