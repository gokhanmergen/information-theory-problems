# Reviewer check (2026-11-27): float BSSC sum-rate bounds on a 200001-point envelope grid: UV,
# Geng's functional (GLN eq. (15)) at J = BSC(0.1), BSC(0.189987), BSC(0.3), and Marton (RTD), in bits.
# Run: python3 bssc_float.py
# Runtime: about 3 s. Needs numpy.
# float sanity check of BSSC sum-rate bounds quoted in the broadcast-channel attempt (bits)
import numpy as np
N = 200001
p = np.linspace(0, 1, N)  # p = P(X=1)


def h(q):
    q = np.clip(q, 1e-300, 1)
    r = np.clip(1 - q, 1e-300, 1)
    return -(q * np.log2(q) + r * np.log2(r))


# T_Y: X=0 -> uniform, X=1 -> 1 ; T_Z: X=0 -> 0, X=1 -> uniform  (GLN Fig. 2)
IY = h((1 - p) * 0.5 + p) - (1 - p) * 1.0
IZ = h(p * 0.5) - p * 1.0


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


mid = N // 2
UV = 0.5 * IY + 0.5 * IZ + 0.5 * uce(IY - IZ) + 0.5 * uce(IZ - IY)
print("UV sum-rate at p=1/2: %.9f   max over p: %.9f" % (UV[mid], UV.max()))


def SRJ(d):
    IJ = h(p * (1 - d) + (1 - p) * d) - h(np.full(N, d))
    t = (0.5 * IY + 0.5 * uce(IY - IJ + 2 * uce(IJ - IY))
         + 0.5 * IZ + 0.5 * uce(IZ - IJ + 2 * uce(IJ - IZ)))
    return t[mid], t.max()


for d in [0.1, 0.189986556858845, 0.3]:
    print("Geng functional at J=BSC(%.6f): at p=1/2 %.9f ; max_p %.9f" % ((d,) + SRJ(d)))
M = 0.5 * IY + 0.5 * IZ + 0.5 * uce(np.maximum(IY - IZ, IZ - IY))
print("Marton (RTD) sum-rate at p=1/2 with envelope: %.9f" % M[mid])
