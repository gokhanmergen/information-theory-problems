# Reviewer check (2026-11-27, Claim 6, heuristic): 801 x 801 grid of coded-swap splits vs the best
# single split, TDM and TIN for P in {30, 100, 1000} (lower bounds only).
# Run: python3 swap_scan.py
# Runtime: about 1 s. Needs numpy.
# Reviewer spot-check of Claim 6 coded-swap values (lower bounds only).
import numpy as np
C = lambda x: 0.5 * np.log2(1 + x)


def terms(s, p, v1, v2):
    u1, u2 = p - v1, p - v2
    N1, N2 = 1 + s * v2, 1 + s * v1
    A1, A2 = C(p / N1), C(p / N2)
    all1, all2 = C((p + s * u2) / N1), C((p + s * u1) / N2)
    pr1, pr2 = C(v1 / N1), C(v2 / N2)
    pc1, pc2 = C((v1 + s * u2) / N1), C((v2 + s * u1) / N2)
    return np.stack([A1, A2, all1 + pr2, all2 + pr1, pc1 + pc2, all1 + pr1 + pc2, all2 + pr2 + pc1])


def g(T):
    A1, A2, S1, S2, S3, D1, D2 = T
    return np.minimum.reduce([A1 + A2, S1, S2, S3, (A1 + D2) / 2, (D1 + A2) / 2, (D1 + D2) / 3])


for P in (30., 100., 1000.):
    for a in (0.4, 0.5, 0.6, np.sqrt(.5), 0.8):
        s = a * a
        f = np.linspace(0, 1, 801)
        F1, F2 = np.meshgrid(f, f, indexing='ij')
        cod = g(0.5 * (terms(s, P, F1 * P, F2 * P) + terms(s, P, F2 * P, F1 * P)))
        nots = g(terms(s, P, F1 * P, F2 * P))
        i, j = np.unravel_index(np.argmax(cod), cod.shape)
        print(f"P={P:g} a={a:.4f}: coded swap {cod[i, j]:.4f} at ({f[i]:.4f},{f[j]:.4f}); "
              f"best single split {nots.max():.4f}; TDM C(2P)={C(2 * P):.4f}; TIN {2 * C(P / (1 + s * P)):.4f}")
