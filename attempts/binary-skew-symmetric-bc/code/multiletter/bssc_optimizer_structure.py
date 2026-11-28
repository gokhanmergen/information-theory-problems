#!/usr/bin/env python3
"""
Structure of the near-optimal two-letter BSSC dual distributions at (alpha, a) = (1/2, 0):
for every map class whose best mirror-ascent value is within TOL of 2 B_1, report
  I(X1;X2)  (0 for product inputs),  I(U;V|X1X2)  (0 = Markov U - X - V),
  the input marginals P(X1=1), P(X2=1)  (one-letter optimiser q* = 0.15843 or 1 - q*).

Usage: python bssc_optimizer_structure.py [B] [iters] [seed]
"""
import sys
import numpy as np
from ml_core import bssc, B1, canonical_maps, TwoLetterDual, mirror_ascent, ent

TOL = 1e-7


def main():
    B = int(sys.argv[1]) if len(sys.argv) > 1 else 32
    iters = int(sys.argv[2]) if len(sys.argv) > 2 else 2000
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 5
    TY, TZ = bssc()
    target = 2 * B1(TY, TZ, 0.5, [0, 0])
    rng = np.random.default_rng(seed)
    worst = (0.0, 0.0)
    n_att = 0
    for nu, nv in ((2, 3), (3, 2)):
        maps = canonical_maps(nu, nv)
        D = TwoLetterDual(TY, TZ, 0.5, [0, 0], maps)
        G, P = mirror_ascent(D, B, iters, rng)
        for m in range(len(maps)):
            b = int(np.argmax(G[m]))
            if G[m, b] < target - TOL:
                continue
            n_att += 1
            F, p = maps[m], P[m, b]
            PX = np.zeros(4)
            PUVX = np.zeros((nu, nv, 4))
            for u in range(nu):
                for v in range(nv):
                    PX[F[u, v]] += p[u, v]
                    PUVX[u, v, F[u, v]] = p[u, v]
            PX12 = PX.reshape(2, 2)
            IX = ent(PX12.sum(1)) + ent(PX12.sum(0)) - ent(PX)
            # I(U;V|X) = H(UX)+H(VX)-H(UVX)-H(X)
            IUVX = (ent(PUVX.sum(1).ravel()) + ent(PUVX.sum(0).ravel()) - ent(PUVX.ravel()) - ent(PX))
            worst = (max(worst[0], IX), max(worst[1], IUVX))
            print("%d%d f=%s  G-2B1=%+.1e  I(X1;X2)=%.1e  I(U;V|X)=%.1e  P(X1=1)=%.5f P(X2=1)=%.5f"
                  % (nu, nv, F.ravel().tolist(), G[m, b] - target, IX, IUVX, PX12[1].sum(), PX12[:, 1].sum()))
    print("near-optimal classes: %d ; max I(X1;X2) = %.2e ; max I(U;V|X) = %.2e" % (n_att, *worst))


if __name__ == "__main__":
    main()
