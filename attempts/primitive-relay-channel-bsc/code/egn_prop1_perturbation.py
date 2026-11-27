#!/usr/bin/env python3
"""HEURISTIC first-order check for EGN Proposition 1 (arXiv:2101.11139) on the
symmetric BSC primitive relay (rho = 0.1, uniform X).  Proposition 1 reads
  C <= max_{p(x)p(v|x,z)} min{ I(X;Y) + a1, I(X;Y) + R0 - b1 },
  a1 = I(X;V|Y) - I(V;X|Z),   b1 = I(V;Z|X),   (Z = relay output Yr).
Around a chain V - X - Z (where a1 = b1 = 0) we perturb p(v|x,z) = q(v|x) +
eps r(v|x,z) and observe a1 = Theta(eps), b1 = Theta(eps^2); choosing
eps ~ R0 then gives a Proposition-1 value 1-h(rho) + R0 - O(R0^2), i.e. slope 1
at R0 = 0 (cited in the Dead ends section of the attempt).
"""
import numpy as np

rho = 0.1
W = np.array([[1 - rho, rho], [rho, 1 - rho]])


def H(P):
    P = P[P > 0]
    return -(P * np.log2(P)).sum()


def a1_b1(Pv_xz):
    J = 0.5 * W[:, :, None, None] * W[:, None, :, None] * Pv_xz[:, None, :, :]  # [x,y,z,v]
    Pxyv, Pxzv = J.sum(2), J.sum(1)
    Pxv, Pyv, Pzv = J.sum((1, 2)), J.sum((0, 2)), J.sum((0, 1))
    Pxy, Pxz = J.sum((2, 3)), J.sum((1, 3))
    Px, Py, Pz = J.sum((1, 2, 3)), J.sum((0, 2, 3)), J.sum((0, 1, 3))
    I_xv_y = H(Pxy) + H(Pyv) - H(Pxyv) - H(Py)
    I_vx_z = H(Pxz) + H(Pzv) - H(Pxzv) - H(Pz)
    I_vz_x = H(Pxz) + H(Pxv) - H(Pxzv) - H(Px)
    return I_xv_y - I_vx_z, I_vz_x


q = np.array([[0.8, 0.2], [0.3, 0.7]])            # q[x, v]
base = np.repeat(q[:, None, :], 2, axis=1)         # [x, z, v]
r = np.array([[0.3, -0.2], [0.1, 0.25]])
r = np.stack([r, -r], -1)                          # rows sum to zero in v
for eps in (1e-1, 1e-2, 1e-3, 1e-4):
    a1, b1 = a1_b1(base + eps * r)
    print(f"eps={eps:g}: a1={a1:.4e}  b1={b1:.4e}  a1/b1={a1 / b1:.1f}")
