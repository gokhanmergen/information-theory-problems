#!/usr/bin/env python3
"""Energy per bit of block-linear relaying (EMZ 2006 Sec. V; Kosut-Effros-Langberg 2024 eq. (6)).
Heuristic local search only: it gives UPPER bounds on E*_lin and proves nothing about its value.

Companion code for
  attempts/gaussian-relay-channel-capacity/2026-11-27-claude-opus-5-5-egn-low-snr-slope.md

Model (EMZ normalisation): Yr = a X + Zr, Y = X + b Xr + Z, unit noises.  A k-dimensional linear
code uses a Gaussian source vector with covariance Sigma and relay output Xr = D Yr with D strictly
lower triangular.  Its energy per bit is
  E(Sigma, D) = tr(Sigma + a^2 D Sigma D^T + D D^T) /
                ( 1/2 log2 det((I+abD) Sigma (I+abD)^T + I + b^2 D D^T) - 1/2 log2 det(I + b^2 D D^T) ),
and E*_lin = inf over k, Sigma, D (KEL eq. (6)).  Normalised by 2 ln 2 (direct transmission = 1).

Sections:
  L1  a = b = 1: best value found for k = 1..6 (rank-1 and full-rank Sigma), many random starts.
  L2  a = 1, continuation in b from 1.6 down to 1.0 for k in {4, 6, 8, 12} (rank-1 Sigma):
      the smallest b at which linear relaying beats direct transmission decreases with k.
Expected (2026-11-27 run): L1 gives 1.00000 for every k; in L2 values < 1 appear down to
b = 1.05 at k = 12 (0.99999), and every k gives >= 1 at b = 1.0.

Run:  python3 lr_energy.py     (about 10-20 min)
Requires numpy, scipy.
"""
import numpy as np
from scipy.optimize import minimize

LN2 = np.log(2)


def E(params, k, a, b, rank1):
    idx = np.tril_indices(k, -1)
    nD = len(idx[0])
    Dm = np.zeros((k, k))
    Dm[idx] = params[:nD]
    if rank1:
        s = params[nD:nD + k]
        Sig = np.outer(s, s)
    else:
        L = np.zeros((k, k))
        L[np.tril_indices(k)] = params[nD:]
        Sig = L @ L.T
    I = np.eye(k)
    num = np.trace(Sig + a * a * Dm @ Sig @ Dm.T + Dm @ Dm.T)
    A = I + a * b * Dm
    M1 = A @ Sig @ A.T + I + b * b * Dm @ Dm.T
    M2 = I + b * b * Dm @ Dm.T
    rate = 0.5 * (np.linalg.slogdet(M1)[1] - np.linalg.slogdet(M2)[1]) / LN2
    if rate <= 1e-300:
        return 1e9
    return num / rate / (2 * LN2)


def best(k, a, b, rank1=True, starts=60, seed=0):
    rng = np.random.default_rng(seed)
    nD = k * (k - 1) // 2
    nS = k if rank1 else k * (k + 1) // 2
    bv, bx = np.inf, None
    for _ in range(starts):
        x0 = np.r_[rng.normal(size=nD) * np.exp(rng.normal()),
                   rng.normal(size=nS) * np.exp(rng.normal() * 1.5)]
        r = minimize(lambda x: E(x, k, a, b, rank1), x0, method="BFGS", options={"maxiter": 5000})
        if r.fun < bv:
            bv, bx = r.fun, r.x
    return bv, bx


def L1():
    print("L1: a = b = 1, best E/(2 ln 2) found")
    for k in range(1, 7):
        v1, _ = best(k, 1.0, 1.0, True)
        vf = best(k, 1.0, 1.0, False)[0] if k <= 4 else float("nan")
        print(f"  k={k}: rank-1 {v1:.5f}   full-rank {vf:.5f}", flush=True)


def L2():
    print("L2: a = 1, continuation in b (rank-1), best E/(2 ln 2) found")
    for k in [4, 6, 8, 12]:
        v, x = best(k, 1.0, 1.6, True, starts=30, seed=k)
        out = [(1.6, round(v, 6))]
        for b in [1.4, 1.3, 1.2, 1.15, 1.1, 1.05, 1.0]:
            r = minimize(lambda z: E(z, k, 1.0, b, True), x, method="BFGS",
                         options={"maxiter": 20000, "gtol": 1e-10})
            x = r.x
            out.append((b, round(r.fun, 6)))
        print(f"  k={k}: " + ", ".join(f"b={bb}: {vv}" for bb, vv in out), flush=True)


if __name__ == "__main__":
    L1()
    L2()
