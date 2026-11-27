#!/usr/bin/env python3
"""Numerical evaluation of the compress-and-forward (CF) rate of the primitive
relay channel with BSC components (floating point; HEURISTIC, not certified).

Model: X ~ Bern(pi) (pi = P(X=1)), Y = X + Bern(p1) (destination),
Yr = X + Bern(p2) (relay), conditionally independent given X.

For fixed pi the CF rate (either the "classic" form max I(X;Y,U) s.t.
I(U;Yr|Y) <= R0, or the min-form used in problems/primitive-relay-channel-bsc.md;
they coincide because I(U;X|Y) <= I(U;Yr|Y)) equals I(X;Y) + g_pi(R0), where

    g_pi(R) = sup { I(U;X|Y) : U - Yr - (X,Y), I(U;Yr|Y) <= R }.

Writing theta_u = P(Yr=1 | U=u), both I(U;X|Y) and I(U;Yr|Y) are averages over u
of functions of theta_u, so by Lagrange duality

    g_pi(R) = inf_{lam >= 0} [ lam R + Env_{theta_bar}( a - lam b ) ],

where a(theta) = H(X|Y)|_{theta_bar} - H(X|Y)|_theta, b likewise with Yr, and
Env is the upper concave envelope evaluated at theta_bar = P(Yr=1).  The
envelope at a point is computed as  inf_mu max_theta [F(theta) - mu (theta -
theta_bar)]  on a fine theta grid.  Everything here is floating point and grid
based: the outputs are numerical evidence only.

Usage:
  python3 cf_dual.py <p1> <p2> <R0,R0,...>     # CF at uniform and optimized pi
"""
from __future__ import annotations

import sys

import numpy as np
from scipy.optimize import minimize_scalar


def h(x):
    x = np.clip(x, 1e-300, 1 - 1e-16)
    return -(x * np.log2(x) + (1 - x) * np.log2(1 - x))


def _H(P, axis):
    P = np.clip(P, 1e-300, None)
    return -(P * np.log2(P)).sum(axis=axis)


def cond_entropies(pi, p1, p2, theta):
    """Return (H(X|Y), H(Yr|Y)) when Yr ~ Bern(theta) and X|Yr is the true
    posterior under input bias pi, Y|X ~ BSC(p1)."""
    px = np.array([1 - pi, pi])
    Pr_x = np.array([[1 - p2, p2], [p2, 1 - p2]])  # [x, yr]
    Py_x = np.array([[1 - p1, p1], [p1, 1 - p1]])  # [x, y]
    Pxr = px[:, None] * Pr_x
    Pr = Pxr.sum(0)
    Px_r = Pxr / Pr[None, :]
    theta = np.asarray(theta, dtype=float)
    Pth = np.stack([1 - theta, theta], -1)
    J = Pth[..., None, None, :] * Px_r[None, :, None, :] * Py_x[None, :, :, None]
    Jxy = J.sum(-1)
    Jy = Jxy.sum(-2)
    Jyr = J.sum(-3)
    A = _H(Jxy, (-1, -2)) - _H(Jy, -1)
    B = _H(Jyr, (-1, -2)) - _H(Jy, -1)
    return A, B, Pr[1]


THETA = np.unique(np.concatenate([
    np.linspace(0.0, 1.0, 8001),
    np.logspace(-12, -1, 400),
    1 - np.logspace(-12, -1, 400),
]))


def _envelope_at(F, theta_bar):
    f = lambda mu: float(np.max(F - mu * (THETA - theta_bar)))
    return minimize_scalar(f, bounds=(-200, 200), method="bounded",
                           options={"xatol": 1e-10}).fun


def g_cf(pi, p1, p2, R):
    A, B, tb = cond_entropies(pi, p1, p2, THETA)
    A0, B0, _ = cond_entropies(pi, p1, p2, np.array([tb]))
    a = A0[0] - A
    b = B0[0] - B
    dual = lambda lam: lam * R + _envelope_at(a - lam * b, tb)
    return minimize_scalar(dual, bounds=(0.0, 1.5), method="bounded",
                           options={"xatol": 1e-9}).fun


def mi_xy(pi, p1):
    return float(h(pi * (1 - p1) + (1 - pi) * p1) - h(p1))


def cf_rate(pi, p1, p2, R):
    return mi_xy(pi, p1) + g_cf(pi, p1, p2, R)


def cf_rate_opt(p1, p2, R):
    """Maximize over pi in [0.2,0.5] (the channel is symmetric under pi->1-pi)."""
    res = minimize_scalar(lambda pi: -cf_rate(pi, p1, p2, R), bounds=(0.2, 0.5),
                          method="bounded", options={"xatol": 1e-5})
    return -res.fun, res.x


if __name__ == "__main__":
    p1, p2 = float(sys.argv[1]), float(sys.argv[2])
    for R in (float(x) for x in sys.argv[3].split(",")):
        best, pi_star = cf_rate_opt(p1, p2, R)
        print(f"R0={R:.4f}  CF(uniform)={cf_rate(0.5, p1, p2, R):.7f}  "
              f"CF(opt pi)={best:.7f}  pi*={pi_star:.4f}", flush=True)
