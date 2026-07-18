#!/usr/bin/env python3
"""Blahut-Arimoto bounds on C_n(d) = (1/n) max_p I(X^n; Y) for the binary
deletion channel, plus the derived rigorous bounds on C(d).

Facts used (both classical; see Dalai, ISIT 2011, Lemma 1, and
Fertonani-Duman, IEEE T-IT 2010, Sec. "markers" / survey eq. (16)):

  (U)  n C_n is subadditive, so C(d) = inf_n C_n(d) <= C_n(d) for every n.
  (L)  C(d) >= C_n(d) - H(Bin(n, 1-d))/n   (undeletable-marker genie).

Blahut-Arimoto gives, at every iteration with input distribution p and
induced output q_p:
  * I(p) <= n C_n            (any input distribution is admissible), and
  * n C_n <= max_x D(P(.|x) || q)  for ANY output distribution q
    (the minimax redundancy / capacity duality certificate),
so both an under- and an over-estimate of C_n with a certified gap, without
assuming convergence.  Combining:

  rigorous upper bound on C:   (1/n) max_x D(P(.|x) || q_p)
  rigorous lower bound on C:   (1/n) [ I(p) - H(Bin(n, 1-d)) ]

The channel matrix is exact: P(y|x) = N(x,y) d^(n-|y|) (1-d)^|y| with N the
embedding-count DP from exact_mi.py.

Usage: python3 ba_bounds.py [nmax]     (default 12; memory ~2^(2n+4) bytes)
Writes ba_results.json next to this file.
"""

import json
import sys
import time
from math import comb, log2
from pathlib import Path

import numpy as np

from exact_mi import embedding_counts


def binomial_entropy(n, p):
    """H(Bin(n, p)) in bits, exact enumeration."""
    probs = np.array([comb(n, k) * p ** k * (1 - p) ** (n - k)
                      for k in range(n + 1)])
    probs = probs[probs > 0]
    return float(-(probs * np.log2(probs)).sum())


def count_matrix(n):
    """Ncnt[x, col] = N(x, y) with columns enumerating y by length then value."""
    ncols = (1 << (n + 1)) - 1
    M = np.zeros((1 << n, ncols), dtype=np.uint32)
    offs = np.cumsum([0] + [1 << m for m in range(n + 1)])
    for x in range(1 << n):
        xbits = [(x >> (n - 1 - i)) & 1 for i in range(n)]
        A = embedding_counts(xbits, n)
        for m in range(n + 1):
            M[x, offs[m]:offs[m + 1]] = A[m]
    return M, offs


def ba_bounds(n, d, M, offs, tol=1e-6, max_iter=3000):
    """Return (I_lb, U_ub) in bits per channel use (not yet divided by n)."""
    ncols = M.shape[1]
    c = np.empty(ncols)
    for m in range(n + 1):
        c[offs[m]:offs[m + 1]] = d ** (n - m) * (1 - d) ** m
    P = M.astype(np.float64) * c[None, :]
    # rows sum to 1
    assert np.allclose(P.sum(axis=1), 1.0, atol=1e-12)
    # E[x] = sum_y P log2 P  (0 log 0 = 0)
    with np.errstate(divide="ignore", invalid="ignore"):
        PlogP = np.where(P > 0, P * np.log2(np.where(P > 0, P, 1.0)), 0.0)
    E = PlogP.sum(axis=1)
    nx = P.shape[0]
    p = np.full(nx, 1.0 / nx)
    I_lb = U_ub = None
    for it in range(max_iter):
        q = p @ P
        # Every y is a subsequence of some x, so mathematically q > 0, but
        # BA can drive some p(x) so small that q(y) underflows to 0 in
        # float64.  Clamp and renormalize: the dual upper bound
        # n C_n <= max_x D(P(.|x)||q) holds for ANY probability vector q,
        # so the clamped-and-renormalized q still yields a valid bound.
        q = np.maximum(q, 1e-300)
        q /= q.sum()
        D = E - P @ np.log2(q)
        I_lb = float(p @ D)
        U_ub = float(D.max())
        if U_ub - I_lb < tol:
            break
        # BA update: p <- p * 2^D / normalization (in log space for stability)
        w = D - D.max()
        p = p * np.exp2(w)
        p /= p.sum()
    return I_lb, U_ub, it + 1


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    ds = [0.1, 0.3, 0.5, 0.7, 0.9]
    res = {"ds": ds, "Cn": {}, "H_bin": {}}
    for n in range(1, nmax + 1):
        t0 = time.time()
        M, offs = count_matrix(n)
        row = {}
        hb = {}
        for d in ds:
            lb, ub, iters = ba_bounds(n, d, M, offs)
            row[d] = {"I_lb": lb, "maxD_ub": ub, "iters": iters}
            hb[d] = binomial_entropy(n, 1 - d)
        res["Cn"][n] = row
        res["H_bin"][n] = hb
        msg = f"n={n:2d} ({time.time()-t0:.1f}s)  "
        for d in ds:
            up = row[d]["maxD_ub"] / n
            lo = (row[d]["I_lb"] - hb[d]) / n
            msg += f" d={d}: C<= {up:.4f}, C>= {lo:.4f} |"
        print(msg)
    out = Path(__file__).parent / "ba_results.json"
    out.write_text(json.dumps(res, indent=1))
    print(f"wrote {out}")


if __name__ == "__main__":
    main()
