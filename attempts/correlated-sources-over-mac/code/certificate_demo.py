#!/usr/bin/env python3
"""Certificates for the lower semi-computability of rho*(P, W)
(attempt 2026-11-26-claude-opus-5-5-lower-semicomputability.md, Claims 3-4).

A certificate is a finite JSCC code (k, n, enc1, enc2, dec) with exact rational error
eps = jsccError(...) (same formula as the Lean `jsccError`), together with rational
lower bounds A1 <= C1, A2 <= C2 on the single-user capacities.  The bootstrap theorem
(Claim 3) gives

    rho* > r   whenever   r * (n + phi(eps) * (1/A1 + 1/A2)) < k,
    phi(eps) = h(eps) + eps * k * log2(|U| |V|).

This script
  (1) computes eps EXACTLY (fractions) for the uncoded k = n = 1 code on the
      Cover-El Gamal-Salehi example (eps = 0) and certifies rho* >= 1; together with
      the cooperative cut-set bound this gives rho* = 1 exactly (Claim 6);
  (2) on a noisy variant (adder MAC followed by a ternary symmetric channel with
      crossover 1/100), computes the exact error of the uncoded code with the MAP
      decoder and the resulting certified lower bound on rho*, and the cut-set upper
      bound for comparison.
The log-dependent comparisons are evaluated with mpmath at 50 digits; they are far
from equality, so the strict inequalities are certain.
Run: python3 certificate_demo.py
"""
from fractions import Fraction as F
from itertools import product
import mpmath as mp

mp.mp.dps = 50


def log2(x):
    return mp.log(x) / mp.log(2)


def h2(x):
    # Reviewer fix (2026-11-27): mpmath 1.3.0 cannot build an mpf from a Fraction.
    x = mp.mpf(x.numerator) / x.denominator if isinstance(x, F) else mp.mpf(x)
    return mp.mpf(0) if x in (0, 1) else -x * log2(x) - (1 - x) * log2(1 - x)


def jscc_error(P, W, k, n, enc1, enc2, dec, Ualph, Valph, Yalph):
    """Exact error: sum_s P^k(s) sum_y W^n(y | enc1(u), enc2(v)) [dec(y) != s]."""
    err = F(0)
    for s in product(list(P.keys()), repeat=k):
        ps = F(1)
        for z in s:
            ps *= P[z]
        if ps == 0:
            continue
        u = tuple(z[0] for z in s); v = tuple(z[1] for z in s)
        x1 = enc1(u); x2 = enc2(v)
        for y in product(Yalph, repeat=n):
            if dec(y) != (u, v):
                py = F(1)
                for i in range(n):
                    py *= W[(x1[i], x2[i])][y[i]]
                err += ps * py
    return err


def map_decoder(P, W, k, n, enc1, enc2, Yalph):
    """MAP decoder table for a given encoder pair (ties broken deterministically)."""
    table = {}
    blocks = list(product(list(P.keys()), repeat=k))
    for y in product(Yalph, repeat=n):
        best, bestv = None, F(-1)
        for s in blocks:
            ps = F(1)
            for z in s:
                ps *= P[z]
            u = tuple(z[0] for z in s); v = tuple(z[1] for z in s)
            x1 = enc1(u); x2 = enc2(v)
            py = F(1)
            for i in range(n):
                py *= W[(x1[i], x2[i])][y[i]]
            if ps * py > bestv:
                best, bestv = (u, v), ps * py
        table[y] = best
    return lambda y: table[y]


def mutual_info_uniform_pair(W, x_pair_fixed, which, Yalph):
    """I(X;Y) for X uniform on {0,1} at encoder `which`, other input fixed."""
    rows = []
    for x in (0, 1):
        key = (x, x_pair_fixed) if which == 1 else (x_pair_fixed, x)
        rows.append([mp.mpf(W[key][y].numerator) / W[key][y].denominator for y in Yalph])
    py = [(rows[0][j] + rows[1][j]) / 2 for j in range(len(Yalph))]
    I = mp.mpf(0)
    for r in rows:
        for j in range(len(Yalph)):
            if r[j] > 0:
                I += r[j] / 2 * log2(r[j] / py[j])
    return I


def cert_value(k, n, eps, A1, A2, nU, nV):
    phi = h2(eps) + mp.mpf(eps.numerator) / eps.denominator * k * log2(nU * nV)
    return k / (n + phi * (1 / A1 + 1 / A2))


def main():
    # Cover-El Gamal-Salehi example: (U,V) uniform on {(0,0),(0,1),(1,1)}, Y = X1 + X2.
    P = {(0, 0): F(1, 3), (0, 1): F(1, 3), (1, 1): F(1, 3)}
    Yalph = (0, 1, 2)
    Wadd = {(a, b): {y: F(int(a + b == y)) for y in Yalph} for a in (0, 1) for b in (0, 1)}
    enc1 = lambda u: u
    enc2 = lambda v: v
    dec_tab = {(0,): ((0,), (0,)), (1,): ((0,), (1,)), (2,): ((1,), (1,))}
    dec = lambda y: dec_tab[y]
    eps = jscc_error(P, Wadd, 1, 1, enc1, enc2, dec, (0, 1), (0, 1), Yalph)
    A1 = mutual_info_uniform_pair(Wadd, 0, 1, Yalph)
    A2 = mutual_info_uniform_pair(Wadd, 0, 2, Yalph)
    c = cert_value(1, 1, eps, A1, A2, 2, 2)
    HUV = log2(3)
    print("CES example: exact error of uncoded code =", eps, "; A1 =", mp.nstr(A1, 6),
          "A2 =", mp.nstr(A2, 6))
    print("  certificate: every rho < %s is transmissible  =>  rho* >= 1" % mp.nstr(c, 6))
    print("  cut-set: rho* <= max I(X1X2;Y)/H(U,V) <= log2(3)/log2(3) = %s" % mp.nstr(log2(3) / HUV, 6))

    # Noisy variant: adder output through a ternary symmetric channel, crossover 1/100.
    d = F(1, 100)
    T = {y: {z: (1 - d if z == y else d / 2) for z in Yalph} for y in Yalph}
    Wn = {(a, b): {z: sum(Wadd[(a, b)][y] * T[y][z] for y in Yalph) for z in Yalph}
          for a in (0, 1) for b in (0, 1)}
    decn = map_decoder(P, Wn, 1, 1, enc1, enc2, Yalph)
    epsn = jscc_error(P, Wn, 1, 1, enc1, enc2, decn, (0, 1), (0, 1), Yalph)
    A1n = mutual_info_uniform_pair(Wn, 0, 1, Yalph)
    A2n = mutual_info_uniform_pair(Wn, 0, 2, Yalph)
    cn = cert_value(1, 1, epsn, A1n, A2n, 2, 2)
    # cut-set upper bound: max_{p(x1,x2)} I(X1X2;Y) <= max over output dists = channel
    # capacity of the 4-input DMC (x1,x2) -> Y; for this symmetric ternary channel the
    # inputs (0,0),(0,1),(1,1) give the TSC, whose capacity is log2 3 - H(1-d, d/2, d/2).
    dm = mp.mpf(d.numerator) / d.denominator
    HT = -(1 - dm) * log2(1 - dm) - dm * log2(dm / 2)
    print("Noisy variant (TSC 1/100 after adder): exact MAP error of uncoded code =", epsn,
          "=", mp.nstr(mp.mpf(epsn.numerator) / epsn.denominator, 8))
    print("  A1 =", mp.nstr(A1n, 8), " A2 =", mp.nstr(A2n, 8))
    print("  certificate: rho* > %s" % mp.nstr(cn, 8))
    print("  cut-set:     rho* <= (log2 3 - H_T)/log2 3 = %s" % mp.nstr((log2(3) - HT) / HUV, 8))


if __name__ == '__main__':
    main()
