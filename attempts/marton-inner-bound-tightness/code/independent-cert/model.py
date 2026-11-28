#!/usr/bin/env python3
"""Shared exact data and objective decomposition for the independent certificate of
HLL (arXiv:2608.19869v1) eq. (25):  B_T := max_{P_UVX} G_T  <=  target_B  (= G_T(19) + ~5e-7).

All constants are the decimals printed in HLL (14)-(17), (19), read as exact rationals.  They are
taken from ../hll_check.py (the earlier attempt's transcription, itself cross-checked against the
arXiv PDF by the reviewer, see ../review/indep_check.out) and re-asserted here.

Objective (nats).  With alpha = alpha_0 of (17), abar = 1 - alpha:
  G(P_UVX) = -alpha H(Y) - abar H(Z) + I(U;Y) + I(V;Z) - I(U;V) + sum_x p(x) a_x
           = abar H(Y) + alpha H(Z) + H(U,V) - H(U,Y) - H(V,Z) + sum_x p(x) a_x .
For X = f(U,V) with U,V binary, every entropy is a sum of h(t) = -t ln t (concave) or
g(t) = t ln t (convex) of a nonnegative linear form t = c.p of the 4-vector p = P_UV
(cells ordered (u,v) = 00, 01, 10, 11), plus a linear term.  A Model lists these pieces:
  G(p) = sum_j w_j h(c_j . p) + sum_k w_k g(d_k . p) + lin . p ,   w > 0, c, d >= 0.
"""
from __future__ import annotations

import importlib.util
import itertools
import os
from dataclasses import dataclass
from fractions import Fraction as Fr

HERE = os.path.dirname(os.path.abspath(__file__))

TY_S = [["0.385361043864", "0.358548005177", "0.256090950959"],
        ["0.790302113033", "0.091025394735", "0.118672492232"],
        ["0.113168779849", "0.520687239901", "0.366143980250"]]
TZ_S = [["0.390396602690", "0.207292393713", "0.402311003597"],
        ["0.293627666338", "0.040944965497", "0.665427368165"],
        ["0.396880111705", "0.507497881167", "0.095622007128"]]
PSTAR_S = ["0.704504835923", "0.172563088231", "0.122932075846"]
ALPHA_S = "0.546388044486"
AVEC_S = ["0", "-0.393210549796", "-0.149290191142"]
# HLL (19): X = f(U,V) = [[0,1],[2,0]], P_UV = [[p00,p01],[p10,p11]]
F19 = (0, 1, 2, 0)
P19_S = ["0.013502132210", "0.172563088231", "0.122932075846", "0.691002703713"]
UB25_S = "0.0916508833913554746710"      # HLL printed (25)


def _crosscheck_with_hll_check():
    """Reuse: assert the constants equal those in the earlier attempt's ../hll_check.py."""
    path = os.path.join(HERE, "..", "hll_check.py")
    if not os.path.exists(path):
        return False
    src = open(path, encoding="utf-8").read()
    ns: dict = {}
    # execute only the constant block (avoids importing scipy/mpmath)
    start = src.index("TY = [[")
    stop = src.index("TABLE = [")
    exec(src[start:stop], ns)  # noqa: S102  (our own repository file)
    assert ns["TY"] == TY_S and ns["TZ"] == TZ_S and ns["PSTAR"] == PSTAR_S
    assert ns["ALPHA"] == ALPHA_S and ns["AVEC"] == AVEC_S
    return True


CROSSCHECKED = _crosscheck_with_hll_check()

TY = [[Fr(x) for x in r] for r in TY_S]
TZ = [[Fr(x) for x in r] for r in TZ_S]
ALPHA = Fr(ALPHA_S)
ABAR = 1 - ALPHA
AVEC = [Fr(x) for x in AVEC_S]
PSTAR = [Fr(x) for x in PSTAR_S]
P19 = [Fr(x) for x in P19_S]
for _M in (TY, TZ):
    for _r in _M:
        assert sum(_r) == 1 and min(_r) > 0
assert sum(P19) == 1 and sum(PSTAR) == 1


@dataclass(frozen=True)
class Model:
    name: str
    n: int                                   # number of coordinates (4 cells, or 3 for p_X)
    h_terms: tuple                           # ((w, (c_0..c_{n-1})), ...)  w*h(c.p), h=-t ln t
    g_terms: tuple                           # ((w, (d_0..)), ...)          w*g(d.p), g=t ln t
    lin: tuple                               # exact rationals, or None entries resolved later
    lin_entropy_rows: tuple = ()             # superposition: lin_i = a_i - H(row_i); rows here


def map_model(f) -> Model:
    f = tuple(f)
    cells = [(0, 0), (0, 1), (1, 0), (1, 1)]
    h = []
    for y in range(3):
        h.append((ABAR, tuple(TY[f[i]][y] for i in range(4))))
    for z in range(3):
        h.append((ALPHA, tuple(TZ[f[i]][z] for i in range(4))))
    for j in range(4):
        h.append((Fr(1), tuple(Fr(int(i == j)) for i in range(4))))
    g = []
    for u in range(2):
        for y in range(3):
            g.append((Fr(1), tuple(TY[f[i]][y] if cells[i][0] == u else Fr(0) for i in range(4))))
    for v in range(2):
        for z in range(3):
            g.append((Fr(1), tuple(TZ[f[i]][z] if cells[i][1] == v else Fr(0) for i in range(4))))
    lin = tuple(AVEC[f[i]] for i in range(4))
    return Model("map_" + "".join(map(str, f)), 4, tuple(h), tuple(g), lin)


def superposition_model(side: str) -> Model:
    """side 'u': U = X, V const.  G = abar H(Y) - abar H(Z) - H(Y|X) + a.p
       side 'v': V = X, U const.  G = alpha H(Z) - alpha H(Y) - H(Z|X) + a.p"""
    if side == "u":
        h = tuple((ABAR, tuple(TY[x][y] for x in range(3))) for y in range(3))
        g = tuple((ABAR, tuple(TZ[x][z] for x in range(3))) for z in range(3))
        rows = tuple(tuple(TY[x]) for x in range(3))
    else:
        h = tuple((ALPHA, tuple(TZ[x][z] for x in range(3))) for z in range(3))
        g = tuple((ALPHA, tuple(TY[x][y] for x in range(3))) for y in range(3))
        rows = tuple(tuple(TZ[x]) for x in range(3))
    return Model("superposition_" + side, 3, h, g, tuple(AVEC), rows)


def orbit_representatives():
    """The 81 maps f:{0,1}^2->{0,1,2} modulo relabelling U (swap rows) and V (swap columns).
    G is invariant under these relabellings, so one representative per orbit suffices."""
    reps, seen = [], set()
    for f in itertools.product(range(3), repeat=4):
        orb = {f, (f[2], f[3], f[0], f[1]), (f[1], f[0], f[3], f[2]), (f[3], f[2], f[1], f[0])}
        key = min(orb)
        if key not in seen:
            seen.add(key)
            reps.append((key, sorted(orb)))
    return reps


if __name__ == "__main__":
    reps = orbit_representatives()
    print("constants cross-checked with ../hll_check.py:", CROSSCHECKED)
    print("orbits:", len(reps), " covering", sum(len(o) for _, o in reps), "maps")
