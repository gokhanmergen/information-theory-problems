#!/usr/bin/env python3
"""Independent rigorous branch-and-bound for HLL (arXiv:2608.19869v1) eq. (25).

Claim certified (if every job prints certified=True):
    G(p) < T   for every p in the closed simplex, for every map f:{0,1}^2->{0,1,2}
               (27 orbit representatives under U/V relabelling), and for the two
               one-sided branches (U=X,V const) and (V=X,U const) over p_X,
where T is a 1e-30-grid rational (the largest one below the lower endpoint of an arb enclosure;
conservative, not necessarily the largest grid rational) with  alpha H_{p*}(Y) + abar H_{p*}(Z) + T - a.p*
<= 0.0916508833913554746710  (HLL's printed (25)), computed with outward-rounded arb.

Arithmetic.  Box corners are exact integers / 2^D.  Linear forms c.p (c has denominator
10^12) are evaluated *exactly* with Python integers; only logarithms use python-flint arb
(ball arithmetic, guaranteed enclosures), and every quantity entering the final bound is an
upper endpoint of a ball.  No floating point is used anywhere in the proof path.

Box bound (difference-of-concave linearisation, then an exact LP):
  * h(t) = -t ln t (concave):  h(t) <= m - (1 + ln m) t  for all t >= 0 and any m > 0
    (tangent at m; valid also at t = 0).  m = midpoint of the exact range of t on the box.
  * g(t) = t ln t (convex):  on [t1,t2] (exact range of t on the box),
    g(t) <= A + (B - A)(t - t1)/(t2 - t1)  for any A >= g(t1), B >= g(t2)  (chord).
  * The resulting affine function of p (coefficients replaced by upper endpoints; legal since
    p >= 0) is maximised exactly over {lo <= p <= hi, sum p = 1} by the greedy (fractional
    knapsack) rule with exact comparisons.
The domain is the closed simplex: both linearisations remain valid at t = 0 (h(0)=g(0)=0), so
no boundary cutoff or face recursion is needed.  Boxes are split at the midpoint of the
longest side of the bounds-consistent hull; coverage holds by construction (a box is either
proved < T or split into two boxes whose union contains it).

Usage:
  python -I bnb_rigorous.py --job map:0120 [--max-nodes N]
  python -I bnb_rigorous.py --all --procs 5 --out results.json
  negative control (must FAIL, since G(19) > T):
  python -I bnb_rigorous.py --job map:0120 --target -1064713410442773850/1000000000000000000 --max-nodes 2000000
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from fractions import Fraction as Fr
from multiprocessing import Pool

from flint import arb, ctx, fmpq

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import model as M  # noqa: E402

ctx.prec = 128
D = 160                       # box coordinates are integers / 2^D
ONE = 1 << D
SCALE = 10 ** 12              # every coefficient c_i is an integer / 10^12



def _check(cond, msg):
    """Soundness check that, unlike `assert`, survives `python -O`."""
    if not cond:
        raise RuntimeError("soundness check failed: " + msg)

def A(q: Fr) -> arb:
    return arb(fmpq(q.numerator, q.denominator))


def up(x: arb) -> arb:
    """Exact upper endpoint of a ball (an arb with zero radius)."""
    return x.upper()


def lo_end(x: arb) -> arb:
    return x.lower()


def ln_ball(q: Fr) -> arb:
    return A(q).log()


def g_upper(t: Fr) -> arb:
    """exact point >= t ln t (t >= 0 exact rational)."""
    if t == 0:
        return arb(0)
    return up(A(t) * ln_ball(t))


def h_upper(t: Fr) -> arb:
    if t == 0:
        return arb(0)
    return up(-(A(t) * ln_ball(t)))


# ---------------------------------------------------------------- exact target T
def entropy_upper(dist) -> arb:
    s = arb(0)
    for t in dist:
        if t:
            s += -(A(t) * ln_ball(t))
    return up(s)


def entropy_lower(dist) -> arb:
    s = arb(0)
    for t in dist:
        if t:
            s += -(A(t) * ln_ball(t))
    return lo_end(s)


def compute_target():
    pY = [sum(M.PSTAR[x] * M.TY[x][y] for x in range(3)) for y in range(3)]
    pZ = [sum(M.PSTAR[x] * M.TZ[x][z] for x in range(3)) for z in range(3)]
    ap = sum(M.AVEC[x] * M.PSTAR[x] for x in range(3))
    # (25) holds iff  T <= UB25 - alpha H(Y*) - abar H(Z*) + a.p* ; take a lower endpoint
    rhs = A(Fr(M.UB25_S)) - A(M.ALPHA) * entropy_upper(pY) - A(M.ABAR) * entropy_upper(pZ) + A(ap)
    rlo = rhs.lower()
    # round down to a 1e-30 grid rational (exact): T = floor(rlo * 1e30) / 1e30
    tq = _floor_to_grid(rlo, 10 ** 30)
    _check(A(tq) <= rlo, "target T does not imply (25)")
    return tq


def _floor_to_grid(x_point: arb, den: int) -> Fr:
    """Largest k/den with k/den <= x (x an exact point)."""
    y = x_point * den
    k = int(y.floor().unique_fmpz())
    while A(Fr(k, den)) > x_point:          # never triggers for exact points; defensive
        k -= 1
    return Fr(k, den)


def g_at_point_lower(f, P) -> arb:
    """Lower endpoint of G at an exact point for a map model (used for G(19))."""
    mdl = M.map_model(f)
    s = arb(0)
    for w, c in mdl.h_terms:
        t = sum(ci * pi for ci, pi in zip(c, P))
        if t:
            s += A(w) * (-(A(t) * ln_ball(t)))
    for w, c in mdl.g_terms:
        t = sum(ci * pi for ci, pi in zip(c, P))
        if t:
            s += A(w) * (A(t) * ln_ball(t))
    s += A(sum(li * pi for li, pi in zip(mdl.lin, P)))
    return s


# ---------------------------------------------------------------- compiled model
class Compiled:
    def __init__(self, mdl: M.Model):
        self.name = mdl.name
        self.n = mdl.n
        def comp(terms):
            out = []
            for w, c in terms:
                C = tuple(int(ci * SCALE) for ci in c)
                _check(all(Fr(Ci, SCALE) == ci for Ci, ci in zip(C, c)), "coefficient not exact over 10^12")
                if any(C):
                    out.append((A(w), C, tuple(A(ci) for ci in c)))
            return out
        self.h = comp(mdl.h_terms)
        self.g = comp(mdl.g_terms)
        lin = []
        for i, li in enumerate(mdl.lin):
            v = A(li)
            if mdl.lin_entropy_rows:            # superposition: a_i - H(row_i), upper endpoint
                v = v - entropy_lower(mdl.lin_entropy_rows[i])
            lin.append(up(v))
        self.lin = lin


def tighten(lo, hi):
    slo, shi = sum(lo), sum(hi)
    if slo > ONE or shi < ONE:
        return None
    nlo = [max(l, ONE - (shi - h)) for l, h in zip(lo, hi)]
    nhi = [min(h, ONE - (slo - l)) for l, h in zip(lo, hi)]
    if any(a > b for a, b in zip(nlo, nhi)):
        return None
    return nlo, nhi


def lp_int(C, lo, hi, maximize):
    """exact extreme of sum C_i p_i over {lo<=p<=hi, sum p = ONE}; integers -> integer."""
    order = sorted(range(len(C)), key=lambda i: C[i], reverse=maximize)
    cap = ONE - sum(lo)
    val = sum(c * l for c, l in zip(C, lo))
    for i in order:
        if cap == 0:
            break
        inc = min(hi[i] - lo[i], cap)
        val += C[i] * inc
        cap -= inc
    _check(cap == 0, "LP capacity not exhausted")
    return val


def lp_arb(W, lo, hi):
    """max sum W_i p_i over the box slice; W_i exact arb points; returns exact upper point."""
    order = sorted(range(len(W)), key=lambda i: W[i].mid(), reverse=True)
    # exact ordering check: ties/near-ties are resolved by exact comparison below
    for a, b in zip(order, order[1:]):
        if W[a] < W[b]:
            raise ArithmeticError("ordering")
    cap = ONE - sum(lo)
    p = list(lo)
    for i in order:
        if cap == 0:
            break
        inc = min(hi[i] - p[i], cap)
        p[i] += inc
        cap -= inc
    _check(cap == 0, "LP capacity not exhausted")
    s = arb(0)
    for w, pi in zip(W, p):
        if pi:
            s += w * arb(fmpq(pi, ONE))
    return up(s)


def box_upper(cm: Compiled, lo, hi) -> arb:
    n = cm.n
    const = arb(0)
    coef = [arb(0)] * n
    den = SCALE * ONE
    for w, C, cA in cm.h:
        t1 = lp_int(C, lo, hi, False)
        t2 = lp_int(C, lo, hi, True)
        if t2 == 0:
            continue                                   # t == 0 on the box: h = 0
        if t1 == t2:
            const += w * h_upper(Fr(t1, den))
            continue
        m = Fr(t1 + t2, 2 * den)
        lm = ln_ball(m)
        const += w * A(m)
        slope = -(1 + lm)                              # coefficient of t
        for i in range(n):
            if C[i]:
                coef[i] = coef[i] + up(w * slope * cA[i])
    for w, C, cA in cm.g:
        t1 = lp_int(C, lo, hi, False)
        t2 = lp_int(C, lo, hi, True)
        T1, T2 = Fr(t1, den), Fr(t2, den)
        Aup = g_upper(T1)
        if t1 == t2:
            const += w * Aup
            continue
        Bup = g_upper(T2)
        s_up = up((Bup - Aup) / A(T2 - T1))
        const += w * (Aup - s_up * A(T1))
        for i in range(n):
            if C[i]:
                coef[i] = coef[i] + up(w * s_up * cA[i])
    W = [up(coef[i] + cm.lin[i]) for i in range(n)]
    return up(const) + lp_arb(W, lo, hi)


def certify(cm: Compiled, T: Fr, max_nodes: int, report_every: int = 0):
    Tq = A(T)
    root = tighten([0] * cm.n, [ONE] * cm.n)
    stack = [(root[0], root[1], 0)]
    nodes = leaves = 0
    max_depth = 0
    worst = None                     # largest proved upper bound among leaves
    t0 = time.time()
    while stack:
        lo, hi, d = stack.pop()
        nodes += 1
        if nodes > max_nodes:
            return dict(certified=False, reason="max_nodes", nodes=nodes, leaves=leaves,
                        max_depth=max_depth, open_boxes=len(stack) + 1)
        ub = box_upper(cm, lo, hi)
        if ub < Tq:
            leaves += 1
            if worst is None or ub > worst:
                worst = ub
            continue
        widths = [b - a for a, b in zip(lo, hi)]
        ax = max(range(cm.n), key=lambda i: (widths[i], -i))
        if widths[ax] < 2:
            return dict(certified=False, reason="unsplittable", nodes=nodes, leaves=leaves,
                        lo=[str(x) for x in lo], hi=[str(x) for x in hi])
        mid = (lo[ax] + hi[ax]) // 2
        for left in (False, True):
            nlo, nhi = list(lo), list(hi)
            if left:
                nhi[ax] = mid
            else:
                nlo[ax] = mid
            ch = tighten(nlo, nhi)
            if ch is not None:
                stack.append((ch[0], ch[1], d + 1))
                max_depth = max(max_depth, d + 1)
        if report_every and nodes % report_every == 0:
            print(f"  {cm.name}: nodes={nodes} stack={len(stack)} {time.time()-t0:.0f}s", flush=True)
    return dict(certified=True, nodes=nodes, leaves=leaves, max_depth=max_depth,
                worst_leaf_upper=float(worst.mid()) if worst is not None else None,
                margin_to_T=float((Tq - worst).mid()) if worst is not None else None)


def run_job(args):
    job, T, max_nodes = args
    kind, key = job.split(":")
    if kind == "map":
        mdl = M.map_model(tuple(int(ch) for ch in key))
    else:
        mdl = M.superposition_model(key)
    cm = Compiled(mdl)
    t0 = time.time()
    res = certify(cm, T, max_nodes)
    res.update(job=job, seconds=round(time.time() - t0, 1))
    print(json.dumps(res), flush=True)
    return res


def all_jobs():
    jobs = []
    for rep, orb in M.orbit_representatives():
        jobs.append(("map:" + "".join(map(str, rep)), orb))
    jobs.append(("sup:u", None))
    jobs.append(("sup:v", None))
    return jobs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--job")
    ap.add_argument("--all", action="store_true")
    ap.add_argument("--procs", type=int, default=4)
    ap.add_argument("--max-nodes", type=int, default=40_000_000)
    ap.add_argument("--out")
    ap.add_argument("--target", help="override T (exact fraction string); for negative controls")
    a = ap.parse_args()
    T = Fr(a.target) if a.target else compute_target()
    G19 = g_at_point_lower(M.F19, M.P19)
    print("T =", T, "~", float(T))
    print("G(19) enclosure =", G19)
    print("T - G(19) =", (A(T) - G19))
    jobs = [a.job] if a.job else [j for j, _ in all_jobs()]
    done = {}
    if a.out and os.path.exists(a.out):
        prev = json.load(open(a.out))
        if prev.get("T") != f"{T.numerator}/{T.denominator}":
            raise SystemExit(f"refusing to resume: {a.out} was produced for T={prev.get('T')}, "
                             f"not the current T={T.numerator}/{T.denominator}")
        done = {r["job"]: r for r in prev["results"] if r.get("certified")}
        jobs = [j for j in jobs if j not in done]
        print("resuming;", len(done), "jobs already certified")
    t0 = time.time()
    results = list(done.values())
    with Pool(a.procs) as pool:
        for r in pool.imap_unordered(run_job, [(j, T, a.max_nodes) for j in jobs]):
            results.append(r)
            if a.out:
                json.dump(dict(T=f"{T.numerator}/{T.denominator}", results=results),
                          open(a.out, "w"), indent=1)
    ok = all(r["certified"] for r in results)
    print("ALL CERTIFIED" if ok else "NOT ALL CERTIFIED", "jobs", len(results),
          "nodes", sum(r["nodes"] for r in results), "time %.0fs" % (time.time() - t0))


if __name__ == "__main__":
    main()
