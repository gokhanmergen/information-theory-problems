# Reviewer check (2026-11-27, Claim 6): the attempt's term-by-term tangency coefficient table,
# recomputed with sympy.
# Run: python3 tangency_table.py
# Runtime: under 1 s. Needs sympy. The printed rows agree once the leftover logs are expanded
# by hand (log((1-p)^2) = 2 log(1-p), log(2p - p^2) = log p + log(2 - p)).
"""Check the attempt's term-by-term tangency table (Claim 6): coefficients of ln2, ln p, ln(1-2p),
ln(1-p), ln(2-p) in f(p,qh)-f(p,0) and in qh*f_q(p,qh), qh = 1-2p, everything in nats."""
import sympy as sp

p, q = sp.symbols('p q', positive=True)
L2, Lp, L1m2p, L1mp, L2mp = sp.symbols('L2 Lp L1m2p L1mp L2mp')


def h(x):
    return -x * sp.log(x) - (1 - x) * sp.log(1 - x)


f = (2 * p - 1) * h(q) - 2 * p * h((1 + q) / 2) + h(q + (1 - q) * p / 2) + p * (1 - q) * sp.log(2)
fq = sp.diff(f, q)
qh = 1 - 2 * p
f0 = h(p / 2) - 2 * p * sp.log(2) + p * sp.log(2)          # f(p,0) in nats
lhs = f.subs(q, qh) - f0
rhs = qh * fq.subs(q, qh)

def to_basis(e):
    e = sp.expand_log(sp.expand(e), force=True)
    # rewrite composite logs into the basis
    rep = {sp.log(1 - 2 * p): L1m2p, sp.log(1 - p): L1mp, sp.log(2 - p): L2mp, sp.log(p): Lp, sp.log(2): L2}
    e = e.subs({sp.log(-p + 1): L1mp, sp.log(-2 * p + 1): L1m2p, sp.log(-p + 2): L2mp})
    e = e.subs(rep)
    # remaining logs like log(1 - p/2) = log(2-p) - log 2 ; log(p**2-2p+1) = 2 log(1-p) ; log(p*(2-p))
    e = e.subs({sp.log(1 - p / 2): L2mp - L2, sp.log(-p / 2 + 1): L2mp - L2, sp.log(p / 2): Lp - L2})
    return sp.expand(e)

for name, e in [("LHS", lhs), ("RHS", rhs)]:
    E = to_basis(e)
    leftover = E.atoms(sp.log)
    print(name, "leftover logs:", leftover)
    for sym in (L2, Lp, L1m2p, L1mp, L2mp):
        print("   ", sym, ":", sp.factor(sp.expand(E.coeff(sym))))
    print("    const:", sp.simplify(E.subs({L2: 0, Lp: 0, L1m2p: 0, L1mp: 0, L2mp: 0})))
