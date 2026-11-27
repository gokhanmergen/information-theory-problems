# Reviewer check (2026-11-27, Claim 6): the attempt's k = 2 closed form F vs the behavioural evaluator,
# and F <= Phi, at 2000 random points (seed 5).
# Run: python3 check_k2_closed_form.py
# Runtime: a few seconds. Needs numpy, scipy.
"""Check the attempt's k=2 closed form F (Details sec. 6) against the independent behavioural
evaluator, and check the majorant F <= Phi (with M = exact max of y h(x)+x h(y) = 2 g*)."""
import os, sys
import numpy as np
from scipy.optimize import minimize_scalar
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from behav import Evaluator, h2

E = Evaluator(2)
idx = E.nidx
rng = np.random.default_rng(5)
h = lambda p: float(h2(np.array(p)))
gstar = -minimize_scalar(lambda x: -x * h(x), bounds=(0.5, 0.9), method="bounded",
                         options={"xatol": 1e-13}).fun
M = 2 * gstar


def psi(g):
    if g <= 0:
        return 0.0
    c = 1 / (1 + 2 ** (-h(g) / g))
    return g * h(c) + c * h(g)


maxdiff = 0; viol = 0
for _ in range(2000):
    a, g1, f0, f1, b, g2, e0, e1 = rng.uniform(0, 1, 8)
    b1 = np.zeros(len(E.nodes)); b2 = np.zeros(len(E.nodes))
    b1[idx[()]] = a; b1[idx[((0, 0),)]] = g1; b1[idx[((1, 0),)]] = f0; b1[idx[((1, 1),)]] = f1
    b2[idx[()]] = b; b2[idx[((0, 0),)]] = g2; b2[idx[((1, 0),)]] = e0; b2[idx[((1, 1),)]] = e1
    c = (1 - a) * g1 + a * f0; cp = (1 - b) * g2 + b * e0
    F = (b * h(a) + a * h(b) + (1 - b) * g2 * h(c) + a * (1 - b) * f0 * h(g2)
         + (1 - a) * g1 * h(cp) + b * (1 - a) * e0 * h(g1) + a * b * (e1 * h(f1) + f1 * h(e1)))
    maxdiff = max(maxdiff, abs(F - E.F(b1, b2)))
    Phi = (b * h(a) + a * h(b) + M * a * b + (1 - b) * psi(g2) + (1 - a) * psi(g1)
           - (1 - a) * (1 - b) * (g1 * h(g2) + g2 * h(g1)))
    viol += F > Phi + 1e-12
print("max |closed form - behavioural evaluator| over 2000 random points:", maxdiff)
print("violations of F <= Phi:", viol)
print("4 g* =", 4 * gstar)
